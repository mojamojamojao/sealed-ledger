#!/usr/bin/env python3
"""Standalone third-party verifier for the sealed prediction ledger.

Ships with the public ledger repository (copied verbatim; stdlib only, no
project imports) so anyone can check, from bytes alone:

- every sealed JSON (schedule / race payloads / market-record hashes /
  manifest) recomputes to the sha256 the day manifest claims;
- every payload is bound to its day schedule and every day links to the
  previous sealed day's manifest (hash chain, genesis = 64 zeros);
- the declared race count matches schedule contents and the manifest's
  sealed+missing partition;
- calendar gaps between the first and last sealed day are listed (holes are
  part of the record, never hidden).

Usage:
    python verify_chain.py [--root DIR]   # DIR contains daily/<YYYYMMDD>/

Exit code 0 = every check passed; 1 = the ledger does not verify.
Output is ASCII only: a buyer whose console is cp932 (the Japanese Windows
default) must get a verdict, not a UnicodeEncodeError.

RFC 3161 responses (*.tsr) are checked separately with openssl (see the
verification page); this script is the hash-chain half.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from datetime import datetime, timedelta
from pathlib import Path

GENESIS = "0" * 64
DATE_DIR = re.compile(r"^\d{8}$")


def canonical_sha256(value: dict) -> str:
    text = json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def load(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def fail(message: str) -> None:
    print(f"NG: {message}")
    raise SystemExit(1)


def verify_day(day_dir: Path, expected_prev: str) -> str | None:
    date = day_dir.name
    schedule_path = day_dir / "schedule.json"
    if not schedule_path.exists():
        fail(f"{date}: schedule.json missing")
    schedule = load(schedule_path)
    schedule_sha = canonical_sha256(schedule)
    if schedule.get("date") != date:
        fail(f"{date}: schedule date field mismatch")
    if schedule.get("prev_day_manifest_sha256") != expected_prev:
        fail(f"{date}: previous-day chain link mismatch")
    declared = [str(r["race_id"]) for r in schedule.get("races", [])]
    deadlines = {
        str(r["race_id"]): str(r.get("deadline_jst") or "") for r in schedule.get("races", [])
    }
    if len(set(declared)) != schedule.get("race_count"):
        fail(f"{date}: race_count does not match declared races")

    payloads: dict[str, str] = {}
    markets: dict[str, str] = {}
    races_dir = day_dir / "races"
    if races_dir.exists():
        for path in sorted(races_dir.glob("*.json")):
            if path.name.endswith(".tsa_failed.json") or path.name.endswith(".tsr.json"):
                continue
            record = load(path)
            race_id = str(record.get("race_id"))
            is_market = path.name.endswith(".market.json")
            expected_name = f"{race_id}.market.json" if is_market else f"{race_id}.json"
            if path.name != expected_name:
                fail(f"{date}: file {path.name} carries race_id {race_id}")
            if race_id not in declared:
                fail(f"{date}: sealed race {race_id} is not on the schedule")
            if record.get("schedule_sha256") != schedule_sha:
                fail(f"{date}: {path.name} bound to a different schedule")
            if not is_market:
                # The promise: nothing is sealed after its deadline. Live seals
                # must be strictly earlier; retrospective days are rebuilt at
                # the betting close, so equality is expected there.
                as_of = str(record.get("as_of") or "")
                deadline = deadlines.get(race_id, "")
                if not as_of or not deadline:
                    fail(f"{date}: {race_id} has no as_of/deadline to check")
                if as_of > deadline or (
                    as_of == deadline and str(record.get("mode")) == "live"
                ):
                    fail(f"{date}: {race_id} sealed at {as_of}, not before deadline {deadline}")
            if not is_market:
                # Six lanes, no negatives, sums to one. Without this, a payload
                # whose numbers were garbage would still verify as long as its
                # hash matched. Tolerance 1e-5: live days round to exactly 1,
                # the retrospective days predate that rule and sit within 2e-6.
                for key in ("probabilities", "probabilities_raw", "probabilities_staged"):
                    vector = record.get(key)
                    if not vector:
                        continue
                    values = [float(value) for value in vector.values()]
                    if len(values) != 6:
                        fail(f"{date}: {race_id} {key} has {len(values)} lanes, not 6")
                    if any(value < 0.0 or value > 1.0 for value in values):
                        fail(f"{date}: {race_id} {key} has a value outside [0,1]")
                    if abs(sum(values) - 1.0) > 1e-5:
                        fail(f"{date}: {race_id} {key} sums to {sum(values):.9f}, not 1")
            digest = canonical_sha256(record)
            (markets if is_market else payloads)[race_id] = digest
    manifest_path = day_dir / "manifest.json"
    # The seal-time market records are withheld from publication (odds-board
    # redistribution is a pending legal question), but their hashes travel in
    # the manifest -- so the binding stays verifiable even when the plaintext
    # is absent: payload.market_sha256 must equal the manifest's entry.
    manifest_markets: dict[str, str] = {}
    if manifest_path.exists():
        manifest_markets = load(manifest_path).get("markets") or {}
    unbound: list[str] = []
    for race_id in payloads:
        payload = load(races_dir / f"{race_id}.json")
        bound = payload.get("market_sha256")
        if race_id in markets:
            known = markets[race_id]
        elif race_id in manifest_markets:
            known = manifest_markets[race_id]
        elif bound is None:
            continue  # no board was sealed for this race; nothing to bind
        else:
            # A day that never closed carries no manifest, so in the public
            # mirror -- where the market records themselves are withheld --
            # there is nothing left to compare the binding against. That is a
            # gap in the evidence, not a failed check, and it must read as one.
            unbound.append(race_id)
            continue
        if bound != known:
            fail(f"{date}: {race_id} market binding mismatch")
    if unbound:
        print(
            f"  {date}: market binding not checkable for {len(unbound)} race(s)"
            " -- the day has no manifest and the market records are not published"
        )
    if not manifest_path.exists():
        print(f"  {date}: UNCLOSED (no manifest) -- visible hole, chain continues past it")
        return None
    manifest = load(manifest_path)
    if manifest.get("schedule_sha256") != schedule_sha:
        fail(f"{date}: manifest points at a different schedule")
    if manifest.get("races") != payloads:
        fail(f"{date}: manifest race hashes do not match sealed payloads")
    if markets and manifest.get("markets") != markets:
        # only checkable when the market plaintext is present (full ledger);
        # in the public mirror the manifest hashes stand on their own
        fail(f"{date}: manifest market hashes do not match sealed records")
    if manifest.get("missing") != sorted(set(declared) - set(payloads)):
        fail(f"{date}: manifest missing-list inconsistent")
    if manifest.get("prev_day_manifest_sha256") != schedule.get("prev_day_manifest_sha256"):
        fail(f"{date}: manifest chain link differs from schedule")
    manifest_sha = canonical_sha256(manifest)
    root_path = day_dir / "root_hash.txt"
    if root_path.exists():
        expected_line = f"{date} publisher manifest sha256 {manifest_sha}\n"
        if root_path.read_text(encoding="utf-8") != expected_line:
            fail(f"{date}: root_hash.txt does not match the manifest")
    print(f"  {date}: OK (declared {len(declared)}, sealed {len(payloads)}, missing {len(manifest.get('missing', []))})")
    return manifest_sha


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=".", help="directory containing daily/<YYYYMMDD>/")
    args = parser.parse_args()
    daily = Path(args.root) / "daily"
    if not daily.exists():
        fail(f"no daily/ directory under {args.root}")
    days = sorted(d for d in daily.iterdir() if d.is_dir() and DATE_DIR.match(d.name))
    if not days:
        fail("no sealed days found")

    expected_prev = GENESIS
    for day_dir in days:
        manifest_sha = verify_day(day_dir, expected_prev)
        if manifest_sha is not None:
            expected_prev = manifest_sha

    first = datetime.strptime(days[0].name, "%Y%m%d")
    last = datetime.strptime(days[-1].name, "%Y%m%d")
    sealed = {d.name for d in days}
    gaps = []
    cursor = first
    while cursor <= last:
        stamp = cursor.strftime("%Y%m%d")
        if stamp not in sealed:
            gaps.append(stamp)
        cursor += timedelta(days=1)
    if gaps:
        print(f"calendar holes (absent days are part of the record): {', '.join(gaps)}")
    print(f"CHAIN OK: {len(days)} days verified, {len(gaps)} calendar holes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
