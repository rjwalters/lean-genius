#!/usr/bin/env python3
"""Bank re-validation manifest: one row per 2026-08 bank object (<tag>.compact.lrat.gz) with every
producer ledger candidate (trim=VERIFIED, compact=ok) — the worker accepts the object only if its
streamed gz/LRAT sha256 equals one candidate's compact_gz_sha256/compact_lrat_sha256 and the
regenerated CNF equals that candidate's cnf_sha256. Also reports exact H1 coverage sets."""
import glob, json, hashlib, collections, sys
from pathlib import Path
R = Path(__file__).resolve().parent.parent
LED = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-bank-ledgers-20261006")
OUT = Path(sys.argv[1])
objs = [o for o in json.load(open(R / "phase_b_h1_h3/h1-object-list.json")) if o["Key"].endswith(".compact.lrat.gz") and o["Size"] > 0]
cands = collections.defaultdict(list)
for f in sorted(glob.glob(str(LED / "*/*.line"))):
    for line in open(f):
        p = line.split()
        if len(p) < 3 or p[2:3] and not p[2].startswith("p="):
            continue
        kv = dict(x.split("=", 1) for x in p[2:] if "=" in x)
        if p[3:4] == ["i=0"] or True:
            if kv.get("trim") == "VERIFIED" and kv.get("compact") == "ok" and all(k in kv for k in ("cnf_sha256", "compact_lrat_sha256", "compact_gz_sha256")):
                c = {k: kv[k] for k in ("p", "cnf_sha256", "compact_lrat_sha256", "compact_gz_sha256", "compact_bytes", "solve_s")}
                c["ledger"] = str(Path(f).relative_to(LED))
                if c not in cands[p[1]]:
                    cands[p[1]].append(c)
PHASEB = {r["tag"] for r in json.load(open(R / "phase_b_h1_h3/h1-frozen-candidates.json"))["rows"]}
rows, missing = [], []
for o in objs:
    tag = o["Key"].rsplit("/", 1)[1].split(".")[0]
    if not cands[tag]:
        missing.append(tag)
        if tag in PHASEB:
            continue  # already certified in the October census (historical object conflict)
        # no producer ledger: still checkable (pinned-emitter CNF + cake_lpr); lrat size unknown -> gz x 4
        rows.append({"tag": tag, "key": o["Key"], "gz_size": o["Size"], "candidates": [], "lrat_bytes_max": o["Size"] * 4})
        continue
    rows.append({"tag": tag, "key": o["Key"], "gz_size": o["Size"], "candidates": cands[tag],
                 "lrat_bytes_max": max(int(c["compact_bytes"]) for c in cands[tag])})
rows.sort(key=lambda r: -r["lrat_bytes_max"])
(OUT / "bank_manifest.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
cap = {r["tag"] for r in json.load(open(R / "closure-inventory-evidence/h1-exact-set-join.json"))["rows"]}
phaseb = {r["tag"] for r in json.load(open(R / "phase_b_h1_h3/h1-frozen-candidates.json"))["rows"]}
bank = {r["tag"] for r in rows}
outside = cap - bank - phaseb
summary = {"bank_objects": len(objs), "manifest_rows": len(rows), "objects_without_ledger_candidate": missing,
           "multi_candidate_rows": sum(len(r["candidates"]) > 1 for r in rows),
           "distinct_cnf_per_row_max": max(len({c["cnf_sha256"] for c in r["candidates"]}) for r in rows),
           "capacity": len(cap), "phase_b": len(phaseb), "bank": len(bank), "bank_in_capacity": len(bank & cap),
           "bank_and_phase_b": len(bank & phaseb), "outside_bank_and_phase_b": len(outside), "outside_tags": sorted(outside),
           "no_ledger_rows": [r["tag"] for r in rows if not r["candidates"]], "lrat_bytes_total": sum(r["lrat_bytes_max"] for r in rows if r["candidates"]), "gz_bytes_total": sum(r["gz_size"] for r in rows),
           "manifest_sha256": hashlib.sha256((OUT / "bank_manifest.jsonl").read_bytes()).hexdigest()}
(OUT / "bank_manifest_summary.json").write_text(json.dumps(summary, indent=1) + "\n")
print(json.dumps({k: v for k, v in summary.items() if k != "outside_tags"}, indent=1))
