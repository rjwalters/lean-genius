#!/usr/bin/env python3
"""Goal #48: freight manifest for the cert run — one row per census UNSAT_CROSSCHECKED H1 root.

For each row, take the census attempt that was UNSAT_CROSSCHECKED, open EXACTLY
<run>/<id>/preparation.json and <run>/<id>/solve/<id>/result.json (never a directory-wide search,
because Mac pilot run dirs hold many cases), require the table, the preparation and the solve
result to agree on cnf_sha256, and copy table.json into freight/tables/<id>.json.
Writes freight/manifest.jsonl sorted longest-first (census CaDiCaL seconds) and prints totals.
"""
import hashlib, json, shutil, sys
from pathlib import Path
CENSUS = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-verdict-cloud-20260921/census/table-final-20260927T172217Z.json")
OUT = Path(sys.argv[1]); (OUT / "tables").mkdir(parents=True, exist_ok=True)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows, bad = [], []
for r in json.loads(CENSUS.read_text())["rows"]:
    a = [x for x in r["attempts"] if x["status"] == "UNSAT_CROSSCHECKED"]
    if not a: continue
    run = Path(a[-1]["run"]); i = r["id"]
    prep = json.loads((run / i / "preparation.json").read_text())
    res = json.loads((run / i / "solve" / i / "result.json").read_text())
    table = run / i / "input" / "table.json"
    ok = prep["id"] == i and res["id"] == i and prep["cnf_sha256"] == res["cnf_sha256"] == a[-1]["cnf_sha256"] \
         and sha(table) == prep["table_sha256"]
    if not ok: bad.append(i); continue
    shutil.copyfile(table, OUT / "tables" / f"{i}.json")
    rows.append({"id": i, "profile": prep["profile"], "cnf_sha256": prep["cnf_sha256"], "table_sha256": prep["table_sha256"],
                 "census_cadical_seconds": res["crosscheck"]["elapsed_seconds"], "census_kissat_seconds": res["primary"]["elapsed_seconds"]})
rows.sort(key=lambda x: -x["census_cadical_seconds"])
(OUT / "manifest.jsonl").write_text("".join(json.dumps(x) + "\n" for x in rows))
print(len(rows), "rows;", len(bad), "inconsistent:", bad[:5], "; cadical core-h %.0f" % (sum(x["census_cadical_seconds"] for x in rows) / 3600))
