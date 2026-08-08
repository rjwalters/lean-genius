# Emit a compact renumbered LRAT text file (leading pre-addition deletions
# dropped) for include_str + pure parseLRATProof consumption in Lean.
import sys, hashlib, os
lrat_path, num_orig, out_path = sys.argv[1], int(sys.argv[2]), sys.argv[3]
first = num_orig + 1
mapping = {}; next_id = first
def mid(i): return i if i < first else mapping[i]
raw = open(lrat_path).read()
out = []
last_add = num_orig
seen_add = False
for line in raw.splitlines():
    toks = line.split()
    if not toks: continue
    if len(toks) >= 2 and toks[1] == 'd':
        ids = [mid(int(x)) for x in toks[2:-1]]
        if not seen_add: continue          # drop pre-addition deletions
        out.append(f"{last_add} d {' '.join(map(str, ids))} 0")
        continue
    oid = int(toks[0]); rest = [int(x) for x in toks[1:]]
    z1 = rest.index(0); lits = rest[:z1]; hints_raw = rest[z1+1:-1]
    mapped_hints = []
    for h in hints_raw:
        mapped_hints.append(-mid(-h) if h < 0 else mid(h))
    mapping[oid] = next_id
    body = lits + [0] + mapped_hints + [0]
    out.append(f"{next_id} {' '.join(map(str, body))}")
    last_add = next_id; next_id += 1; seen_add = True
open(out_path, "w").write("\n".join(out) + "\n")
print(f"{os.path.basename(out_path)}: {len(out)} lines, "
      f"{os.path.getsize(out_path)/1048576:.2f} MB, "
      f"src sha256 {hashlib.sha256(raw.encode()).hexdigest()[:16]}…")
