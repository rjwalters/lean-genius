# Emit a renumbered LRAT proof as N separate Lean chunk modules + aggregator.
import sys, hashlib, os
lrat_path, num_orig, base, outdir, nchunks = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4], int(sys.argv[5])
first = num_orig + 1
mapping = {}
next_id = first
def mid(i):
    return i if i < first else mapping[i]
actions = []
raw = open(lrat_path).read()
for line in raw.splitlines():
    toks = line.split()
    if not toks: continue
    if len(toks) >= 2 and toks[1] == 'd':
        actions.append(('del', [mid(int(x)) for x in toks[2:-1]]))
        continue
    oid = int(toks[0]); rest = [int(x) for x in toks[1:]]
    z1 = rest.index(0); lits = rest[:z1]; hints_raw = rest[z1+1:-1]
    if any(h < 0 for h in hints_raw):
        k=0; rup=[]
        while k < len(hints_raw) and hints_raw[k] > 0: rup.append(mid(hints_raw[k])); k+=1
        groups=[]
        while k < len(hints_raw):
            cid = mid(-hints_raw[k]); k+=1; hs=[]
            while k < len(hints_raw) and hints_raw[k] > 0: hs.append(mid(hints_raw[k])); k+=1
            groups.append((cid, hs))
        mapping[oid] = next_id
        actions.append(('rat', next_id, lits, lits[0], rup, groups)); next_id += 1
    else:
        hints = [mid(h) for h in hints_raw]
        mapping[oid] = next_id
        actions.append((('rup', next_id, lits, hints) if lits else ('empty', next_id, hints)))
        next_id += 1
lead = 0
while lead < len(actions) and actions[lead][0] == 'del': lead += 1
actions = actions[lead:]
def arr(xs): return "#[" + ", ".join(map(str, xs)) + "]"
def render(a):
    if a[0]=='del': return f"  .del {arr(a[1])}"
    if a[0]=='rup': return f"  .addRup {a[1]} {arr(a[2])} {arr(a[3])}"
    if a[0]=='empty': return f"  .addEmpty {a[1]} {arr(a[2])}"
    _, nid, lits, pivot, rup, groups = a
    gs = "#[" + ", ".join(f"({c}, {arr(h)})" for c,h in groups) + "]"
    return f"  .addRat {nid} {arr(lits)} {pivot} {arr(rup)} {gs}"
sha = hashlib.sha256(raw.encode()).hexdigest()
per = (len(actions) + nchunks - 1)//nchunks
os.makedirs(outdir, exist_ok=True)
names = []
for ci in range(nchunks):
    seg = actions[ci*per:(ci+1)*per]
    if not seg: break
    name = f"{base}Chunk{ci}"
    names.append(name)
    L = ["import Std.Tactic.BVDecide", "",
         f"/- GENERATED chunk {ci} of {base} from {os.path.basename(lrat_path)} (sha256 {sha[:16]}…). -/", "",
         "set_option maxRecDepth 2000000", "set_option maxHeartbeats 0", "",
         "namespace Erdos85", "",
         f"def {name[0].lower()+name[1:]} : Array Std.Tactic.BVDecide.LRAT.IntAction := #["]
    L.append(",\n".join(render(a) for a in seg))
    L += ["]", "", "end Erdos85"]
    open(os.path.join(outdir, f"Erdos85{name}.lean"), "w").write("\n".join(L) + "\n")
agg = ["\n".join(f"import Proofs.Erdos85{n}" for n in names), "",
       f"/- GENERATED aggregator for {base}: {len(actions)} actions across {len(names)} chunks;",
       f"   source {os.path.basename(lrat_path)} sha256 {sha};",
       f"   renumbered vs numOriginalClauses = {num_orig}; leading deletions omitted. -/", "",
       "namespace Erdos85", "",
       f"def {base[0].lower()+base[1:]} : Array Std.Tactic.BVDecide.LRAT.IntAction :="]
agg.append("  " + " ++ ".join(f"{n[0].lower()+n[1:]}" for n in names))
agg += ["", "end Erdos85"]
open(os.path.join(outdir, f"Erdos85{base}.lean"), "w").write("\n".join(agg) + "\n")
sizes = [os.path.getsize(os.path.join(outdir, f"Erdos85{n}.lean")) for n in names]
print(f"{base}: {len(actions)} actions, {len(names)} chunks, sizes {min(sizes)//1024}-{max(sizes)//1024} KB")
