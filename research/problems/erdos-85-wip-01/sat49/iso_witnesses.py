# h=9 classification witness table generator (deterministic, ~2s).
# For every raw prefix-normalized linear triple system on 9 points
# (T1=(0,1,2); T2 in {(3,4,5),(0,3,4)}; remaining triples raw ascending;
# point-degree <= 4; no repeated internal pair) find its canonical rep index
# and an EXPLICIT witness permutation of {0..8} mapping the system onto the
# rep as sets of sets. Search: enumerate triple->triple bijections (<= t!),
# extend point maps by backtracking; every found witness is re-verified by
# direct image comparison before being recorded.
# Outputs: iso_witnesses.json (rows {sys, rep, perm}) — the Lean data file
# Erdos85OrderFortyNineWitnessTable.lean is a mechanical transcription.
# Verified result 2026-08-07: t=2: 2/2, t=3: 60/60, t=4: 921/921 matched,
# zero unmatched (confirming the 2/5/11 iso classification).
import itertools, json, time

H = list(range(9))
ALL = list(itertools.combinations(H, 3))
def lin(a, b): return len(set(a) & set(b)) <= 1
T2S = [(3,4,5), (0,3,4)]
T2REPS = [((0,1,2),(3,4,5)), ((0,1,2),(0,3,4))]
T3REPS = [((0,1,2),(3,4,5),(3,6,7)), ((0,1,2),(3,4,5),(6,7,8)), ((0,1,2),(0,3,4),(0,5,6)),
          ((0,1,2),(0,3,4),(1,3,5)), ((0,1,2),(0,3,4),(1,5,6))]
T4REPS = [((0,1,2),(3,4,5),(3,6,7),(4,6,8)), ((0,1,2),(0,3,4),(0,5,6),(0,7,8)),
          ((0,1,2),(0,3,4),(0,5,6),(1,3,5)), ((0,1,2),(0,3,4),(0,5,6),(1,3,7)),
          ((0,1,2),(0,3,4),(0,5,6),(1,7,8)), ((0,1,2),(0,3,4),(1,3,5),(2,4,5)),
          ((0,1,2),(0,3,4),(1,3,5),(2,4,6)), ((0,1,2),(0,3,4),(1,3,5),(2,6,7)),
          ((0,1,2),(0,3,4),(1,5,6),(2,7,8)), ((0,1,2),(0,3,4),(1,5,6),(3,5,7)),
          ((0,1,2),(0,3,4),(1,5,6),(3,7,8))]

def witness(S, R):
    t = len(S)
    Rsets = [set(T) for T in R]
    Ssets = [set(T) for T in S]
    degS = {w: sum(1 for T in Ssets if w in T) for w in H}
    degR = {w: sum(1 for T in Rsets if w in T) for w in H}
    for assign in itertools.permutations(range(t)):
        pmap = {}
        used = set()
        def bt(idx):
            if idx == t:
                remS = [w for w in H if w not in pmap]
                remR = [w for w in H if w not in used]
                for w, z in zip(remS, remR):
                    pmap[w] = z
                return True
            SS, RR = Ssets[idx], Rsets[assign[idx]]
            fixed = {w for w in SS if w in pmap}
            if any(pmap[w] not in RR for w in fixed): return False
            freeS = [w for w in SS if w not in pmap]
            freeR = [z for z in RR if z not in used]
            if len(freeS) != len(freeR): return False
            for perm in itertools.permutations(freeR):
                if any(degS[w] != degR[z] for w, z in zip(freeS, perm)): continue
                for w, z in zip(freeS, perm): pmap[w] = z; used.add(z)
                if bt(idx + 1): return True
                for w, z in zip(freeS, perm): del pmap[w]; used.discard(z)
            return False
        if bt(0):
            img = frozenset(frozenset(pmap[x] for x in T) for T in S)
            assert img == frozenset(frozenset(T) for T in R)
            return [pmap[i] for i in range(9)]
    return None

def raw_systems(t):
    out = []
    if t == 2:
        return [((0,1,2), T2) for T2 in T2S]
    for T2 in T2S:
        base = [(0,1,2), T2]
        if t == 3:
            for T3 in ALL:
                if T3 <= T2: continue
                if lin(T3, base[0]) and lin(T3, base[1]): out.append(tuple(base + [T3]))
        else:
            for T3 in ALL:
                if T3 <= T2 or not (lin(T3, base[0]) and lin(T3, base[1])): continue
                for T4 in ALL:
                    if T4 <= T3 or not all(lin(T4, X) for X in base + [T3]): continue
                    out.append(tuple(base + [T3, T4]))
    return out

if __name__ == "__main__":
    results = {}
    t0 = time.time()
    for t, reps in ((2, T2REPS), (3, T3REPS), (4, T4REPS)):
        rows = []; unmatched = []
        for S in raw_systems(t):
            internal = set(); ok = True
            for T in S:
                for a, b in itertools.combinations(sorted(T), 2):
                    if (a, b) in internal: ok = False
                    internal.add((a, b))
            if not ok: continue
            deg = {w: sum(1 for T in S if w in T) for w in H}
            if max(deg.values()) > 4: continue
            found = False
            for ri, R in enumerate(reps):
                w = witness(S, R)
                if w is not None:
                    rows.append({"sys": [list(T) for T in S], "rep": ri, "perm": w})
                    found = True
                    break
            if not found: unmatched.append(S)
        print(f"t={t}: {len(rows)} matched, {len(unmatched)} unmatched ({time.time()-t0:.0f}s)", flush=True)
        for S in unmatched[:5]: print("  UNMATCHED", S, flush=True)
        results[t] = rows
    json.dump(results, open("iso_witnesses.json", "w"))
    print("WITNESS TABLE COMPLETE", flush=True)
