# Certify the 16 canonical h=9 t=3/t=4 linear-triple-system representatives:
# deterministic CNF dump + DRAT proof from solving the exact archived clause
# list. See README.md in this directory for variable semantics.
import itertools, time, hashlib
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool, CNF

T3REPS = [((0,1,2),(3,4,5),(3,6,7)), ((0,1,2),(3,4,5),(6,7,8)), ((0,1,2),(0,3,4),(0,5,6)),
          ((0,1,2),(0,3,4),(1,3,5)), ((0,1,2),(0,3,4),(1,5,6))]
T4REPS = [((0,1,2),(3,4,5),(3,6,7),(4,6,8)), ((0,1,2),(0,3,4),(0,5,6),(0,7,8)),
          ((0,1,2),(0,3,4),(0,5,6),(1,3,5)), ((0,1,2),(0,3,4),(0,5,6),(1,3,7)),
          ((0,1,2),(0,3,4),(0,5,6),(1,7,8)), ((0,1,2),(0,3,4),(1,3,5),(2,4,5)),
          ((0,1,2),(0,3,4),(1,3,5),(2,4,6)), ((0,1,2),(0,3,4),(1,3,5),(2,6,7)),
          ((0,1,2),(0,3,4),(1,5,6),(2,7,8)), ((0,1,2),(0,3,4),(1,5,6),(3,5,7)),
          ((0,1,2),(0,3,4),(1,5,6),(3,7,8))]
H = list(range(9))

def build(SYS):
    internal = set()
    for T in SYS:
        for a, b in itertools.combinations(sorted(T), 2):
            assert (a, b) not in internal, "repeated internal pair"
            internal.add((a, b))
    pairs = [p for p in itertools.combinations(H, 2) if p not in internal]
    N = 49
    pool = IDPool()
    def ev(i, j):
        a, b = min(i, j), max(i, j)
        return pool.id(('e', a, b))
    # Pre-allocate edge variables in lexicographic order so the DIMACS number
    # of edge {i,j} (i<j) is exactly its 1-based index in the lex enumeration
    # of all C(49,2) = 1176 pairs. Auxiliary (cardinality) variables follow.
    for i in range(N):
        for j in range(i + 1, N):
            ev(i, j)
    cl = []
    kof = {}
    v = 9
    for T in SYS: kof[v] = set(T); v += 1
    for p in pairs: kof[v] = set(p); v += 1
    tm = {w: sum(1 for T in SYS if w in T) for w in H}
    for w in H:
        for _ in range(tm[w]): kof[v] = {w}; v += 1
    while v < 49: kof[v] = set(); v += 1
    for a, b in itertools.combinations(H, 2): cl.append([-ev(a, b)])
    for y in range(9, 49):
        for w in H:
            cl.append([ev(y, w)] if w in kof[y] else [-ev(y, w)])
    for i, j in itertools.combinations(range(N), 2):
        others = [w for w in range(N) if w != i and w != j]
        for w, w2 in itertools.combinations(others, 2):
            cl.append([-ev(i, w), -ev(j, w), -ev(i, w2), -ev(j, w2)])
    for x in range(N):
        lits = [ev(x, y) for y in range(N) if y != x]
        cnf = CardEnc.equals(lits=lits, bound=(8 if x < 9 else 7), vpool=pool,
                             encoding=EncType.seqcounter)
        cl.extend(cnf.clauses)
    NB = {w: [y for y in range(9, 49) if w in kof[y]] for w in H}
    for y in range(9, 49):
        for w in H:
            cl.append([ev(y, x) for x in NB[w] if x != y])
    return cl

if __name__ == "__main__":
    manifest = []
    for tag, reps in (("t3", T3REPS), ("t4", T4REPS)):
        for i, SYS in enumerate(reps):
            cl = build(SYS)
            name = f"{tag}_rep{i}"
            CNF(from_clauses=cl).to_file(name + ".cnf")
            s = Cadical195(bootstrap_with=cl, with_proof=True)
            t0 = time.time(); res = s.solve()
            assert not res, f"{name} SAT?!"
            pf = s.get_proof()
            open(name + ".drat", "w").write("\n".join(pf))
            hc = hashlib.sha256(open(name + ".cnf", "rb").read()).hexdigest()
            hd = hashlib.sha256(open(name + ".drat", "rb").read()).hexdigest()
            manifest.append(f"{name} {SYS} UNSAT {time.time()-t0:.1f}s cnf:{hc} drat:{hd}")
            print(manifest[-1], flush=True)
            s.delete()
    open("t34_manifest.txt", "w").write("\n".join(manifest))
    print("CERTIFICATION COMPLETE")
