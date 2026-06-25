#!/usr/bin/env python3
"""
Z3 threshold scan for the Erdős 895 formalization (proofs/Proofs/Erdos895Problem.lean).

Encodes "∃ a triangle-free graph G on Fin N with NO independent additive triple"
(a counterexample) as a SAT instance.  Z3 `unsat` is a sound proof that EVERY
triangle-free graph on Fin N has an independent additive triple.

Two readings of the additive triple are scanned:
  * loose  (a <= b)  == the file's IsAdditiveTriple (admits degenerate (a,a,2a))
  * strict (a <  b)  == Barber's theorem (three distinct vertices a, b, a+b)

Lean predicate encoding (vertices = values 0..N-1; vertex 0 is inert):
  triangle-free            : forall distinct i,j,k  not(e ij and e jk and e ik)
  no independent add triple: forall add. triple (a,b,a+b)  (e ab or e b(a+b) or e a(a+b))

Run:  python3 sat-threshold-scan.py
Requires z3-solver (`pip install z3-solver`).
"""
import z3, itertools

def has_counterexample(N, strict):
    """Returns (result, n_triples, edges_or_None) for Fin N."""
    E = {(i, j): z3.Bool(f"e_{i}_{j}") for i in range(N) for j in range(i + 1, N)}
    def edge(i, j):
        if i == j:
            return z3.BoolVal(False)
        a, b = (i, j) if i < j else (j, i)
        return E[(a, b)]
    s = z3.Solver()
    # triangle-free
    for i, j, k in itertools.combinations(range(N), 3):
        s.add(z3.Not(z3.And(edge(i, j), edge(j, k), edge(i, k))))
    # no independent additive triple
    nt = 0
    for a in range(1, N):
        for b in range(a + 1 if strict else a, N):
            c = a + b
            if c <= N - 1:
                nt += 1
                s.add(z3.Or(edge(a, b), edge(b, c), edge(a, c)))
    r = s.check()
    edges = None
    if r == z3.sat:
        m = s.model()
        edges = sorted([k for k in E if m.eval(E[k], model_completion=True)])
    return r, nt, edges

for label, strict in [("LOOSE (a<=b, == file's IsAdditiveTriple)", False),
                      ("STRICT (a<b, distinct == Barber)", True)]:
    print(f"\n=== {label} ===")
    for N in range(8, 22):
        r, nt, edges = has_counterexample(N, strict)
        tag = "counterexample EXISTS" if r == z3.sat else "property HOLDS (no counterexample)"
        extra = f"  [{len(edges)} edges]" if edges else ""
        print(f"  Fin {N:2d}: triples={nt:3d}  {str(r):6}  -> {tag}{extra}")
