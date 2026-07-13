#!/usr/bin/env python3
"""
Self-contained verification of the Erdős 895 formalization finding.

Re-checks, with NO solver (pure Python), the explicit Fin-18 counterexample graph
against the EXACT Lean predicates of proofs/Proofs/Erdos895Problem.lean:

  IsTriangleFree G            := ∀ a b c, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)
  IsAdditiveTriple a b c      := a.val + b.val = c.val ∧ a.val > 0 ∧ b.val > 0
  IsIndependentTriple G a b c := ¬G.Adj a b ∧ ¬G.Adj b c ∧ ¬G.Adj a c
  HasIndependentAdditiveTriple G := ∃ a b c, IsAdditiveTriple a b c ∧ IsIndependentTriple G a b c

Run:  python3 verify-counterexample.py
(The exhaustive UNSAT direction — "every triangle-free graph on Fin 17 has an
 independent additive triple" — is established by Z3 in sat-threshold-scan.py.)
"""
import json, itertools, os
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
N = 18  # SimpleGraph (Fin 18) == vertices {0,…,17}; value 0 is inert (never in a triple)

def has_edge(edges, i, j):
    if i == j:
        return False
    a, b = (i, j) if i < j else (j, i)
    return (a, b) in edges

def is_triangle_free(edges):
    for i, j, k in itertools.combinations(range(N), 3):
        if has_edge(edges, i, j) and has_edge(edges, j, k) and has_edge(edges, i, k):
            return False, (i, j, k)
    return True, None

def find_independent_additive_triple(edges, strict):
    """strict=True  -> a < b (three DISTINCT vertices, matching Barber)
       strict=False -> a <= b (the file's loose IsAdditiveTriple, which admits a=b)."""
    for a in range(1, N):
        for b in range(a + 1 if strict else a, N):
            c = a + b
            if c <= N - 1:
                if (not has_edge(edges, a, b) and not has_edge(edges, b, c)
                        and not has_edge(edges, a, c)):
                    return (a, b, c)
    return None

edges = set(tuple(e) for e in json.load(open(os.path.join(HERE, "counterexample-fin18.json"))))
tf, tri = is_triangle_free(edges)
w_strict = find_independent_additive_triple(edges, strict=True)
w_loose = find_independent_additive_triple(edges, strict=False)
v0 = [e for e in edges if 0 in e]

print(f"Explicit Fin-18 graph (= {{1,…,17}}, vertex 0 isolated), {len(edges)} edges")
print(f"  edges touching vertex 0                       : {v0}")
print(f"  triangle-free                                 : {tf}" + ("" if tf else f"  (triangle {tri})"))
print(f"  independent additive triple, DISTINCT (a<b)   : {w_strict}  (None => valid counterexample)")
print(f"  independent additive triple, LOOSE   (a<=b)   : {w_loose}  (the file's def: (1,1,2) sneaks in)")

deg = Counter()
for (i, j) in edges:
    deg[i] += 1; deg[j] += 1
print(f"  degrees                                       : {dict(sorted(deg.items()))}")

assert tf and w_strict is None and w_loose is not None, "verification FAILED"
print("\nOK: counterexample valid under the DISTINCT-vertex reading; the file's loose")
print("    IsAdditiveTriple (a=b allowed) is satisfied by (1,1,2), so the graph is NOT")
print("    a counterexample under the file's definition — exactly the definitional bug.")

print("""
SUMMARY (Z3 sound UNSAT + this pure-Python check of SAT witnesses):
  LOOSE def (a=b allowed, == the Lean file's IsAdditiveTriple):
     'every triangle-free graph has an independent additive triple' holds on Fin N for all N >= 12
     => barber_theorem (n >= 18): TRUE ;  counterexample_17 (Fin 17): FALSE (UNSAT)
  STRICT def (a < b, distinct vertices, == Barber's theorem):
     property holds on Fin N iff N >= 19  (counterexample exists for N <= 18)
     => barber_theorem (n >= 18): FALSE at n=18 (Fin-18 counterexample exists); needs n >= 19
        counterexample_17 (Fin 17): TRUE (a Fin-17 counterexample exists strictly)
  => No single definition makes BOTH barber_theorem(n>=18) AND counterexample_17 true.
""")
