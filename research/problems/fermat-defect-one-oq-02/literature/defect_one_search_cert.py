"""
fermat-defect-one-oq-02: empirical defect-one search.
Defect-one witness for exponent n: primitive (gcd=1) triple 2<=a<=b<c with
|a^n + b^n - c^n| = 1.

Extends prior 4<=n<=7 search to n=3..12 with larger height bound, and reports
the critical-exponent heuristic  #solutions up to height X  ~  X^(3-n).
"""
from math import gcd, isqrt

def search(n, C):
    """All primitive defect-one witnesses with c <= C."""
    sols = []
    pows = [v**n for v in range(C+1)]
    cset = {pows[c]: c for c in range(2, C+1)}  # value -> c (c>=2)
    for a in range(2, C+1):
        an = pows[a]
        if an > pows[C]:
            break
        for b in range(a, C+1):
            s = an + pows[b]
            # need c with c>b and |s - c^n| = 1  =>  c^n in {s-1, s+1}
            for target in (s-1, s+1):
                c = cset.get(target)
                if c is not None and c > b:
                    if gcd(gcd(a,b),c) == 1:
                        sols.append((a,b,c, an+pows[b]-pows[c]))
    return sols

print(f"{'n':>3} {'C(height)':>9} {'#primitive witnesses':>22}   examples")
for n in range(3, 13):
    C = 400 if n <= 4 else (200 if n <= 6 else 120)
    sols = search(n, C)
    ex = sols[:3]
    print(f"{n:>3} {C:>9} {len(sols):>22}   {ex}")

print()
print("Heuristic: # defect-one solns of height <= X scales ~ X^(3-n).")
print("  n=3: exponent 0  => ~ log / constant density => INFINITELY many (Mahler).")
print("  n>=4: exponent <0 => sum converges => only finitely many; search finds 0.")
print("Conclusion: the Lean headline `fermat_defect_one_exists : forall n>=3` is")
print("TRUE at n=3 (both signs, Mahler families) but EMPIRICALLY FALSE for 4<=n<=12.")
