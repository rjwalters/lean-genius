#!/usr/bin/env python3
"""
Build-free certificate for the sufficiency direction of Legendre's three-square
theorem (zsqrtd-neg-two-oq-02), targeting the axiom-reduction path in
`proofs/Proofs/ThreeSquares.lean` and the open PR #24443
(`ThreeSquaresSufficiency.lean`).

PR #24443 reduces the sufficiency axiom `not_excluded_form_is_sum_three_sq` to a
single hypothesis it calls `DirichletWitnessProperty`:

    ∀ {m}, ¬IsExcludedForm m → ¬(4 ∣ m) → 1 < m →
      ∃ d p, 0 < d ∧ p = d*m - 1 ∧ p.Prime ∧ legendreSym p (-d) = 1

This script makes two findings precise and reproducible:

FINDING 1 (the witness symbol is a residue function).
  `legendreSym (d*n-1) (-d)` is completely determined by `(n mod 8, d mod 8)`
  (verified constant over every prime `p = d*n-1` in range). The +1 classes are:
      n≡1,5 (mod 8): d ≡ 2,6 (mod 8)
      n≡2,6 (mod 8): d ≡ 1,2,5,6 (mod 8)
      n≡3   (mod 8): NONE
  (Odd d with odd n gives p even ⇒ no odd prime, so only even d are admissible
  when n is odd.)

FINDING 2 (DirichletWitnessProperty is FALSE on n ≡ 3 mod 8 — a GAP in #24443).
  For every non-excluded `n ≡ 3 (mod 8)` with `4∤n`, NO witness `(d, p=d*n-1)`
  exists: every admissible `d` yields `legendreSym p (-d) = -1`. Yet all such `n`
  ARE sums of three squares. Hence `DirichletWitnessProperty` as stated is
  unsatisfiable for the whole class `n ≡ 3 (mod 8)`, so PR #24443's proposed
  "next step" (discharge `DirichletWitnessProperty`) is impossible as written.

FINDING 3 (the correct n ≡ 3 mod 8 route — matches ThreeSquares.lean:600 hint).
  For every `n ≡ 3 (mod 8)` there is an ODD `t` with `(n - t^2)/2` a sum of two
  squares `a^2 + b^2`, giving the three-square representation
      n = t^2 + 2a^2 + 2b^2 = t^2 + (a+b)^2 + (a-b)^2.
  ( `(n-t^2)/2 ≡ 1 (mod 4)` for odd t since `t^2 ≡ 1 (mod 8)` and `n ≡ 3`, and a
    suitable value can be taken prime ≡ 1 mod 4 via Dirichlet — a sum of two
    squares.) So the witness property must be SPLIT by residue:
      n ≢ 3 (mod 8): Dirichlet witness (d, p=dn-1), -d a QR mod p.
      n ≡ 3 (mod 8): the t^2 + 2(a^2+b^2) two-squares route.

Run:  python3 verify_dirichlet_witness.py     (needs sympy)
Exits non-zero on any mismatch.
"""
import sys, math
from collections import defaultdict, Counter
from sympy import isprime, legendre_symbol

FAILED = False
def check(name, cond, detail=""):
    global FAILED
    print(f"[{'OK' if cond else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))
    if not cond:
        FAILED = True

def is_excluded(n):
    while n % 4 == 0:
        n //= 4
    return n % 8 == 7

def is_sum2(m):
    if m < 0:
        return False
    a = 0
    while a * a <= m:
        c = m - a * a
        if math.isqrt(c) ** 2 == c:
            return True
        a += 1
    return False

def two_sq(m):
    a = 0
    while a * a <= m:
        c = m - a * a
        s = math.isqrt(c)
        if s * s == c:
            return a, s
        a += 1
    return None

# ---- FINDING 1: symbol determined by (n%8, d%8) ----------------------------
sym = defaultdict(set)
for n in range(2, 4000):
    if n % 4 == 0 or is_excluded(n):
        continue
    for d in range(1, 40):
        p = d * n - 1
        if p < 3 or not isprime(p):
            continue
        sym[(n % 8, d % 8)].add(legendre_symbol((-d) % p, p))
nonconst = {k: v for k, v in sym.items() if len(v) > 1}
check("legendreSym(d*n-1, -d) is a function of (n%8, d%8)", not nonconst,
      detail=("non-constant: " + str(nonconst)) if nonconst else "all classes constant")

plus = {k for k, v in sym.items() if v == {1}}
expected_plus = {(1, 2), (1, 6), (5, 2), (5, 6),
                 (2, 1), (2, 2), (2, 5), (2, 6),
                 (6, 1), (6, 2), (6, 5), (6, 6)}
check("the +1 (n%8,d%8) classes match the documented selection table",
      plus == expected_plus, detail=f"{sorted(plus)}")
check("n ≡ 3 (mod 8) has NO +1 class (no admissible witness residue)",
      not any(nm == 3 for (nm, _) in plus))

# ---- FINDING 2: witness exists iff n ≢ 3 (mod 8) ---------------------------
DMAX = 200
no_witness = []
for n in range(2, 6000):
    if n % 4 == 0 or is_excluded(n):
        continue
    found = False
    for d in range(1, DMAX):
        p = d * n - 1
        if p < 3 or not isprime(p):
            continue
        if legendre_symbol((-d) % p, p) == 1:
            found = True
            break
    if not found:
        no_witness.append(n)
classes = Counter(n % 8 for n in no_witness)
check("every non-excluded n with 4∤n and n≢3 (mod 8) HAS a Dirichlet witness",
      all(n % 8 == 3 for n in no_witness),
      detail=f"failures by n%8: {dict(classes)}")
check("the witness gap is EXACTLY the class n ≡ 3 (mod 8)",
      set(classes) == {3} and classes[3] > 0,
      detail=f"{len(no_witness)} witness-less n, all ≡ 3 (mod 8)")
# and they are genuinely representable
def is_sum3(n):
    a = 0
    while a * a <= n:
        b = a
        while a * a + b * b <= n:
            c2 = n - a * a - b * b
            if math.isqrt(c2) ** 2 == c2:
                return True
            b += 1
        a += 1
    return False
check("all witness-less n ARE sums of three squares (gap is real, not vacuous)",
      all(is_sum3(n) for n in no_witness[:300]))

# ---- FINDING 3: correct route for n ≡ 3 (mod 8) ----------------------------
bad_route, bad_id = [], 0
for n in range(3, 8000, 8):  # n ≡ 3 (mod 8)
    ok = False
    t = 1
    while t * t <= n:
        if t % 2 == 1:
            r = n - t * t
            if r >= 0 and r % 2 == 0 and is_sum2(r // 2):
                a, b = two_sq(r // 2)
                if t * t + (a + b) ** 2 + (a - b) ** 2 != n:
                    bad_id += 1
                ok = True
                break
        t += 1
    if not ok:
        bad_route.append(n)
check("every n ≡ 3 (mod 8): ∃ odd t with (n-t^2)/2 a sum of two squares",
      not bad_route, detail=(f"failures: {bad_route[:10]}" if bad_route else "n<8000"))
check("the identity n = t^2 + (a+b)^2 + (a-b)^2 holds for that witness",
      bad_id == 0)

if FAILED:
    print("\nVERIFICATION FAILED")
    sys.exit(1)
print("\nAll Dirichlet-witness / three-square arithmetic verified.")
