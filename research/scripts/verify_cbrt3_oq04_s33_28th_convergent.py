#!/usr/bin/env python3
"""
cube-root-3-irrational-oq-04 — S33 certificate for the 28th CF convergent of ∛3.

Anti-typo discipline (see helpers file): independently RE-DERIVE the partial
quotients aᵢ from a high-precision recomputation of ∛3 (do NOT re-quote a prior
sketch tail), then verify (a) the convergent recursion against the previous two
convergents and (b) the EXACT integer cube-side direction that the Lean proof
relies on.

28th convergent = idx 27 (0-indexed), an UPPER bound (odd index):

    ∛3  <  p₂₇ / q₂₇      ⟺   p³ > 3 q³.
"""
from mpmath import mp, mpf, floor, cbrt

mp.dps = 600
x = cbrt(3)

# --- Independent CF re-derivation (high precision, integer floors) ---
a = []
y = x
for _ in range(34):
    ai = int(floor(y))
    a.append(ai)
    y = 1 / (y - ai)

print("CF a[0..29] =", a[:30])

# --- Convergents via the standard recurrence pₖ = aₖ pₖ₋₁ + pₖ₋₂ ---
H = []  # numerators p
K = []  # denominators q
for i, ai in enumerate(a):
    if i == 0:
        H.append(ai); K.append(1)
    elif i == 1:
        H.append(ai * H[0] + 1); K.append(ai * K[0] + 0)
    else:
        H.append(ai * H[i - 1] + H[i - 2])
        K.append(ai * K[i - 1] + K[i - 2])

# Sanity: 26th & 27th convergents must match the merged helpers file.
assert (H[25], K[25]) == (1310497171657, 908647988973), (H[25], K[25])
assert (H[26], K[26]) == (6304779645157, 4371490049266), (H[26], K[26])
print("idx25 (26th):", H[25], "/", K[25], "  (UPPER, matches PR #24767)")
print("idx26 (27th):", H[26], "/", K[26], "  (LOWER, matches PR #24782)")

# --- The new rung: 28th convergent = idx 27 ---
a27 = a[27]
p, q = H[27], K[27]
# recursion cross-check
assert p == a27 * H[26] + H[25]
assert q == a27 * K[26] + K[25]
print(f"\na27 = {a27}")
print(f"idx27 (28th): {p} / {q}")

# --- EXACT integer cube-side direction (the trap) ---
# idx 27 is ODD ⇒ UPPER bound ⇒ need p³ > 3 q³.
lhs = p ** 3
rhs = 3 * q ** 3
print(f"\np³        = {lhs}")
print(f"3 q³      = {rhs}")
print(f"p³ - 3q³  = {lhs - rhs}")
assert lhs > rhs, "UPPER bound requires p³ > 3 q³"
print("\nOK: p³ > 3 q³  ⇒  (p/q)³ > 3  ⇒  ∛3 < p/q  (UPPER, odd index 27).")

# relative gap
gap = mpf(p) / mpf(q) - x
print(f"relative gap (p/q - ∛3) ≈ {gap}")

# word-form theorem name for the numerator/denominator
_words = {'0':'zero','1':'one','2':'two','3':'three','4':'four',
          '5':'five','6':'six','7':'seven','8':'eight','9':'nine'}
def words(n): return '_'.join(_words[c] for c in str(n))
print(f"\nLean theorem name:\ncbrt3_lt_{words(p)}_over_{words(q)}")
print(f"  -- statement: ∛3 < ({p} / {q} : ℝ)")
