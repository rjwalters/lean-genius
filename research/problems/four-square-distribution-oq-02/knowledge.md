# Knowledge Base: four-square-distribution-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Open question: bound the number of distinct **representation types** of `n` as a
sum of four squares — the orbits of the hyperoctahedral group
`B_4 = (Z/2)^4 ⋊ S_4` (sign changes + coordinate permutations, order
`2^4 · 4! = 384`) acting on the solution set `{(x_1,…,x_4) ∈ Z^4 : Σ x_i^2 = n}` —
in terms of `r_4(n)` (Jacobi total) and divisor data.

A type is exactly the sorted multiset of absolute values `(a ≤ b ≤ c ≤ d)` with
`a²+b²+c²+d² = n`. So `numTypes(n) = #{(a,b,c,d) ∈ ℕ⁴ : a≤b≤c≤d, Σ = n}`.

---

## Insights

### S1 (2026-06-14, ORIENT) — orbit-size formula + clean valid bound (sympy-verified)

All claims below are **independently brute-force verified** for `n = 1..400` by
`verify/verify_orbit_count.py` (enumerates the actual signed/ordered vectors; it
does NOT assume the formulas it certifies).

1. **Jacobi (recomputed, not assumed):** `r_4(n) = 8·σ*(n)`,
   `σ*(n) = Σ_{d|n, 4∤d} d`. Verified `n=1..400`.

2. **Orbit-size formula.** For a type `t` with `k` nonzero coordinates and
   distinct-value multiplicities `m_v` (the value `0` counted as a value):
   `|orbit(t)| = 2^k · 4! / ∏_v (m_v!)`.
   Matches brute-force orbit sizes for **every** realized type, `n=1..400`.
   (Reasoning: `2^k` distinct sign assignments on the nonzero coords, times the
   `4!/∏ m_v!` distinct orderings of the multiset.)

3. **Orbit-sum identity (Burnside/orbit–stabilizer accounting):**
   `Σ_{types t of n} |orbit(t)| = r_4(n)`. Verified `n=1..400`.

4. **Minimum orbit size for `n>0` is exactly `8`,** attained ONLY by the type
   `(0,0,0,√n)` (`k=1`, multiplicities `(1,3)`): `2^1 · 4!/3! = 8`. The full
   table of minimum orbit sizes by structural class:

   | k nonzero | mult. pattern | orbit size | example |
   |-----------|---------------|-----------:|---------|
   | 1 | (1,3) | **8**  | n=1, (0,0,0,1) |
   | 2 | (2,2) | 24 | n=2, (0,0,1,1) |
   | 2 | (1,1,2) | 48 | n=5, (0,0,1,2) |
   | 3 | (1,3) | 32 | n=3, (0,1,1,1) |
   | 3 | (1,1,2) | 96 | n=6, (0,1,1,2) |
   | 3 | (1,1,1,1) | 192 | n=14, (0,1,2,3) |
   | 4 | (4) | 16 | n=4, (1,1,1,1) |
   | 4 | (1,3) | 64 | n=7, (1,1,1,2) |
   | 4 | (2,2) | 96 | n=10, (1,1,2,2) |
   | 4 | (1,1,2) | 192 | n=15, (1,1,2,3) |
   | 4 | (1,1,1,1) | 384 | n=30, (1,2,3,4) |

5. **Clean valid bound (candidate Lean target):** since every orbit of a nonzero
   solution has size `≥ 8`,
   > **`numTypes(n) ≤ r_4(n) / 8`,  equivalently  `8·numTypes(n) ≤ r_4(n)`,  for all `n>0`.**

   Verified: **no counterexamples** in `n=1..400`.

6. **Sharpness.** Equality `8·numTypes(n) = r_4(n)` holds for `n=1..399` ONLY at
   `n = 1`. For `n ≥ 2` it is strict, because some type necessarily has orbit
   size `> 8` (any type other than `(0,0,0,m)`). This is the sharp boundary of
   the `/8` bound.

### Proof strategy for the Lean target

`numTypes(n) ≤ r_4(n)/8` reduces to the **orbit lower bound**: every B_4-orbit of
a *nonzero* solution vector has size `≥ 8`. By orbit–stabilizer
(`|orbit| = 384/|stab|`), this is the **stabilizer upper bound**
`|Stab_{B_4}(v)| ≤ 48` for `v ≠ 0`. The maximal stabilizer `48` is realized at
`(0,0,0,m)`: `S_3` on the three zeros (`6`) × sign flips on those zeros (`2^3=8`)
= `48`; the nonzero coordinate kills the remaining sign freedom and the full
symmetric permutation. Then
`numTypes(n) = #orbits ≤ (Σ|orbit|)/min|orbit| = r_4(n)/8`.

Mathlib path: `MulAction`, `MulAction.orbitEquivQuotientStabilizer`,
`Nat.card`/`Finset.card`, with the `2^k·4!/∏m!` count as a finite combinatorial
lemma. Jacobi's exact `r_4` can be taken as a hypothesis (from the parent
`four-square-distribution`) rather than reformalized.

---

## Dead Ends

- **Crude bound `numTypes ≤ r_4/16`** (using the all-equal type `(m,m,m,m)`,
  size 16, as the supposed minimum) is WRONG: the true global minimum orbit size
  is 8, not 16, because `(0,0,0,m)` is smaller. The correct denominator is 8.
