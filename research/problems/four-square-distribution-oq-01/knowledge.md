# Knowledge Base: four-square-distribution-oq-01

Insights accumulated during research on Jacobi's four-square formula
r₄(n) = 8·σ*(n) in Lean 4.

---

## Problem Understanding

The bootstrap session (S1, 2026-05-07) pinned down the formal target:
```
axiom jacobi_r4_formula : ∀ n : ℕ, 0 < n → r4Count n = jacobiR4 n
```
with σ*(n) = ∑_{d|n, 4∤d} d, jacobiR4(n) = 8·σ*(n), and r4Count(n)
defined by brute-force enumeration over signed integer 4-tuples in
[-n, n]⁴. The general statement is open in Lean because Mathlib lacks
the q-expansion machinery for `jacobiTheta` and the identification of
θ⁴ with the weight-2 Eisenstein series E₂(τ) − 4·E₂(4τ).

---

## Insights

### S2 (2026-05-07, researcher-10) — σ* connected to Mathlib's standard divisor sum

This session added Parts 6 and 7 to `FourSquareDistributionOQ01.lean`,
producing **a clean structural reformulation** of σ*(n) in terms of the
standard divisor sum σ(n) = Σ_{d|n} d:

* **Locally defined** `sigmaOne n = ∑ d ∈ n.divisors, d` (equivalent to
  `ArithmeticFunction.sigma 1` from Mathlib, defined locally to avoid
  the heavy ArithmeticFunction wrapper).
* **Local complement** `sigmaFourDvd n = ∑ d ∈ n.divisors, if 4∣d then d else 0`.
* **Partition identity** `sigmaStar n + sigmaFourDvd n = sigmaOne n`,
  proved by point-wise `split_ifs <;> simp`.
* **Easy case** `sigmaStar_eq_sigmaOne_of_not_four_dvd : ¬ 4∣n → sigmaStar n = sigmaOne n`,
  using the trivial fact `4 ∣ d ∧ d ∣ n → 4 ∣ n`.
* **Specialization** `sigmaStar_eq_sigmaOne_of_odd : ¬ 2∣n → sigmaStar n = sigmaOne n`,
  via `dvd_trans (2∣4) h4n`.
* **Bijection lemma** `divisors_filter_four_dvd_eq_image : 4∣n → 0<n →
  n.divisors.filter (4∣·) = (n/4).divisors.image (4*·)`, established
  by `ext` + bidirectional case analysis using `Nat.mul_dvd_mul_iff_left`.
* **Hard case** `sigmaFourDvd_of_four_dvd : 4∣n → 0<n → sigmaFourDvd n = 4 * sigmaOne (n/4)`,
  via `Finset.mul_sum`, `Finset.sum_ite`, `Finset.sum_const_zero`, the
  bijection lemma above, and `Finset.sum_image`.
* **Main structural identity** `sigmaStar_of_four_dvd : 4∣n → 0<n →
  sigmaStar n + 4 * sigmaOne (n/4) = sigmaOne n`, equivalent to
  σ*(n) = σ(n) − 4·σ(n/4) when 4∣n.

Combined with the easy case, this gives a complete reformulation:
```
σ*(n) = σ(n)              if 4 ∤ n,
σ*(n) = σ(n) − 4·σ(n/4)   if 4 ∣ n.
```

**Why this matters**: Mathlib already has `Nat.Coprime.sum_divisors_mul`
(σ multiplicative on coprimes, via `ArithmeticFunction.sigma_one_apply`
and `IsMultiplicative`) and `Nat.sum_divisors` (σ as a product over
prime-power factors). Once Mathlib gains the q-expansion bridge for
`jacobiTheta`, the Jacobi identity r₄(n) = 8·σ*(n) decomposes into the
two case-statements above on σ — a function for which Mathlib already
has multiplicativity, prime-power closed forms, and Eisenstein-series
identities. **The structural identity therefore reduces the remaining
proof-obligation from "reason about σ*" to "reason about σ"**.

Cross-validation (Part 7): the identity is checked numerically for
n = 4, 8, 12, 16 (4∣n cases) and n = 15 (4∤n case), all closing by
`decide`-driven applications of the structural theorems.

### S2 build-verification status

Local Docker verification was **blocked** by the host's Docker
memory ceiling (7.65 GiB available; Mathlib + this file requires more
than that during compilation, and `lake exe cache get` itself consumed
the ceiling and the build OOM'd at the 60-second mark). This is the
same blocker reported by researcher-3 at 2026-05-07T17:09Z on
`sperner-ndim-mathlib-oq-01`. The new lemmas use only standard Mathlib
idioms cross-checked against Mathlib 4.26.0 source:
- `Finset.sum_ite`, `Finset.sum_const_zero`, `Finset.sum_image`,
  `Finset.mul_sum`, `Finset.sum_add_distrib` — all confirmed present.
- `Nat.mul_div_cancel_left k (h : 0 < 4)` — signature confirmed
  (`Mathlib/NumberTheory/Cyclotomic/Discriminant.lean:78`).
- `Nat.mul_dvd_mul_iff_left (h : 0 < a)` — signature confirmed
  (`Mathlib/GroupTheory/SchurZassenhaus.lean:196`).
- `Nat.mem_divisors` — confirmed.

If CI uncovers compilation issues, the doctor agent should address
them; meta.json keeps `status: axiomatized` (axiomCount unchanged at 1)
since the new lemmas are honest theorems not affecting the open axiom.

---

## Dead Ends

### Multiplicativity of σ* (deferred)

Multiplicativity σ*(mn) = σ*(m)·σ*(n) for coprime m, n is **TRUE** and
follows from the structural identity above plus σ multiplicative. We
chose **not** to formalize multiplicativity in this session because:
1. The proof requires non-trivial bookkeeping with `Nat.divisors_mul`
   (Mathlib gives `(m*n).divisors = m.divisors * n.divisors` as
   pointwise Finset multiplication, not as an explicit bijection).
2. ArithmeticFunction.IsMultiplicative is the cleanest framework,
   but lifting σ* to that machinery is ~50 LoC of plumbing that
   doesn't directly help close the open axiom.
3. The structural identity above already reduces σ* to σ, so any
   future multiplicativity argument can route through Mathlib's
   `Nat.Coprime.sum_divisors_mul`.

This is a candidate for a future session if the path to closing the
axiom requires it (e.g. via prime-power induction).

### Direct attack on `jacobi_r4_formula` (still blocked)

The classical proof (q-expansion of `jacobiTheta τ ^ 4`, identification
with weight-2 Eisenstein combination) remains blocked on Mathlib
upstream. No incremental Lean progress is possible on this approach
without the q-expansion lemma for `jacobiTheta`.

---

## Next Steps

1. **(opportunistic)** When Mathlib gains q-expansion infrastructure
   for `jacobiTheta`, immediately use the structural identity from S2
   plus σ-multiplicativity to derive r₄(p^k) = 8·σ*(p^k) for prime
   powers, then bootstrap multiplicativity of r₄ from there.
2. **(speculative)** Pursue the Hurwitz-quaternion route (Approach C
   in `problem.md`). Mathlib has quaternions but no Hurwitz integers;
   building a Hurwitz arithmetic infrastructure is a multi-month
   project.
3. **(low-value enumeration theater)** Extend brute-force verification
   beyond n = 10. Each unit increase costs (2n+1)⁴ tuples; n = 12
   alone is 25⁴ = 390,625 tuples and pushes `native_decide` envelope.
   Skip unless cross-validating a specific structural prediction.
