/-
# The exact algebraic degree of every prime radical: [ℚ(p^{1/n}) : ℚ] = n
  (fourth-root-2-irrational OQ-02)

The parent gallery entry **fourth-root-2-irrational** (`FourthRoot2Degree4.lean`)
proves that `⁴√2` has degree exactly 4 over ℚ, via Eisenstein's criterion at the
prime 2 on `X⁴ − 2` followed by Gauss's lemma. Its open question OQ-02 asks
whether that Eisenstein-then-Gauss route can be **packaged as a reusable lemma**
for `X^{2^k} − 2` (or `X^{p^k} − p`), filling the even-exponent / prime-power gap
that Mathlib's Kummer lemmas (`X_pow_sub_C_irreducible_of_prime_pow`, which needs
`p ≠ 2`, and `…_of_odd`, which needs odd exponent) mark with explicit `TODO`s.

The *irreducibility* half of that packaging already exists in the gallery:
`CubeRoot3IrrationalOQ01.irreducible_X_pow_sub_C_prime_{int,rat}` proves `Xⁿ − p`
irreducible over ℤ and ℚ for **every** prime `p` and **every** `n ≥ 1` — with no
parity or prime-power restriction — and `NthRootIrrationalOQ01` uses it to prove
`p^{1/n}` *irrational*. But irrationality only certifies algebraic degree `≥ 2`.
No file pins the degree of the real radical at *exactly* `n`.

This file closes that gap. Building directly on the existing irreducibility
lemma, it identifies the **minimal polynomial of the real radical** and computes
the **exact field degree**, uniformly in `p` and `n`:

  * `minpoly_primeRoot`          — `minpoly ℚ (p^{1/n}) = Xⁿ − p`;
  * `finrank_adjoin_primeRoot`   — `[ℚ(p^{1/n}) : ℚ] = n`;
  * `linearIndependent_primeRoot_powers` — `{1, r, …, rⁿ⁻¹}` are ℚ-independent.

The headline specializations are exactly the cases OQ-02 names:

  * `finrank_adjoin_two_pow_k` — `[ℚ(2^{1/2^k}) : ℚ] = 2^k`   (the even / prime-power exponent `2^k`);
  * `finrank_adjoin_prime_pow` — `[ℚ(p^{1/p^k}) : ℚ] = p^k`   (the general `X^{p^k} − p` case);
  * `finrank_adjoin_fourthRoot_two` — `[ℚ(2^{1/4}) : ℚ] = 4`, recovering the parent.

The real radical is modeled as `(p : ℝ) ^ ((1 : ℝ) / n)` (`Real.rpow`), matching
`NthRootIrrationalOQ01`, so the present degree results sit on top of that file's
irrationality results for the *same* term.

Zero axioms; reuses only Mathlib and the sibling irreducibility lemma.
-/
import Mathlib
import Proofs.CubeRoot3IrrationalOQ01

open Polynomial IntermediateField

namespace FourthRoot2IrrationalOQ02

/-! ### The real radical and its defining power relation -/

/-- `(p^{1/n})ⁿ = p` for `p > 0`, `n ≥ 1`: the real `n`-th root of `p`, modeled as
`Real.rpow`, raised back to the `n`-th power returns `p`. -/
theorem rpow_inv_natCast_pow {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    ((p : ℝ) ^ ((1 : ℝ) / n)) ^ n = (p : ℝ) := by
  rw [← Real.rpow_natCast ((p : ℝ) ^ ((1 : ℝ) / n)) n,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p)]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [one_div, inv_mul_cancel₀ hn', Real.rpow_one]

/-- The real radical `p^{1/n}` is a root of `Xⁿ − p` over ℚ. -/
theorem aeval_primeRoot {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    (Polynomial.aeval ((p : ℝ) ^ ((1 : ℝ) / n))) (X ^ n - C (p : ℚ)) = 0 := by
  simp only [map_sub, map_pow, aeval_X, rpow_inv_natCast_pow hp hn,
    map_natCast, sub_self]

/-- `p^{1/n}` is integral over ℚ: a root of the monic `Xⁿ − p`. -/
theorem primeRoot_isIntegral {p n : ℕ} (hp : 0 < p) (hn : 0 < n) :
    IsIntegral ℚ ((p : ℝ) ^ ((1 : ℝ) / n)) :=
  ⟨X ^ n - C (p : ℚ), monic_X_pow_sub_C _ hn.ne', aeval_primeRoot hp hn⟩

/-! ### The minimal polynomial and the exact degree -/

/-- **The minimal polynomial of `p^{1/n}` over ℚ is `Xⁿ − p`.** This uses the
sibling irreducibility lemma (Eisenstein at `p` + Gauss) and the fact that the
radical is a root of the monic `Xⁿ − p`. It is the sharp statement: the radical's
minimal polynomial is *the* full Eisenstein polynomial, not a proper factor. -/
theorem minpoly_primeRoot {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    minpoly ℚ ((p : ℝ) ^ ((1 : ℝ) / n)) = X ^ n - C (p : ℚ) :=
  (minpoly.eq_of_irreducible_of_monic
    (CubeRoot3IrrationalOQ01.irreducible_X_pow_sub_C_prime_rat hp hn)
    (aeval_primeRoot hp.pos hn)
    (monic_X_pow_sub_C _ hn.ne')).symm

/-- The minimal polynomial of `p^{1/n}` has degree exactly `n`. -/
theorem minpoly_natDegree_primeRoot {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (minpoly ℚ ((p : ℝ) ^ ((1 : ℝ) / n))).natDegree = n := by
  rw [minpoly_primeRoot hp hn, natDegree_X_pow_sub_C]

/-- **The exact field degree `[ℚ(p^{1/n}) : ℚ] = n`** for every prime `p` and
every `n ≥ 1`. This is strictly stronger than irrationality (degree `≥ 2`): it
pins the algebraic degree of the real radical at exactly `n`, with no parity or
prime-power restriction on the exponent. -/
theorem finrank_adjoin_primeRoot {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    Module.finrank ℚ ℚ⟮((p : ℝ) ^ ((1 : ℝ) / n))⟯ = n := by
  rw [IntermediateField.adjoin.finrank (primeRoot_isIntegral hp.pos hn),
      minpoly_natDegree_primeRoot hp hn]

/-- **The power basis `{1, r, r², …, rⁿ⁻¹}` of `r = p^{1/n}` is ℚ-linearly
independent.** Immediate from `[ℚ(r):ℚ] = n`: the powers below the minimal-
polynomial degree are independent. Generalizes the parent's
`linearIndependent_fr2_powers` (the `Fin 4` case for `⁴√2`). -/
theorem linearIndependent_primeRoot_powers {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    LinearIndependent ℚ (fun i : Fin n => ((p : ℝ) ^ ((1 : ℝ) / n)) ^ (i : ℕ)) := by
  have h := linearIndependent_pow (K := ℚ) ((p : ℝ) ^ ((1 : ℝ) / n))
  rw [minpoly_natDegree_primeRoot hp hn] at h
  exact h

/-! ### The headline specializations named by OQ-02 -/

/-- **`[ℚ(2^{1/2^k}) : ℚ] = 2^k`** — the even / prime-power exponent `2^k`. This is
precisely the case Mathlib's Kummer API cannot reach (it requires `p ≠ 2` or odd
exponent); Eisenstein at 2 is exponent-agnostic and handles it uniformly. -/
theorem finrank_adjoin_two_pow_k (k : ℕ) :
    Module.finrank ℚ ℚ⟮(((2 : ℕ) : ℝ) ^ ((1 : ℝ) / ((2 ^ k : ℕ) : ℝ)))⟯ = 2 ^ k :=
  finrank_adjoin_primeRoot (p := 2) (n := 2 ^ k) (by norm_num) (by positivity)

/-- **`[ℚ(p^{1/p^k}) : ℚ] = p^k`** — the general `X^{p^k} − p` case named by OQ-02,
for an arbitrary prime `p`. -/
theorem finrank_adjoin_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Module.finrank ℚ ℚ⟮((p : ℝ) ^ ((1 : ℝ) / ((p ^ k : ℕ) : ℝ)))⟯ = p ^ k :=
  finrank_adjoin_primeRoot hp (pow_pos hp.pos k)

/-- **`[ℚ(2^{1/4}) : ℚ] = 4`** — recovering the parent entry's `finrank_adjoin_fr2`
as the `k = 2` instance of `finrank_adjoin_two_pow_k` (note `2^{1/4} = ⁴√2`). -/
theorem finrank_adjoin_fourthRoot_two :
    Module.finrank ℚ ℚ⟮(((2 : ℕ) : ℝ) ^ ((1 : ℝ) / ((4 : ℕ) : ℝ)))⟯ = 4 :=
  finrank_adjoin_primeRoot (p := 2) (n := 4) (by norm_num) (by norm_num)

end FourthRoot2IrrationalOQ02
