/-
  Joint Typicality Lemma — combinatorial core

  Shannon channel coding, OQ-02 / OQ-02: "Formalize the joint typicality lemma."

  The joint typicality lemma (Cover & Thomas, Thm 7.6.1 / 15.2.3) underlies the random-coding
  achievability proof of the channel coding theorem. For i.i.d. length-`n` sequences it asserts
  three properties of the jointly ε-typical set `A_ε^{(n)} ⊆ 𝒳ⁿ × 𝒴ⁿ`:

    (1)  P( (Xⁿ,Yⁿ) ∈ A_ε )            → 1            as n → ∞.            [AEP / LLN]
    (2)  |A_ε|                          ≤ 2^{n(H(X,Y)+ε)}.                  [size bound]
    (3)  P( (X̃ⁿ,Ỹⁿ) ∈ A_ε )           ≤ 2^{-n(I(X;Y)-3ε)}                 [independence bound]
         where (X̃ⁿ,Ỹⁿ) ~ p(xⁿ)·p(yⁿ) are independent with the same marginals.

  Property (1) is the genuinely analytic part — it is the weak law of large numbers applied to the
  empirical information density, and is NOT formalized here (see closing remark). Properties (2)
  and (3) are the *combinatorial* core: they follow purely from the per-sequence probability bounds
  that **define** membership in the typical set, with no probabilistic limit. This file isolates
  and **fully verifies (0 axioms, 0 sorries)** that combinatorial core, abstractly over any finite
  sequence space `Ω = 𝒳ⁿ × 𝒴ⁿ`.

  Key bookkeeping:
  * A jointly ε-typical sequence `ω` has joint probability `p ω ≥ 2^{-n(H(X,Y)+ε)}`
    (typicality in `(X,Y)`), forcing the size bound (2).
  * Under the product law `q = p_X·p_Y`, a typical sequence has `q ω ≤ 2^{-n(H(X)+H(Y)-2ε)}`
    (typicality in `X` and in `Y`), and with (2) and `I = H(X)+H(Y)-H(X,Y)` this gives (3).

  Results (0 axioms, 0 sorries)
  * `typicalSet_card_le`        — abstract: a set whose elements each carry mass ≥ δ under a
                                  sub-probability `p` has at most `1/δ` elements.
  * `prob_le_card_mul`          — abstract: mass of a set under `q` is ≤ |set| · (max element mass).
  * `jointlyTypicalSet_card_le` — Property (2): `|A_ε| ≤ 2^{n(H(X,Y)+ε)}`.
  * `joint_typicality_independence_bound` — Property (3): product-law mass `≤ 2^{-n(I-3ε)}`.

  References
  - Cover, T.M. & Thomas, J.A. "Elements of Information Theory" (2nd ed.), §7.6 (Joint AEP) and
    Thm 7.6.1; the channel coding achievability proof (§7.7) consumes exactly properties (1)–(3).
  - Shannon, C.E. (1948). "A Mathematical Theory of Communication."
-/

import Mathlib

namespace InformationTheory.ChannelCoding.JointTypicality

variable {Ω : Type*} [Fintype Ω]

/-! ## Abstract combinatorial lemmas

These two facts carry all the content of properties (2) and (3); they are pure finite-sum
inequalities with no information-theoretic input. -/

/-- **Size bound from a uniform lower mass bound.**
    If `p` is a sub-probability (`0 ≤ p`, `∑ p ≤ 1`) and every element of a finite set `A` carries
    mass at least `δ > 0`, then `A` has at most `1/δ` elements. This is the engine behind the
    typical-set size bound: typical sequences are individually "not too likely", so there cannot be
    too many of them. -/
theorem typicalSet_card_le {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω ≤ 1)
    {A : Finset Ω} {δ : ℝ} (hδ : 0 < δ) (hmem : ∀ ω ∈ A, δ ≤ p ω) :
    (A.card : ℝ) ≤ 1 / δ := by
  have hAδ : (A.card : ℝ) * δ ≤ 1 := by
    calc (A.card : ℝ) * δ = ∑ _ω ∈ A, δ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ω ∈ A, p ω := Finset.sum_le_sum hmem
      _ ≤ ∑ ω, p ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun ω _ _ => hp ω)
      _ ≤ 1 := hsum
  rw [le_div_iff₀ hδ]
  exact hAδ

/-- **Mass of a set is at most its size times the largest element mass.**
    If every element of `A` carries mass at most `M` under `q`, then the total `q`-mass of `A` is
    at most `|A| · M`. This converts the size bound into the product-law probability bound. -/
theorem prob_le_card_mul {q : Ω → ℝ} {A : Finset Ω} {M : ℝ}
    (hmem : ∀ ω ∈ A, q ω ≤ M) :
    ∑ ω ∈ A, q ω ≤ (A.card : ℝ) * M := by
  calc ∑ ω ∈ A, q ω ≤ ∑ _ω ∈ A, M := Finset.sum_le_sum hmem
    _ = (A.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Property (2): the typical-set size bound

Membership in the jointly ε-typical set guarantees `p ω ≥ 2^{-n(H(X,Y)+ε)}`. -/

/-- **Joint typicality, Property (2): `|A_ε| ≤ 2^{n(H(X,Y)+ε)}`.**
    `p` is the true joint pmf on the sequence space `Ω = 𝒳ⁿ × 𝒴ⁿ`. Every jointly ε-typical
    sequence has joint probability at least `2^{-n(HXY+ε)}`, so there are at most `2^{n(HXY+ε)}`
    of them. -/
theorem jointlyTypicalSet_card_le (n : ℕ) (ε HXY : ℝ)
    {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hpsum : ∑ ω, p ω ≤ 1) {A : Finset Ω}
    (hpmem : ∀ ω ∈ A, (2 : ℝ) ^ (-((n : ℝ) * (HXY + ε))) ≤ p ω) :
    (A.card : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (HXY + ε)) := by
  have hδpos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * (HXY + ε))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h := typicalSet_card_le hp hpsum hδpos hpmem
  rwa [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_inv] at h

/-! ## Property (3): the independence bound

Under the product law `q = p_X · p_Y`, joint typicality also forces `q ω ≤ 2^{-n(HX+HY-2ε)}`
(typicality in each marginal). Combined with Property (2) and `I = HX + HY - HXY`, this bounds the
probability that independently-drawn sequences look jointly typical. -/

/-- **Joint typicality, Property (3): the independence bound.**
    If, on the jointly ε-typical set `A`, the joint pmf satisfies the typicality lower bound and the
    product-of-marginals pmf `q` satisfies the typicality upper bound, then the total `q`-mass of
    `A` is at most `2^{-n((HX+HY-HXY) - 3ε)} = 2^{-n(I - 3ε)}`, where `I = HX + HY - HXY` is the
    mutual information. This is exactly the bound that makes the random-coding decoding-error
    probability vanish for rates below capacity. -/
theorem joint_typicality_independence_bound (n : ℕ) (ε HX HY HXY : ℝ)
    {p q : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hpsum : ∑ ω, p ω ≤ 1) {A : Finset Ω}
    (hpmem : ∀ ω ∈ A, (2 : ℝ) ^ (-((n : ℝ) * (HXY + ε))) ≤ p ω)
    (hqmem : ∀ ω ∈ A, q ω ≤ (2 : ℝ) ^ (-((n : ℝ) * (HX + HY - 2 * ε)))) :
    ∑ ω ∈ A, q ω ≤ (2 : ℝ) ^ (-((n : ℝ) * ((HX + HY - HXY) - 3 * ε))) := by
  have hcard := jointlyTypicalSet_card_le n ε HXY hp hpsum hpmem
  have hMnn : (0 : ℝ) ≤ (2 : ℝ) ^ (-((n : ℝ) * (HX + HY - 2 * ε))) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  calc ∑ ω ∈ A, q ω
      ≤ (A.card : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (HX + HY - 2 * ε))) := prob_le_card_mul hqmem
    _ ≤ (2 : ℝ) ^ ((n : ℝ) * (HXY + ε)) * (2 : ℝ) ^ (-((n : ℝ) * (HX + HY - 2 * ε))) :=
        mul_le_mul_of_nonneg_right hcard hMnn
    _ = (2 : ℝ) ^ ((n : ℝ) * (HXY + ε) + -((n : ℝ) * (HX + HY - 2 * ε))) :=
        (Real.rpow_add (by norm_num) _ _).symm
    _ = (2 : ℝ) ^ (-((n : ℝ) * ((HX + HY - HXY) - 3 * ε))) := by
        rw [show (n : ℝ) * (HXY + ε) + -((n : ℝ) * (HX + HY - 2 * ε))
              = -((n : ℝ) * ((HX + HY - HXY) - 3 * ε)) from by ring]

/-!
## Closing remark: what is proved and what is deferred

This file formalizes the **non-asymptotic, combinatorial core** of the joint typicality lemma —
Properties (2) and (3) — by taking the per-sequence probability bounds that *define* the jointly
ε-typical set as hypotheses. That is faithful: those bounds are definitional (a sequence is in
`A_ε^{(n)}` precisely when its empirical entropies in `X`, `Y`, and `(X,Y)` are within `ε` of the
true values), and the size/independence bounds are then exact finite-sum inequalities.

The **analytic** half — Property (1), `P((Xⁿ,Yⁿ) ∈ A_ε) → 1` — is the weak law of large numbers
applied to the empirical information density `-(1/n) log p(Xⁿ,Yⁿ)`, and is deliberately NOT
axiomatized here (no `axiom` is introduced; the count stays at 0). Formalizing it requires the
i.i.d.-product construction and an `L²`/Chebyshev concentration argument; that is the natural next
target, building on Mathlib's `ProbabilityTheory` law-of-large-numbers infrastructure.
-/

#check @typicalSet_card_le
#check @prob_le_card_mul
#check @jointlyTypicalSet_card_le
#check @joint_typicality_independence_bound

end InformationTheory.ChannelCoding.JointTypicality
