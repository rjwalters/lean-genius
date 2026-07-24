import Mathlib
import Proofs.GaussWilsonNonCyclic

/-!
# Sylow-2 Boundary Shapes in (ZMod n)ˣ — the Cyclic Half (OQ-02, S3 ACT)

## Problem (gauss-wilson-non-cyclic-oq-02)

Does the 2-torsion bound of the parent entry extend to characterize when
the Sylow 2-subgroup of `(ZMod n)ˣ` is *elementary abelian* versus
*cyclic*?

## This file (S3 scope)

The **cyclic half**, fully proved: the Sylow 2-subgroup of the finite
abelian group `(ZMod n)ˣ` is cyclic iff its 2-torsion has rank ≤ 1, i.e.
iff every square root of 1 is `±1` — and, remarkably, this Sylow-local
condition already detects the **global** cyclic classification:

* `two_torsion_pm_one_iff_isCyclic` :
  `(∀ x : (ZMod n)ˣ, x² = 1 → x = 1 ∨ x = -1) ↔ IsCyclic (ZMod n)ˣ`
  (`n ≥ 3`). Forward = contrapositive of the parent's
  `exists_third_sqrt_of_not_cyclic`; reverse = a cyclic group has at
  most two square roots of 1 (`IsCyclic.card_pow_eq_one_le`) while
  `{1, -1, x}` would be three.

Two kernel-`decide` anchors pin the **exponent** phenomenon that the
elementary-abelian half (S4 target) is about — rank does not see it:

* `zmod8_units_sq_eq_one` : `(ZMod 8)ˣ` has exponent 2 (elementary
  abelian, `S₂ ≅ C₂ × C₂`).
* `zmod16_units_exists_order_four` : `(ZMod 16)ˣ` has an element of
  order 4 (`S₂ ≅ C₂ × C₄` — same 2-rank as `n = 8`, different exponent).

## S4 target (the elementary-abelian half; Sylow-free formulation)

`(∀ x : (ZMod n)ˣ, x⁴ = 1 → x² = 1) ↔`
`(∀ p, p.Prime → Odd p → p ∣ n → p % 4 = 3) ∧ n.factorization 2 ≤ 3`.

("No element of order 4" is exactly "the Sylow 2-subgroup is elementary
abelian" for a finite abelian group.) Route: CRT decomposition
(`ZMod.chineseRemainder`, as in the parent), cyclicity of odd
prime-power unit groups with `v₂(p−1) = 1 ⟺ p ≡ 3 (mod 4)`, and the
2-adic cap from the `(ZMod 2^a)ˣ ≅ C₂ × C_{2^{a-2}}` structure
(`a ≥ 3`) — the one piece likely absent from Mathlib (~80–150 LOC).

Sorries: 0. Axioms: 0 (kernel `decide` only — no `native_decide`).
-/

namespace GaussWilsonNonCyclicOQ02

open GaussWilsonNonCyclic

/-- For `n ≥ 3`, `-1 ≠ 1` in `(ZMod n)ˣ`: otherwise `2 = 0` in
`ZMod n`, forcing `n ∣ 2`. (The parent proves this privately; re-derived
here via `CharP.cast_eq_zero_iff`.) -/
theorem neg_one_ne_one_units {n : ℕ} (hn : 3 ≤ n) [NeZero n] :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  intro h
  have hv : (-1 : ZMod n) = 1 := by
    have hval := congrArg (Units.val : (ZMod n)ˣ → ZMod n) h
    simpa using hval
  have h2 : ((2 : ℕ) : ZMod n) = 0 := by
    push_cast
    linear_combination -hv
  have hdvd : n ∣ 2 := (CharP.cast_eq_zero_iff (ZMod n) n 2).mp h2
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- **The cyclic half of OQ-02.** The Sylow 2-subgroup of `(ZMod n)ˣ`
is cyclic — equivalently, rank₂ ≤ 1, equivalently every square root of
unity is `±1` — if and only if `(ZMod n)ˣ` is itself cyclic. The
Sylow-local shape detects the global classification: rank₂ ≤ 1 already
forces `n ∈ {1, 2, 4, p^k, 2p^k}`.

Forward: contrapositive of the parent's
`exists_third_sqrt_of_not_cyclic` (a non-cyclic unit group carries a
third square root of 1). Reverse: in a cyclic group `y² = 1` has at
most two solutions, but `1`, `-1`, and a putative third root `x` are
pairwise distinct. -/
theorem two_torsion_pm_one_iff_isCyclic {n : ℕ} (hn : 3 ≤ n) [NeZero n] :
    (∀ x : (ZMod n)ˣ, x ^ 2 = 1 → x = 1 ∨ x = -1) ↔ IsCyclic (ZMod n)ˣ := by
  constructor
  · intro h
    by_contra hncyc
    obtain ⟨x, hx_sq, hx1, hxn1⟩ := exists_third_sqrt_of_not_cyclic hn hncyc
    rcases h (unitOfSqEqOne x hx_sq) (unitOfSqEqOne_sq x hx_sq) with h1 | h1
    · exact unitOfSqEqOne_ne_one hx_sq hx1 h1
    · exact unitOfSqEqOne_ne_neg_one hx_sq hxn1 h1
  · intro hcyc x hx_sq
    by_contra hne
    push_neg at hne
    obtain ⟨hne1, hnen1⟩ := hne
    have hcard2 : (Finset.univ.filter fun y : (ZMod n)ˣ => y ^ 2 = 1).card ≤ 2 :=
      hcyc.card_pow_eq_one_le (by norm_num)
    have hne_1_n1 : (-1 : (ZMod n)ˣ) ≠ 1 := neg_one_ne_one_units hn
    have hsub : ({1, -1, x} : Finset (ZMod n)ˣ) ⊆
        Finset.univ.filter fun y : (ZMod n)ˣ => y ^ 2 = 1 := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hy with rfl | rfl | rfl
      · simp
      · simp
      · exact hx_sq
    have hcard3 : ({1, -1, x} : Finset (ZMod n)ˣ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h | h)
          · exact hne_1_n1 h.symm
          · exact hne1 h.symm),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          intro h
          exact hnen1 h.symm),
        Finset.card_singleton]
    have := Finset.card_le_card hsub
    omega

/-- `(ZMod 8)ˣ` is elementary abelian: every unit squares to 1
(`S₂(8) ≅ C₂ × C₂`, rank 2, exponent 2). Kernel `decide`. -/
theorem zmod8_units_sq_eq_one : ∀ x : (ZMod 8)ˣ, x ^ 2 = 1 := by decide

/-- `(ZMod 16)ˣ` is NOT elementary abelian: it carries an element of
order 4 (`S₂(16) ≅ C₂ × C₄` — same 2-rank as `n = 8`, larger exponent;
this is exactly the invariant OQ-02 adds beyond OQ-03's square-root
count, which is `2^rank = 4` for both). Kernel `decide`. -/
theorem zmod16_units_exists_order_four :
    ∃ x : (ZMod 16)ˣ, x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by decide

end GaussWilsonNonCyclicOQ02
