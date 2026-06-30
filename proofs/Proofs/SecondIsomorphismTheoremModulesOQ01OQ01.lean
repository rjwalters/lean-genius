import Mathlib.Tactic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-
# Three submodules: the iterated modular dimension law and the failure of
  naive inclusion–exclusion — OQ01·OQ01

## Question

The parent entry (`second-isomorphism-theorem-modules-oq-01`) derives the **two-submodule
modular dimension law**

  `finrank (p ⊔ q) + finrank (p ⊓ q) = finrank p + finrank q`

*structurally*, as a corollary of the second (diamond) isomorphism theorem
`LinearMap.quotientInfEquivSupQuotient`. Its first open question asks whether the analogous
count for **three** submodules `p, q, r` can be obtained in the same structural way, given the
warning that the symmetric set-theoretic inclusion–exclusion formula

  `finrank (p ⊔ q ⊔ r) =? finrank p + finrank q + finrank r`
  `                      - finrank (p ⊓ q) - finrank (p ⊓ r) - finrank (q ⊓ r)`
  `                      + finrank (p ⊓ q ⊓ r)`

**fails**, because the lattice of submodules is *modular* but not *distributive*.

## Answer

* The correct three-submodule identity is **asymmetric** and is obtained by iterating the
  two-submodule modular law twice (once on `p, q`, once on `p ⊔ q, r`). In the
  subtraction-free `ℕ` form it reads

    `finrank (p ⊔ q ⊔ r) + finrank (p ⊓ q) + finrank ((p ⊔ q) ⊓ r)`
    `      = finrank p + finrank q + finrank r`.                       (`finrank_sup_three`)

  The whole chain rests on the second isomorphism theorem: we re-derive the two-term law
  (`finrank_modular_law`) from `secondIso` and then apply it twice. The "correction" term
  `finrank ((p ⊔ q) ⊓ r)` *replaces* the symmetric combination
  `finrank (p ⊓ r) + finrank (q ⊓ r) - finrank (p ⊓ q ⊓ r)` of the naive formula.

* The naive symmetric formula is genuinely **false**: three distinct lines in `ℝ²`
  (`counterexample_naive_inclusion_exclusion`) give

    `finrank (p ⊔ q ⊔ r) + finrank (p ⊓ q) + finrank (p ⊓ r) + finrank (q ⊓ r)`
    `   = 2 ≠ 3 = finrank p + finrank q + finrank r + finrank (p ⊓ q ⊓ r)`,

  the gap `3 - 2 = 1` being exactly the failure of distributivity, i.e. of
  `(p ⊔ q) ⊓ r = (p ⊓ r) ⊔ (q ⊓ r)`.

## What this establishes

* `secondIso` — the second isomorphism theorem as a named `LinearEquiv` (any ring/module).
* `finrank_modular_law` — the two-submodule modular law, re-derived from `secondIso`.
* `finrank_sup_three` — the exact iterated three-submodule identity (`ℕ`, subtraction-free).
* `finrank_sup_three_sub` — the same identity in `ℤ` subtraction form.
* `finrank_sup_three_of_pairwise_bot` — the clean special case when `p ⊓ q = ⊥` and
  `(p ⊔ q) ⊓ r = ⊥`: dimensions simply add.
* `counterexample_naive_inclusion_exclusion` — an explicit `ℝ²` witness showing the symmetric
  inclusion–exclusion formula fails.
-/

open Submodule FiniteDimensional Module

namespace SecondIsomorphismTheoremModulesOQ01OQ01

section AnyRing

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **Second (diamond) isomorphism theorem** as a named linear equivalence:
`p ⧸ (p ⊓ p') ≃ₗ (p ⊔ p') ⧸ p'`, read inside the appropriate ambient submodules. -/
noncomputable def secondIso (p p' : Submodule R M) :
    (↥p ⧸ Submodule.comap p.subtype (p ⊓ p')) ≃ₗ[R]
      (↥(p ⊔ p') ⧸ Submodule.comap (p ⊔ p').subtype p') :=
  LinearMap.quotientInfEquivSupQuotient p p'

end AnyRing

section FiniteDimensional

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- **Two-submodule modular dimension law**, re-derived *from the second isomorphism theorem*
(`secondIso`), so that the three-submodule identity below rests entirely on the structural
diamond equivalence. This reproduces the parent entry's result self-containedly. -/
theorem finrank_modular_law (p q : Submodule K V) :
    Module.finrank K ↥(p ⊔ q) + Module.finrank K ↥(p ⊓ q)
      = Module.finrank K ↥p + Module.finrank K ↥q := by
  -- The two diamond quotients have equal dimension because `secondIso` is an equivalence.
  have hiso :
      Module.finrank K (↥p ⧸ Submodule.comap p.subtype (p ⊓ q))
        = Module.finrank K (↥(p ⊔ q) ⧸ Submodule.comap (p ⊔ q).subtype q) :=
    (secondIso p q).finrank_eq
  -- Rank–nullity on the left quotient (ambient `↥p`); comap preserves dimension.
  have hL :
      Module.finrank K (↥p ⧸ Submodule.comap p.subtype (p ⊓ q))
        + Module.finrank K ↥(p ⊓ q) = Module.finrank K ↥p := by
    have h := Submodule.finrank_quotient_add_finrank (Submodule.comap p.subtype (p ⊓ q))
    rwa [(Submodule.comapSubtypeEquivOfLe (inf_le_left)).finrank_eq] at h
  -- Rank–nullity on the right quotient (ambient `↥(p ⊔ q)`).
  have hR :
      Module.finrank K (↥(p ⊔ q) ⧸ Submodule.comap (p ⊔ q).subtype q)
        + Module.finrank K ↥q = Module.finrank K ↥(p ⊔ q) := by
    have h := Submodule.finrank_quotient_add_finrank (Submodule.comap (p ⊔ q).subtype q)
    rwa [(Submodule.comapSubtypeEquivOfLe (le_sup_right)).finrank_eq] at h
  omega

/-- **Iterated three-submodule dimension identity** (subtraction-free `ℕ` form):

`finrank (p ⊔ q ⊔ r) + finrank (p ⊓ q) + finrank ((p ⊔ q) ⊓ r) = finrank p + finrank q + finrank r`.

Obtained by applying the modular law to `p, q` and then to `p ⊔ q, r`. Note `p ⊔ q ⊔ r`
parses as `(p ⊔ q) ⊔ r`, so the second application closes the goal directly. -/
theorem finrank_sup_three (p q r : Submodule K V) :
    Module.finrank K ↥(p ⊔ q ⊔ r) + Module.finrank K ↥(p ⊓ q)
        + Module.finrank K ↥((p ⊔ q) ⊓ r)
      = Module.finrank K ↥p + Module.finrank K ↥q + Module.finrank K ↥r := by
  have h1 := finrank_modular_law p q
  have h2 := finrank_modular_law (p ⊔ q) r
  omega

/-- The same identity in `ℤ`, written with genuine subtraction to match the textbook form
`finrank (p ⊔ q ⊔ r) = finrank p + finrank q + finrank r - finrank (p ⊓ q) - finrank ((p ⊔ q) ⊓ r)`. -/
theorem finrank_sup_three_sub (p q r : Submodule K V) :
    (Module.finrank K ↥(p ⊔ q ⊔ r) : ℤ)
      = Module.finrank K ↥p + Module.finrank K ↥q + Module.finrank K ↥r
        - Module.finrank K ↥(p ⊓ q) - Module.finrank K ↥((p ⊔ q) ⊓ r) := by
  have h := finrank_sup_three p q r
  omega

/-- **Direct-sum special case**: if `p ⊓ q = ⊥` and `(p ⊔ q) ⊓ r = ⊥`, the three dimensions
simply add. This is the genuinely "additive" situation; the general law differs from it by the
two correction terms. -/
theorem finrank_sup_three_of_pairwise_bot (p q r : Submodule K V)
    (hpq : p ⊓ q = ⊥) (hr : (p ⊔ q) ⊓ r = ⊥) :
    Module.finrank K ↥(p ⊔ q ⊔ r)
      = Module.finrank K ↥p + Module.finrank K ↥q + Module.finrank K ↥r := by
  have h := finrank_sup_three p q r
  rw [hpq, hr, finrank_bot] at h
  omega

end FiniteDimensional

/-! ## Counterexample: the symmetric inclusion–exclusion formula fails

We exhibit three distinct lines in `ℝ²`:
`p = span {(1,0)}`, `q = span {(0,1)}`, `r = span {(1,1)}`.
Each is `1`-dimensional, every pairwise (hence triple) intersection is `⊥`, yet
`p ⊔ q ⊔ r = ⊤` is `2`-dimensional. The naive symmetric count predicts `3`, not `2`. -/

section Counterexample

/-- The three lines as submodules of `ℝ²`. -/
private def p₀ : Submodule ℝ (ℝ × ℝ) := Submodule.span ℝ {((1 : ℝ), (0 : ℝ))}
private def q₀ : Submodule ℝ (ℝ × ℝ) := Submodule.span ℝ {((0 : ℝ), (1 : ℝ))}
private def r₀ : Submodule ℝ (ℝ × ℝ) := Submodule.span ℝ {((1 : ℝ), (1 : ℝ))}

private theorem finrank_p₀ : Module.finrank ℝ ↥p₀ = 1 :=
  finrank_span_singleton (by simp [Prod.ext_iff])

private theorem finrank_q₀ : Module.finrank ℝ ↥q₀ = 1 :=
  finrank_span_singleton (by simp [Prod.ext_iff])

private theorem finrank_r₀ : Module.finrank ℝ ↥r₀ = 1 :=
  finrank_span_singleton (by simp [Prod.ext_iff])

/-- A vector lying in two distinct lines through the origin is `0`: helper that turns a
membership pair into the two scalar witnesses and a coordinate identity. -/
private theorem inf_span_eq_bot {u v : ℝ × ℝ}
    (hindep : ∀ a b : ℝ, a • u = b • v → a • u = 0) :
    Submodule.span ℝ {u} ⊓ Submodule.span ℝ {v} = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxu, hxv⟩ := hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxu
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hxv
  have : a • u = b • v := by rw [ha, hb]
  rw [Submodule.mem_bot, ← ha]
  exact hindep a b this

private theorem inf_pq : p₀ ⊓ q₀ = ⊥ :=
  inf_span_eq_bot fun a b h => by
    rw [Prod.ext_iff] at h
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero] at h ⊢
    rw [Prod.ext_iff]; constructor <;> simp_all

private theorem inf_pr : p₀ ⊓ r₀ = ⊥ :=
  inf_span_eq_bot fun a b h => by
    rw [Prod.ext_iff] at h
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero] at h ⊢
    obtain ⟨h1, h2⟩ := h
    rw [Prod.ext_iff]; constructor <;> simp_all

private theorem inf_qr : q₀ ⊓ r₀ = ⊥ :=
  inf_span_eq_bot fun a b h => by
    rw [Prod.ext_iff] at h
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero] at h ⊢
    obtain ⟨h1, h2⟩ := h
    rw [Prod.ext_iff]; constructor <;> simp_all

/-- The first two lines already span the whole plane. -/
private theorem sup_pq_top : p₀ ⊔ q₀ = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have hrw : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    simp
  rw [hrw]
  refine add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private theorem sup_pqr_top : p₀ ⊔ q₀ ⊔ r₀ = ⊤ := by
  rw [sup_pq_top]; simp

/-- **The naive symmetric inclusion–exclusion formula fails.** With the three lines above,

`finrank (p ⊔ q ⊔ r) + finrank (p ⊓ q) + finrank (p ⊓ r) + finrank (q ⊓ r)`
`  = 2`,  while
`finrank p + finrank q + finrank r + finrank (p ⊓ q ⊓ r) = 3`,

so the two sides differ: there is **no** symmetric inclusion–exclusion law for subspace
dimensions. (Both sides are written subtraction-free over `ℕ`.) -/
theorem counterexample_naive_inclusion_exclusion :
    Module.finrank ℝ ↥(p₀ ⊔ q₀ ⊔ r₀) + Module.finrank ℝ ↥(p₀ ⊓ q₀)
        + Module.finrank ℝ ↥(p₀ ⊓ r₀) + Module.finrank ℝ ↥(q₀ ⊓ r₀)
      ≠ Module.finrank ℝ ↥p₀ + Module.finrank ℝ ↥q₀ + Module.finrank ℝ ↥r₀
        + Module.finrank ℝ ↥(p₀ ⊓ q₀ ⊓ r₀) := by
  have htriple : p₀ ⊓ q₀ ⊓ r₀ = ⊥ := by rw [inf_pq]; simp
  rw [sup_pqr_top, htriple, inf_pq, inf_pr, inf_qr]
  -- finrank ℝ (ℝ × ℝ) = 2; left side = 2, right side = 3
  simp [finrank_p₀, finrank_q₀, finrank_r₀, finrank_top, finrank_bot,
    Module.finrank_prod, Module.finrank_self]

end Counterexample

end SecondIsomorphismTheoremModulesOQ01OQ01
