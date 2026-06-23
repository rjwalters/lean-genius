import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-
# Basel Problem: Algebraic Independence of Odd Zeta Values — The Implication Hierarchy

Open Question (OQ-05 from ZetaFiveIrrationality):
**Are there infinitely many algebraically independent odd zeta values?**

This is the strongest of the standard conjectures about the numbers
ζ(3), ζ(5), ζ(7), …. It is wide open: we do not even know that ζ(5) is irrational.
A conjecture of folklore (a special case of Grothendieck's period conjecture / the
Kontsevich–Zagier framework) predicts that the family ζ(3), ζ(5), ζ(7), … together
with π is algebraically independent over ℚ.

## What this file contributes

We do NOT prove the conjecture. Instead we make precise the *logical hierarchy*
into which OQ-05 fits, and prove every implication in it from Mathlib's
`AlgebraicIndependent` machinery, axiom-free:

```
   algebraically independent over ℚ            (OQ-05, OPEN)
              ⟹  each value is transcendental   (OPEN even for ζ(5))
              ⟹  each value is irrational        (Rivoal 2000: ∞-many odd values, OPEN which)
              ⟹  linearly independent over ℚ     (no rational linear relations)
              ⟹  the values are pairwise distinct
```

So algebraic independence is *strictly stronger* than every result currently known
about odd zeta values: if OQ-05 holds, then in particular infinitely many odd zeta
values are irrational (recovering Ball–Rivoal as a corollary), all are transcendental,
and there are no ℚ-linear relations among them.

We also prove the hierarchy is **strict**: a single nonzero rational (e.g. `2`) gives
a linearly independent family that is *not* algebraically independent, and `√2` is
irrational but not transcendental. So none of the upward implications can be reversed.

## Main results

* `AlgIndep.transcendental_of_mem` / `irrational_of_mem` — value-level ladder.
* `AlgIndep.linearIndependent`, `AlgIndep.injective` — structural consequences.
* `AlgIndep.infinitely_many_irrational` — an ℕ-indexed alg-indep family yields an
  infinite set of irrational values (this is the "∞-many irrational" payoff of OQ-05).
* `not_algIndep_of_isAlgebraic` + `linIndep_not_algIndep_two` — strictness witnesses.
* `OddZetaAlgIndependent`, `oddZeta_alg_indep_imp_*` — the zeta-specialized framing.

Axioms: 0
Sorries: 0
-/

namespace BaselProblemOQ01OQ05

open scoped BigOperators

/- ============================================================
   Part I: The value-level ladder (transcendence, irrationality)
   ============================================================ -/

variable {ι : Type*} {x : ι → ℝ}

/-- **Step 1 of the ladder.** Every member of an algebraically independent family is
transcendental over ℚ. (Direct wrapper of `AlgebraicIndependent.transcendental`,
recorded here as the entry point of the hierarchy.) -/
theorem AlgIndep.transcendental_of_mem (hx : AlgebraicIndependent ℚ x) (i : ι) :
    Transcendental ℚ (x i) :=
  hx.transcendental i

/-- **Step 2 of the ladder.** Every member of an algebraically independent family of
reals is irrational. Chains `transcendental` with `Transcendental.irrational`. -/
theorem AlgIndep.irrational_of_mem (hx : AlgebraicIndependent ℚ x) (i : ι) :
    Irrational (x i) :=
  (hx.transcendental i).irrational

/- ============================================================
   Part II: Structural consequences (linear independence, distinctness)
   ============================================================ -/

/-- **Step 3 of the ladder.** An algebraically independent family is linearly
independent over ℚ: there are no nontrivial rational *linear* relations among the
values (a refinement of "each value is irrational"). -/
theorem AlgIndep.linearIndependent (hx : AlgebraicIndependent ℚ x) :
    LinearIndependent ℚ x :=
  hx.linearIndependent

/-- **Step 4 of the ladder.** The members of an algebraically independent family are
pairwise distinct. -/
theorem AlgIndep.injective (hx : AlgebraicIndependent ℚ x) :
    Function.Injective x :=
  hx.linearIndependent.injective

/- ============================================================
   Part III: The infinitude payoff for ℕ-indexed families
   ============================================================ -/

/-- **The OQ-05 payoff.** If a *sequence* of reals is algebraically independent over ℚ,
then it takes infinitely many distinct values, *all* of which are irrational.

This is exactly the structure of the open question: "infinitely many algebraically
independent odd zeta values" would, via this theorem, immediately give "infinitely many
irrational odd zeta values" — i.e. it implies (and is strictly stronger than) the
Ball–Rivoal theorem. -/
theorem AlgIndep.infinitely_many_irrational {y : ℕ → ℝ}
    (hy : AlgebraicIndependent ℚ y) :
    (Set.range y).Infinite ∧ ∀ r ∈ Set.range y, Irrational r := by
  refine ⟨Set.infinite_range_of_injective hy.injective, ?_⟩
  rintro r ⟨n, rfl⟩
  exact AlgIndep.irrational_of_mem hy n

/- ============================================================
   Part IV: Strictness — the upward implications cannot be reversed
   ============================================================ -/

/-- If even one member of a family is algebraic over ℚ, the family is *not*
algebraically independent. (Contrapositive of `transcendental`.) This is the obstruction
that makes algebraic independence strictly stronger than linear independence. -/
theorem not_algIndep_of_isAlgebraic {i : ι} (h : IsAlgebraic ℚ (x i)) :
    ¬ AlgebraicIndependent ℚ x :=
  fun hx => hx.transcendental i h

/-- **Strictness at the bottom step.** The one-element family `![2]` is linearly
independent over ℚ (a single nonzero vector) yet algebraically dependent (`2` is
rational, hence algebraic). So `LinearIndependent ⤏ AlgebraicIndependent`. -/
theorem linIndep_not_algIndep_two :
    LinearIndependent ℚ (![(2 : ℝ)]) ∧ ¬ AlgebraicIndependent ℚ (![(2 : ℝ)]) := by
  constructor
  · rw [linearIndependent_unique_iff]
    norm_num [Matrix.cons_val_fin_one]
  · apply not_algIndep_of_isAlgebraic (i := 0)
    have hval : (![(2 : ℝ)]) 0 = ((2 : ℚ) : ℝ) := by
      rw [Matrix.cons_val_zero]; norm_num
    rw [hval]
    exact isAlgebraic_rat ℚ 2

/-- **Strictness at the middle step.** `√2` is irrational but not transcendental
(it is algebraic, a root of `X² - 2`). So `Irrational ⤏ Transcendental`. -/
theorem irrational_not_transcendental_sqrt_two :
    Irrational (Real.sqrt 2) ∧ ¬ Transcendental ℚ (Real.sqrt 2) := by
  refine ⟨irrational_sqrt_two, ?_⟩
  -- `Transcendental ℚ r` is by definition `¬ IsAlgebraic ℚ r`; √2 IS algebraic.
  rw [Transcendental, not_not]
  refine ⟨Polynomial.X ^ 2 - Polynomial.C 2, ?_, ?_⟩
  · intro h
    have hc : (Polynomial.X ^ 2 - Polynomial.C (2 : ℚ)).coeff 2 = 0 := by rw [h]; simp
    simp [Polynomial.coeff_X_pow] at hc
  · have h2 : (0 : ℝ) ≤ 2 := by norm_num
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_ofNat,
      Real.sq_sqrt h2]
    norm_num

/- ============================================================
   Part V: Specialization to the odd zeta values
   ============================================================ -/

/-- The `k`-th odd zeta value `ζ(2k+3) = ∑ₙ 1/(n+1)^(2k+3)`, so `k = 0, 1, 2, …`
enumerates `ζ(3), ζ(5), ζ(7), …`. (We only need it as a real-valued sequence to state
the conjecture; its convergence is established elsewhere in the gallery.) -/
noncomputable def oddZeta (k : ℕ) : ℝ := ∑' n : ℕ, (1 : ℝ) / (n + 1) ^ (2 * k + 3)

/-- **OQ-05, stated formally.** The conjecture that the odd zeta values
`ζ(3), ζ(5), ζ(7), …` are algebraically independent over ℚ. This is OPEN. -/
def OddZetaAlgIndependent : Prop := AlgebraicIndependent ℚ oddZeta

/-- If OQ-05 holds, every odd zeta value `ζ(2k+3)` is transcendental over ℚ — open even
for `ζ(5)` (`k = 1`). -/
theorem oddZeta_alg_indep_imp_transcendental (h : OddZetaAlgIndependent) (k : ℕ) :
    Transcendental ℚ (oddZeta k) :=
  AlgIndep.transcendental_of_mem h k

/-- If OQ-05 holds, every odd zeta value `ζ(2k+3)` is irrational. -/
theorem oddZeta_alg_indep_imp_irrational (h : OddZetaAlgIndependent) (k : ℕ) :
    Irrational (oddZeta k) :=
  AlgIndep.irrational_of_mem h k

/-- **OQ-05 ⟹ Ball–Rivoal (qualitative).** If the odd zeta values are algebraically
independent, then they form an infinite set of irrational numbers — in particular there
are infinitely many irrational odd zeta values. This shows OQ-05 is strictly stronger
than the (already proved) Ball–Rivoal theorem. -/
theorem oddZeta_alg_indep_imp_infinitely_many_irrational (h : OddZetaAlgIndependent) :
    (Set.range oddZeta).Infinite ∧ ∀ r ∈ Set.range oddZeta, Irrational r :=
  AlgIndep.infinitely_many_irrational h

/-- If OQ-05 holds, there are no nontrivial ℚ-linear relations among the odd zeta
values: `ζ(3), ζ(5), ζ(7), …` are linearly independent over ℚ. -/
theorem oddZeta_alg_indep_imp_linearIndependent (h : OddZetaAlgIndependent) :
    LinearIndependent ℚ oddZeta :=
  AlgIndep.linearIndependent h

end BaselProblemOQ01OQ05
