import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-
# The Converse Multisection: Residue-Subseries Summability ⟺ Summability

## What This Proves

The parent (`GeometricSeriesOQ09OQ01OQ01OQ01`) proved the *forward* multisection of
an arbitrary summable family `f : ℕ → M`: from `Summable f` one obtains, for every
modulus `q ≥ 1`, the summability of each residue subseries `n ↦ f (q·n + a)`
(`a < q`) and the regrouping identity

  `∑_{a<q} ∑'_n f (q·n + a) = ∑'_m f m`.

That direction relied on `M` being a **complete** Hausdorff uniform abelian group
(completeness so that each residue subseries converges).

This file answers its open question — the **converse** — and finds it both true and
*structurally cheaper*:

* **Converse (no completeness, no group).**  If each residue subseries
  `n ↦ f (q·n + a)` has sum `S a`, then `f` has sum `∑_{a<q} S a` — over *any*
  topological commutative additive monoid with continuous addition.
* **Value identity over a mere Hausdorff monoid.**  When the residue subseries are
  summable, `∑_{a<q} ∑'_n f (q·n + a) = ∑'_m f m` holds with **no completeness
  hypothesis** — only `T2`.
* **Equivalence (asymmetric hypotheses).**  The *forward* implication
  `Summable f → Summable (residue)` is genuinely harder: extracting an infinite
  subseries needs the Cauchy criterion, i.e. a *complete* uniform group.  Over such a
  group the characterisation is two-sided:
  `Summable f ↔ ∀ a : Fin q, Summable (fun n => f (q·n + a))`.

## The Minimal Hypotheses (answering the open question)

The open question asks for the minimal hypotheses under which residue-subseries
summability is *equivalent* to summability of `f`, and whether the regrouping value
identity survives the drop from complete to merely Hausdorff `M`.

The answer is as clean as possible.  The **converse** direction
(`hasSum_of_residues`) — the heart of the matter — needs only that `M` is a
topological commutative additive *monoid* with `ContinuousAdd`: no group structure,
no uniform/Cauchy structure, and crucially **no completeness**.  Because the number
of residues `q` is *finite*, the converse is a finite combination of `HasSum`s
(`hasSum_sum`), each obtained by viewing a residue subseries as a function on
`ℕ × Fin q` supported on a single fiber.  Completeness was an artifact of the
*forward* direction (proving each subseries converges); the converse takes that
convergence as a hypothesis and so never needs it.

For the two-sided *equivalence* one additionally needs the forward inclusion
`Summable f → Summable (residue)`.  This direction is *not* free: a subseries of a
convergent series converges only by the Cauchy criterion, so `Summable.comp_injective`
requires a **complete** uniform abelian group.  Thus the two implications are
genuinely asymmetric — the converse holds over a bare monoid, the forward needs
completeness — and the equivalence holds over a complete uniform abelian group (the
same setting as the parent's forward multisection).

## Why This Is Not Already in Mathlib

Mathlib has `Nat.divModEquiv`, `Equiv.hasSum_iff`, `Function.Injective.hasSum_iff`,
`hasSum_sum`, and `Summable.comp_injective`, but not their assembly into the
two-sided characterisation `Summable f ↔ residue-subseries summable` for a finite
modulus, nor the observation that the converse regrouping holds over an arbitrary
Hausdorff topological additive monoid.

## Status: 0 sorries, 0 axioms
-/

namespace GeometricSeriesOQ09OQ01OQ01OQ01OQ01

set_option linter.unusedSectionVars false

/-! ## Injectivity of the residue map -/

/-- For `q ≠ 0` the residue map `n ↦ q·n + a` is injective `ℕ → ℕ`. -/
theorem residue_injective {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    Function.Injective (fun n : ℕ => q * n + a) := by
  intro n m h
  simp only at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) (Nat.add_right_cancel h)

/-! ## The converse over a topological commutative additive monoid

No completeness and no group structure: only `ContinuousAdd` (for the finite sum of
`HasSum`s) and `T2` (for the value identity). -/

section Monoid

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] {f : ℕ → M}

/-- The residue subseries `a`, embedded into `ℕ × Fin q` supported on the fiber
`p.2 = a`. -/
private def fiber (f : ℕ → M) (q : ℕ) (a : Fin q) (p : ℕ × Fin q) : M :=
  if p.2 = a then f (q * p.1 + (a : ℕ)) else 0

/-- The single-fiber embedding `fiber f q a` has the same sum `S` as the residue
subseries `n ↦ f (q·n + a)` itself: viewing the subseries as a function on
`ℕ × Fin q` supported on one fiber leaves its `HasSum` unchanged. -/
theorem hasSum_fiber {q : ℕ} (a : Fin q) {S : M}
    (ha : HasSum (fun n : ℕ => f (q * n + (a : ℕ))) S) :
    HasSum (fiber f q a) S := by
  have hinj : Function.Injective (fun n : ℕ => (n, a)) := by
    intro n m h; simpa using congrArg Prod.fst h
  have hvanish : ∀ p : ℕ × Fin q, p ∉ Set.range (fun n : ℕ => (n, a)) →
      fiber f q a p = 0 := by
    intro p hp
    have hp2 : p.2 ≠ a := fun h => hp ⟨p.1, by ext <;> simp [h]⟩
    simp [fiber, hp2]
  have hcomp : (fiber f q a) ∘ (fun n : ℕ => (n, a))
      = fun n : ℕ => f (q * n + (a : ℕ)) := by funext n; simp [fiber]
  exact (hinj.hasSum_iff hvanish).mp (by rw [hcomp]; exact ha)

variable [ContinuousAdd M]

/-- **Converse multisection (`HasSum` form).**  If each residue subseries
`n ↦ f (q·n + a)` has sum `S a`, then `f` has sum `∑_{a<q} S a`.  Requires *no*
completeness and *no* group structure: with `q` residues the total is a finite sum
of `HasSum`s. -/
theorem hasSum_of_residues {q : ℕ} [NeZero q] {S : Fin q → M}
    (hS : ∀ a : Fin q, HasSum (fun n : ℕ => f (q * n + (a : ℕ))) (S a)) :
    HasSum f (∑ a : Fin q, S a) := by
  -- A finite sum of the `q` single-fiber embeddings.
  have hsum : HasSum (fun p : ℕ × Fin q => ∑ a : Fin q, fiber f q a p)
      (∑ a : Fin q, S a) :=
    hasSum_sum fun a _ => hasSum_fiber a (hS a)
  -- The fiberwise sum collapses to the reindexed term `f (q·p.1 + p.2)`.
  have hpt : (fun p : ℕ × Fin q => ∑ a : Fin q, fiber f q a p)
      = fun p : ℕ × Fin q => f (q * p.1 + (p.2 : ℕ)) := by
    funext p
    rw [show f (q * p.1 + (p.2 : ℕ)) = fiber f q p.2 p by simp [fiber]]
    exact Finset.sum_eq_single p.2
      (fun a _ ha => by simp [fiber, Ne.symm ha])
      (fun h => absurd (Finset.mem_univ _) h)
  rw [hpt] at hsum
  -- Transport the two-dimensional `HasSum` back to `ℕ` along `(divModEquiv q).symm`.
  have hcomp : (f ∘ (Nat.divModEquiv q).symm)
      = fun p : ℕ × Fin q => f (q * p.1 + (p.2 : ℕ)) := by
    funext p
    rw [Function.comp_apply, Nat.divModEquiv_symm_apply, Nat.mul_comm p.1 q]
  exact ((Nat.divModEquiv q).symm.hasSum_iff).mp (by rw [hcomp]; exact hsum)

/-- **Converse multisection (`Summable` form).**  If each residue subseries is
summable, so is `f`. -/
theorem summable_of_residues {q : ℕ} [NeZero q]
    (hS : ∀ a : Fin q, Summable (fun n : ℕ => f (q * n + (a : ℕ)))) :
    Summable f :=
  ⟨_, hasSum_of_residues fun a => (hS a).hasSum⟩

/-- **Multisection value identity without completeness.**  When the residue
subseries are summable, the regrouping `∑_{a<q} ∑'_n f (q·n + a) = ∑'_m f m` holds
over any *Hausdorff* topological commutative additive monoid — the completeness
hypothesis of the forward file is dropped. -/
theorem tsum_multisection_of_residues [T2Space M] {q : ℕ} [NeZero q]
    (hS : ∀ a : Fin q, Summable (fun n : ℕ => f (q * n + (a : ℕ)))) :
    ∑ a : Fin q, (∑' n : ℕ, f (q * n + (a : ℕ))) = ∑' m : ℕ, f m :=
  (hasSum_of_residues (S := fun a : Fin q => ∑' n : ℕ, f (q * n + (a : ℕ)))
    fun a => (hS a).hasSum).tsum_eq.symm

/-- `Finset.range` form of the value identity. -/
theorem tsum_multisection_range_of_residues [T2Space M] {q : ℕ} [NeZero q]
    (hS : ∀ a : Fin q, Summable (fun n : ℕ => f (q * n + (a : ℕ)))) :
    ∑ a ∈ Finset.range q, (∑' n : ℕ, f (q * n + a)) = ∑' m : ℕ, f m := by
  rw [← tsum_multisection_of_residues hS,
    Fin.sum_univ_eq_sum_range (fun a => ∑' n : ℕ, f (q * n + a)) q]

/-- **Even/odd converse.**  If the even-indexed and odd-indexed subseries are both
summable, so is `f`. -/
theorem summable_of_even_odd
    (he : Summable (fun n : ℕ => f (2 * n))) (ho : Summable (fun n : ℕ => f (2 * n + 1))) :
    Summable f := by
  apply summable_of_residues (q := 2)
  intro a; fin_cases a
  · simpa using he
  · simpa using ho

/-- **Even/odd value identity over a Hausdorff monoid.**
`∑'_n f (2n) + ∑'_n f (2n+1) = ∑'_m f m`, with no completeness assumption. -/
theorem tsum_even_add_odd_of_residues [T2Space M]
    (he : Summable (fun n : ℕ => f (2 * n))) (ho : Summable (fun n : ℕ => f (2 * n + 1))) :
    (∑' n : ℕ, f (2 * n)) + (∑' n : ℕ, f (2 * n + 1)) = ∑' m : ℕ, f m := by
  have h : ∀ a : Fin 2, Summable (fun n : ℕ => f (2 * n + (a : ℕ))) := by
    intro a; fin_cases a
    · simpa using he
    · simpa using ho
  simpa [Finset.sum_range_succ] using tsum_multisection_range_of_residues h

end Monoid

/-! ## The forward direction and the equivalence

The forward inclusion `Summable f → Summable (residue)` is **not free**: extracting an
infinite subseries from a convergent series requires the Cauchy criterion, hence a
*complete* uniform group (`Summable.comp_injective`).  This is the asymmetry with the
converse, which needs nothing.  Over a complete uniform group both directions hold and
we obtain the two-sided characterisation. -/

section Group

variable {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
  [CompleteSpace M] {f : ℕ → M}

/-- **Forward direction.**  Each residue subseries of a summable family is summable.
Unlike the converse, this consumes completeness (`Summable.comp_injective` lives in
the complete-uniform-group section): a subseries of a convergent series converges only
because the ambient group is complete. -/
theorem summable_residue (hf : Summable f) {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    Summable (fun n : ℕ => f (q * n + a)) := by
  simpa [Function.comp_def] using hf.comp_injective (residue_injective hq a)

/-- **Equivalence (the two-sided characterisation).**  For any fixed modulus `q ≥ 1`,
over a complete Hausdorff-free uniform abelian group, summability of `f` is equivalent
to summability of all `q` residue subseries.  The forward implication needs the
completeness; the converse (`summable_of_residues`) needs none of it. -/
theorem summable_iff_residues {q : ℕ} [NeZero q] :
    Summable f ↔ ∀ a : Fin q, Summable (fun n : ℕ => f (q * n + (a : ℕ))) :=
  ⟨fun hf a => summable_residue hf (NeZero.ne q) (a : ℕ), summable_of_residues⟩

end Group

/-! ## Concrete check -/

/-- Sanity check: the converse recovers summability of `n ↦ (1/2)^n` from the
summability of its even and odd subseries, and the value identity holds — with no
completeness invoked at the multisection step. -/
example :
    (∑' n : ℕ, (1 / 2 : ℝ) ^ (2 * n)) + (∑' n : ℕ, (1 / 2 : ℝ) ^ (2 * n + 1))
      = ∑' m : ℕ, (1 / 2 : ℝ) ^ m := by
  have hbase : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply tsum_even_add_odd_of_residues
  · simpa using summable_residue hbase (by norm_num) 0
  · simpa using summable_residue hbase (by norm_num) 1

end GeometricSeriesOQ09OQ01OQ01OQ01OQ01
