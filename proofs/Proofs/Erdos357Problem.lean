/-
# Erdős Problem #357: Distinct Consecutive Sums

Let f(n) be the maximal k such that there exist integers 1 ≤ a₁ < a₂ < ... < aₖ ≤ n
with all "consecutive sums" Σᵢ₌ᵤᵛ aᵢ distinct. Is f(n) = o(n)?

**Known**: f(n) ≥ (2+o(1))√n (Weisenberg, via B₂ sequences).

**Non-monotone variant**: For unrestricted sequences, g(n) = Θ(n) (Hegyvári 1986).

**Infinite set conjectures**: If A ⊆ ℕ is infinite with distinct consecutive sums,
then A has lower density 0 (proved) and density 0 (conjectured), and Σ 1/aₙ converges (conjectured).

**References**:
- Erdős (1977): Problems and results on combinatorial number theory III
- Hegyvári (1986): On consecutive sums in sequences. Acta Math. Hungar. 48, 193–200
- Erdős-Turán (1941): On a problem of Sidon. J. London Math. Soc. 16, 212–215
- https://erdosproblems.com/357
-/

import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

open Filter Asymptotics Real

namespace Erdos357

/- ## Core Definition -/

/--
A sequence a : ι → α **has distinct sums** over ord-connected intervals if
the map J ↦ Σ_{i ∈ J} a(i) is injective on the family of ord-connected Finsets.

An interval J ⊆ ι is ord-connected if: i ∈ J and k ∈ J and i ≤ j ≤ k implies j ∈ J.
-/
def HasDistinctSums {ι α : Type*} [Preorder ι] [AddCommMonoid α] (a : ι → α) : Prop :=
  {J : Finset ι | J.OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, a x)

/- ## The Function f(n) -/

/--
The **Erdős #357 function** f(n): the maximal k such that there exist integers
1 ≤ a₁ < a₂ < ... < aₖ ≤ n with all consecutive sums Σᵢ₌ᵤᵛ aᵢ distinct.

Defined as the supremum over all valid sequence lengths k. Using sSup
makes this noncomputable but gives a clean definition.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a}

/--
The **non-monotone variant** g(n): maximal k for sequences 1 ≤ a₁, ..., aₖ ≤ n
(not necessarily strictly increasing) with distinct consecutive sums.

Since every strictly increasing sequence is a valid input for g, we have f(n) ≤ g(n).
-/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℕ, Set.range a ⊆ Set.Icc 1 n ∧ HasDistinctSums a}

/--
The **weakly monotone variant** h(n): maximal k for sequences 1 ≤ a₁ ≤ ... ≤ aₖ ≤ n
(weakly increasing, ties allowed) with distinct consecutive sums.

Since every strictly increasing sequence is weakly increasing, f(n) ≤ h(n).
-/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ Monotone a ∧ HasDistinctSums a}

/- ## The Main Conjecture -/

/--
**Erdős Problem #357 (OPEN)**

The main question: is f(n) = o(n)? That is, does the maximal sequence length
grow strictly sublinearly in n?

Since g(n) = Θ(n) (Hegyvári 1986), the strict monotonicity constraint is essential.
-/
def Erdos357Conjecture : Prop :=
  (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ))

/--
**Alternative formulation**: f(n)/n → 0 as n → ∞.

The ratio formulation is often more convenient to work with than the little-o
form, e.g. when transferring density statements.
-/
def Erdos357ConjectureAlt : Prop :=
  Tendsto (fun n ↦ (f n : ℝ) / n) atTop (𝓝 0)

/--
The little-o formulation and the ratio-limit formulation of the main conjecture
are equivalent.

This is `Asymptotics.isLittleO_iff_tendsto'`: for `f =o[l] g`, the side condition
`g x = 0 → f x = 0` only needs to hold eventually, and along `atTop` the
denominator `n` is eventually nonzero, so the implication is vacuous there.
-/
theorem conjecture_equiv : Erdos357Conjecture ↔ Erdos357ConjectureAlt := by
  unfold Erdos357Conjecture Erdos357ConjectureAlt
  have hgf : ∀ᶠ n : ℕ in atTop, (n : ℝ) = 0 → (f n : ℝ) = 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn h0
    rw [Nat.cast_eq_zero] at h0
    omega
  exact isLittleO_iff_tendsto' hgf

/- ## Known Results (Axiomatized) -/

/--
**Weisenberg's lower bound**: f(n) ≥ (2 + o(1))√n.

Proved via the connection to **B₂ sequences** (Sidon sets): any set A ⊆ [1,n]
where all pairwise sums aᵢ + aⱼ are distinct automatically has distinct
consecutive sums. The largest B₂ set in [1,n] has size (1 + o(1))√n
(Erdős-Turán 1941), giving the √n lower bound.
-/
axiom weisenberg_lower_bound :
  ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n : ℕ in atTop, (2 + o n) * Real.sqrt n ≤ (f n : ℝ)

/--
**Hegyvári (1986) bounds for g(n)**: (1/3 + o(1))n ≤ g(n) ≤ (2/3 + o(1))n.

This shows g(n) = Θ(n) — dramatically larger than the conjectured f(n) = o(n).
The key: without monotonicity, "most" elements can be included.
-/
axiom hegyvari_bounds :
  ∃ o₁ o₂ : ℕ → ℝ, o₁ =o[atTop] (1 : ℕ → ℝ) ∧ o₂ =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n : ℕ in atTop, (1/3 + o₁ n) * n ≤ (g n : ℝ) ∧
      (g n : ℝ) ≤ (2/3 + o₂ n) * n

/-- **Lower density 0** for infinite sets with distinct consecutive sums (proved).
Any infinite strictly increasing sequence A : ℕ → ℕ with distinct consecutive sums
has lower density 0. The density conjectured to be 0 (stronger) is open. -/
axiom infinite_set_lower_density_zero (A : ℕ → ℕ) (hA : StrictMono A)
    (hDist : HasDistinctSums A) :
    Filter.liminf (fun n : ℕ => #{k | A k ≤ n} / (n : ℝ)) atTop = 0

/- ## Open Conjectures for Infinite Sets -/

/-- **Density 0 conjecture** (OPEN): any infinite A with distinct consecutive sums
has density 0 (stronger than lower density 0, which is proved). -/
def InfiniteDensityZeroConjecture : Prop :=
  ∀ A : ℕ → ℕ, StrictMono A → HasDistinctSums A →
    Filter.Tendsto (fun n : ℕ => #{k | A k ≤ n} / (n : ℝ)) atTop (𝓝 0)

/-- **Sum convergence conjecture** (OPEN): for any infinite A with distinct consecutive sums,
the series Σ 1/A(k) converges. -/
def InfiniteSumConvergesConjecture : Prop :=
  ∀ A : ℕ → ℕ, StrictMono A → HasDistinctSums A →
    Summable (fun k => (1 : ℝ) / A k)

/- ## Observation: g(n) Dominates f(n) -/

/-- The strictly increasing constraint makes f more restrictive than g,
so g(n) ≥ f(n). Formally comparing the two requires relating sums over ℤ-sequences
to sums over ℕ-sequences; this is recorded here as a remark for future work. -/
def g_ge_f_Remark : Prop := ∀ n, f n ≤ g n

end Erdos357
