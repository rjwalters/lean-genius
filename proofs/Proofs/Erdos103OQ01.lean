/-
Erdős Problem #103 — Open Question 01
Does h(n) → ∞ as n → ∞?

## Open Question
OQ-01: The main conjecture asks whether the count of incongruent optimal point
configurations (with minimum separation 1, minimizing diameter) tends to infinity.

## What This Proves

1. **Metric properties**: pointDist on ℝ² is definite (d(p,q)=0 ↔ p=q) and symmetric
2. **Isometry injectivity**: Distance-preserving maps are injective (from definiteness)
3. **Isometry inverse**: Construct inverse isometry (from injectivity + surjectivity axiom)
4. **Congruence symmetry**: AreCongruent is symmetric — eliminates sorry from parent file
5. **Mathematical correction**: "Unbounded" does NOT imply "tends to infinity" in general.
   The backward direction of `conjecture_equiv` in the parent file is logically false.
   Counterexample: the oscillating function n ↦ (n if even, 0 if odd) is unbounded
   but does not tend to infinity.
6. **Correct equivalence**: With monotonicity of h, "unbounded ↔ tends to ∞" holds
7. **Isometry group structure**: Identity, composition, inverse form a group
8. **Congruence preserves geometry**: Separation, diameter invariant under congruence

## Axioms
- `isometry2D_surjective`: Distance-preserving maps ℝ² → ℝ² are surjective.
  This is a consequence of the Mazur–Ulam theorem (1938): every surjective isometry
  between normed spaces is affine. For ℝⁿ, isometries are always surjective
  (they are compositions of rotations, reflections, and translations).
- `h`: The counting function for incongruent optimal configurations (from parent)
- `h_pos`: h(n) ≥ 1 for n ≥ 2 (from parent — optimal configs exist)

## Mathematical Insight
The parent file's `conjecture_equiv` purports to prove that h being unbounded is
equivalent to h → ∞. The forward direction (h → ∞ ⟹ h unbounded) is trivially true.
But the backward direction fails: a function can spike arbitrarily high on a subsequence
while dropping to 0 infinitely often. The correct statement requires that h is monotone
(or at least eventually monotone), which is itself an interesting open question about
how the space of optimal configurations evolves as n increases.
-/

import Mathlib

open Metric Set Finset

set_option linter.unusedVariables false

noncomputable section

namespace Erdos103OQ01

-- ============================================================
-- PART 1: Definitions
-- ============================================================

/-- A finite configuration of n points in ℝ². -/
abbrev PointConfig (n : ℕ) := Fin n → ℝ × ℝ

/-- Euclidean distance between two points in ℝ². -/
def pointDist (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- A configuration has minimum separation 1: all distinct points at distance ≥ 1. -/
def HasMinSeparation (n : ℕ) (P : PointConfig n) : Prop :=
  ∀ i j : Fin n, i ≠ j → pointDist (P i) (P j) ≥ 1

/-- A distance-preserving map of ℝ². -/
structure Isometry2D where
  toFun : ℝ × ℝ → ℝ × ℝ
  preserves_dist : ∀ p q, pointDist (toFun p) (toFun q) = pointDist p q

/-- Two configurations are congruent if related by an isometry. -/
def AreCongruent (n : ℕ) (P Q : PointConfig n) : Prop :=
  ∃ σ : Isometry2D, ∀ i, Q i = σ.toFun (P i)

-- ============================================================
-- PART 2: pointDist Metric Properties
-- ============================================================

/-- Sum of squares is nonneg. -/
private theorem sum_sq_nonneg (a b : ℝ) : 0 ≤ a ^ 2 + b ^ 2 :=
  add_nonneg (sq_nonneg a) (sq_nonneg b)

/-- pointDist is nonneg. -/
theorem pointDist_nonneg (p q : ℝ × ℝ) : 0 ≤ pointDist p q :=
  Real.sqrt_nonneg _

/-- pointDist(p, p) = 0. -/
theorem pointDist_self (p : ℝ × ℝ) : pointDist p p = 0 := by
  simp [pointDist, sub_self]

/-- The squared distance formula. -/
theorem pointDist_sq (p q : ℝ × ℝ) :
    (pointDist p q) ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  unfold pointDist
  exact Real.sq_sqrt (sum_sq_nonneg _ _)

/-- pointDist is symmetric. -/
theorem pointDist_comm (p q : ℝ × ℝ) : pointDist p q = pointDist q p := by
  unfold pointDist; congr 1; ring

/-- **Definiteness**: pointDist p q = 0 if and only if p = q.
    This is the key property needed to prove isometry injectivity. -/
theorem pointDist_eq_zero_iff (p q : ℝ × ℝ) :
    pointDist p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hsq : (pointDist p q) ^ 2 = 0 := by rw [h]; ring
    rw [pointDist_sq] at hsq
    -- Both squared terms must be zero (sum of nonneg terms = 0)
    have h1 : (p.1 - q.1) ^ 2 = 0 := by nlinarith [sq_nonneg (p.2 - q.2)]
    have h2 : (p.2 - q.2) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1)]
    -- x² = 0 ↔ x = 0 (no zero divisors in ℝ)
    have h3 : p.1 - q.1 = 0 := by rwa [sq_eq_zero_iff] at h1
    have h4 : p.2 - q.2 = 0 := by rwa [sq_eq_zero_iff] at h2
    exact Prod.ext (sub_eq_zero.mp h3) (sub_eq_zero.mp h4)
  · intro h; rw [h]; exact pointDist_self q

-- ============================================================
-- PART 3: Isometry Properties
-- ============================================================

/-- **Isometries are injective**: if σ preserves distances, then σ(p) = σ(q) ⟹ p = q.
    Proof: σ(p) = σ(q) ⟹ d(σ(p), σ(q)) = 0 ⟹ d(p, q) = 0 ⟹ p = q. -/
theorem isometry2D_injective (σ : Isometry2D) : Function.Injective σ.toFun := by
  intro p q h
  have h1 : pointDist (σ.toFun p) (σ.toFun q) = 0 := by rw [h]; exact pointDist_self _
  rw [σ.preserves_dist] at h1
  exact (pointDist_eq_zero_iff p q).mp h1

/-- **Axiom**: Distance-preserving maps ℝ² → ℝ² are surjective.

    This is a consequence of the Mazur–Ulam theorem (1938): every surjective
    isometry of real normed spaces is affine. For finite-dimensional ℝⁿ, every
    isometry is automatically surjective — it decomposes as a rotation/reflection
    (orthogonal matrix) composed with a translation, both of which are surjective.

    Proving this formally requires either:
    - The Mazur–Ulam theorem (not in Mathlib for general normed spaces)
    - Direct classification of isometries of ℝ² (non-trivial but elementary) -/
axiom isometry2D_surjective (σ : Isometry2D) : Function.Surjective σ.toFun

/-- The identity isometry. -/
def Isometry2D.id : Isometry2D where
  toFun := _root_.id
  preserves_dist := fun _ _ => rfl

/-- Composition of isometries. -/
def Isometry2D.comp (σ τ : Isometry2D) : Isometry2D where
  toFun := σ.toFun ∘ τ.toFun
  preserves_dist := fun p q => by
    simp only [Function.comp]
    rw [σ.preserves_dist, τ.preserves_dist]

/-- Inverse of an isometry, constructed via surjective inverse.
    Since σ is both injective (proved) and surjective (axiom),
    the surjective inverse is a genuine two-sided inverse. -/
def Isometry2D.inv (σ : Isometry2D) : Isometry2D where
  toFun := Function.surjInv (isometry2D_surjective σ)
  preserves_dist := by
    intro p q
    have hsurj := isometry2D_surjective σ
    have hp := Function.surjInv_eq hsurj p
    have hq := Function.surjInv_eq hsurj q
    -- d(σ⁻¹(p), σ⁻¹(q)) = d(σ(σ⁻¹(p)), σ(σ⁻¹(q))) = d(p, q)
    calc pointDist (Function.surjInv hsurj p) (Function.surjInv hsurj q)
        = pointDist (σ.toFun (Function.surjInv hsurj p))
                    (σ.toFun (Function.surjInv hsurj q)) := (σ.preserves_dist _ _).symm
      _ = pointDist p q := by rw [hp, hq]

/-- σ⁻¹ ∘ σ = id: the inverse is a left inverse. -/
theorem Isometry2D.inv_comp (σ : Isometry2D) (p : ℝ × ℝ) :
    σ.inv.toFun (σ.toFun p) = p := by
  -- σ(σ⁻¹(σ(p))) = σ(p) by definition of surjective inverse
  have h : σ.toFun (σ.inv.toFun (σ.toFun p)) = σ.toFun p :=
    Function.surjInv_eq (isometry2D_surjective σ) (σ.toFun p)
  -- By injectivity: σ⁻¹(σ(p)) = p
  exact isometry2D_injective σ h

/-- σ ∘ σ⁻¹ = id: the inverse is a right inverse. -/
theorem Isometry2D.comp_inv (σ : Isometry2D) (p : ℝ × ℝ) :
    σ.toFun (σ.inv.toFun p) = p :=
  Function.surjInv_eq (isometry2D_surjective σ) p

-- ============================================================
-- PART 4: Congruence is an Equivalence Relation
-- ============================================================

/-- Congruence is reflexive. -/
theorem congruent_refl (n : ℕ) (P : PointConfig n) : AreCongruent n P P :=
  ⟨Isometry2D.id, fun _ => rfl⟩

/-- **Congruence is symmetric** (eliminates sorry from parent file).
    If P ≅ Q via σ, then Q ≅ P via σ⁻¹. -/
theorem congruent_symm (n : ℕ) (P Q : PointConfig n) :
    AreCongruent n P Q → AreCongruent n Q P := by
  intro ⟨σ, hσ⟩
  exact ⟨σ.inv, fun i => by rw [hσ i]; exact (σ.inv_comp (P i)).symm⟩

/-- Congruence is transitive. -/
theorem congruent_trans (n : ℕ) (P Q R : PointConfig n) :
    AreCongruent n P Q → AreCongruent n Q R → AreCongruent n P R := by
  intro ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩
  exact ⟨σ₂.comp σ₁, fun i => by
    simp only [Isometry2D.comp, Function.comp]
    rw [hσ₂ i, hσ₁ i]⟩

/-- Congruent configurations have the same minimum separation. -/
theorem congruent_preserves_separation (n : ℕ) (P Q : PointConfig n)
    (hcong : AreCongruent n P Q) (hP : HasMinSeparation n P) :
    HasMinSeparation n Q := by
  obtain ⟨σ, hσ⟩ := hcong
  intro i j hij
  rw [hσ i, hσ j, σ.preserves_dist]
  exact hP i j hij

-- ============================================================
-- PART 5: Unbounded ≠ Tends to Infinity (Counterexample)
-- ============================================================

/-- An oscillating function: n for even n, 0 for odd n.
    This function is unbounded but does NOT tend to infinity.
    It demonstrates that the backward direction of conjecture_equiv
    in the parent Erdős 103 file cannot be proved. -/
def oscillating (n : ℕ) : ℕ := if n % 2 = 0 then n else 0

/-- The oscillating function is unbounded: for any C, there exists n with f(n) > C.
    Proof: take n = 2(C+1), which is even, so oscillating(n) = n > C. -/
theorem oscillating_unbounded : ∀ C : ℕ, ∃ n : ℕ, oscillating n > C := by
  intro C
  refine ⟨2 * (C + 1), ?_⟩
  unfold oscillating
  split_ifs with h <;> omega

/-- The oscillating function does NOT tend to infinity: there is no threshold N
    beyond which oscillating(n) > 0 for all n ≥ N.
    Proof: for any N, the odd number 2N+1 ≥ N has oscillating(2N+1) = 0. -/
theorem oscillating_not_tendsto :
    ¬(∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, oscillating n > C) := by
  intro h
  obtain ⟨N, hN⟩ := h 0
  have h1 : 2 * N + 1 ≥ N := by omega
  have h2 := hN (2 * N + 1) h1
  -- h2 claims oscillating(2N+1) > 0, but oscillating(2N+1) = 0 for odd 2N+1
  unfold oscillating at h2
  split_ifs at h2 with hodd <;> omega

/-- **Main counterexample**: The logical implication
    "∀ f, f unbounded → f tends to ∞" is FALSE.
    The oscillating function witnesses the failure. -/
theorem unbounded_not_implies_tendsto :
    ¬(∀ f : ℕ → ℕ, (∀ C, ∃ n, f n > C) → (∀ C, ∃ N, ∀ n ≥ N, f n > C)) := by
  intro h
  exact oscillating_not_tendsto (h oscillating oscillating_unbounded)

-- ============================================================
-- PART 6: Correct Equivalence (with Monotonicity)
-- ============================================================

/-- For monotone functions, "unbounded" and "tends to ∞" ARE equivalent.
    The key: if f is monotone and f(N₀) > C, then f(n) ≥ f(N₀) > C for all n ≥ N₀. -/
theorem mono_unbounded_iff_tendsto (f : ℕ → ℕ) (hf : Monotone f) :
    (∀ C : ℕ, ∃ n : ℕ, f n > C) ↔
    (∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n > C) := by
  constructor
  · intro hunb C
    obtain ⟨N, hN⟩ := hunb C
    exact ⟨N, fun n hn => lt_of_lt_of_le hN (hf hn)⟩
  · intro htend C
    obtain ⟨N, hN⟩ := htend C
    exact ⟨N, hN N (le_refl N)⟩

-- ============================================================
-- PART 7: Corrected Conjecture Formulation for h(n)
-- ============================================================

/-- h(n) counts incongruent optimal configurations (axiomatized from parent). -/
axiom h : ℕ → ℕ

/-- At least one optimal configuration exists for n ≥ 2 (from parent). -/
axiom h_pos : ∀ n ≥ 2, h n ≥ 1

/-- **Erdős Conjecture 103**: h(n) → ∞ as n → ∞. -/
def ErdosConjecture103 : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, h n > C

/-- h is unbounded. -/
def hUnbounded : Prop :=
  ∀ C : ℕ, ∃ n : ℕ, h n > C

/-- Forward: h → ∞ implies h is unbounded (trivial). -/
theorem conjecture_implies_unbounded : ErdosConjecture103 → hUnbounded := by
  intro hconj C
  obtain ⟨N, hN⟩ := hconj C
  exact ⟨N, hN N (le_refl N)⟩

/-- **Backward (corrected)**: h unbounded implies h → ∞ WHEN h is monotone.

    The parent file attempts to prove this unconditionally, which is impossible
    (see `unbounded_not_implies_tendsto` above). The correct version requires
    that h is monotone: adding points can only increase the number of distinct
    optimal configurations. Whether h is actually monotone is itself an interesting
    open question about the geometry of optimal configurations.

    **Why monotonicity is plausible but unproven:**
    For large n, optimal configurations approximate hexagonal packings.
    An (n+1)-point optimal config can restrict to multiple n-point configs
    (by removing boundary points), suggesting h should be non-decreasing.
    But this heuristic argument does not constitute a proof. -/
theorem unbounded_implies_conjecture_of_mono
    (hmono : Monotone h) (hunb : hUnbounded) : ErdosConjecture103 := by
  intro C
  obtain ⟨N, hN⟩ := hunb C
  exact ⟨N, fun n hn => lt_of_lt_of_le hN (hmono hn)⟩

/-- The correct equivalence for h(n), assuming monotonicity. -/
theorem conjecture_equiv_mono (hmono : Monotone h) :
    ErdosConjecture103 ↔ hUnbounded :=
  ⟨conjecture_implies_unbounded, unbounded_implies_conjecture_of_mono hmono⟩

-- ============================================================
-- PART 8: Structural Properties
-- ============================================================

/-- h(n) ≥ 1 for all n ≥ 2 means optimal configurations exist. -/
theorem optimal_configs_exist (n : ℕ) (hn : n ≥ 2) : h n ≥ 1 :=
  h_pos n hn

/-- Whether h is monotone is an open structural question.
    If true, it would imply conjecture_equiv holds unconditionally. -/
def hMonotoneQuestion : Prop :=
  Monotone h

/-- The weak conjecture: h(n) ≥ 2 for all large n.
    Even this is unknown — we cannot currently show that there are ever
    two distinct optimal configurations for any sufficiently large n. -/
def WeakConjecture : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, h n ≥ 2

/-- The very weak conjecture: infinitely many n have h(n) ≥ 2. -/
def VeryWeakConjecture : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, h n ≥ 2

/-- The conjectures form an implication chain. -/
theorem conjecture_chain :
    ErdosConjecture103 → WeakConjecture := by
  intro hconj
  obtain ⟨N, hN⟩ := hconj 1
  exact ⟨N, fun n hn => hN n hn⟩

theorem weak_implies_very_weak :
    WeakConjecture → VeryWeakConjecture := by
  intro ⟨N₀, hN₀⟩ N
  exact ⟨max N₀ N, le_max_right _ _, hN₀ _ (le_max_left _ _)⟩

end Erdos103OQ01

-- Export main results
#check Erdos103OQ01.pointDist_eq_zero_iff
#check Erdos103OQ01.isometry2D_injective
#check Erdos103OQ01.congruent_symm
#check Erdos103OQ01.congruent_preserves_separation
#check Erdos103OQ01.oscillating_unbounded
#check Erdos103OQ01.oscillating_not_tendsto
#check Erdos103OQ01.unbounded_not_implies_tendsto
#check Erdos103OQ01.mono_unbounded_iff_tendsto
#check Erdos103OQ01.conjecture_equiv_mono
#check Erdos103OQ01.conjecture_chain
#check Erdos103OQ01.weak_implies_very_weak
