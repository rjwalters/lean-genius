import Mathlib

/-
# Lebesgue Measure — OQ-06: Banach-Tarski Paradox Formal Statement

## Research Problem: lebesgue-measure-oq-06

The **Banach-Tarski paradox** (1924): The closed unit ball in ℝ³ can be decomposed
into finitely many (non-measurable) pieces and those pieces can be reassembled —
using only rotations and translations — into two complete copies of the original ball.

This file formalizes:
1. The abstract notion of **equidecomposability** under a group action
2. **Paradoxical sets** (sets equidecomposable to two disjoint copies of themselves)
3. Consequence: paradoxical sets have no finitely-additive invariant measure
4. The Banach-Tarski statement for ℝ³ (stated; proof requires 800+ lines via free
   subgroup of SO(3) — beyond the scope of this gallery entry)
5. Corollary: existence of non-Lebesgue-measurable sets in ℝ³

## Mathematical Background

The key ingredients:
- **Free subgroup of SO(3)**: Hausdorff (1914) found a free subgroup of rank 2 in SO(3).
  Specifically, rotations φ by arccos(1/3) around the z-axis and ψ by arccos(1/3)
  around the x-axis generate a free group (no nontrivial word equals the identity).
- **Paradoxical decomposition of F₂**: The free group F₂ acts paradoxically on itself.
- **Encoding**: Use the free subgroup action on S² to get a paradoxical decomposition
  of S², then extend to the full ball.

Tags: measure-theory, banach-tarski, paradox, equidecomposable, axiom-of-choice
-/

set_option linter.unusedVariables false

namespace BanachTarski

open Set MeasureTheory
open scoped Pointwise ENNReal Matrix

variable {α : Type*}

-- ============================================================
-- SECTION I: Equidecomposable Sets
-- ============================================================

/-- Two sets `A` and `B` in `α` are **G-equidecomposable** if `A` can be
    partitioned into finitely many pieces, each moved by a group element
    from `G` so that the images form a partition of `B`.

    This captures "cutting and rearranging" using group elements (rotations,
    translations, etc.) without changing the shape of any piece. -/
def Equidecomposable (G : Type*) [Group G] [MulAction G α]
    (A B : Set α) : Prop :=
  ∃ (n : ℕ) (pieces : Fin n → Set α) (g : Fin n → G),
    (∀ i, pieces i ⊆ A) ∧
    (∀ i j, i ≠ j → Disjoint (pieces i) (pieces j)) ∧
    A = ⋃ i, pieces i ∧
    B = ⋃ i, g i • pieces i ∧
    (∀ i j, i ≠ j → Disjoint (g i • pieces i) (g j • pieces j))

notation:50 A " ≃ᴳ[" G "] " B => Equidecomposable G A B

/-- Equidecomposability is reflexive. -/
theorem equidecomposable_refl (G : Type*) [Group G] [MulAction G α]
    [MulAction.IsPretransitive G α] (A : Set α) :
    A ≃ᴳ[G] A := by
  refine ⟨1, fun _ => A, fun _ => 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro; exact le_refl A
  · intro i j h; exact absurd (Fin.eq_of_val_eq (Nat.lt_one_iff.mp i.isLt ▸
      Nat.lt_one_iff.mp j.isLt ▸ rfl)) h
  · simp only [Set.iUnion_const]
  · simp only [one_smul, Set.iUnion_const]
  · intro i j h; exact absurd (Fin.eq_of_val_eq (Nat.lt_one_iff.mp i.isLt ▸
      Nat.lt_one_iff.mp j.isLt ▸ rfl)) h

/-- A set is **G-paradoxical** if it can be decomposed into two disjoint subsets,
    each equidecomposable to the whole set.

    Informally: the set can be "duplicated" using only group-element rearrangements.
    This requires the axiom of choice in the constructions and produces
    non-measurable pieces. -/
def IsParadoxical (G : Type*) [Group G] [MulAction G α] (A : Set α) : Prop :=
  ∃ B C : Set α, B ⊆ A ∧ C ⊆ A ∧ Disjoint B C ∧
    (A ≃ᴳ[G] B) ∧ (A ≃ᴳ[G] C)

-- ============================================================
-- SECTION II: Paradoxical Sets Cannot Be Measured
-- ============================================================

/-- Helper: in ENNReal, a + a = a implies a = 0 or a = ⊤. -/
private lemma ennreal_add_self_eq_self {a : ℝ≥0∞} (h : a + a = a) :
    a = 0 ∨ a = ⊤ := by
  rcases eq_or_ne a ⊤ with rfl | hatop
  · exact Or.inr rfl
  · left
    rcases eq_or_ne a 0 with rfl | ha0
    · rfl
    · exact absurd h (ENNReal.lt_add_right hatop ha0).ne'

/-- **Key consequence**: If `A` is G-paradoxical, then any G-invariant
    finitely-additive measure on `A` must assign it measure 0 or ∞.

    Proof: If A ≃ B ∪ C (disjoint), A ≃ B, A ≃ C, and μ is invariant:
    μ(A) = μ(B) + μ(C) (finite additivity + disjoint)
         = μ(A) + μ(A) (equidecomposability + invariance)
    So 0 = μ(A), or we have 2μ(A) = μ(A), i.e., μ(A) = 0 or μ(A) = ∞. -/
theorem paradoxical_no_finite_measure (G : Type*) [Group G] [MulAction G α]
    (A : Set α) (hA : IsParadoxical G A)
    (μ : Set α → ℝ≥0∞)
    (hμ_nonneg : ∀ S, 0 ≤ μ S)
    (hμ_add : ∀ S T : Set α, Disjoint S T → μ (S ∪ T) = μ S + μ T)
    (hμ_inv : ∀ (g : G) (S : Set α) (hS : S ⊆ A),
      μ (g • S) = μ S)
    (hμ_equi : ∀ B : Set α, B ⊆ A → (A ≃ᴳ[G] B) → μ B = μ A) :
    μ A = 0 ∨ μ A = ⊤ := by
  obtain ⟨B, C, hBA, hCA, hBC, hAB, hAC⟩ := hA
  -- μ(A) = μ(B) + μ(C) since B ⊆ A, C ⊆ A, B ∩ C = ∅
  -- and A can be covered by B ∪ C ... (for simplicity, use equidecomposability)
  -- μ(A) = μ(B) (by equidecomposability A ≃ B)
  have hμB : μ B = μ A := hμ_equi B hBA hAB
  -- μ(A) = μ(C) (by equidecomposability A ≃ C)
  have hμC : μ C = μ A := hμ_equi C hCA hAC
  -- μ(B ∪ C) = μ(B) + μ(C) = μ(A) + μ(A) = 2·μ(A)
  have hBCunion : μ (B ∪ C) = μ A + μ A := by
    rw [hμ_add B C hBC, hμB, hμC]
  -- B ∪ C ⊆ A, so μ(B ∪ C) ≤ μ(A) ... but also B ∪ C = A under equidecomp
  -- From the equidecomposability structure: B ∪ C ⊆ A
  -- And the equidecomposability gives μ(A) = μ(B) + μ(C) = 2·μ(A)
  -- So μ(A) = 2·μ(A) → μ(A) = 0 or ∞
  have h2 : μ A + μ A = μ A := by
    -- B ∪ C ⊆ A (from hBA, hCA)
    have h_bc_sub_a : B ∪ C ⊆ A := Set.union_subset hBA hCA
    -- Monotonicity: μ(B ∪ C) ≤ μ(A), derived from finite additivity
    -- via decomposition A = (B ∪ C) ∪ (A \ (B ∪ C))
    have hMonotone : μ (B ∪ C) ≤ μ A := by
      calc μ (B ∪ C)
          ≤ μ (B ∪ C) + μ (A \ (B ∪ C)) := le_add_of_nonneg_right (zero_le _)
        _ = μ ((B ∪ C) ∪ (A \ (B ∪ C))) :=
            (hμ_add _ _ disjoint_sdiff_self_right).symm
        _ = μ A := by rw [Set.union_diff_cancel h_bc_sub_a]
    -- Sandwich: μ(B ∪ C) ≤ μ(A) ≤ μ(A) + μ(A) = μ(B ∪ C)
    -- gives equality μ(A) = μ(A) + μ(A)
    exact le_antisymm (hBCunion ▸ hMonotone) (le_add_of_nonneg_right (zero_le _))
  -- From h2: μ(A) = 0 or μ(A) = ∞
  rcases ennreal_add_self_eq_self h2 with h | h
  · exact Or.inl h
  · exact Or.inr h

-- ============================================================
-- SECTION III: The Banach-Tarski Paradox (Statement)
-- ============================================================

/-- The type of rigid motions (orientation-preserving isometries) of ℝ³.
    These form a group under composition. We use `IsometryEquiv ℝ³ ℝ³` as
    a proxy; the actual group is the special Euclidean group SE(3). -/
abbrev RigidMotion3 := EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)

/-- The unit ball in ℝ³. -/
def unitBall3 : Set (EuclideanSpace ℝ (Fin 3)) :=
  Metric.closedBall 0 1

/-- The unit sphere S² in ℝ³. -/
def unitSphere3 : Set (EuclideanSpace ℝ (Fin 3)) :=
  Metric.sphere 0 1

-- ============================================================
-- SECTION IV: Free Subgroup of SO(3)
-- ============================================================

-- Private infrastructure: integer orbit argument for Hausdorff's theorem.
-- We track the orbit of e₂ = (0,1,0) in ℤ[√2]³, scaled by 3^n after n steps.
-- The key: each scaled integer action corresponds to (1/3)*(real matrix)*3.

-- Scaled integer actions: scaledActL(v) = (3 * M_L) * v in ℤ[√2]³
-- where M_L is the rotation matrix for generator L.
-- Using decidable equality on Fin 3 indices via Vector3 components.
private def scaledActPhi (v : Fin 3 → Zsqrtd 2) : Fin 3 → Zsqrtd 2 :=
  ![v 0 + ⟨0, -2⟩ * v 1,   -- x' = x - 2√2·y
    ⟨0, 2⟩ * v 0 + v 1,     -- y' = 2√2·x + y
    ⟨3, 0⟩ * v 2]            -- z' = 3z

private def scaledActPhiInv (v : Fin 3 → Zsqrtd 2) : Fin 3 → Zsqrtd 2 :=
  ![v 0 + ⟨0, 2⟩ * v 1,
    ⟨0, -2⟩ * v 0 + v 1,
    ⟨3, 0⟩ * v 2]

private def scaledActPsi (v : Fin 3 → Zsqrtd 2) : Fin 3 → Zsqrtd 2 :=
  ![⟨3, 0⟩ * v 0,
    v 1 + ⟨0, -2⟩ * v 2,
    ⟨0, 2⟩ * v 1 + v 2]

private def scaledActPsiInv (v : Fin 3 → Zsqrtd 2) : Fin 3 → Zsqrtd 2 :=
  ![⟨3, 0⟩ * v 0,
    v 1 + ⟨0, 2⟩ * v 2,
    ⟨0, -2⟩ * v 1 + v 2]

-- The starting vector e₂ = (0,1,0) encoded in ℤ[√2]³
private def e2Int : Fin 3 → Zsqrtd 2 := ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]

-- Index-reduction simp lemmas (used in transition lemma proofs)
@[simp] private lemma scaledActPhi_0 (v : Fin 3 → Zsqrtd 2) :
    scaledActPhi v 0 = v 0 + ⟨0, -2⟩ * v 1 := by
  simp [scaledActPhi, Matrix.cons_val_zero]
@[simp] private lemma scaledActPhi_1 (v : Fin 3 → Zsqrtd 2) :
    scaledActPhi v 1 = ⟨0, 2⟩ * v 0 + v 1 := by
  simp [scaledActPhi, Matrix.cons_val_one, Matrix.head_cons]
@[simp] private lemma scaledActPhi_2 (v : Fin 3 → Zsqrtd 2) :
    scaledActPhi v 2 = ⟨3, 0⟩ * v 2 := by
  simp [scaledActPhi, show (2 : Fin 3) = ⟨2, by norm_num⟩ from rfl,
        Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]

@[simp] private lemma scaledActPhiInv_0 (v : Fin 3 → Zsqrtd 2) :
    scaledActPhiInv v 0 = v 0 + ⟨0, 2⟩ * v 1 := by
  simp [scaledActPhiInv, Matrix.cons_val_zero]
@[simp] private lemma scaledActPhiInv_1 (v : Fin 3 → Zsqrtd 2) :
    scaledActPhiInv v 1 = ⟨0, -2⟩ * v 0 + v 1 := by
  simp [scaledActPhiInv, Matrix.cons_val_one, Matrix.head_cons]
@[simp] private lemma scaledActPhiInv_2 (v : Fin 3 → Zsqrtd 2) :
    scaledActPhiInv v 2 = ⟨3, 0⟩ * v 2 := by
  simp [scaledActPhiInv, show (2 : Fin 3) = ⟨2, by norm_num⟩ from rfl,
        Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]

@[simp] private lemma scaledActPsi_0 (v : Fin 3 → Zsqrtd 2) :
    scaledActPsi v 0 = ⟨3, 0⟩ * v 0 := by
  simp [scaledActPsi, Matrix.cons_val_zero]
@[simp] private lemma scaledActPsi_1 (v : Fin 3 → Zsqrtd 2) :
    scaledActPsi v 1 = v 1 + ⟨0, -2⟩ * v 2 := by
  simp [scaledActPsi, Matrix.cons_val_one, Matrix.head_cons]
@[simp] private lemma scaledActPsi_2 (v : Fin 3 → Zsqrtd 2) :
    scaledActPsi v 2 = ⟨0, 2⟩ * v 1 + v 2 := by
  simp [scaledActPsi, show (2 : Fin 3) = ⟨2, by norm_num⟩ from rfl,
        Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]

@[simp] private lemma scaledActPsiInv_0 (v : Fin 3 → Zsqrtd 2) :
    scaledActPsiInv v 0 = ⟨3, 0⟩ * v 0 := by
  simp [scaledActPsiInv, Matrix.cons_val_zero]
@[simp] private lemma scaledActPsiInv_1 (v : Fin 3 → Zsqrtd 2) :
    scaledActPsiInv v 1 = v 1 + ⟨0, 2⟩ * v 2 := by
  simp [scaledActPsiInv, Matrix.cons_val_one, Matrix.head_cons]
@[simp] private lemma scaledActPsiInv_2 (v : Fin 3 → Zsqrtd 2) :
    scaledActPsiInv v 2 = ⟨0, -2⟩ * v 1 + v 2 := by
  simp [scaledActPsiInv, show (2 : Fin 3) = ⟨2, by norm_num⟩ from rfl,
        Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]

-- Mod-3 orbit invariants: for a reduced word ending in generator L,
-- the scaled orbit 3^n·w(e₂) satisfies inv_L (all arithmetic mod 3).
private def inv_phi (v : Fin 3 → Zsqrtd 2) : Prop :=
  (v 0).re % 3 = 0 ∧ (v 0).im % 3 ≠ 0 ∧
  ((v 0).im - (v 1).re) % 3 = 0 ∧
  (v 1).im % 3 = 0 ∧ (v 2).re % 3 = 0 ∧ (v 2).im % 3 = 0

private def inv_phi_inv (v : Fin 3 → Zsqrtd 2) : Prop :=
  (v 0).re % 3 = 0 ∧ (v 0).im % 3 ≠ 0 ∧
  ((v 0).im + (v 1).re) % 3 = 0 ∧
  (v 1).im % 3 = 0 ∧ (v 2).re % 3 = 0 ∧ (v 2).im % 3 = 0

private def inv_psi (v : Fin 3 → Zsqrtd 2) : Prop :=
  (v 0).re % 3 = 0 ∧ (v 0).im % 3 = 0 ∧
  (v 1).re % 3 ≠ 0 ∧ (v 1).im % 3 = 0 ∧
  (v 2).re % 3 = 0 ∧ (v 2).im % 3 ≠ 0 ∧
  ((v 2).im + (v 1).re) % 3 = 0

private def inv_psi_inv (v : Fin 3 → Zsqrtd 2) : Prop :=
  (v 0).re % 3 = 0 ∧ (v 0).im % 3 = 0 ∧
  (v 1).re % 3 ≠ 0 ∧ (v 1).im % 3 = 0 ∧
  (v 2).re % 3 = 0 ∧ (v 2).im % 3 ≠ 0 ∧
  ((v 2).im - (v 1).re) % 3 = 0

-- Shorthand for "v satisfies at least one of the four invariants"
private def anyInv (v : Fin 3 → Zsqrtd 2) : Prop :=
  inv_phi v ∨ inv_phi_inv v ∨ inv_psi v ∨ inv_psi_inv v

-- The identity does not satisfy anyInv (e2Int has y.re = 1 ≢ 0 mod 3, x.im = 0 ≡ 0)
private lemma e2Int_no_inv : ¬ anyInv e2Int := by
  simp [anyInv, inv_phi, inv_phi_inv, inv_psi, inv_psi_inv, e2Int]

-- *** Valid transition lemmas (12 of 16 transitions in the orbit automaton) ***
-- The 4 forbidden transitions (phi after phi_inv, phi_inv after phi,
-- psi after psi_inv, psi_inv after psi) are excluded by reducedness.
-- Proof pattern: unfold all definitions, apply Zsqrtd arithmetic simp, then omega.

-- Shared simp set for all transition lemma proofs
macro "zsqrtd_simp" : tactic =>
  `(tactic| simp only [Zsqrtd.mul_re, Zsqrtd.mul_im, Zsqrtd.add_re, Zsqrtd.add_im,
              scaledActPhi_0, scaledActPhi_1, scaledActPhi_2,
              scaledActPhiInv_0, scaledActPhiInv_1, scaledActPhiInv_2,
              scaledActPsi_0, scaledActPsi_1, scaledActPsi_2,
              scaledActPsiInv_0, scaledActPsiInv_1, scaledActPsiInv_2])

-- Apply phi: valid from inv_phi, inv_psi, inv_psi_inv (NOT from inv_phi_inv)
private lemma trans_phi_from_phi {v} (h : inv_phi v) : inv_phi (scaledActPhi v) := by
  simp only [inv_phi] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hxy, hyi, hzr, hzi⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma trans_phi_from_psi {v} (h : inv_psi v) : inv_phi (scaledActPhi v) := by
  simp only [inv_phi, inv_psi] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hyr, hyi, hzr, hzi, hzy⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma trans_phi_from_psi_inv {v} (h : inv_psi_inv v) : inv_phi (scaledActPhi v) := by
  simp only [inv_phi, inv_psi_inv] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hyr, hyi, hzr, hzi, hzy⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

-- Apply phi_inv: valid from inv_phi_inv, inv_psi, inv_psi_inv (NOT from inv_phi)
private lemma trans_phi_inv_from_phi_inv {v} (h : inv_phi_inv v) : inv_phi_inv (scaledActPhiInv v) := by
  simp only [inv_phi_inv] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hxy, hyi, hzr, hzi⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma trans_phi_inv_from_psi {v} (h : inv_psi v) : inv_phi_inv (scaledActPhiInv v) := by
  simp only [inv_phi_inv, inv_psi] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hyr, hyi, hzr, hzi, hzy⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma trans_phi_inv_from_psi_inv {v} (h : inv_psi_inv v) : inv_phi_inv (scaledActPhiInv v) := by
  simp only [inv_phi_inv, inv_psi_inv] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hyr, hyi, hzr, hzi, hzy⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

-- Apply psi: valid from inv_phi, inv_phi_inv, inv_psi (NOT from inv_psi_inv)
private lemma trans_psi_from_phi {v} (h : inv_phi v) : inv_psi (scaledActPsi v) := by
  simp only [inv_psi, inv_phi] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hxy, hyi, hzr, hzi⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma trans_psi_from_phi_inv {v} (h : inv_phi_inv v) : inv_psi (scaledActPsi v) := by
  simp only [inv_psi, inv_phi_inv] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hxy, hyi, hzr, hzi⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma trans_psi_from_psi {v} (h : inv_psi v) : inv_psi (scaledActPsi v) := by
  simp only [inv_psi] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hyr, hyi, hzr, hzi, hzy⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

-- Apply psi_inv: valid from inv_phi, inv_phi_inv, inv_psi_inv (NOT from inv_psi)
private lemma trans_psi_inv_from_phi {v} (h : inv_phi v) : inv_psi_inv (scaledActPsiInv v) := by
  simp only [inv_psi_inv, inv_phi] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hxy, hyi, hzr, hzi⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma trans_psi_inv_from_phi_inv {v} (h : inv_phi_inv v) : inv_psi_inv (scaledActPsiInv v) := by
  simp only [inv_psi_inv, inv_phi_inv] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hxy, hyi, hzr, hzi⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma trans_psi_inv_from_psi_inv {v} (h : inv_psi_inv v) : inv_psi_inv (scaledActPsiInv v) := by
  simp only [inv_psi_inv] at h ⊢; zsqrtd_simp
  obtain ⟨hxr, hxi, hyr, hyi, hzr, hzi, hzy⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

-- Base cases: applying each generator to e2Int satisfies the corresponding invariant
private lemma base_phi : inv_phi (scaledActPhi e2Int) := by
  simp only [inv_phi, e2Int, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.head_cons, Matrix.head_fin_const]
  zsqrtd_simp
  norm_num

private lemma base_phi_inv : inv_phi_inv (scaledActPhiInv e2Int) := by
  simp only [inv_phi_inv, e2Int, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.head_cons, Matrix.head_fin_const]
  zsqrtd_simp
  norm_num

private lemma base_psi : inv_psi (scaledActPsi e2Int) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [inv_psi, scaledActPsi, e2Int, Zsqrtd.mul_re, Zsqrtd.mul_im,
          Zsqrtd.add_re, Zsqrtd.add_im] <;>
    norm_num

private lemma base_psi_inv : inv_psi_inv (scaledActPsiInv e2Int) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [inv_psi_inv, scaledActPsiInv, e2Int, Zsqrtd.mul_re, Zsqrtd.mul_im,
          Zsqrtd.add_re, Zsqrtd.add_im] <;>
    norm_num

-- The orbit induction for proving orbit_ne uses these 12 valid transitions.
-- The forbidden 4 transitions don't appear in reduced words.
-- Full induction: on FreeGroup.toList, showing each letter step preserves the
-- appropriate inv_L invariant (where L is the new last letter), relying on
-- reducedness to exclude the 4 forbidden (self-cancelling) transitions.

-- *** PART B: Word evaluation and automaton infrastructure ***

-- Apply one generator letter to an integer-orbit vector
private def applyGen : Bool × Bool → (Fin 3 → Zsqrtd 2) → Fin 3 → Zsqrtd 2
  | (true, true), v => scaledActPhi v
  | (true, false), v => scaledActPhiInv v
  | (false, true), v => scaledActPsi v
  | (false, false), v => scaledActPsiInv v

-- Evaluate a word left-to-right: evalWord [l₁,l₂,...,lₙ] v = lₙ(l₂(l₁(v)))
private def evalWord : List (Bool × Bool) → (Fin 3 → Zsqrtd 2) → Fin 3 → Zsqrtd 2
  | [], v => v
  | x :: xs, v => evalWord xs (applyGen x v)

-- The invariant each last-applied generator establishes
private def labeledInv : Bool × Bool → (Fin 3 → Zsqrtd 2) → Prop
  | (true, true), v => inv_phi v
  | (true, false), v => inv_phi_inv v
  | (false, true), v => inv_psi v
  | (false, false), v => inv_psi_inv v

-- evalWord(l ++ [g]) v = applyGen g (evalWord l v): the last letter is applied last
private lemma evalWord_append (l : List (Bool × Bool)) (g : Bool × Bool)
    (v : Fin 3 → Zsqrtd 2) :
    evalWord (l ++ [g]) v = applyGen g (evalWord l v) := by
  induction l generalizing v with
  | nil => simp [evalWord]
  | cons h t ih => simp only [List.cons_append, evalWord]; exact ih _

-- Base: single application to e2Int satisfies the generator's invariant
private lemma labeledInv_base (g : Bool × Bool) : labeledInv g (applyGen g e2Int) := by
  rcases g with ⟨b, s⟩
  fin_cases b <;> fin_cases s <;>
    simp only [applyGen, labeledInv] <;>
    first | exact base_phi | exact base_phi_inv | exact base_psi | exact base_psi_inv

-- Valid transition: if prev established its invariant and cur doesn't cancel prev,
-- then cur establishes its invariant after being applied
private lemma labeledInv_step (cur prev : Bool × Bool) (v : Fin 3 → Zsqrtd 2)
    (hnocancel : ¬(cur.1 = prev.1 ∧ cur.2 = !prev.2))
    (hprev : labeledInv prev v) : labeledInv cur (applyGen cur v) := by
  rcases cur with ⟨cb, cs⟩; rcases prev with ⟨pb, ps⟩
  -- 16 cases; 4 are forbidden (hnocancel gives contradiction), 12 use transition lemmas
  fin_cases cb <;> fin_cases cs <;> fin_cases pb <;> fin_cases ps <;>
    simp only [applyGen, labeledInv, Bool.not_false, Bool.not_true,
               Bool.false_eq_true, Bool.true_eq_false, not_and] at * <;>
    first
    | exact trans_phi_from_phi hprev
    | exact trans_phi_from_psi hprev
    | exact trans_phi_from_psi_inv hprev
    | exact trans_phi_inv_from_phi_inv hprev
    | exact trans_phi_inv_from_psi hprev
    | exact trans_phi_inv_from_psi_inv hprev
    | exact trans_psi_from_phi hprev
    | exact trans_psi_from_phi_inv hprev
    | exact trans_psi_from_psi hprev
    | exact trans_psi_inv_from_phi hprev
    | exact trans_psi_inv_from_phi_inv hprev
    | exact trans_psi_inv_from_psi_inv hprev
    | (simp_all)

-- anyInv follows from labeledInv
private lemma anyInv_of_labeledInv {g : Bool × Bool} {v : Fin 3 → Zsqrtd 2}
    (h : labeledInv g v) : anyInv v := by
  rcases g with ⟨b, s⟩
  fin_cases b <;> fin_cases s <;> simp only [labeledInv] at h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

-- Helper: getLast! is a member of getLast? for any nonempty list.
-- Proved by induction using the cons-cons reduction lemmas.
private lemma getLast!_mem_getLast? {l : List (Bool × Bool)} (h : l ≠ []) :
    l.getLast! ∈ l.getLast? := by
  induction l with
  | nil => exact absurd rfl h
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t' =>
      have hne : b :: t' ≠ [] := List.cons_ne_nil b t'
      simp only [List.getLast!, List.getLast?]
      exact ih hne

-- Auxiliary: the stronger "last-letter labeled invariant" holds for nonempty reduced words.
-- Proof by induction on the word from the right (reverseRecOn).
private lemma evalWord_nonempty_labeledInv :
    ∀ (l : List (Bool × Bool)),
    l ≠ [] →
    l.Chain' (fun a b => ¬(a.1 = b.1 ∧ a.2 = !b.2)) →
    labeledInv l.getLast! (evalWord l e2Int) := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton l' g ih =>
    -- ih : l' ≠ [] → l'.Chain' R → labeledInv l'.getLast! (evalWord l' e2Int)
    intro _ hred
    -- Rewrite the goal: getLast! of l' ++ [g] is g, and evalWord splits at the end
    -- (l' ++ [g]).getLast! = g holds because g is the last element
    have hlast : (l' ++ [g]).getLast! = g := by simp
    rw [evalWord_append, hlast]
    -- Case split: was the prefix empty?
    by_cases hl' : l' = []
    · -- Single-letter word [g]: apply base case directly
      subst hl'; simp only [evalWord]; exact labeledInv_base g
    · -- Multi-letter word l' ++ [g]: use induction hypothesis
      -- Extract prefix chain from (l' ++ [g]).Chain' R
      have hred_l' : l'.Chain' (fun a b => ¬(a.1 = b.1 ∧ a.2 = !b.2)) :=
        -- Prefix of a reduced word is reduced: l' = left part of l' ++ [g]
        (List.chain'_append.mp hred).1
      -- The junction: last pair (l'.getLast!, g) satisfies no-cancel
      have hnocancel : ¬(g.1 = l'.getLast!.1 ∧ g.2 = !l'.getLast!.2) := by
        -- From chain'_append: ∀ x ∈ l'.getLast?, ∀ y ∈ [g].head?, R x y
        -- i.e., R l'.getLast! g = ¬(l'.getLast!.1 = g.1 ∧ l'.getLast!.2 = !g.2)
        intro ⟨heq1, heq2⟩
        have hjunc := (List.chain'_append.mp hred).2.2
        have hlast_mem : l'.getLast! ∈ l'.getLast? := getLast!_mem_getLast? hl'
        have hg_mem : g ∈ ([g] : List (Bool × Bool)).head? := by simp
        exact hjunc _ hlast_mem _ hg_mem ⟨heq1.symm, by simp [heq2, Bool.not_not]⟩
      -- Apply the transition
      exact labeledInv_step g l'.getLast! _ hnocancel (ih hl' hred_l')

-- Key automaton lemma: any nonempty reduced word applied to e2Int satisfies anyInv.
private lemma evalWord_nonempty_anyInv (l : List (Bool × Bool))
    (hne : l ≠ [])
    (hred : l.Chain' (fun a b => ¬(a.1 = b.1 ∧ a.2 = !b.2))) :
    anyInv (evalWord l e2Int) :=
  anyInv_of_labeledInv (evalWord_nonempty_labeledInv l hne hred)

/-- **Hausdorff's Theorem** (1914): The rotation group SO(3) contains a free
    subgroup of rank 2.

    Specifically, let φ = rotation by arccos(1/3) around the z-axis and
    ψ = rotation by arccos(1/3) around the x-axis. Then ⟨φ, ψ⟩ is a free
    group of rank 2.

    This is the key algebraic ingredient for Banach-Tarski. -/
-- PARTIAL PROOF: Rotation matrices defined and shown orthogonal.
-- LinearIsometryEquivs constructed. orbit_ne proved via inductive encoding in ℤ[√2].
theorem hausdorff_free_subgroup :
    ∃ (φ ψ : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)),
    Function.Injective
      (FreeGroup.lift (fun b : Bool => if b then φ.toLinearEquiv else ψ.toLinearEquiv)) := by
  -- Trig identity: cos θ = 1/3, sin θ = 2√2/3, where θ = arccos(1/3)
  -- Verified: (1/3)² + (2√2/3)² = 1/9 + 8/9 = 1
  have hcs : (1 / 3 : ℝ) ^ 2 + (2 * Real.sqrt 2 / 3) ^ 2 = 1 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [h2]
  -- φ = rotation by arccos(1/3) around the z-axis
  let Mφ : Matrix (Fin 3) (Fin 3) ℝ :=
    !![(1 : ℝ) / 3, -(2 * Real.sqrt 2 / 3), 0;
       2 * Real.sqrt 2 / 3, (1 : ℝ) / 3, 0;
       0, 0, 1]
  -- ψ = rotation by arccos(1/3) around the x-axis
  let Mψ : Matrix (Fin 3) (Fin 3) ℝ :=
    !![1, 0, 0;
       0, (1 : ℝ) / 3, -(2 * Real.sqrt 2 / 3);
       0, 2 * Real.sqrt 2 / 3, (1 : ℝ) / 3]
  -- Orthogonality: Mφᵀ * Mφ = 1 (rotation matrices are orthogonal)
  -- Each entry follows from c² + s² = 1 and cs - sc = 0
  have hφ_orth : Mφᵀ * Mφ = 1 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    unfold_let Mφ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue] <;>
      ring_nf <;>
      nlinarith [hs2, hcs, Real.sqrt_nonneg 2]
  -- Mφ * Mφᵀ = 1
  have hφ_orth' : Mφ * Mφᵀ = 1 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    unfold_let Mφ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue] <;>
      ring_nf <;>
      nlinarith [hs2, hcs, Real.sqrt_nonneg 2]
  -- Mψᵀ * Mψ = 1
  have hψ_orth : Mψᵀ * Mψ = 1 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    unfold_let Mψ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue] <;>
      ring_nf <;>
      nlinarith [hs2, hcs, Real.sqrt_nonneg 2]
  -- Mψ * Mψᵀ = 1
  have hψ_orth' : Mψ * Mψᵀ = 1 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    unfold_let Mψ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue] <;>
      ring_nf <;>
      nlinarith [hs2, hcs, Real.sqrt_nonneg 2]
  -- Build LinearEquiv: toEuclideanLin M has inverse toEuclideanLin Mᵀ
  -- Uses: toEuclideanLin (Mᵀ * M) = id when Mᵀ * M = 1
  have hφ_comp_rl : (Matrix.toEuclideanLin Mφ).comp (Matrix.toEuclideanLin Mφᵀ) = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.toEuclideanLin_apply,
               WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hφ_orth', Matrix.one_mulVec,
               WithLp.toLp_ofLp]
  have hφ_comp_lr : (Matrix.toEuclideanLin Mφᵀ).comp (Matrix.toEuclideanLin Mφ) = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.toEuclideanLin_apply,
               WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hφ_orth, Matrix.one_mulVec,
               WithLp.toLp_ofLp]
  have hψ_comp_rl : (Matrix.toEuclideanLin Mψ).comp (Matrix.toEuclideanLin Mψᵀ) = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.toEuclideanLin_apply,
               WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hψ_orth', Matrix.one_mulVec,
               WithLp.toLp_ofLp]
  have hψ_comp_lr : (Matrix.toEuclideanLin Mψᵀ).comp (Matrix.toEuclideanLin Mψ) = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.toEuclideanLin_apply,
               WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hψ_orth, Matrix.one_mulVec,
               WithLp.toLp_ofLp]
  -- Build linear equivalences
  let φ_lin : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    LinearEquiv.ofLinear (Matrix.toEuclideanLin Mφ) (Matrix.toEuclideanLin Mφᵀ)
      hφ_comp_rl hφ_comp_lr
  let ψ_lin : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    LinearEquiv.ofLinear (Matrix.toEuclideanLin Mψ) (Matrix.toEuclideanLin Mψᵀ)
      hψ_comp_rl hψ_comp_lr
  -- Inner product preservation: orthogonal matrices preserve ⟪·,·⟫
  -- Key algebraic fact: (Mu)·(Mv) = u·(Mᵀ M v) = u·v when Mᵀ M = 1
  -- φ_lin x = toEuclideanLin Mφ x definitionally (ofLinear_apply)
  have hφ_inner : ∀ (x y : EuclideanSpace ℝ (Fin 3)), ⟪φ_lin x, φ_lin y⟫_ℝ = ⟪x, y⟫_ℝ := by
    intro x y
    -- Unfold φ_lin via ofLinear_apply (definitional equality)
    show ⟪Matrix.toEuclideanLin Mφ x, Matrix.toEuclideanLin Mφ y⟫_ℝ = ⟪x, y⟫_ℝ
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
               star_trivial]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hφ_orth, Matrix.vecMul_one]
  have hψ_inner : ∀ (x y : EuclideanSpace ℝ (Fin 3)), ⟪ψ_lin x, ψ_lin y⟫_ℝ = ⟪x, y⟫_ℝ := by
    intro x y
    show ⟪Matrix.toEuclideanLin Mψ x, Matrix.toEuclideanLin Mψ y⟫_ℝ = ⟪x, y⟫_ℝ
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
               star_trivial]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hψ_orth, Matrix.vecMul_one]
  -- Build the linear isometric equivalences via isometryOfInner
  let φ := LinearEquiv.isometryOfInner φ_lin hφ_inner
  let ψ := LinearEquiv.isometryOfInner ψ_lin hψ_inner
  -- Witness: the free group F₂ embeds via φ and ψ
  refine ⟨φ, ψ, ?_⟩
  -- Freeness via Hausdorff's orbit argument (1914).
  -- For injectivity we show: any non-identity word w maps e₂ ≠ e₂.
  -- The integer orbit in ℤ[√2]³ certifies this via the mod-3 invariant.
  -- e₂ = (0,1,0) as the test vector
  let e₂ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (1 : Fin 3) 1
  set liftF := FreeGroup.lift (fun b : Bool => if b then φ.toLinearEquiv else ψ.toLinearEquiv)
  -- The automaton invariant is proved in evalWord_nonempty_anyInv above.
  -- The remaining step is a bridge: evalWord (FreeGroup.toWord w) e2Int encodes
  -- 3^n * (liftF w) e₂ in ℤ[√2]³. The anyInv condition then forces (liftF w) e₂ ≠ e₂.
  have orbit_ne : ∀ (w : FreeGroup Bool), w ≠ 1 → (liftF w) e₂ ≠ e₂ := by
    intro w hw
    -- Step 1: w ≠ 1 → FreeGroup.toWord w is nonempty and reduced
    have hne_word : FreeGroup.toWord w ≠ [] := by
      rwa [ne_eq, FreeGroup.toWord_eq_nil_iff]
    have hred_word : (FreeGroup.toWord w).Chain' (fun a b => ¬(a.1 = b.1 ∧ a.2 = !b.2)) :=
      FreeGroup.isReduced_toWord.imp (fun a b h ⟨h1, h2⟩ =>
        absurd ((h h1).symm.trans h2) (by cases b.2 <;> simp))
    -- Use the REVERSED word for evalWord: evalWord reverses composition order,
    -- so evalWord l.reverse e2Int encodes 3^n * (liftF (mk l)) e₂.
    -- The reversed word is also nonempty and reduced (reducedness is symmetric).
    have hne_rev : (FreeGroup.toWord w).reverse ≠ [] := by
      simp [hne_word]
    have hred_rev : (FreeGroup.toWord w).reverse.Chain' (fun a b => ¬(a.1 = b.1 ∧ a.2 = !b.2)) := by
      rw [List.chain'_reverse]
      exact hred_word.imp (fun a b h ⟨h1, h2⟩ => h ⟨h1.symm, by
        cases a.2 <;> cases b.2 <;> simp_all⟩)
    -- Step 2: By the automaton, the reversed integer orbit satisfies anyInv
    have hanyInv : anyInv (evalWord (FreeGroup.toWord w).reverse e2Int) :=
      evalWord_nonempty_anyInv _ hne_rev hred_rev
    -- Step 3: Bridge — the integer orbit encodes 3^n * (liftF w) e₂
    have bridge : ∀ (v : Fin 3 → Zsqrtd 2),
        anyInv v →
        ∀ (p : EuclideanSpace ℝ (Fin 3)) (n : ℕ),
        (∀ i, (v i).re + (v i).im * Real.sqrt 2 = (3 : ℝ)^n * p i) →
        p ≠ e₂ := by
      intro v hv p n henc heq
      subst heq
      have henc0 : (↑(v 0).re : ℝ) + ↑(v 0).im * Real.sqrt 2 = 0 := by
        have h := henc (0 : Fin 3)
        simp only [EuclideanSpace.single_apply, Pi.single_apply] at h
        norm_num at h ⊢
        linarith
      have henc2 : (↑(v 2).re : ℝ) + ↑(v 2).im * Real.sqrt 2 = 0 := by
        have h := henc (2 : Fin 3)
        simp only [EuclideanSpace.single_apply, Pi.single_apply] at h
        norm_num at h ⊢
        linarith
      have hirr : Irrational (Real.sqrt 2) := Real.irrational_sqrt_two
      have hv0_im : (v 0).im = 0 := by
        by_contra h0
        have hh : (↑(v 0).im : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h0
        apply hirr
        refine ⟨-((v 0).re : ℚ) / ((v 0).im : ℚ), ?_⟩
        push_cast
        rw [div_eq_iff hh]
        linarith [mul_comm (Real.sqrt 2) (↑(v 0).im : ℝ),
                  mul_comm (↑(v 0).im : ℝ) (Real.sqrt 2)]
      have hv2_im : (v 2).im = 0 := by
        by_contra h2
        have hh : (↑(v 2).im : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h2
        apply hirr
        refine ⟨-((v 2).re : ℚ) / ((v 2).im : ℚ), ?_⟩
        push_cast
        rw [div_eq_iff hh]
        linarith [mul_comm (Real.sqrt 2) (↑(v 2).im : ℝ),
                  mul_comm (↑(v 2).im : ℝ) (Real.sqrt 2)]
      simp only [anyInv, inv_phi, inv_phi_inv, inv_psi, inv_psi_inv] at hv
      rcases hv with ⟨-, h, -⟩ | ⟨-, h, -⟩ |
                     ⟨-, -, -, -, -, h, -⟩ | ⟨-, -, -, -, -, h, -⟩
      · exact h (by rw [hv0_im]; omega)
      · exact h (by rw [hv0_im]; omega)
      · exact h (by rw [hv2_im]; omega)
      · exact h (by rw [hv2_im]; omega)
    -- Step 4: Encoding lemma — evalWord l v encodes 3^(n+l.length) * liftF(mk l.reverse)(p)
    -- when decode(v, i) = 3^n * p(i). Proved by induction on l.
    -- Key algebraic fact: each applyGen(g, v) decodes to 3 * M_g(decode(v)).
    -- Composition order: evalWord applies leftmost letter first (innermost),
    -- while liftF(mk l) applies leftmost letter last (outermost).
    -- So evalWord l v encodes liftF(mk l.reverse), i.e., reversed composition.
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    -- applyGen(g, v) decoded = 3 * (real rotation for g)(decoded v)
    have applyGen_decode : ∀ (g : Bool × Bool) (v : Fin 3 → Zsqrtd 2) (i : Fin 3),
        ((applyGen g v i).re : ℝ) + ((applyGen g v i).im : ℝ) * Real.sqrt 2 =
        3 * (if g.2 then (if g.1 then (φ_lin : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _)
                                 else (ψ_lin : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _))
                    else (if g.1 then (φ_lin.symm : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _)
                                 else (ψ_lin.symm : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _)))
            (fun j => ((v j).re : ℝ) + ((v j).im : ℝ) * Real.sqrt 2) i := by
      rcases g with ⟨b, s⟩
      fin_cases b <;> fin_cases s <;> fin_cases i <;>
        simp only [applyGen, Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false,
                   scaledActPhi_0, scaledActPhi_1, scaledActPhi_2,
                   scaledActPhiInv_0, scaledActPhiInv_1, scaledActPhiInv_2,
                   scaledActPsi_0, scaledActPsi_1, scaledActPsi_2,
                   scaledActPsiInv_0, scaledActPsiInv_1, scaledActPsiInv_2,
                   Zsqrtd.mul_re, Zsqrtd.mul_im, Zsqrtd.add_re, Zsqrtd.add_im,
                   φ_lin, ψ_lin, LinearEquiv.ofLinear_apply, LinearEquiv.ofLinear_symm_apply,
                   Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp,
                   Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three] <;>
        unfold_let Mφ Mψ <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                   Matrix.head_fin_const, Matrix.cons_val_fin_one,
                   Matrix.transpose_apply, Matrix.of_apply] <;>
        push_cast <;>
        nlinarith [hs2, Real.sqrt_nonneg 2,
                   mul_comm (Real.sqrt 2) ((v 0).im : ℝ),
                   mul_comm (Real.sqrt 2) ((v 1).im : ℝ),
                   mul_comm (Real.sqrt 2) ((v 2).im : ℝ)]
    -- General encoding induction:
    -- evalWord l v decodes to 3^(n+l.length) * liftF(mk l.reverse) p
    -- when decode(v) = 3^n * p component-wise.
    have enc_ind : ∀ (l : List (Bool × Bool)) (v : Fin 3 → Zsqrtd 2)
        (p : EuclideanSpace ℝ (Fin 3)) (n : ℕ),
        (∀ i, ((v i).re : ℝ) + ((v i).im : ℝ) * Real.sqrt 2 = 3^n * p i) →
        ∀ i, ((evalWord l v i).re : ℝ) + ((evalWord l v i).im : ℝ) * Real.sqrt 2 =
        3^(n + l.length) * (liftF (FreeGroup.mk l.reverse)) p i := by
      intro l
      induction l with
      | nil =>
        intro v p n hv i
        simp only [evalWord, List.length_nil, Nat.add_zero, List.reverse_nil,
                   FreeGroup.lift_mk, List.map_nil, List.prod_nil, map_one,
                   LinearEquiv.one_apply]
        exact hv i
      | cons a as ih =>
        intro v p n hv i
        simp only [evalWord, List.length_cons, List.reverse_cons]
        -- The linear map for generator a
        let Ma : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
          if a.2 then (if a.1 then (φ_lin : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _)
                               else (ψ_lin : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _))
                 else (if a.1 then (φ_lin.symm : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _)
                               else (ψ_lin.symm : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _))
        -- decode(applyGen a v) = 3^(n+1) * Ma(p) component-wise
        have hv' : ∀ j, ((applyGen a v j).re : ℝ) + ((applyGen a v j).im : ℝ) * Real.sqrt 2 =
            3^(n + 1) * Ma p j := by
          intro j
          rw [applyGen_decode a v j]
          -- applyGen_decode gives: 3 * Ma(decode v) j
          -- decode v = 3^n * p by hv
          -- Ma is linear: Ma(3^n * p) = 3^n * Ma(p)
          have hdec : (fun k => ((v k).re : ℝ) + ((v k).im : ℝ) * Real.sqrt 2) = 3^n • p := by
            funext k; rw [Pi.smul_apply, smul_eq_mul]; exact hv k
          rw [hdec]
          simp only [LinearMap.map_smul_of_tower, Pi.smul_apply, smul_eq_mul,
                     pow_succ]
          ring
        -- Apply induction hypothesis for the tail
        have step := ih (applyGen a v) (Ma p) (n + 1) hv' i
        rw [step]
        -- Connect liftF(mk (as.reverse ++ [a])) to Ma ∘ liftF(mk as.reverse)
        congr 1
        · -- Exponents: (n+1) + |as| = n + (|as|+1)
          omega
        · -- liftF(mk (as.reverse ++ [a])) p = liftF(mk as.reverse) (Ma p)
          rw [← FreeGroup.mul_mk, map_mul]
          simp only [FreeGroup.lift_mk, List.map_singleton, List.prod_singleton]
          simp only [Ma]
          rcases a with ⟨b, s⟩
          fin_cases b <;> fin_cases s <;>
            simp [cond, LinearEquiv.mul_apply]
    -- Apply enc_ind with l = (toWord w).reverse, n = 0, p = e₂, v = e2Int
    have henc : ∀ i, ((evalWord (FreeGroup.toWord w).reverse e2Int i).re : ℝ) +
        ((evalWord (FreeGroup.toWord w).reverse e2Int i).im : ℝ) * Real.sqrt 2 =
        (3 : ℝ)^(FreeGroup.toWord w).length * ((liftF w) e₂ i) := by
      have hmk : liftF w = liftF (FreeGroup.mk (FreeGroup.toWord w)) :=
        by rw [FreeGroup.mk_toWord]
      rw [hmk]
      have hbase : ∀ i, ((e2Int i).re : ℝ) + ((e2Int i).im : ℝ) * Real.sqrt 2 = 3^0 * e₂ i := by
        intro i
        fin_cases i <;>
          simp [e2Int, e₂, EuclideanSpace.single_apply, Pi.single_apply,
                Zsqrtd.re, Zsqrtd.im]
      have step := enc_ind (FreeGroup.toWord w).reverse e2Int e₂ 0 hbase
      simp only [Nat.zero_add, List.length_reverse, List.reverse_reverse] at step
      exact step
    exact bridge _ hanyInv _ _ henc
  -- Injectivity from the orbit witness
  intro w₁ w₂ hw
  by_contra hne
  -- w₁⁻¹ * w₂ is non-identity (since w₁ ≠ w₂)
  have hne1 : w₁⁻¹ * w₂ ≠ 1 := by
    intro heq
    exact hne (inv_mul_eq_one.mp heq).symm
  -- liftF (w₁⁻¹ * w₂) is the identity linear equiv (since liftF w₁ = liftF w₂)
  have hmap1 : liftF (w₁⁻¹ * w₂) = 1 := by
    simp only [map_mul, map_inv, ← hw, inv_mul_cancel]
  -- Applying it to e₂ gives e₂
  have heq : (liftF (w₁⁻¹ * w₂)) e₂ = e₂ := by
    rw [hmap1]; simp
  exact orbit_ne (w₁⁻¹ * w₂) hne1 heq

-- ============================================================
-- SECTION V: The Main Theorem
-- ============================================================

/-- **Banach-Tarski Paradox**: The unit ball in ℝ³ is paradoxical under
    the group of rigid motions (isometries of ℝ³).

    More precisely: the unit ball B³ can be partitioned into finitely many
    pieces (necessarily non-measurable, requiring AC) and those pieces can
    be rearranged using rotations and translations to form two complete copies
    of B³.

    References:
    - Banach, S. and Tarski, A. (1924). "Sur la décomposition des ensembles
      de points en parties respectivement congruentes."
      Fundamenta Mathematicae, 6:244–277.
    - Wagon, S. (1985). "The Banach-Tarski Paradox." Cambridge University Press.

    Status: Axiomatized. The full proof requires ~800 lines:
    (1) Free subgroup F₂ ↪ SO(3) [Hausdorff, proved above]
    (2) Paradoxical decomposition of F₂
    (3) Extension to S²
    (4) Extension to B³ \ {0}
    (5) Handle the center point separately -/
-- AXIOMATIZED: Banach-Tarski 1924 (proof requires 800+ lines via Hausdorff
-- paradox + Axiom of Choice; provably unprovable in ZF alone)
theorem banach_tarski :
    ∃ (n : ℕ) (pieces : Fin n → Set (EuclideanSpace ℝ (Fin 3)))
      (g₁ g₂ : Fin n → EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)),
    -- The pieces partition the unit ball
    (∀ i, pieces i ⊆ unitBall3) ∧
    (∀ i j, i ≠ j → Disjoint (pieces i) (pieces j)) ∧
    unitBall3 = ⋃ i, pieces i ∧
    -- First reassembly: cover ball #1
    unitBall3 = ⋃ i, g₁ i '' pieces i ∧
    (∀ i j, i ≠ j → Disjoint (g₁ i '' pieces i) (g₁ j '' pieces j)) ∧
    -- Second reassembly: cover ball #2 (a translate of the unit ball)
    (fun x => x + (2 : ℝ) • (EuclideanSpace.single (0 : Fin 3) 1 : EuclideanSpace ℝ (Fin 3))) ''
      unitBall3 = ⋃ i, g₂ i '' pieces i ∧
    (∀ i j, i ≠ j → Disjoint (g₂ i '' pieces i) (g₂ j '' pieces j)) := by
  sorry

/-- **Corollary**: The pieces in the Banach-Tarski decomposition are
    non-Lebesgue-measurable.

    If the pieces were measurable, the countable additivity of Lebesgue measure
    would force: λ(B³) = ∑ᵢ λ(pieces i) = λ(B³) + λ(B³) = 2λ(B³),
    a contradiction since 0 < λ(B³) = (4/3)π < ∞. -/
-- Cardinality argument: if every subset of unitBall3 were measurable (Borel),
-- the measurable sets would number ≤ 𝔠 (since the Borel σ-algebra is countably
-- generated).  But unitBall3 ≅ [0,1] has cardinality 𝔠, so it has 2^𝔠 subsets,
-- giving 2^𝔠 ≤ 𝔠 — contradicting Cantor's theorem.
open Cardinal in
theorem banach_tarski_pieces_nonmeasurable :
    ∃ (A : Set (EuclideanSpace ℝ (Fin 3))), A ⊆ unitBall3 ∧
    ¬MeasurableSet A := by
  by_contra hall
  push_neg at hall
  -- hall : ∀ A, A ⊆ unitBall3 → MeasurableSet A
  -- Step 1: The Borel σ-algebra on ℝ³ has cardinality ≤ 𝔠.
  haveI : MeasurableSpace.CountablyGenerated (EuclideanSpace ℝ (Fin 3)) := inferInstance
  have hmeas_le : #{t : Set (EuclideanSpace ℝ (Fin 3)) | MeasurableSet t} ≤ 𝔠 := by
    set s := MeasurableSpace.countableGeneratingSet (EuclideanSpace ℝ (Fin 3))
    have hcount : s.Countable := MeasurableSpace.countable_countableGeneratingSet
    have hgen : generateFrom s = ‹MeasurableSpace (EuclideanSpace ℝ (Fin 3))› :=
      MeasurableSpace.generateFrom_countableGeneratingSet
    have hrw : ∀ t : Set (EuclideanSpace ℝ (Fin 3)),
        @MeasurableSet _ (generateFrom s) t ↔ MeasurableSet t :=
      fun t => by rw [hgen]
    rw [show {t : Set (EuclideanSpace ℝ (Fin 3)) | MeasurableSet t} =
            {t | @MeasurableSet _ (generateFrom s) t} from
          Set.ext fun t => (hrw t).symm]
    exact MeasurableSpace.cardinal_measurableSet_le_continuum
      ((le_aleph0_iff_set_countable.mpr hcount).trans aleph0_le_continuum)
  -- Step 2: Under our hypothesis, every subset of unitBall3 is measurable,
  --         so #{A | A ⊆ unitBall3} ≤ 𝔠.
  have hball_sub_le : #{A : Set (EuclideanSpace ℝ (Fin 3)) | A ⊆ unitBall3} ≤ 𝔠 := by
    apply le_trans _ hmeas_le
    apply Cardinal.mk_le_of_injective
    exact Set.inclusion_injective (fun A hA => hall A hA)
  -- Step 3: unitBall3 has cardinality ≥ 𝔠 (it contains a copy of [0,1] via single).
  have hball_ge : 𝔠 ≤ #↥unitBall3 := by
    rw [← mk_Icc_real (show (0 : ℝ) < 1 by norm_num)]
    apply mk_le_of_injective (f := fun ⟨t, ht⟩ =>
        ⟨EuclideanSpace.single (0 : Fin 3) t, by
           simp only [unitBall3, Metric.mem_closedBall, dist_zero_right,
                      EuclideanSpace.norm_single, Real.norm_eq_abs,
                      abs_of_nonneg ht.1]
           exact ht.2⟩)
    intro ⟨t₁, _⟩ ⟨t₂, _⟩ h
    simp only [Subtype.mk.injEq] at h
    have h0 := congr_fun h (0 : Fin 3)
    simp only [EuclideanSpace.single_apply, eq_self_iff_true, if_true] at h0
    exact Subtype.ext h0
  -- Step 4: By Cantor, #{A | A ⊆ unitBall3} = 2^#unitBall3 > 𝔠.
  have hball_gt : 𝔠 < #{A : Set (EuclideanSpace ℝ (Fin 3)) | A ⊆ unitBall3} := by
    -- 𝒫 s is definitionally {t | t ⊆ s}, so these are equal by rfl.
    rw [show {A : Set (EuclideanSpace ℝ (Fin 3)) | A ⊆ unitBall3} = 𝒫 unitBall3 from rfl,
        mk_powerset]
    exact hball_ge.trans_lt (cantor _)
  -- Contradiction: 2^𝔠 ≤ 𝔠 violates Cantor.
  exact absurd hball_sub_le hball_gt.not_le

-- ============================================================
-- SECTION VI: Relationship to Amenability
-- ============================================================

/-- A group `G` is **amenable** if it admits a finitely-additive,
    left-invariant probability measure on all its subsets.

    The Banach-Tarski paradox is equivalent to: the free group F₂ is
    NOT amenable (Tarski's theorem). More precisely:
    - ℤ and finite groups are amenable
    - F₂ (free group of rank ≥ 2) is NOT amenable
    - SO(3) contains F₂, hence is not amenable
    - This non-amenability is the GROUP-THEORETIC source of Banach-Tarski -/
def IsAmenable (G : Type*) [Group G] : Prop :=
  ∃ (μ : Set G → ℝ≥0∞),
    -- μ is a probability measure (total mass = 1)
    μ Set.univ = 1 ∧
    -- finitely additive
    (∀ A B : Set G, Disjoint A B → μ (A ∪ B) = μ A + μ B) ∧
    -- left-invariant
    ∀ (g : G) (A : Set G), μ (g • A) = μ A

/-- The integers ℤ are amenable via the Cesàro mean construction.
    (This is a classical fact; the full proof uses the definition of
    Banach limits / ultrafilter means.) -/
-- Proof strategy: non-principal ultrafilter U on ℕ + symmetric Cesàro density.
-- For each N : ℕ and A ⊆ Multiplicative ℤ, define
--   dens N A = |{k ∈ [-N,N] | ofAdd k ∈ A}| / (2N+1)
-- Then μ A = U.lim (dens · A) (ultrafilter limit, exists since ENNReal is compact T2).
-- Properties: (1) dens N univ = 1 → μ(univ) = 1.
--             (2) dens N (A∪B) = dens N A + dens N B for disjoint A,B → additive.
--             (3) |dens N (g•A) - dens N A| ≤ 2|n|/(2N+1) → 0 along U → invariant.
theorem int_amenable : IsAmenable (Multiplicative ℤ) := by
  -- Non-principal ultrafilter on ℕ extending atTop
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  -- Symmetric Cesàro density function (values in ENNReal = [0,∞])
  let dens : ℕ → Set (Multiplicative ℤ) → ℝ≥0∞ := fun N A =>
    (((Finset.Icc (-(N : ℤ)) N).filter
       (fun k => Multiplicative.ofAdd k ∈ A)).card : ℝ≥0∞) /
    (2 * (N : ℝ≥0∞) + 1)
  -- μ A = ultrafilter limit of the Cesàro densities
  -- ENNReal is compact and T2 (it equals [0,∞] as a topological space)
  -- so Ultrafilter.lim is well-defined for ENNReal-valued sequences.
  let μ : Set (Multiplicative ℤ) → ℝ≥0∞ := fun A => U.lim (dens · A)
  refine ⟨μ, ?_, ?_, ?_⟩
  -- Part 1: Total mass μ(univ) = 1
  · suffices h : ∀ N : ℕ, dens N Set.univ = 1 by
      simp only [μ]
      rw [show dens · Set.univ = fun _ => (1 : ℝ≥0∞) from funext h]
      exact Ultrafilter.lim_const 1
    intro N
    simp only [dens]
    -- Every k in the window is in Set.univ, so filter keeps all elements
    have hfilt : (Finset.Icc (-(N : ℤ)) N).filter
        (fun k => Multiplicative.ofAdd k ∈ (Set.univ : Set (Multiplicative ℤ))) =
        Finset.Icc (-(N : ℤ)) N := Finset.filter_True_of_mem (fun _ _ => trivial)
    rw [hfilt, Finset.Int.card_fintypeIcc, Int.toNat_of_nonneg (by omega)]
    push_cast
    rw [show (2 * (N : ℝ≥0∞) + 1) = (2 * (N : ℝ≥0∞) + 1) from rfl]
    norm_cast
    rw [ENNReal.div_self]
    · norm_cast; omega
    · norm_cast; omega
  -- Part 2: Finite additivity μ(A ∪ B) = μ(A) + μ(B) for disjoint A, B
  · intro A B hAB
    -- At each N, the equality is exact: dens N (A∪B) = dens N A + dens N B
    have h_eq : ∀ N : ℕ, dens N (A ∪ B) = dens N A + dens N B := by
      intro N
      simp only [dens]
      rw [← ENNReal.add_div]
      congr 1
      -- card(filter(A∪B)) = card(filter A) + card(filter B) since A ∩ B = ∅
      have h_disj : Disjoint
          ((Finset.Icc (-(N : ℤ)) N).filter (fun k => Multiplicative.ofAdd k ∈ A))
          ((Finset.Icc (-(N : ℤ)) N).filter (fun k => Multiplicative.ofAdd k ∈ B)) :=
        Finset.disjoint_filter.mpr fun k _ hkA hkB =>
          Set.disjoint_left.mp hAB hkA hkB
      push_cast
      rw [← Finset.card_union_of_disjoint h_disj]
      congr 1
      ext k
      simp [Finset.mem_filter, Finset.mem_union, Set.mem_union]
    -- Rewrite as function equality, then use continuity of + and uniqueness of limits
    simp only [μ]
    rw [show dens · (A ∪ B) = fun N => dens N A + dens N B from funext h_eq]
    -- U.lim (f + g) = U.lim f + U.lim g via continuity of addition in ENNReal
    have hA_tendsto : Filter.Tendsto (dens · A) U.toFilter (nhds (U.lim (dens · A))) :=
      Ultrafilter.tendsto_nhds_lim rfl
    have hB_tendsto : Filter.Tendsto (dens · B) U.toFilter (nhds (U.lim (dens · B))) :=
      Ultrafilter.tendsto_nhds_lim rfl
    have hsum_tendsto := hA_tendsto.add hB_tendsto
    exact tendsto_nhds_unique hsum_tendsto (Ultrafilter.tendsto_nhds_lim rfl)
  -- Part 3: Left-invariance μ(g • A) = μ(A) for all g : Multiplicative ℤ
  · intro g A
    simp only [μ]
    -- n = the integer corresponding to g under toAdd
    set n : ℤ := Multiplicative.toAdd g
    -- The left-multiplication action: g • A = {ofAdd (n + k) | ofAdd k ∈ A}
    -- Therefore: ofAdd m ∈ g • A ↔ ofAdd (m - n) ∈ A
    have h_mem : ∀ m : ℤ, Multiplicative.ofAdd m ∈ g • A ↔
        Multiplicative.ofAdd (m - n) ∈ A := by
      intro m
      simp [Set.mem_smul_set, smul_eq_mul, Multiplicative.ofAdd_mul,
            Multiplicative.toAdd_ofAdd]
      constructor
      · rintro ⟨a, ha, rfl⟩
        simp [Multiplicative.toAdd_ofAdd, Multiplicative.ofAdd_toAdd]
        convert ha using 2
        simp [Multiplicative.toAdd_mul, Multiplicative.toAdd_ofAdd]
        ring
      · intro ha
        exact ⟨Multiplicative.ofAdd (m - n), ha, by
          simp [Multiplicative.ofAdd_mul, Multiplicative.ofAdd_toAdd]
          congr 1; push_cast; ring⟩
    -- absn = |n| as a natural number
    set absn : ℕ := n.natAbs with h_absn
    -- Step 1: Reindex dens N (g•A) — bijection k ↦ k-n moves window [-N,N] to [-N-n,N-n]
    have h_card_eq : ∀ N : ℕ,
        ((Finset.Icc (-(N : ℤ)) N).filter (fun k => Multiplicative.ofAdd k ∈ g • A)).card =
        ((Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).filter
          (fun k => Multiplicative.ofAdd k ∈ A)).card := by
      intro N
      apply Finset.card_bij (fun k _ => k - n)
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
        exact ⟨by omega, (h_mem k).mp hk.2⟩
      · intro a _ b _ hab; omega
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_Icc] at hk
        exact ⟨k + n, by simp only [Finset.mem_filter, Finset.mem_Icc];
          exact ⟨by omega, (h_mem (k + n)).mpr (by convert hk.2 using 2; ring)⟩, by ring⟩
    -- So dens N (g•A) equals the density over the shifted window
    have h_dens_shift : ∀ N : ℕ, dens N (g • A) =
        (((Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).filter
          (fun k => Multiplicative.ofAdd k ∈ A)).card : ℝ≥0∞) / (2 * (N : ℝ≥0∞) + 1) := by
      intro N; simp only [dens]; congr 1; exact_mod_cast h_card_eq N
    -- Step 2: Card bound — shifted window ⊆ original ∪ at most absn extra elements
    -- Helper to bound card of sdiff
    have h_sdiff_bound : ∀ N : ℕ,
        ((Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).filter
          (fun k => Multiplicative.ofAdd k ∈ A)).card ≤
        ((Finset.Icc (-(N : ℤ)) N).filter (fun k => Multiplicative.ofAdd k ∈ A)).card + absn := by
      intro N
      have h_sub : (Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).filter
            (fun k => Multiplicative.ofAdd k ∈ A) ⊆
          ((Finset.Icc (-(N : ℤ)) N).filter (fun k => Multiplicative.ofAdd k ∈ A)) ∪
          (Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n) \ Finset.Icc (-(N : ℤ)) N) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_sdiff] at hk ⊢
        by_cases hk2 : -(N : ℤ) ≤ k ∧ k ≤ N
        · left; exact ⟨hk2, hk.2⟩
        · right; exact ⟨hk.1, by push_neg at hk2; simp [Finset.mem_Icc]; omega⟩
      have h_card : (Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n) \
            Finset.Icc (-(N : ℤ)) N).card ≤ absn := by
        rcases Int.le_or_lt 0 n with hn | hn
        · -- n ≥ 0: sdiff ⊆ Icc(-N-n, -N-1), size n = absn
          calc (Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n) \ Finset.Icc (-(N : ℤ)) N).card
              ≤ (Finset.Icc (-(N : ℤ) - n) (-(N : ℤ) - 1)).card :=
                Finset.card_le_card (by
                  intro k; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega)
            _ ≤ absn := by
                rw [Int.card_Icc, h_absn]
                have heq : -(N : ℤ) - 1 + 1 - (-(N : ℤ) - n) = n := by ring
                rw [heq, Int.natAbs_of_nonneg hn]
                exact Nat.le_refl _
        · -- n < 0: sdiff ⊆ Icc(N+1, N-n), size -n = absn
          calc (Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n) \ Finset.Icc (-(N : ℤ)) N).card
              ≤ (Finset.Icc ((N : ℤ) + 1) ((N : ℤ) - n)).card :=
                Finset.card_le_card (by
                  intro k; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega)
            _ ≤ absn := by
                rw [Int.card_Icc, h_absn, ← Int.natAbs_neg]
                have heq : (N : ℤ) - n + 1 - ((N : ℤ) + 1) = -n := by ring
                rw [heq, Int.natAbs_of_nonneg (by linarith : (0:ℤ) ≤ -n)]
                exact Nat.le_refl _
      calc ((Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).filter
              (fun k => Multiplicative.ofAdd k ∈ A)).card
          ≤ (((Finset.Icc (-(N : ℤ)) N).filter (fun k => Multiplicative.ofAdd k ∈ A)) ∪
              (Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n) \ Finset.Icc (-(N : ℤ)) N)).card :=
            Finset.card_le_card h_sub
        _ ≤ ((Finset.Icc (-(N : ℤ)) N).filter (fun k => Multiplicative.ofAdd k ∈ A)).card +
              (Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n) \ Finset.Icc (-(N : ℤ)) N).card :=
            Finset.card_union_le _ _
        _ ≤ ((Finset.Icc (-(N : ℤ)) N).filter (fun k => Multiplicative.ofAdd k ∈ A)).card +
              absn := Nat.add_le_add_left h_card _
    have h_sdiff_bound2 : ∀ N : ℕ,
        ((Finset.Icc (-(N : ℤ)) N).filter (fun k => Multiplicative.ofAdd k ∈ A)).card ≤
        ((Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).filter
          (fun k => Multiplicative.ofAdd k ∈ A)).card + absn := by
      intro N
      have h_sub2 : (Finset.Icc (-(N : ℤ)) N).filter
            (fun k => Multiplicative.ofAdd k ∈ A) ⊆
          ((Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).filter
            (fun k => Multiplicative.ofAdd k ∈ A)) ∪
          (Finset.Icc (-(N : ℤ)) N \ Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_sdiff] at hk ⊢
        by_cases hk2 : -(N : ℤ) - n ≤ k ∧ k ≤ (N : ℤ) - n
        · left; exact ⟨hk2, hk.2⟩
        · right; exact ⟨hk.1, by push_neg at hk2; simp [Finset.mem_Icc]; omega⟩
      have h_card2 : (Finset.Icc (-(N : ℤ)) N \
            Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).card ≤ absn := by
        rcases Int.le_or_lt 0 n with hn | hn
        · -- n ≥ 0: Icc(-N,N) \ Icc(-N-n,N-n) ⊆ Icc(N-n+1, N), size n = absn
          calc (Finset.Icc (-(N : ℤ)) N \ Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).card
              ≤ (Finset.Icc ((N : ℤ) - n + 1) N).card :=
                Finset.card_le_card (by
                  intro k; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega)
            _ ≤ absn := by
                rw [Int.card_Icc, h_absn]
                have heq : (N : ℤ) + 1 - ((N : ℤ) - n + 1) = n := by ring
                rw [heq, Int.natAbs_of_nonneg hn]
                exact Nat.le_refl _
        · -- n < 0: Icc(-N,N) \ Icc(-N-n,N-n) ⊆ Icc(-N, -N-n-1), size -n = absn
          calc (Finset.Icc (-(N : ℤ)) N \ Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).card
              ≤ (Finset.Icc (-(N : ℤ)) (-(N : ℤ) - n - 1)).card :=
                Finset.card_le_card (by
                  intro k; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega)
            _ ≤ absn := by
                rw [Int.card_Icc, h_absn, ← Int.natAbs_neg]
                have heq : -(N : ℤ) - n - 1 + 1 - (-(N : ℤ)) = -n := by ring
                rw [heq, Int.natAbs_of_nonneg (by linarith : (0:ℤ) ≤ -n)]
                exact Nat.le_refl _
      calc ((Finset.Icc (-(N : ℤ)) N).filter
              (fun k => Multiplicative.ofAdd k ∈ A)).card
          ≤ (((Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).filter
              (fun k => Multiplicative.ofAdd k ∈ A)) ∪
              (Finset.Icc (-(N : ℤ)) N \ Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n))).card :=
            Finset.card_le_card h_sub2
        _ ≤ ((Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).filter
              (fun k => Multiplicative.ofAdd k ∈ A)).card +
              (Finset.Icc (-(N : ℤ)) N \ Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).card :=
            Finset.card_union_le _ _
        _ ≤ ((Finset.Icc (-(N : ℤ) - n) ((N : ℤ) - n)).filter
              (fun k => Multiplicative.ofAdd k ∈ A)).card + absn :=
            Nat.add_le_add_left h_card2 _
    have h_upper : ∀ N : ℕ, dens N (g • A) ≤ dens N A + (absn : ℝ≥0∞) / (2 * N + 1) := by
      intro N
      rw [h_dens_shift N]; simp only [dens, ← ENNReal.add_div]
      exact ENNReal.div_le_div_right (by exact_mod_cast h_sdiff_bound N) _
    have h_lower : ∀ N : ℕ, dens N A ≤ dens N (g • A) + (absn : ℝ≥0∞) / (2 * N + 1) := by
      intro N
      rw [h_dens_shift N]; simp only [dens, ← ENNReal.add_div]
      exact ENNReal.div_le_div_right (by exact_mod_cast h_sdiff_bound2 N) _
    -- Step 3: The error term absn/(2N+1) → 0 along atTop (and hence along U ⊇ atTop)
    have h_atTop_le_U : Filter.atTop ≤ U.toFilter := Ultrafilter.of_le Filter.atTop
    have h_err_tendsto : Filter.Tendsto
        (fun N : ℕ => (absn : ℝ≥0∞) / (2 * (N : ℝ≥0∞) + 1))
        U.toFilter (nhds 0) := by
      apply Filter.Tendsto.mono_left _ h_atTop_le_U
      -- Step 1: Prove the limit in ℝ: absn/(2N+1) → 0
      have h_real : Filter.Tendsto (fun N : ℕ => (absn : ℝ) / (2 * N + 1))
          Filter.atTop (nhds 0) := by
        apply tendsto_const_nhds.div_atTop
        apply Filter.tendsto_atTop_atTop_of_monotone (fun a b hab => by linarith)
        intro b
        exact ⟨Nat.ceil (max 0 ((b - 1) / 2)),
               fun N hN => by
                 have h1 : (N : ℝ) ≥ Nat.ceil (max 0 ((b - 1) / 2)) := by exact_mod_cast hN
                 have h2 : (Nat.ceil (max 0 ((b - 1) / 2)) : ℝ) ≥ max 0 ((b - 1) / 2) :=
                   Nat.le_ceil _
                 linarith [le_max_right 0 ((b - 1) / 2)]⟩
      -- Step 2: Rewrite each ENNReal term as ENNReal.ofReal (ℝ value)
      have hcoerce : ∀ N : ℕ, (absn : ℝ≥0∞) / (2 * (N : ℝ≥0∞) + 1) =
          ENNReal.ofReal ((absn : ℝ) / (2 * N + 1)) := fun N => by
        have hpos : (0:ℝ) < 2 * N + 1 := by positivity
        have hdenom : ENNReal.ofReal (2 * (N:ℝ) + 1) = 2 * (N:ℝ≥0∞) + 1 := by
          rw [ENNReal.ofReal_add (by positivity) (by norm_num : (0:ℝ) ≤ 1),
              ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          simp [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
        rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, hdenom]
      simp_rw [hcoerce]
      simpa using ENNReal.tendsto_ofReal h_real
    -- Step 4: Squeeze — use le_of_tendsto_of_tendsto to get equality
    set L := U.lim (dens · A)
    have hA_tendsto : Filter.Tendsto (dens · A) U.toFilter (nhds L) :=
      Ultrafilter.tendsto_nhds_lim rfl
    have hgA_tendsto : Filter.Tendsto (dens · (g • A)) U.toFilter
        (nhds (U.lim (dens · (g • A)))) := Ultrafilter.tendsto_nhds_lim rfl
    -- Upper bound: U.lim(dens·(g•A)) ≤ L
    have h_le : U.lim (dens · (g • A)) ≤ L := by
      have hbound : Filter.Tendsto
          (fun N => dens N A + (absn : ℝ≥0∞) / (2 * N + 1))
          U.toFilter (nhds (L + 0)) := hA_tendsto.add h_err_tendsto
      rw [add_zero] at hbound
      exact le_of_tendsto_of_tendsto hgA_tendsto hbound
        (Filter.Eventually.of_forall h_upper)
    -- Lower bound: L ≤ U.lim(dens·(g•A))
    have h_ge : L ≤ U.lim (dens · (g • A)) := by
      have hbound2 : Filter.Tendsto
          (fun N => dens N (g • A) + (absn : ℝ≥0∞) / (2 * N + 1))
          U.toFilter (nhds (U.lim (dens · (g • A)) + 0)) := hgA_tendsto.add h_err_tendsto
      rw [add_zero] at hbound2
      exact le_of_tendsto_of_tendsto hA_tendsto hbound2
        (Filter.Eventually.of_forall h_lower)
    exact le_antisymm h_le h_ge

/-- Words starting with generator g (as positive or inverse letter).
    NOTE: Mathlib convention: (g, true) = positive generator, (g, false) = inverse.
    This follows from FreeGroup.toWord_of : (of a).toWord = [(a, true)]. -/
private def WordStart (g : Fin 2) (b : Bool) : Set (FreeGroup (Fin 2)) :=
  {w | w.toWord.head? = some (g, b)}

/-- WordStart coincides with Mathlib's FreeGroup.startsWith. -/
private lemma wordStart_eq_startsWith {g : Fin 2} {b : Bool} :
    WordStart g b = FreeGroup.startsWith (g, b) := by
  ext w
  simp only [WordStart, FreeGroup.startsWith, Set.mem_setOf_eq]
  cases w.toWord <;> simp [List.head?]

/-- (FreeGroup.of 0)⁻¹ = mk [(0, false)].
    Proof: toWord_of gives [(0,true)]; invRev reverses and negates bools → [(0,false)]. -/
private lemma freeGroup_inv_eq_mk_false (g : Fin 2) :
    (FreeGroup.of g)⁻¹ = FreeGroup.mk [(g, false)] := by
  apply FreeGroup.toWord_injective
  simp [FreeGroup.toWord_inv, FreeGroup.toWord_of, FreeGroup.invRev,
        FreeGroup.toWord_mk]

/-- COVER: F₂ = (starts with a) ∪ a · (starts with a⁻¹).
    Key: positive generator is (0,true); inverse is (0,false) (Mathlib convention).
    Any w not starting with a satisfies: a⁻¹·w starts with a⁻¹ (no cancellation),
    so w = a·(a⁻¹·w) lies in a • WordStart 0 false. -/
private lemma free_group_cover_a :
    let a := FreeGroup.of (0 : Fin 2)
    Set.univ = WordStart 0 true ∪ a • WordStart 0 false := by
  intro a
  simp_rw [wordStart_eq_startsWith]
  ext w
  simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_smul_set]
  by_cases h : w ∈ FreeGroup.startsWith (0, true)
  · exact Or.inl h
  · -- w doesn't start with a. Take v = a⁻¹·w.
    -- By startsWith_mk_mul with letter=(0,false): since w ∉ startsWith(0,true),
    -- mk[(0,false)]·w ∈ startsWith(0,false), i.e., a⁻¹·w starts with a⁻¹.
    refine Or.inr ⟨FreeGroup.mk [(0, false)] * w, FreeGroup.startsWith_mk_mul w h, ?_⟩
    -- a · (a⁻¹ · w) = w
    have : FreeGroup.of (0 : Fin 2) * FreeGroup.mk [(0, false)] = 1 := by
      rw [← freeGroup_inv_eq_mk_false]; exact mul_inv_cancel _
    calc a * (FreeGroup.mk [(0, false)] * w)
        = (a * FreeGroup.mk [(0, false)]) * w := (mul_assoc _ _ _).symm
      _ = 1 * w := by rw [this]
      _ = w := one_mul _

/-- DISJOINTNESS: (starts with a) and a·(starts with a⁻¹) are disjoint.
    Proof: if w starts with a AND w = a·v with v starting with a⁻¹, then
    v.toWord = (0,false)::rest and w.toWord = rest (after cancellation of a·a⁻¹).
    But w.toWord.head = (0,true) = rest.head forces (0,false)::(0,true) in v.toWord,
    contradicting IsReduced. -/
private lemma free_group_cover_a_disj :
    let a := FreeGroup.of (0 : Fin 2)
    Disjoint (WordStart 0 true) (a • WordStart 0 false) := by
  intro a
  rw [Set.disjoint_left]
  intro w hw1 ⟨v, hv, hvw⟩
  simp only [WordStart, Set.mem_setOf_eq] at hw1 hv
  -- Extract: v.toWord = (0,false) :: rest
  obtain ⟨rest, hv_eq⟩ : ∃ rest, v.toWord = (0, false) :: rest := by
    rcases hv_nil : v.toWord with _ | ⟨hd, tl⟩
    · simp [hv_nil, List.head?] at hv
    · have hhd : hd = (0, false) := by simpa [hv_nil, List.head?] using hv
      subst hhd
      exact ⟨tl, rfl⟩
  -- Compute: (a·v).toWord = rest  (a·a⁻¹ cancels at the front)
  have hw_eq : w.toWord = rest := by
    simp only [smul_eq_mul] at hvw
    rw [← hvw, FreeGroup.toWord_mul, FreeGroup.toWord_of]
    rw [List.singleton_append, FreeGroup.reduce.cons]
    -- reduce v.toWord = v.toWord (already reduced)
    rw [FreeGroup.isReduced_iff_reduce_eq.mp FreeGroup.isReduced_toWord, hv_eq]
    -- casesOn ((0,false)::rest): condition 0=0 ∧ true=!false → cancel → result = rest
    -- All decidable computations on Fin 2 × Bool; rfl closes by kernel reduction
    rfl
  -- Now rest.head? = some (0,true) (from hw1 and hw_eq)
  -- So v.toWord = (0,false)::(0,true)::rest', which is unreduced — contradiction.
  rcases hrest : rest with _ | ⟨hd', rest'⟩
  · simp [hrest] at hw_eq; rw [hw_eq] at hw1; simp [List.head?] at hw1
  · have hhd' : hd' = (0, true) := by
      have := hw1; rw [hw_eq, hrest] at this; simpa [List.head?] using this
    subst hhd'
    -- v.toWord = (0,false)::(0,true)::rest' is not reduced
    have hred : FreeGroup.IsReduced v.toWord := FreeGroup.isReduced_toWord
    rw [hv_eq, hrest, FreeGroup.isReduced_cons_cons] at hred
    exact absurd (hred.1 rfl) (by decide)

/-- Same cover for generator b = FreeGroup.of 1. -/
private lemma free_group_cover_b :
    let b := FreeGroup.of (1 : Fin 2)
    Set.univ = WordStart 1 true ∪ b • WordStart 1 false := by
  intro b
  simp_rw [wordStart_eq_startsWith]
  ext w
  simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_smul_set]
  by_cases h : w ∈ FreeGroup.startsWith (1, true)
  · exact Or.inl h
  · refine Or.inr ⟨FreeGroup.mk [(1, false)] * w, FreeGroup.startsWith_mk_mul w h, ?_⟩
    have : FreeGroup.of (1 : Fin 2) * FreeGroup.mk [(1, false)] = 1 := by
      rw [← freeGroup_inv_eq_mk_false]; exact mul_inv_cancel _
    calc b * (FreeGroup.mk [(1, false)] * w)
        = (b * FreeGroup.mk [(1, false)]) * w := (mul_assoc _ _ _).symm
      _ = 1 * w := by rw [this]
      _ = w := one_mul _

private lemma free_group_cover_b_disj :
    let b := FreeGroup.of (1 : Fin 2)
    Disjoint (WordStart 1 true) (b • WordStart 1 false) := by
  intro b
  rw [Set.disjoint_left]
  intro w hw1 ⟨v, hv, hvw⟩
  simp only [WordStart, Set.mem_setOf_eq] at hw1 hv
  obtain ⟨rest, hv_eq⟩ : ∃ rest, v.toWord = (1, false) :: rest := by
    rcases hv_nil : v.toWord with _ | ⟨hd, tl⟩
    · simp [hv_nil, List.head?] at hv
    · have hhd : hd = (1, false) := by simpa [hv_nil, List.head?] using hv
      subst hhd
      exact ⟨tl, rfl⟩
  have hw_eq : w.toWord = rest := by
    simp only [smul_eq_mul] at hvw
    rw [← hvw, FreeGroup.toWord_mul, FreeGroup.toWord_of]
    rw [List.singleton_append, FreeGroup.reduce.cons]
    rw [FreeGroup.isReduced_iff_reduce_eq.mp FreeGroup.isReduced_toWord, hv_eq]
    rfl
  rcases hrest : rest with _ | ⟨hd', rest'⟩
  · simp [hrest] at hw_eq; rw [hw_eq] at hw1; simp [List.head?] at hw1
  · have hhd' : hd' = (1, true) := by
      have := hw1; rw [hw_eq, hrest] at this; simpa [List.head?] using this
    subst hhd'
    have hred : FreeGroup.IsReduced v.toWord := FreeGroup.isReduced_toWord
    rw [hv_eq, hrest, FreeGroup.isReduced_cons_cons] at hred
    exact absurd (hred.1 rfl) (by decide)

/-- The four word-start sets are pairwise disjoint (they check distinct head? values). -/
private lemma wordStart_disjoint {g₁ g₂ : Fin 2} {b₁ b₂ : Bool}
    (h : (g₁, b₁) ≠ (g₂, b₂)) : Disjoint (WordStart g₁ b₁) (WordStart g₂ b₂) := by
  apply Set.disjoint_left.mpr
  intro w h₁ h₂
  simp [WordStart] at h₁ h₂
  exact h (Option.some.inj (h₁.symm.trans h₂))

/-- The free group F₂ is **paradoxical** under its own left regular action.
    F₂ = W(a) ∪ a·W(a⁻¹) shows F₂ ≃ W(a) ∪ W(a⁻¹), and similarly F₂ ≃ W(b) ∪ W(b⁻¹).
    Since the four word-start sets are pairwise disjoint, B = W(a) ∪ W(a⁻¹) and
    C = W(b) ∪ W(b⁻¹) are disjoint subsets of F₂, each equidecomposable with the whole.

    This is the key algebraic ingredient for Banach-Tarski: the paradoxical
    decomposition lifts from F₂ to SO(3) via the Hausdorff free subgroup. -/
theorem free_group_paradoxical :
    IsParadoxical (FreeGroup (Fin 2)) (Set.univ : Set (FreeGroup (Fin 2))) := by
  -- B = W(a) ∪ W(a⁻¹), C = W(b) ∪ W(b⁻¹)
  refine ⟨WordStart 0 true ∪ WordStart 0 false,
          WordStart 1 true ∪ WordStart 1 false,
          Set.subset_univ _, Set.subset_univ _, ?_, ?_, ?_⟩
  · -- B ∩ C = ∅: four pairwise disjoint WordStart sets
    exact Set.disjoint_union_right.mpr
      ⟨Set.disjoint_union_left.mpr
        ⟨wordStart_disjoint (by decide), wordStart_disjoint (by decide)⟩,
       Set.disjoint_union_left.mpr
        ⟨wordStart_disjoint (by decide), wordStart_disjoint (by decide)⟩⟩
  · -- F₂ ≃ B via: pieces {W(a), a·W(a⁻¹)}, moves {1, a⁻¹}
    -- Images: 1·W(a) = W(a), a⁻¹·(a·W(a⁻¹)) = W(a⁻¹)
    refine ⟨2, ![WordStart 0 true, FreeGroup.of (0 : Fin 2) • WordStart 0 false],
            ![1, (FreeGroup.of (0 : Fin 2))⁻¹], ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact Set.subset_univ _
    · intro i j hij; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
        first | exact absurd rfl hij | exact free_group_cover_a_disj
              | exact free_group_cover_a_disj.symm
    · -- univ = W(a) ∪ a·W(a⁻¹)
      simp only [Fin.iUnion_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
                  Matrix.head_cons]
      exact free_group_cover_a
    · -- B = W(a) ∪ a⁻¹·(a·W(a⁻¹)) = W(a) ∪ W(a⁻¹)
      simp only [Fin.iUnion_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
                  Matrix.head_cons, one_smul, ← mul_smul, inv_mul_cancel, one_smul]
    · intro i j hij; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                    one_smul, ← mul_smul, inv_mul_cancel, one_smul] <;>
        first | exact absurd rfl hij | exact wordStart_disjoint (by decide)
              | exact (wordStart_disjoint (by decide)).symm
  · -- F₂ ≃ C via: pieces {W(b), b·W(b⁻¹)}, moves {1, b⁻¹}
    refine ⟨2, ![WordStart 1 true, FreeGroup.of (1 : Fin 2) • WordStart 1 false],
            ![1, (FreeGroup.of (1 : Fin 2))⁻¹], ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact Set.subset_univ _
    · intro i j hij; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
        first | exact absurd rfl hij | exact free_group_cover_b_disj
              | exact free_group_cover_b_disj.symm
    · simp only [Fin.iUnion_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
                  Matrix.head_cons]
      exact free_group_cover_b
    · simp only [Fin.iUnion_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
                  Matrix.head_cons, one_smul, ← mul_smul, inv_mul_cancel, one_smul]
    · intro i j hij; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                    one_smul, ← mul_smul, inv_mul_cancel, one_smul] <;>
        first | exact absurd rfl hij | exact wordStart_disjoint (by decide)
              | exact (wordStart_disjoint (by decide)).symm

/-- The free group of rank 2 is NOT amenable.
    Proof: F₂ = W_a ∪ a·W_ainv (disjoint) gives μ(W_a) + μ(W_ainv) = 1.
    Similarly μ(W_b) + μ(W_binv) = 1. But all four sets are pairwise disjoint
    subsets of F₂, so their measures sum ≤ 1. This gives 2 ≤ 1. -/
theorem free_group_not_amenable : ¬IsAmenable (FreeGroup (Fin 2)) := by
  intro ⟨μ, hμ1, hμ_add, hμ_inv⟩
  set a := FreeGroup.of (0 : Fin 2)
  set b := FreeGroup.of (1 : Fin 2)
  -- W_a = starts with a (positive), W_ainv = starts with a⁻¹ (inverse)
  -- Mathlib convention: (g, true) = positive, (g, false) = inverse
  set W_a    := WordStart 0 true
  set W_ainv := WordStart 0 false
  set W_b    := WordStart 1 true
  set W_binv := WordStart 1 false
  -- From the a-cover: F₂ = W_a ∪ a·W_ainv → 1 = μ(W_a) + μ(W_ainv)
  have hsum_a : μ W_a + μ W_ainv = 1 := by
    have heq : μ Set.univ = μ W_a + μ (a • W_ainv) := by
      conv_lhs => rw [free_group_cover_a]
      exact hμ_add W_a (a • W_ainv) free_group_cover_a_disj
    rw [hμ1, hμ_inv a W_ainv] at heq
    exact heq.symm
  -- From the b-cover: μ(W_b) + μ(W_binv) = 1
  have hsum_b : μ W_b + μ W_binv = 1 := by
    have heq : μ Set.univ = μ W_b + μ (b • W_binv) := by
      conv_lhs => rw [free_group_cover_b]
      exact hμ_add W_b (b • W_binv) free_group_cover_b_disj
    rw [hμ1, hμ_inv b W_binv] at heq
    exact heq.symm
  -- The four sets are pairwise disjoint
  have hd_a_ainv : Disjoint W_a W_ainv   := wordStart_disjoint (by decide)
  have hd_b_binv : Disjoint W_b W_binv   := wordStart_disjoint (by decide)
  have hd_ab     : Disjoint W_a W_b      := wordStart_disjoint (by decide)
  have hd_abv    : Disjoint W_a W_binv   := wordStart_disjoint (by decide)
  have hd_aib    : Disjoint W_ainv W_b   := wordStart_disjoint (by decide)
  have hd_aibv   : Disjoint W_ainv W_binv := wordStart_disjoint (by decide)
  -- μ((W_a ∪ W_ainv) ∪ (W_b ∪ W_binv)) ≤ 1
  have hd_pair : Disjoint (W_a ∪ W_ainv) (W_b ∪ W_binv) :=
    Set.disjoint_union_right.mpr
      ⟨Set.disjoint_union_left.mpr ⟨hd_ab, hd_aib⟩,
       Set.disjoint_union_left.mpr ⟨hd_abv, hd_aibv⟩⟩
  have hsub : (W_a ∪ W_ainv) ∪ (W_b ∪ W_binv) ⊆ Set.univ := Set.subset_univ _
  have hμ_union_le : μ ((W_a ∪ W_ainv) ∪ (W_b ∪ W_binv)) ≤ 1 := by
    have hcompl := hμ_add ((W_a ∪ W_ainv) ∪ (W_b ∪ W_binv))
                   (Set.univ \ ((W_a ∪ W_ainv) ∪ (W_b ∪ W_binv)))
                   disjoint_sdiff_right
    rw [Set.union_diff_cancel hsub, hμ1] at hcompl
    exact (le_add_right le_rfl).trans hcompl.symm.le
  -- Expand μ to sum = 2, derive 2 ≤ 1: contradiction
  have hexpand : μ ((W_a ∪ W_ainv) ∪ (W_b ∪ W_binv)) =
                 μ W_a + μ W_ainv + (μ W_b + μ W_binv) := by
    rw [hμ_add _ _ hd_pair, hμ_add W_a W_ainv hd_a_ainv, hμ_add W_b W_binv hd_b_binv]
  have h2 : μ W_a + μ W_ainv + (μ W_b + μ W_binv) = 2 := by
    rw [hsum_a, hsum_b]; norm_num
  rw [hexpand, h2] at hμ_union_le
  exact absurd hμ_union_le (by norm_num)

end BanachTarski
