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
open scoped Pointwise ENNReal InnerProductSpace

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
  simp only [anyInv, inv_phi, inv_phi_inv, inv_psi, inv_psi_inv, e2Int,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
             Matrix.head_cons, Matrix.tail_cons,
             show (⟨0, 0⟩ : Zsqrtd 2).re = (0 : ℤ) from rfl,
             show (⟨0, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).re = (1 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl]
  omega

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
  simp only [inv_phi, e2Int]
  zsqrtd_simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
             Matrix.head_cons, Matrix.tail_cons,
             show (⟨0, 0⟩ : Zsqrtd 2).re = (0 : ℤ) from rfl,
             show (⟨0, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).re = (1 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl]
  omega

private lemma base_phi_inv : inv_phi_inv (scaledActPhiInv e2Int) := by
  simp only [inv_phi_inv, e2Int]
  zsqrtd_simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
             Matrix.head_cons, Matrix.tail_cons,
             show (⟨0, 0⟩ : Zsqrtd 2).re = (0 : ℤ) from rfl,
             show (⟨0, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).re = (1 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl]
  omega

private lemma base_psi : inv_psi (scaledActPsi e2Int) := by
  simp only [inv_psi, e2Int]
  zsqrtd_simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
             Matrix.head_cons, Matrix.tail_cons,
             show (⟨0, 0⟩ : Zsqrtd 2).re = (0 : ℤ) from rfl,
             show (⟨0, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).re = (1 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl]
  omega

private lemma base_psi_inv : inv_psi_inv (scaledActPsiInv e2Int) := by
  simp only [inv_psi_inv, e2Int]
  zsqrtd_simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
             Matrix.head_cons, Matrix.tail_cons,
             show (⟨0, 0⟩ : Zsqrtd 2).re = (0 : ℤ) from rfl,
             show (⟨0, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).re = (1 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl]
  omega

-- The orbit induction for proving orbit_ne uses these 12 valid transitions.
-- The forbidden 4 transitions don't appear in reduced words.
-- Full induction: on FreeGroup.toList, showing each letter step preserves the
-- appropriate inv_L invariant (where L is the new last letter), relying on
-- reducedness to exclude the 4 forbidden (self-cancelling) transitions.

-- Convention: generator `true` = φ (z-axis rotation), `false` = ψ (x-axis rotation).
-- A letter (g, true) is positive, (g, false) is inverse.
-- applyGen matches FreeGroup.lift (fun b => if b then φ_lin else ψ_lin).
private def applyGen : Bool × Bool → (Fin 3 → Zsqrtd 2) → Fin 3 → Zsqrtd 2
  | (true, true),  v => scaledActPhi v
  | (true, false), v => scaledActPhiInv v
  | (false, true), v => scaledActPsi v
  | (false, false), v => scaledActPsiInv v

-- evalWord uses foldr so that letter order matches LinearEquiv multiplication:
-- (f * g)(x) = f(g(x)), so list [l₁, l₂, ..., lₙ] maps to l₁ ∘ l₂ ∘ ... ∘ lₙ
-- (lₙ applied first, l₁ applied last).
private def evalWord : List (Bool × Bool) → (Fin 3 → Zsqrtd 2) → Fin 3 → Zsqrtd 2
  | [],      v => v
  | l :: ls, v => applyGen l (evalWord ls v)

-- Labeled invariant: which specific invariant holds after the last generator applied.
-- The label is the FIRST element of the word (= last applied generator in foldr).
private def labelState : Bool × Bool → (Fin 3 → Zsqrtd 2) → Prop
  | (true, true),  v => inv_phi v
  | (true, false), v => inv_phi_inv v
  | (false, true), v => inv_psi v
  | (false, false), v => inv_psi_inv v

-- Base cases: applying any single generator to e2Int yields the labeled invariant.
private lemma labelState_base (letter : Bool × Bool) :
    labelState letter (applyGen letter e2Int) := by
  fin_cases letter <;> simp only [labelState, applyGen]
  · exact base_phi
  · exact base_phi_inv
  · exact base_psi
  · exact base_psi_inv

-- Transition: if labelState prev holds, and prev/next don't cancel (reducedness),
-- then labelState next holds after applying next.
-- hnocancel is the IsReduced condition: same generator ↦ same sign.
private lemma labelState_step {prev next : Bool × Bool} {v : Fin 3 → Zsqrtd 2}
    (h : labelState prev v)
    (hnocancel : next.1 = prev.1 → next.2 = prev.2) :
    labelState next (applyGen next v) := by
  fin_cases prev <;> fin_cases next <;>
    simp only [labelState, applyGen] at h ⊢ <;>
    first
    | exact trans_phi_from_phi h        -- φ → φ
    | exact trans_phi_from_psi h        -- ψ → φ
    | exact trans_phi_from_psi_inv h    -- ψ⁻¹ → φ
    | exact trans_phi_inv_from_phi_inv h -- φ⁻¹ → φ⁻¹
    | exact trans_phi_inv_from_psi h    -- ψ → φ⁻¹
    | exact trans_phi_inv_from_psi_inv h -- ψ⁻¹ → φ⁻¹
    | exact trans_psi_from_phi h        -- φ → ψ
    | exact trans_psi_from_phi_inv h    -- φ⁻¹ → ψ
    | exact trans_psi_from_psi h        -- ψ → ψ
    | exact trans_psi_inv_from_phi h    -- φ → ψ⁻¹
    | exact trans_psi_inv_from_phi_inv h -- φ⁻¹ → ψ⁻¹
    | exact trans_psi_inv_from_psi_inv h -- ψ⁻¹ → ψ⁻¹
    | exact absurd (hnocancel rfl) (by decide) -- 4 forbidden cancelling transitions

-- Main automaton theorem: any non-empty reduced word applied to e2Int satisfies
-- labelState for its first letter (= last applied generator).
private lemma evalWord_labeledInv (l : List (Bool × Bool))
    (hne : l ≠ [])
    (hred : FreeGroup.IsReduced l) :
    labelState (l.head hne) (evalWord l e2Int) := by
  induction l with
  | nil => exact absurd rfl hne
  | cons letter rest ih =>
    cases rest with
    | nil =>
      simp only [evalWord, List.head_cons]
      exact labelState_base letter
    | cons head tail =>
      simp only [List.head_cons, evalWord]
      have hne_rest : (head :: tail) ≠ [] := List.cons_ne_nil _ _
      have hred_rest : FreeGroup.IsReduced (head :: tail) :=
        FreeGroup.isReduced_cons_cons.mp hred |>.2
      have hnocancel : letter.1 = head.1 → letter.2 = head.2 :=
        (FreeGroup.isReduced_cons_cons.mp hred).1
      have hih : labelState (List.head (head :: tail) hne_rest)
                   (evalWord (head :: tail) e2Int) :=
        ih (List.cons_ne_nil _ _) hred_rest
      simp only [List.head_cons] at hih
      exact labelState_step hih hnocancel

-- Helper: labelState for a concrete pair implies anyInv.
-- rcases on Bool × Bool with _|_ enumerates false first, so order is:
-- (false,false)=inv_psi_inv, (false,true)=inv_psi, (true,false)=inv_phi_inv, (true,true)=inv_phi
private lemma labelState_implies_anyInv (g : Bool × Bool) (v : Fin 3 → Zsqrtd 2)
    (h : labelState g v) : anyInv v := by
  unfold anyInv
  rcases g with ⟨⟨_|_⟩, ⟨_|_⟩⟩
  · exact Or.inr (Or.inr (Or.inr h))  -- (false, false): labelState ≡ inv_psi_inv
  · exact Or.inr (Or.inr (Or.inl h))  -- (false, true):  labelState ≡ inv_psi
  · exact Or.inr (Or.inl h)           -- (true, false):  labelState ≡ inv_phi_inv
  · exact Or.inl h                     -- (true, true):   labelState ≡ inv_phi

-- Corollary: anyInv holds for all non-empty reduced words.
private lemma evalWord_anyInv (l : List (Bool × Bool))
    (hne : l ≠ [])
    (hred : FreeGroup.IsReduced l) :
    anyInv (evalWord l e2Int) :=
  labelState_implies_anyInv _ _ (evalWord_labeledInv l hne hred)

-- Decode ℤ[√2] to ℝ: a + b√2 ↦ a + b*√2.
private noncomputable def zsqrtd2ToReal (z : Zsqrtd 2) : ℝ := z.re + z.im * Real.sqrt 2

-- Injectivity of zsqrtd2ToReal from irrationality of √2.
private lemma zsqrtd2ToReal_inj {v w : Zsqrtd 2}
    (h : zsqrtd2ToReal v = zsqrtd2ToReal w) : v = w := by
  simp only [zsqrtd2ToReal] at h
  have hre : (v.re : ℝ) = w.re ∧ (v.im : ℝ) = w.im := by
    rcases eq_or_ne (v.im : ℝ) w.im with him | him
    · have hveq : (v.im : ℝ) * Real.sqrt 2 = (w.im : ℝ) * Real.sqrt 2 := by rw [him]
      exact ⟨by linarith, him⟩
    · exfalso
      have hne : (v.im : ℝ) - w.im ≠ 0 := sub_ne_zero.mpr him
      have h_sqrt : Real.sqrt 2 = -((v.re : ℝ) - w.re) / ((v.im : ℝ) - w.im) := by
        field_simp [hne]; linarith
      have : (Real.sqrt 2 : ℝ) ∈ Set.range ((↑) : ℚ → ℝ) :=
        ⟨-((v.re : ℚ) - w.re) / ((v.im : ℚ) - w.im), by push_cast; linarith [h_sqrt.symm]⟩
      exact irrational_sqrt_two this
  exact Zsqrtd.ext (Int.cast_injective hre.1) (Int.cast_injective hre.2)

-- Helper: (3 : Zsqrtd 2)^n = ⟨3^n, 0⟩ (pure real power, no √2 component).
private lemma zsqrtd_pow3 (n : ℕ) : (3 : Zsqrtd 2)^n = ⟨(3 : ℤ)^n, 0⟩ := by
  induction n with
  | zero => rfl
  | succ k ihk =>
    rw [pow_succ, ihk, show (3 : Zsqrtd 2) = ⟨3, 0⟩ from rfl]
    apply Zsqrtd.ext
    · simp only [Zsqrtd.mul_re, pow_succ]; ring
    · simp only [Zsqrtd.mul_im]; ring

-- Scaling e2Int by 3^n does NOT satisfy anyInv (for n ≥ 1).
-- 3^n * e2Int = ![0, ⟨3^n, 0⟩, 0]; all anyInv conditions fail mod 3.
private lemma not_anyInv_pow3_e2Int (n : ℕ) (hn : 1 ≤ n) :
    ¬anyInv (fun i : Fin 3 => (⟨0, 0⟩ : Zsqrtd 2) + (3 : Zsqrtd 2)^n • e2Int i) := by
  have h3n : ((3 : ℤ)^n) % 3 = 0 := by
    obtain ⟨k, hk⟩ := dvd_pow_self (3 : ℤ) (by omega : n ≠ 0)
    omega
  have hpow3 : (3 : Zsqrtd 2)^n = ⟨(3 : ℤ)^n, 0⟩ := zsqrtd_pow3 n
  simp only [anyInv, inv_phi, inv_phi_inv, inv_psi, inv_psi_inv, not_or,
             e2Int, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
             Matrix.head_cons, Matrix.tail_cons,
             smul_eq_mul, hpow3, zero_add,
             Zsqrtd.mul_re, Zsqrtd.mul_im, Zsqrtd.add_re, Zsqrtd.add_im,
             show (⟨0, 0⟩ : Zsqrtd 2).re = (0 : ℤ) from rfl,
             show (⟨0, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl,
             show (⟨(3 : ℤ)^n, 0⟩ : Zsqrtd 2).re = (3 : ℤ)^n from rfl,
             show (⟨(3 : ℤ)^n, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).re = (1 : ℤ) from rfl,
             show (⟨1, 0⟩ : Zsqrtd 2).im = (0 : ℤ) from rfl]
  omega

/-- **Hausdorff's Theorem** (1914): The rotation group SO(3) contains a free
    subgroup of rank 2.

    Specifically, let φ = rotation by arccos(1/3) around the z-axis and
    ψ = rotation by arccos(1/3) around the x-axis. Then ⟨φ, ψ⟩ is a free
    group of rank 2.

    This is the key algebraic ingredient for Banach-Tarski. -/
-- PARTIAL PROOF: Rotation matrices defined and shown orthogonal.
-- LinearIsometryEquivs constructed. Remaining sorry: freeness (orbit argument in ℤ[√2]).
set_option maxHeartbeats 0 in
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
  have hφ_orth : Mφ.transpose * Mφ = 1 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hMφ : Mφ = !![(1 : ℝ) / 3, -(2 * Real.sqrt 2 / 3), 0;
                       2 * Real.sqrt 2 / 3, (1 : ℝ) / 3, 0; 0, 0, 1] := rfl
    rw [hMφ]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue] <;>
      ring_nf <;>
      nlinarith [hs2, hcs, Real.sqrt_nonneg 2]
  -- Mφ * Mφᵀ = 1
  have hφ_orth' : Mφ * Mφ.transpose = 1 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hMφ : Mφ = !![(1 : ℝ) / 3, -(2 * Real.sqrt 2 / 3), 0;
                       2 * Real.sqrt 2 / 3, (1 : ℝ) / 3, 0; 0, 0, 1] := rfl
    rw [hMφ]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue] <;>
      ring_nf <;>
      nlinarith [hs2, hcs, Real.sqrt_nonneg 2]
  -- Mψᵀ * Mψ = 1
  have hψ_orth : Mψ.transpose * Mψ = 1 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hMψ : Mψ = !![1, 0, 0; 0, (1 : ℝ) / 3, -(2 * Real.sqrt 2 / 3);
                       0, 2 * Real.sqrt 2 / 3, (1 : ℝ) / 3] := rfl
    rw [hMψ]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue] <;>
      ring_nf <;>
      nlinarith [hs2, hcs, Real.sqrt_nonneg 2]
  -- Mψ * Mψᵀ = 1
  have hψ_orth' : Mψ * Mψ.transpose = 1 := by
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hMψ : Mψ = !![1, 0, 0; 0, (1 : ℝ) / 3, -(2 * Real.sqrt 2 / 3);
                       0, 2 * Real.sqrt 2 / 3, (1 : ℝ) / 3] := rfl
    rw [hMψ]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const, Fin.isValue] <;>
      ring_nf <;>
      nlinarith [hs2, hcs, Real.sqrt_nonneg 2]
  -- Build LinearEquiv: toEuclideanLin M has inverse toEuclideanLin Mᵀ
  -- Uses: toEuclideanLin (Mᵀ * M) = id when Mᵀ * M = 1
  have hφ_comp_rl : (Matrix.toEuclideanLin Mφ).comp (Matrix.toEuclideanLin Mφ.transpose) = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.toEuclideanLin_apply,
               WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hφ_orth', Matrix.one_mulVec,
               WithLp.toLp_ofLp]
  have hφ_comp_lr : (Matrix.toEuclideanLin Mφ.transpose).comp (Matrix.toEuclideanLin Mφ) = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.toEuclideanLin_apply,
               WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hφ_orth, Matrix.one_mulVec,
               WithLp.toLp_ofLp]
  have hψ_comp_rl : (Matrix.toEuclideanLin Mψ).comp (Matrix.toEuclideanLin Mψ.transpose) = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.toEuclideanLin_apply,
               WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hψ_orth', Matrix.one_mulVec,
               WithLp.toLp_ofLp]
  have hψ_comp_lr : (Matrix.toEuclideanLin Mψ.transpose).comp (Matrix.toEuclideanLin Mψ) = LinearMap.id := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.toEuclideanLin_apply,
               WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hψ_orth, Matrix.one_mulVec,
               WithLp.toLp_ofLp]
  -- Build linear equivalences
  let φ_lin : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    LinearEquiv.ofLinear (Matrix.toEuclideanLin Mφ) (Matrix.toEuclideanLin Mφ.transpose)
      hφ_comp_rl hφ_comp_lr
  let ψ_lin : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    LinearEquiv.ofLinear (Matrix.toEuclideanLin Mψ) (Matrix.toEuclideanLin Mψ.transpose)
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
  have orbit_ne : ∀ (w : FreeGroup Bool), w ≠ 1 → (liftF w) e₂ ≠ e₂ := by
    intro w hw heq
    set l := w.toWord with hl_def
    have hne : l ≠ [] := FreeGroup.toWord_eq_nil_iff.not.mpr hw
    have hred : FreeGroup.IsReduced l := FreeGroup.isReduced_toWord
    have hmk : FreeGroup.mk l = w := FreeGroup.mk_toWord
    have hn : 1 ≤ l.length := List.length_pos.mpr hne
    have hinv : anyInv (evalWord l e2Int) := evalWord_anyInv l hne hred
    let matOf : Bool × Bool → Matrix (Fin 3) (Fin 3) ℝ
      | (true, true) => Mφ | (true, false) => Mφ.transpose
      | (false, true) => Mψ | (false, false) => Mψ.transpose
    have bridge_single : ∀ (g : Bool × Bool) (v : Fin 3 → Zsqrtd 2) (i : Fin 3),
        zsqrtd2ToReal (applyGen g v i) = 3 * (matOf g *ᵥ fun j => zsqrtd2ToReal (v j)) i := by
      rintro ⟨⟨_|_⟩, ⟨_|_⟩⟩ v i <;> fin_cases i <;>
        simp only [applyGen, matOf, Mφ, Mψ,
                   zsqrtd2ToReal, Zsqrtd.re_add, Zsqrtd.im_add,
                   Zsqrtd.re_mul, Zsqrtd.im_mul,
                   scaledActPhi_0, scaledActPhi_1, scaledActPhi_2,
                   scaledActPhiInv_0, scaledActPhiInv_1, scaledActPhiInv_2,
                   scaledActPsi_0, scaledActPsi_1, scaledActPsi_2,
                   scaledActPsiInv_0, scaledActPsiInv_1, scaledActPsiInv_2,
                   Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
                   Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                   Matrix.head_fin_const, Matrix.transpose_apply] <;>
        push_cast <;> ring_nf <;>
        nlinarith [Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 2]
    let evalReal : List (Bool × Bool) → (Fin 3 → ℝ) → Fin 3 → ℝ
      | [], v => v | g :: gs, v => matOf g *ᵥ evalReal gs v
    have bridge : ∀ (ls : List (Bool × Bool)) (i : Fin 3),
        zsqrtd2ToReal (evalWord ls e2Int i) =
        (3 : ℝ)^ls.length * (evalReal ls (fun j => e₂ j)) i := by
      intro ls
      induction ls with
      | nil =>
        intro i; simp only [evalWord, evalReal, List.length, pow_zero, one_mul]
        fin_cases i <;>
          simp [zsqrtd2ToReal, e2Int, e₂, EuclideanSpace.single_apply,
                Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                Matrix.head_fin_const]
      | cons g rest ih =>
        intro i
        simp only [evalWord, evalReal]
        rw [bridge_single g (evalWord rest e2Int) i]
        have hfun : (fun j => zsqrtd2ToReal (evalWord rest e2Int j)) =
            (3 : ℝ)^rest.length • (evalReal rest (fun j => e₂ j)) := by
          funext j; simp [ih j, Pi.smul_apply]
        rw [hfun, Matrix.mulVec_smul]
        simp only [Pi.smul_apply, smul_eq_mul, List.length_cons, pow_succ]
        ring
    have hφtol : φ.toLinearEquiv = φ_lin := LinearEquiv.isometryOfInner_toLinearEquiv _ _
    have hψtol : ψ.toLinearEquiv = ψ_lin := LinearEquiv.isometryOfInner_toLinearEquiv _ _
    have lift_eval : ∀ (ls : List (Bool × Bool)) (i : Fin 3),
        (FreeGroup.lift (fun b : Bool => if b then φ_lin else ψ_lin) (FreeGroup.mk ls)) e₂ i =
        (evalReal ls (fun j => e₂ j)) i := by
      intro ls
      induction ls with
      | nil => intro i; simp [FreeGroup.lift_one, evalReal]
      | cons g rest ih =>
        intro i
        have hmk_cons : FreeGroup.mk (g :: rest) = FreeGroup.mk [g] * FreeGroup.mk rest := by
          rw [← FreeGroup.mul_mk]; simp
        rw [hmk_cons, map_mul, LinearEquiv.mul_apply]
        have heq_rest : (FreeGroup.lift (fun b => if b then φ_lin else ψ_lin))
              (FreeGroup.mk rest) e₂ = evalReal rest (fun j => e₂ j) := funext ih
        rw [heq_rest, FreeGroup.lift_mk, List.map_singleton, List.prod_singleton]
        rcases g with ⟨⟨_|_⟩, ⟨_|_⟩⟩ <;>
          simp only [cond_true, cond_false, if_true, if_false, evalReal, matOf,
                     φ_lin, ψ_lin, LinearEquiv.ofLinear_apply, LinearEquiv.ofLinear_symm_apply,
                     LinearEquiv.coe_inv, Matrix.ofLp_toEuclideanLin_apply]
    have liftF_eq : ∀ i, (liftF w) e₂ i = (evalReal l (fun j => e₂ j)) i := fun i => by
      rw [← hmk, show liftF = FreeGroup.lift (fun b : Bool => if b then φ_lin else ψ_lin) from by
        congr 1; funext b; simp only [hφtol, hψtol]]
      exact lift_eval l i
    have heval_eq : evalReal l (fun j => e₂ j) = fun j => e₂ j := by
      funext i; rw [← liftF_eq i, heq]
    have hdecode : ∀ i, zsqrtd2ToReal (evalWord l e2Int i) = (3 : ℝ)^l.length * e₂ i := by
      intro i; rw [bridge l i, heval_eq]
    have hpow3 : ∀ m : ℕ, (3 : Zsqrtd 2)^m = ⟨(3 : ℤ)^m, 0⟩ := by
      intro m; induction m with
      | zero => simp
      | succ k ihk =>
        simp only [pow_succ, ihk, show (3 : Zsqrtd 2) = ⟨3, 0⟩ from rfl]
        simp [Zsqrtd.ext_iff, Zsqrtd.mul_re, Zsqrtd.mul_im, pow_succ]
    have enc : evalWord l e2Int = fun i => (0 : Zsqrtd 2) + (3 : Zsqrtd 2)^l.length • e2Int i := by
      funext i
      apply zsqrtd2ToReal_inj
      rw [hdecode i]
      simp only [zero_add, smul_eq_mul, hpow3, zsqrtd2ToReal, Zsqrtd.re_add, Zsqrtd.im_add,
                 Zsqrtd.re_mul, Zsqrtd.im_mul]
      fin_cases i <;>
        simp [e2Int, e₂, EuclideanSpace.single_apply,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
              Matrix.head_fin_const, Int.cast_zero, Int.cast_pow] <;>
        push_cast <;> ring
    exact not_anyInv_pow3_e2Int l.length hn (enc ▸ hinv)
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

section
open Cardinal

/-- **Corollary**: The pieces in the Banach-Tarski decomposition are
    non-Lebesgue-measurable.

    If the pieces were measurable, the countable additivity of Lebesgue measure
    would force: λ(B³) = ∑ᵢ λ(pieces i) = λ(B³) + λ(B³) = 2λ(B³),
    a contradiction since 0 < λ(B³) = (4/3)π < ∞. -/
-- Cardinality argument: if every subset of unitBall3 were measurable (Borel),
-- the measurable sets would number ≤ 𝔠 (since the Borel σ-algebra is countably
-- generated).  But unitBall3 ≅ [0,1] has cardinality 𝔠, so it has 2^𝔠 subsets,
-- giving 2^𝔠 ≤ 𝔠 — contradicting Cantor's theorem.
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
    have hgen : MeasurableSpace.generateFrom s =
        (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin 3))) :=
      MeasurableSpace.generateFrom_countableGeneratingSet
    have hrw : ∀ t : Set (EuclideanSpace ℝ (Fin 3)),
        @MeasurableSet _ (MeasurableSpace.generateFrom s) t ↔ MeasurableSet t :=
      fun t => by rw [hgen]
    rw [show {t : Set (EuclideanSpace ℝ (Fin 3)) | MeasurableSet t} =
            {t | @MeasurableSet _ (MeasurableSpace.generateFrom s) t} from
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
    rw [← Cardinal.mk_Icc_real (show (0 : ℝ) < 1 by norm_num)]
    apply Cardinal.mk_le_of_injective (f := fun ⟨t, ht⟩ =>
        ⟨EuclideanSpace.single (0 : Fin 3) t, by
           simp only [unitBall3, Metric.mem_closedBall, dist_zero_right,
                      EuclideanSpace.norm_single, Real.norm_eq_abs,
                      abs_of_nonneg ht.1]
           exact ht.2⟩)
    intro ⟨t₁, _⟩ ⟨t₂, _⟩ h
    simp only [Subtype.mk.injEq] at h
    have h0 := congr_arg (· 0) h
    simp only [EuclideanSpace.single_apply, eq_self_iff_true, if_true] at h0
    exact Subtype.ext h0
  -- Step 4: By Cantor, #{A | A ⊆ unitBall3} = 2^#unitBall3 > 𝔠.
  have hball_gt : 𝔠 < #{A : Set (EuclideanSpace ℝ (Fin 3)) | A ⊆ unitBall3} := by
    -- 𝒫 s is definitionally {t | t ⊆ s}, so these are equal by rfl.
    rw [show {A : Set (EuclideanSpace ℝ (Fin 3)) | A ⊆ unitBall3} = 𝒫 unitBall3 from rfl,
        Cardinal.mk_powerset]
    exact hball_ge.trans_lt (Cardinal.cantor _)
  -- Contradiction: 2^𝔠 ≤ 𝔠 violates Cantor.
  exact absurd hball_sub_le hball_gt.not_le

end -- open Cardinal

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
  -- Proof via Cesàro density along a non-principal ultrafilter on ℕ.
  -- The measure μ A = limUnder ↑U (fun N => |{k ∈ [-N,N] | ofAdd k ∈ A}| / (2N+1))
  -- is left-invariant because shifting the window by n changes density by ≤ |n|/(2N+1) → 0.
  -- API note: requires Filter.limUnder (not Ultrafilter.lim) and classical decidability.
  sorry

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
