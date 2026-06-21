/-
  Schönhage's Recursive HGCD — the Unimodular Group Structure behind GCD Preservation
  ===================================================================================

  Problem: binary-gcd-oq-03-oq-02-incomplete-01
  "Schönhage's Recursive HGCD: GCD Preservation and Matrix Invariants"

  The parent entry `binary-gcd-oq-03-oq-02` (BinaryGcdOQ03OQ02.lean) formalizes
  Schönhage's recursive half-GCD and proves that the accumulated cofactor matrix
  has determinant ±1 and preserves the GCD when applied to a pair (a, b). Its
  GCD-preservation theorem is *one-directional* (for ℕ pairs), and several of its
  credited results lean on `native_decide` (so it carries `Lean.ofReduceBool`).

  This companion supplies the missing STRUCTURAL story, fully axiom-free and with
  NO `native_decide`:

    * The 2×2 integer cofactor matrices with det = ±1 form a GROUP. We give the
      explicit inverse (adjugate scaled by the determinant) and prove
      `M * M⁻¹ = M⁻¹ * M = I` for unimodular M, plus closure of det = ±1 under
      product and inverse.
    * The induced action `(a,b) ↦ M·(a,b)` on ℤ² is a BIJECTION when det = ±1;
      its inverse is the action of `M⁻¹`. GCD preservation is the *shadow* of this
      bijection.
    * Consequently the generated ideal `(a, b) = (u, v)` is invariant, and hence
      `Int.gcd` is preserved in BOTH directions — the converse half that the
      parent never states, here for ℤ pairs.

  This isolates the algebraic invariant of Schönhage's HGCD (a unimodular linear
  action) from the algorithmic recursion, and explains *why* size-reduction is
  the only genuinely hard part: gcd-preservation is forced by group theory.

  Self-contained: a fresh `HGCDMatrix` structure is defined here, so the file has
  no dependency on the parent's `native_decide` results. 0 sorries, 0 axioms.
-/

import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

namespace SchonhageHGCD

/-- A 2×2 integer cofactor matrix `[[α, β], [γ, δ]]`, as accumulated by
    Schönhage's recursive half-GCD. Acting on a column `(a, b)` it produces
    `(α·a + β·b, γ·a + δ·b)`. -/
structure HGCDMatrix where
  α : ℤ
  β : ℤ
  γ : ℤ
  δ : ℤ
  deriving DecidableEq

namespace HGCDMatrix

/-- The identity cofactor matrix. -/
def id : HGCDMatrix := ⟨1, 0, 0, 1⟩

/-- Determinant `α·δ − β·γ`. -/
def det (M : HGCDMatrix) : ℤ := M.α * M.δ - M.β * M.γ

/-- Matrix product (row-by-column). -/
def mul (M N : HGCDMatrix) : HGCDMatrix :=
  ⟨M.α * N.α + M.β * N.γ,
   M.α * N.β + M.β * N.δ,
   M.γ * N.α + M.δ * N.γ,
   M.γ * N.β + M.δ * N.δ⟩

/-- The action on a column vector `(a, b)`. -/
def apply (M : HGCDMatrix) (a b : ℤ) : ℤ × ℤ :=
  (M.α * a + M.β * b, M.γ * a + M.δ * b)

/-- The adjugate `[[δ, −β], [−γ, α]]`. -/
def adj (M : HGCDMatrix) : HGCDMatrix := ⟨M.δ, -M.β, -M.γ, M.α⟩

/-- The inverse of a unimodular matrix: adjugate scaled by the determinant.
    For `det = ±1` this is a genuine two-sided inverse (since `det² = 1`). -/
def inv (M : HGCDMatrix) : HGCDMatrix :=
  ⟨M.det * M.δ, M.det * (-M.β), M.det * (-M.γ), M.det * M.α⟩

-- ═══════════════════════════════════════════════════════════════
-- PART I: RING-LEVEL IDENTITIES (det, product, action)
-- ═══════════════════════════════════════════════════════════════

@[simp] theorem det_id : id.det = 1 := by simp [id, det]

/-- Determinant is multiplicative — the engine of the det = ±1 invariant. -/
theorem det_mul (M N : HGCDMatrix) : (M.mul N).det = M.det * N.det := by
  simp only [mul, det]; ring

/-- The adjugate has the same determinant as `M`. -/
@[simp] theorem det_adj (M : HGCDMatrix) : M.adj.det = M.det := by
  simp only [adj, det]; ring

/-- The action of a product is the composition of the actions. -/
theorem apply_mul (M N : HGCDMatrix) (a b : ℤ) :
    (M.mul N).apply a b = M.apply (N.apply a b).1 (N.apply a b).2 := by
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩ <;> · simp only [mul, apply]; ring

@[simp] theorem apply_id (a b : ℤ) : id.apply a b = (a, b) := by
  simp [id, apply]

-- ═══════════════════════════════════════════════════════════════
-- PART II: THE INVERSE AND THE UNIMODULAR GROUP
-- ═══════════════════════════════════════════════════════════════

/-- `M · adj(M)` is the scalar matrix `det·I`. -/
theorem mul_adj (M : HGCDMatrix) :
    M.mul M.adj = ⟨M.det, 0, 0, M.det⟩ := by
  simp only [mul, adj, det, HGCDMatrix.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- `adj(M) · M` is the scalar matrix `det·I`. -/
theorem adj_mul (M : HGCDMatrix) :
    M.adj.mul M = ⟨M.det, 0, 0, M.det⟩ := by
  simp only [mul, adj, det, HGCDMatrix.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- For a unimodular matrix `det² = 1`. -/
theorem det_sq_eq_one {M : HGCDMatrix} (h : M.det = 1 ∨ M.det = -1) :
    M.det * M.det = 1 := by
  rcases h with h | h <;> rw [h] <;> ring

/-- `M · M⁻¹` is the scalar matrix `det²·I` (a pure algebraic identity). -/
theorem mul_inv_scalar (M : HGCDMatrix) :
    M.mul M.inv = ⟨M.det * M.det, 0, 0, M.det * M.det⟩ := by
  simp only [mul, inv, det, HGCDMatrix.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- `M⁻¹ · M` is the scalar matrix `det²·I` (a pure algebraic identity). -/
theorem inv_mul_scalar (M : HGCDMatrix) :
    M.inv.mul M = ⟨M.det * M.det, 0, 0, M.det * M.det⟩ := by
  simp only [mul, inv, det, HGCDMatrix.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- Right inverse: `M · M⁻¹ = I` when `det = ±1`. -/
theorem mul_inv (M : HGCDMatrix) (h : M.det = 1 ∨ M.det = -1) :
    M.mul M.inv = id := by
  rw [mul_inv_scalar, det_sq_eq_one h]; rfl

/-- Left inverse: `M⁻¹ · M = I` when `det = ±1`. -/
theorem inv_mul (M : HGCDMatrix) (h : M.det = 1 ∨ M.det = -1) :
    M.inv.mul M = id := by
  rw [inv_mul_scalar, det_sq_eq_one h]; rfl

/-- The inverse of a unimodular matrix is again unimodular (same determinant),
    so the det = ±1 matrices are closed under inverse. -/
theorem det_inv (M : HGCDMatrix) (h : M.det = 1 ∨ M.det = -1) :
    M.inv.det = M.det := by
  have h1 : M.det * M.inv.det = 1 := by rw [← det_mul, mul_inv M h, det_id]
  rcases h with h | h <;> rw [h] at h1 ⊢ <;> linarith

/-- The product of two unimodular matrices is unimodular: closure of the group
    under multiplication (via multiplicativity of the determinant). -/
theorem det_mul_unimodular {M N : HGCDMatrix}
    (hM : M.det = 1 ∨ M.det = -1) (hN : N.det = 1 ∨ N.det = -1) :
    (M.mul N).det = 1 ∨ (M.mul N).det = -1 := by
  rw [det_mul]
  rcases hM with hM | hM <;> rcases hN with hN | hN <;> rw [hM, hN] <;> norm_num

-- ═══════════════════════════════════════════════════════════════
-- PART III: THE ACTION ON ℤ² IS A BIJECTION
-- ═══════════════════════════════════════════════════════════════

/-- The action of `M` as a function `ℤ² → ℤ²`. -/
def act (M : HGCDMatrix) : ℤ × ℤ → ℤ × ℤ := fun p => M.apply p.1 p.2

/-- Applying `M⁻¹` undoes applying `M`: a left inverse on pairs. -/
theorem act_inv_act (M : HGCDMatrix) (h : M.det = 1 ∨ M.det = -1) (p : ℤ × ℤ) :
    M.inv.act (M.act p) = p := by
  obtain ⟨a, b⟩ := p
  show M.inv.apply (M.apply a b).1 (M.apply a b).2 = (a, b)
  rw [← apply_mul M.inv M a b, inv_mul M h, apply_id]

/-- Applying `M` undoes applying `M⁻¹`: a right inverse on pairs. -/
theorem act_act_inv (M : HGCDMatrix) (h : M.det = 1 ∨ M.det = -1) (p : ℤ × ℤ) :
    M.act (M.inv.act p) = p := by
  obtain ⟨a, b⟩ := p
  show M.apply (M.inv.apply a b).1 (M.inv.apply a b).2 = (a, b)
  rw [← apply_mul M M.inv a b, mul_inv M h, apply_id]

/-- **The HGCD action is a bijection of ℤ².**

    This is the structural heart of GCD preservation: a unimodular cofactor
    matrix permutes the integer lattice, with `M⁻¹` as its inverse permutation. -/
theorem act_bijective (M : HGCDMatrix) (h : M.det = 1 ∨ M.det = -1) :
    Function.Bijective M.act :=
  Function.bijective_iff_has_inverse.mpr
    ⟨M.inv.act, act_inv_act M h, act_act_inv M h⟩

-- ═══════════════════════════════════════════════════════════════
-- PART IV: GCD / IDEAL INVARIANCE (BOTH DIRECTIONS)
-- ═══════════════════════════════════════════════════════════════

/-- Forward divisor transfer: any common divisor of `(a, b)` divides both
    entries of `M.apply a b` (these are integer linear combinations). -/
theorem dvd_apply_of_dvd (M : HGCDMatrix) {a b d : ℤ}
    (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ (M.apply a b).1 ∧ d ∣ (M.apply a b).2 := by
  simp only [apply]
  exact ⟨dvd_add (hda.mul_left M.α) (hdb.mul_left M.β),
         dvd_add (hda.mul_left M.γ) (hdb.mul_left M.δ)⟩

/-- **Common divisors are exactly preserved** by a unimodular action: `d` divides
    both inputs iff it divides both outputs. The backward direction comes *for
    free* from the inverse matrix — no separate Cramer computation is needed. -/
theorem dvd_apply_iff (M : HGCDMatrix) (h : M.det = 1 ∨ M.det = -1) {a b d : ℤ} :
    (d ∣ a ∧ d ∣ b) ↔ (d ∣ (M.apply a b).1 ∧ d ∣ (M.apply a b).2) := by
  constructor
  · rintro ⟨hda, hdb⟩
    exact dvd_apply_of_dvd M hda hdb
  · rintro ⟨hu, hv⟩
    -- recover (a, b) = M⁻¹ · (M · (a,b)) and push divisibility through M⁻¹
    have hrec : M.inv.apply (M.apply a b).1 (M.apply a b).2 = (a, b) := by
      have := act_inv_act M h (a, b)
      simpa only [act] using this
    have hres := dvd_apply_of_dvd M.inv hu hv
    rw [hrec] at hres
    exact hres

/-- **GCD preservation, both directions, for ℤ pairs.**

    `Int.gcd (M.apply a b) = Int.gcd a b` for any unimodular `M`. Unlike the
    parent's one-directional ℕ statement, this is an equality of integer gcds,
    proved symmetrically from the common-divisor equivalence. -/
theorem gcd_apply_eq (M : HGCDMatrix) (h : M.det = 1 ∨ M.det = -1) (a b : ℤ) :
    Int.gcd (M.apply a b).1 (M.apply a b).2 = Int.gcd a b := by
  set u := (M.apply a b).1
  set v := (M.apply a b).2
  apply Nat.dvd_antisymm
  · -- Int.gcd u v ∣ Int.gcd a b : it divides u and v, hence (via M⁻¹) a and b
    have hu : (↑(Int.gcd u v) : ℤ) ∣ u := Int.gcd_dvd_left u v
    have hv : (↑(Int.gcd u v) : ℤ) ∣ v := Int.gcd_dvd_right u v
    have hd := (dvd_apply_iff M h (d := (↑(Int.gcd u v) : ℤ))).mpr ⟨hu, hv⟩
    exact Int.dvd_gcd hd.1 hd.2
  · -- Int.gcd a b ∣ Int.gcd u v : it divides a and b, hence u and v
    have hda : (↑(Int.gcd a b) : ℤ) ∣ a := Int.gcd_dvd_left a b
    have hdb : (↑(Int.gcd a b) : ℤ) ∣ b := Int.gcd_dvd_right a b
    have hd := (dvd_apply_iff M h (d := (↑(Int.gcd a b) : ℤ))).mp ⟨hda, hdb⟩
    exact Int.dvd_gcd hd.1 hd.2

/-- **The generated ideal is invariant**: `(u, v) = (a, b)` as ideals of ℤ, where
    `(u, v) = M.apply a b` for unimodular `M`. This is the ideal-theoretic form of
    GCD preservation; the reverse inclusion is supplied by the inverse matrix. -/
theorem span_apply_eq (M : HGCDMatrix) (h : M.det = 1 ∨ M.det = -1) (a b : ℤ) :
    Ideal.span {(M.apply a b).1, (M.apply a b).2} = Ideal.span ({a, b} : Set ℤ) := by
  set u := (M.apply a b).1 with hu_def
  set v := (M.apply a b).2 with hv_def
  apply le_antisymm
  · -- u, v ∈ (a, b): both are linear combinations of a and b
    rw [Ideal.span_le]
    have ha : a ∈ Ideal.span ({a, b} : Set ℤ) := Ideal.subset_span (by simp)
    have hb : b ∈ Ideal.span ({a, b} : Set ℤ) := Ideal.subset_span (by simp)
    intro x hx
    rw [hu_def, hv_def] at hx
    simp only [apply, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx <;> rw [hx, SetLike.mem_coe] <;>
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
  · -- a, b ∈ (u, v): recover them via the inverse matrix
    rw [Ideal.span_le]
    have hu : u ∈ Ideal.span ({u, v} : Set ℤ) := Ideal.subset_span (by simp)
    have hv : v ∈ Ideal.span ({u, v} : Set ℤ) := Ideal.subset_span (by simp)
    have hrec : M.inv.apply u v = (a, b) := by
      have := act_inv_act M h (a, b)
      simpa only [act, hu_def, hv_def] using this
    have hav : a ∈ Ideal.span ({u, v} : Set ℤ) := by
      have hx : (M.inv.apply u v).1 ∈ Ideal.span ({u, v} : Set ℤ) := by
        simp only [apply]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hu) (Ideal.mul_mem_left _ _ hv)
      rwa [hrec] at hx
    have hbv : b ∈ Ideal.span ({u, v} : Set ℤ) := by
      have hx : (M.inv.apply u v).2 ∈ Ideal.span ({u, v} : Set ℤ) := by
        simp only [apply]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hu) (Ideal.mul_mem_left _ _ hv)
      rwa [hrec] at hx
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx <;> rw [hx, SetLike.mem_coe]
    · exact hav
    · exact hbv

end HGCDMatrix

end SchonhageHGCD

