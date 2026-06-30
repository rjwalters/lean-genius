import Mathlib
import Proofs.CauchyInterlacingWeyl

/-
# The dual (upper) Weyl eigenvalue inequality, via negation

This file completes the two-sided Weyl perturbation bracket begun in
`CauchyInterlacingWeyl.lean`. There the **subadditive** Weyl inequality

  `weyl_add_le` :  `i + j ≤ k  →  ρ k ≤ μ i + ν j`

is derived from the Courant–Fischer keystone, where `μ`, `ν`, `ρ` are the
descending (antitone) eigenvalue enumerations of `T`, `U`, `T + U`.  Its mirror
image — the **superadditive** (dual upper) Weyl inequality

  `weyl_add_ge` :  `k + (n-1) ≤ i + j  →  μ i + ν j ≤ ρ k`

is *not* a new variational fact: it is the subadditive inequality read off the
negated operators `-T`, `-U`.  Together the two bound `ρ k` from both sides and
recover the full classical statement
`λ_{i+1}(A) + λ_{j+1}(B) ≤ λ_{i+j+1-n+1}(A+B) ≤ λ_{i'+1}(A) + λ_{j'+1}(B)`.

## The negation trick

For a symmetric operator presented by an orthonormal eigenbasis `b` and an
*antitone* enumeration `μ` (`T (b i) = μ i • b i`), the operator `-T` is
presented by:

* the **reversed** basis `b ∘ Fin.rev` (i.e. `b.reindex Fin.revPerm`), still
  orthonormal, and
* the enumeration `t ↦ -μ (Fin.rev t)`, which is again antitone (the negative of
  a monotone reindexing of an antitone function).

Feeding `-T`, `-U`, `-(T+U)` into `weyl_add_le` at the reversed indices
`Fin.rev i`, `Fin.rev j`, `Fin.rev k` turns the hypothesis `i' + j' ≤ k'` into
`(n-1-i)+(n-1-j) ≤ n-1-k`, i.e. `k + (n-1) ≤ i + j`, and the conclusion
`ρ' k' ≤ μ' i' + ν' j'` into `-ρ k ≤ -μ i - ν j`, i.e. `μ i + ν j ≤ ρ k`.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped InnerProductSpace

namespace CauchyInterlacing.Weyl

/-- The negated operator `-T`, in the reversed eigenbasis `b.reindex Fin.revPerm`,
is presented by the enumeration `t ↦ -μ (Fin.rev t)`.  This is the single
algebraic fact behind the negation trick: `(-T) (b (rev t)) = -(μ (rev t) • b
(rev t)) = (-μ (rev t)) • b (rev t)`. -/
theorem neg_reindex_eigen
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {n : ℕ} (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hbT : ∀ i, T (b i) = (μ i : 𝕜) • b i) (t : Fin n) :
    (-T) ((b.reindex Fin.revPerm) t)
      = ((-μ (Fin.rev t) : ℝ) : 𝕜) • (b.reindex Fin.revPerm) t := by
  have hbt : (b.reindex Fin.revPerm) t = b (Fin.rev t) := by
    simp [OrthonormalBasis.reindex_apply]
  rw [hbt, LinearMap.neg_apply, hbT (Fin.rev t)]
  push_cast
  rw [neg_smul]

/-- A negated, reversed antitone enumeration is again antitone:
`t ↦ -μ (Fin.rev t)` is antitone whenever `μ` is. -/
theorem antitone_neg_rev {n : ℕ} {μ : Fin n → ℝ} (hμ : Antitone μ) :
    Antitone (fun t => -μ (Fin.rev t)) := by
  intro a c hac
  have hrev : Fin.rev c ≤ Fin.rev a := by
    rw [Fin.le_def, Fin.val_rev, Fin.val_rev]
    have := Fin.le_def.1 hac
    omega
  simpa using neg_le_neg (hμ hrev)

/-- **Dual (upper) Weyl inequality.** Let `T`, `U`, and `T + U` be presented by
descending (antitone) eigenvalue enumerations `μ` (basis `b`), `ν` (basis `c`),
`ρ` (basis `d`).  For any indices with `(k : ℕ) + (n - 1) ≤ (i : ℕ) + (j : ℕ)`,

  `μ i + ν j ≤ ρ k`.

This is the superadditive companion of `weyl_add_le`.  In classical 1-based
descending notation it reads `λ_{i+1}(A) + λ_{j+1}(B) ≤ λ_{i+j+1-(n-1)}(A+B)`.
Proof: apply `weyl_add_le` to `-T`, `-U`, `-(T+U)` in the reversed eigenbases
and at the reversed indices; the negation flips both the index hypothesis and
the inequality. -/
theorem weyl_add_ge
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T U : E →ₗ[𝕜] E)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hbT : ∀ i, T (b i) = (μ i : 𝕜) • b i) (hμ : Antitone μ)
    (c : OrthonormalBasis (Fin n) 𝕜 E) (ν : Fin n → ℝ)
    (hcU : ∀ i, U (c i) = (ν i : 𝕜) • c i) (hν : Antitone ν)
    (d : OrthonormalBasis (Fin n) 𝕜 E) (ρ : Fin n → ℝ)
    (hdW : ∀ i, (T + U) (d i) = (ρ i : 𝕜) • d i) (hρ : Antitone ρ)
    (i j k : Fin n) (hk : (k : ℕ) + (n - 1) ≤ (i : ℕ) + (j : ℕ)) :
    μ i + ν j ≤ ρ k := by
  -- The negated, reversed presentations of T, U, and T + U.
  have hb'T := neg_reindex_eigen T b μ hbT
  have hc'U := neg_reindex_eigen U c ν hcU
  -- For the sum we use `(-T) + (-U) = -(T + U)`, so its negated presentation is
  -- the negated presentation of `T + U`.
  have hd'W : ∀ t, ((-T) + (-U)) ((d.reindex Fin.revPerm) t)
      = ((-ρ (Fin.rev t) : ℝ) : 𝕜) • (d.reindex Fin.revPerm) t := by
    intro t
    have hsum : ((-T) + (-U)) = -(T + U) := by
      ext x; simp [LinearMap.add_apply, LinearMap.neg_apply]
    rw [hsum]
    exact neg_reindex_eigen (T + U) d ρ hdW t
  -- Antitone enumerations for the negated operators.
  have hμ' := antitone_neg_rev hμ
  have hν' := antitone_neg_rev hν
  have hρ' := antitone_neg_rev hρ
  -- The reversed-index hypothesis required by `weyl_add_le`.
  have hidx : (Fin.rev i : ℕ) + (Fin.rev j : ℕ) ≤ (Fin.rev k : ℕ) := by
    have hi := i.isLt; have hj := j.isLt; have hkk := k.isLt
    simp only [Fin.val_rev]
    omega
  -- Apply the subadditive inequality to the negated data at reversed indices.
  have key := weyl_add_le (-T) (-U)
      (b.reindex Fin.revPerm) (fun t => -μ (Fin.rev t)) hb'T hμ'
      (c.reindex Fin.revPerm) (fun t => -ν (Fin.rev t)) hc'U hν'
      (d.reindex Fin.revPerm) (fun t => -ρ (Fin.rev t)) hd'W hρ'
      (Fin.rev i) (Fin.rev j) (Fin.rev k) hidx
  -- `weyl_add_le` gives `-ρ k ≤ -μ i - ν j`; rearrange.
  simp only [Fin.rev_rev] at key
  linarith

end CauchyInterlacing.Weyl
