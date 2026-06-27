/-
  Fourth-Moment British Flag Defect for a General Parallelepiped
  Open-question follow-up: british-flag-theorem-oq-01-oq-02-oq-01 (higher moments)

  The parent file (`BritishFlagParallelepipedOQ010201`) proves that the alternating
  *squared*-distance defect over the `2ⁿ` vertices of a parallelepiped,

      defect₂ = ∑_{t ⊆ {0,…,n-1}} (-1)^{|t|} · ‖X − vertex t‖²,

  vanishes for `n ≥ 3`.  The mechanism: `‖X − vertex t‖²` is a degree-`2` polynomial
  in the membership indicators `[i ∈ t]`, and the operator `g ↦ ∑_t (-1)^{|t|} g t`
  is the `n`-th iterated finite difference, which annihilates every monomial that
  omits at least one coordinate.  For `n ≥ 3` every degree-`2` monomial omits a
  coordinate, so the defect is identically zero.

  ## What this file adds

  The next moment.  We study the **fourth-moment** defect

      defect₄ = ∑_{t ⊆ {0,…,n-1}} (-1)^{|t|} · ‖X − vertex t‖⁴.

  Now `‖X − vertex t‖⁴ = (‖X − vertex t‖²)²` is a degree-`4` polynomial in the
  indicators, so the same finite-difference mechanism forces `defect₄ = 0` as soon as
  every degree-`4` monomial omits a coordinate, i.e. for `n ≥ 5`.

  ### Key generalization: the finite-difference principle as one clean lemma

  We isolate the mechanism as a single statement, `monomial_term_zero`:

      for any proper subset `S ⊊ univ`, the signed powerset sum of the indicator
      `[S ⊆ t]` vanishes.

  Taking `S = ∅, {i}, {i,j}` recovers the constant / linear / quadratic pieces of the
  parent.  Taking `|S| = 3, 4` gives the new `cubic_term_zero` (needs `n ≥ 4`) and
  `quartic_term_zero` (needs `n ≥ 5`) pieces, which — together with the parent's three
  lower pieces — annihilate every term in the expansion of `(‖w‖² − 2L + Q)²`.

  ## Main results

  * `monomial_term_zero` — the finite-difference principle: `∑_t (-1)^{|t|} [S ⊆ t] = 0`
    whenever `S ≠ univ`.  Short proof from the parent's structural heart
    `alt_sum_eq_zero_of_indep`.
  * `cubic_term_zero` / `quartic_term_zero` — the degree-`3` / degree-`4` term
    vanishing (`n ≥ 4` / `n ≥ 5`).
  * `fourth_moment_defect_eq_zero` — **headline**: for `n ≥ 5`, `defect₄ = 0` for every
    parallelepiped, observer `X`, base `c`, and arbitrary (possibly skew) edges `u`.

  Everything is `sorry`-free and axiom-free; the parent's lemmas are reused by import.

  The first nonzero case `n = 4` carries an explicit top-degree "pairing" defect
      8 · (⟪u₀,u₁⟫⟪u₂,u₃⟫ + ⟪u₀,u₂⟫⟪u₁,u₃⟫ + ⟪u₀,u₃⟫⟪u₁,u₂⟫),
  which is left as a documented next step.
-/

import Mathlib
import Proofs.BritishFlagParallelepipedOQ010201

open Finset
open scoped RealInnerProductSpace

namespace BritishFlagFourthMomentOQ010201

open BritishFlagParallelepipedOQ010201

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Restriction helper: a full-universe sum with an indicator is a sum over the set -/

/-- `∑_{i} [i ∈ t] · f i = ∑_{i ∈ t} f i`.  Self-contained so the file does not depend
    on the exact spelling of any Mathlib restriction lemma. -/
private theorem sum_ite_mem_eq' (t : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ i, if i ∈ t then f i else 0) = ∑ i ∈ t, f i := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x; simp

/-! ### The finite-difference principle as a monomial lemma -/

/-- **Finite-difference / monomial vanishing.**  For any subset `S ≠ univ`, the signed
    powerset sum of the indicator `[S ⊆ t]` (scaled by a constant `a`) vanishes.

    This is the heart of the British-flag mechanism, abstracted away from the specific
    moment: `S = ∅, {i}, {i,j}` recover the constant, linear, and quadratic pieces of
    the parent.  Proof: pick a coordinate `k ∉ S`; the indicator `[S ⊆ ·]` does not
    depend on `k`, so the parent's `alt_sum_eq_zero_of_indep` applies. -/
theorem monomial_term_zero (S : Finset (Fin n)) (hS : S ≠ univ) (a : ℝ) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset,
        (-1 : ℝ) ^ t.card * (if S ⊆ t then a else 0) = 0 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, k ∉ S := by
    by_contra h
    push_neg at h
    apply hS
    ext x
    simpa using h x
  refine alt_sum_eq_zero_of_indep k (fun t => if S ⊆ t then a else 0) ?_
  intro s hks
  have hiff : S ⊆ insert k s ↔ S ⊆ s := by
    constructor
    · intro h x hx
      rcases mem_insert.mp (h hx) with rfl | hxs
      · exact absurd hx hk
      · exact hxs
    · exact fun h => h.trans (subset_insert k s)
  simp only [hiff]

/-! ### Cubic and quartic term vanishing -/

/-- Bridge: membership of three points in `t` is `{i,j,l} ⊆ t`. -/
private theorem mem3_iff_subset (i j l : Fin n) (t : Finset (Fin n)) :
    (i ∈ t ∧ j ∈ t ∧ l ∈ t) ↔ ({i, j, l} : Finset (Fin n)) ⊆ t := by
  simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]

/-- Bridge: membership of four points in `t` is `{i,j,k,l} ⊆ t`. -/
private theorem mem4_iff_subset (i j k l : Fin n) (t : Finset (Fin n)) :
    (i ∈ t ∧ j ∈ t ∧ k ∈ t ∧ l ∈ t) ↔ ({i, j, k, l} : Finset (Fin n)) ⊆ t := by
  simp [Finset.insert_subset_iff, Finset.singleton_subset_iff]

/-- **The cubic piece vanishes for `n ≥ 4`.**  `∑_t (-1)^{|t|} ∑_{i,j,l ∈ t} c i j l = 0`. -/
theorem cubic_term_zero (hn : 4 ≤ n) (c : Fin n → Fin n → Fin n → ℝ) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset,
        (-1 : ℝ) ^ t.card * (∑ i ∈ t, ∑ j ∈ t, ∑ l ∈ t, c i j l) = 0 := by
  classical
  -- rewrite the triple `∑_{·∈t}` as a triple `∑_·` with a single conjunction indicator
  have hrw : ∀ t : Finset (Fin n),
      (∑ i ∈ t, ∑ j ∈ t, ∑ l ∈ t, c i j l)
        = ∑ i, ∑ j, ∑ l, if i ∈ t ∧ j ∈ t ∧ l ∈ t then c i j l else 0 := by
    intro t
    have inner2 : ∀ i j, (∑ l ∈ t, c i j l) = ∑ l, if l ∈ t then c i j l else 0 :=
      fun i j => (sum_ite_mem_eq' t (c i j)).symm
    simp_rw [inner2]
    have inner1 : ∀ i, (∑ j ∈ t, ∑ l, if l ∈ t then c i j l else 0)
        = ∑ j, if j ∈ t then (∑ l, if l ∈ t then c i j l else 0) else 0 :=
      fun i => (sum_ite_mem_eq' t _).symm
    simp_rw [inner1]
    rw [← sum_ite_mem_eq' t
      (fun i => ∑ j, if j ∈ t then (∑ l, if l ∈ t then c i j l else 0) else 0)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ t
    · rw [if_pos hi]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ t
      · rw [if_pos hj]
        apply Finset.sum_congr rfl
        intro l _
        by_cases hl : l ∈ t
        · rw [if_pos hl, if_pos ⟨hi, hj, hl⟩]
        · rw [if_neg hl, if_neg (by tauto)]
      · rw [if_neg hj, eq_comm]
        apply Finset.sum_eq_zero
        intro l _
        rw [if_neg (by tauto)]
    · rw [if_neg hi, eq_comm]
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro l _
      rw [if_neg (by tauto)]
  simp_rw [hrw, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l _
  -- now a pure monomial term: `{i,j,l} ⊆ t`, and `{i,j,l} ≠ univ` since `n ≥ 4`
  have hne : ({i, j, l} : Finset (Fin n)) ≠ univ := by
    intro heq
    have h3 : ({i, j, l} : Finset (Fin n)).card ≤ 3 := by
      have a := Finset.card_insert_le i ({j, l} : Finset (Fin n))
      have b := Finset.card_insert_le j ({l} : Finset (Fin n))
      simp only [Finset.card_singleton] at b
      omega
    have hc : ({i, j, l} : Finset (Fin n)).card = n := by
      rw [heq, Finset.card_univ, Fintype.card_fin]
    omega
  simp_rw [mem3_iff_subset i j l]
  exact monomial_term_zero _ hne _

/-- **The quartic piece vanishes for `n ≥ 5`.**  `∑_t (-1)^{|t|} ∑_{i,j,k,l ∈ t} d i j k l = 0`. -/
theorem quartic_term_zero (hn : 5 ≤ n) (d : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset,
        (-1 : ℝ) ^ t.card * (∑ i ∈ t, ∑ j ∈ t, ∑ k ∈ t, ∑ l ∈ t, d i j k l) = 0 := by
  classical
  have hrw : ∀ t : Finset (Fin n),
      (∑ i ∈ t, ∑ j ∈ t, ∑ k ∈ t, ∑ l ∈ t, d i j k l)
        = ∑ i, ∑ j, ∑ k, ∑ l, if i ∈ t ∧ j ∈ t ∧ k ∈ t ∧ l ∈ t then d i j k l else 0 := by
    intro t
    have inner3 : ∀ i j k, (∑ l ∈ t, d i j k l) = ∑ l, if l ∈ t then d i j k l else 0 :=
      fun i j k => (sum_ite_mem_eq' t (d i j k)).symm
    simp_rw [inner3]
    have inner2 : ∀ i j, (∑ k ∈ t, ∑ l, if l ∈ t then d i j k l else 0)
        = ∑ k, if k ∈ t then (∑ l, if l ∈ t then d i j k l else 0) else 0 :=
      fun i j => (sum_ite_mem_eq' t _).symm
    simp_rw [inner2]
    have inner1 : ∀ i, (∑ j ∈ t, ∑ k, if k ∈ t then (∑ l, if l ∈ t then d i j k l else 0) else 0)
        = ∑ j, if j ∈ t then
            (∑ k, if k ∈ t then (∑ l, if l ∈ t then d i j k l else 0) else 0) else 0 :=
      fun i => (sum_ite_mem_eq' t _).symm
    simp_rw [inner1]
    rw [← sum_ite_mem_eq' t
      (fun i => ∑ j, if j ∈ t then
        (∑ k, if k ∈ t then (∑ l, if l ∈ t then d i j k l else 0) else 0) else 0)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ t
    · rw [if_pos hi]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ t
      · rw [if_pos hj]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k ∈ t
        · rw [if_pos hk]
          apply Finset.sum_congr rfl
          intro l _
          by_cases hl : l ∈ t
          · rw [if_pos hl, if_pos ⟨hi, hj, hk, hl⟩]
          · rw [if_neg hl, if_neg (by tauto)]
        · rw [if_neg hk, eq_comm]
          apply Finset.sum_eq_zero
          intro l _
          rw [if_neg (by tauto)]
      · rw [if_neg hj, eq_comm]
        apply Finset.sum_eq_zero
        intro k _
        apply Finset.sum_eq_zero
        intro l _
        rw [if_neg (by tauto)]
    · rw [if_neg hi, eq_comm]
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro k _
      apply Finset.sum_eq_zero
      intro l _
      rw [if_neg (by tauto)]
  simp_rw [hrw, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l _
  have hne : ({i, j, k, l} : Finset (Fin n)) ≠ univ := by
    intro heq
    have h4 : ({i, j, k, l} : Finset (Fin n)).card ≤ 4 := by
      have a := Finset.card_insert_le i ({j, k, l} : Finset (Fin n))
      have b := Finset.card_insert_le j ({k, l} : Finset (Fin n))
      have e := Finset.card_insert_le k ({l} : Finset (Fin n))
      simp only [Finset.card_singleton] at e
      omega
    have hc : ({i, j, k, l} : Finset (Fin n)).card = n := by
      rw [heq, Finset.card_univ, Fintype.card_fin]
    omega
  simp_rw [mem4_iff_subset i j k l]
  exact monomial_term_zero _ hne _

/-! ### The fourth-moment defect -/

/-- The fourth power of the distance from the observer `X` to the parallelepiped vertex
    indexed by `t`. -/
def sqDist4 (X c : V) (u : Fin n → V) (t : Finset (Fin n)) : ℝ :=
  ‖X - pVertex c u t‖ ^ 4

/-- The **fourth-moment British-flag defect**: the alternating (`(-1)^{|t|}`-weighted) sum
    of fourth powers of distances over all `2ⁿ` vertices of the parallelepiped. -/
def defect4 (X c : V) (u : Fin n → V) : ℝ :=
  ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * sqDist4 X c u t

/-- **Fourth-moment defect formula, `n ≥ 5`.**  For any parallelepiped in a real inner
    product space with base `c`, arbitrary (possibly skew) edge vectors `u`, and any
    observer `X`, the alternating fourth-power defect over the `2ⁿ` vertices is identically
    zero whenever `n ≥ 5`.

    `‖X − vertex t‖⁴ = (‖w‖² − 2 ∑_{i∈t}⟪w,uᵢ⟫ + ∑_{i,j∈t}⟪uᵢ,uⱼ⟫)²` is a degree-`4`
    polynomial in the indicators; expanding the square produces six pieces of degrees
    `0,1,2,2,3,4`, each annihilated by the signed powerset sum once `n` exceeds its
    degree.  The binding constraint is the degree-`4` piece, requiring `n ≥ 5`. -/
theorem fourth_moment_defect_eq_zero (hn : 5 ≤ n) (X c : V) (u : Fin n → V) :
    defect4 X c u = 0 := by
  -- expand each summand of `defect₄` into the six pieces via `sqDist_expand` and `ring`
  have key : ∀ t : Finset (Fin n), (-1 : ℝ) ^ t.card * sqDist4 X c u t
      = (-1 : ℝ) ^ t.card * (‖X - c‖ ^ 2) ^ 2
        - (-1 : ℝ) ^ t.card * (4 * ‖X - c‖ ^ 2 * (∑ i ∈ t, ⟪X - c, u i⟫))
        + (-1 : ℝ) ^ t.card * (2 * ‖X - c‖ ^ 2 * (∑ i ∈ t, ∑ j ∈ t, ⟪u i, u j⟫))
        + (-1 : ℝ) ^ t.card * (4 * ((∑ i ∈ t, ⟪X - c, u i⟫) * (∑ j ∈ t, ⟪X - c, u j⟫)))
        - (-1 : ℝ) ^ t.card * (4 * ((∑ i ∈ t, ⟪X - c, u i⟫) * (∑ j ∈ t, ∑ l ∈ t, ⟪u j, u l⟫)))
        + (-1 : ℝ) ^ t.card * ((∑ i ∈ t, ∑ j ∈ t, ⟪u i, u j⟫) * (∑ k ∈ t, ∑ l ∈ t, ⟪u k, u l⟫)) := by
    intro t
    have hsq : sqDist4 X c u t = (sqDist X c u t) ^ 2 := by
      simp only [sqDist4, sqDist]; ring
    rw [hsq, sqDist_expand]
    ring
  -- the six pieces, each killed by the appropriate term lemma
  have h1 : ∑ t ∈ (univ : Finset (Fin n)).powerset,
      (-1 : ℝ) ^ t.card * (‖X - c‖ ^ 2) ^ 2 = 0 :=
    const_term_zero (by omega) ((‖X - c‖ ^ 2) ^ 2)
  have h2 : ∑ t ∈ (univ : Finset (Fin n)).powerset,
      (-1 : ℝ) ^ t.card * (4 * ‖X - c‖ ^ 2 * (∑ i ∈ t, ⟪X - c, u i⟫)) = 0 := by
    have hpt : ∀ t : Finset (Fin n),
        (-1 : ℝ) ^ t.card * (4 * ‖X - c‖ ^ 2 * (∑ i ∈ t, ⟪X - c, u i⟫))
          = 4 * ‖X - c‖ ^ 2 * ((-1 : ℝ) ^ t.card * (∑ i ∈ t, ⟪X - c, u i⟫)) := fun t => by ring
    simp_rw [hpt]
    rw [← Finset.mul_sum, linear_term_zero (by omega) (fun i => ⟪X - c, u i⟫), mul_zero]
  have h3 : ∑ t ∈ (univ : Finset (Fin n)).powerset,
      (-1 : ℝ) ^ t.card * (2 * ‖X - c‖ ^ 2 * (∑ i ∈ t, ∑ j ∈ t, ⟪u i, u j⟫)) = 0 := by
    have hpt : ∀ t : Finset (Fin n),
        (-1 : ℝ) ^ t.card * (2 * ‖X - c‖ ^ 2 * (∑ i ∈ t, ∑ j ∈ t, ⟪u i, u j⟫))
          = 2 * ‖X - c‖ ^ 2 * ((-1 : ℝ) ^ t.card * (∑ i ∈ t, ∑ j ∈ t, ⟪u i, u j⟫)) :=
      fun t => by ring
    simp_rw [hpt]
    rw [← Finset.mul_sum, quadratic_term_zero (by omega) (fun i j => ⟪u i, u j⟫), mul_zero]
  have h4 : ∑ t ∈ (univ : Finset (Fin n)).powerset,
      (-1 : ℝ) ^ t.card * (4 * ((∑ i ∈ t, ⟪X - c, u i⟫) * (∑ j ∈ t, ⟪X - c, u j⟫))) = 0 := by
    have hconv : ∀ t : Finset (Fin n),
        (∑ i ∈ t, ⟪X - c, u i⟫) * (∑ j ∈ t, ⟪X - c, u j⟫)
          = ∑ i ∈ t, ∑ j ∈ t, ⟪X - c, u i⟫ * ⟪X - c, u j⟫ := by
      intro t; rw [Finset.sum_mul_sum]
    have hpt : ∀ t : Finset (Fin n),
        (-1 : ℝ) ^ t.card * (4 * ((∑ i ∈ t, ⟪X - c, u i⟫) * (∑ j ∈ t, ⟪X - c, u j⟫)))
          = 4 * ((-1 : ℝ) ^ t.card * (∑ i ∈ t, ∑ j ∈ t, ⟪X - c, u i⟫ * ⟪X - c, u j⟫)) := by
      intro t; rw [hconv t]; ring
    simp_rw [hpt]
    rw [← Finset.mul_sum,
      quadratic_term_zero (by omega) (fun i j => ⟪X - c, u i⟫ * ⟪X - c, u j⟫), mul_zero]
  have h5 : ∑ t ∈ (univ : Finset (Fin n)).powerset,
      (-1 : ℝ) ^ t.card * (4 * ((∑ i ∈ t, ⟪X - c, u i⟫) * (∑ j ∈ t, ∑ l ∈ t, ⟪u j, u l⟫))) = 0 := by
    have hconv : ∀ t : Finset (Fin n),
        (∑ i ∈ t, ⟪X - c, u i⟫) * (∑ j ∈ t, ∑ l ∈ t, ⟪u j, u l⟫)
          = ∑ i ∈ t, ∑ j ∈ t, ∑ l ∈ t, ⟪X - c, u i⟫ * ⟪u j, u l⟫ := by
      intro t
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]
    have hpt : ∀ t : Finset (Fin n),
        (-1 : ℝ) ^ t.card * (4 * ((∑ i ∈ t, ⟪X - c, u i⟫) * (∑ j ∈ t, ∑ l ∈ t, ⟪u j, u l⟫)))
          = 4 * ((-1 : ℝ) ^ t.card * (∑ i ∈ t, ∑ j ∈ t, ∑ l ∈ t, ⟪X - c, u i⟫ * ⟪u j, u l⟫)) := by
      intro t; rw [hconv t]; ring
    simp_rw [hpt]
    rw [← Finset.mul_sum,
      cubic_term_zero (by omega) (fun i j l => ⟪X - c, u i⟫ * ⟪u j, u l⟫), mul_zero]
  have h6 : ∑ t ∈ (univ : Finset (Fin n)).powerset,
      (-1 : ℝ) ^ t.card * ((∑ i ∈ t, ∑ j ∈ t, ⟪u i, u j⟫) * (∑ k ∈ t, ∑ l ∈ t, ⟪u k, u l⟫)) = 0 := by
    have hconv : ∀ t : Finset (Fin n),
        (∑ i ∈ t, ∑ j ∈ t, ⟪u i, u j⟫) * (∑ k ∈ t, ∑ l ∈ t, ⟪u k, u l⟫)
          = ∑ i ∈ t, ∑ k ∈ t, ∑ j ∈ t, ∑ l ∈ t, ⟪u i, u j⟫ * ⟪u k, u l⟫ := by
      intro t
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_mul_sum]
    have hpt : ∀ t : Finset (Fin n),
        (-1 : ℝ) ^ t.card * ((∑ i ∈ t, ∑ j ∈ t, ⟪u i, u j⟫) * (∑ k ∈ t, ∑ l ∈ t, ⟪u k, u l⟫))
          = (-1 : ℝ) ^ t.card * (∑ i ∈ t, ∑ k ∈ t, ∑ j ∈ t, ∑ l ∈ t, ⟪u i, u j⟫ * ⟪u k, u l⟫) := by
      intro t; rw [hconv t]
    simp_rw [hpt]
    exact quartic_term_zero (by omega) (fun i k j l => ⟪u i, u j⟫ * ⟪u k, u l⟫)
  -- assemble
  unfold defect4
  simp_rw [key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3, h4, h5, h6]
  ring

end BritishFlagFourthMomentOQ010201
