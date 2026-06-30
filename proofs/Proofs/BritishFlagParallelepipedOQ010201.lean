/-
  British Flag Defect for a General (Non-Orthogonal) Parallelepiped
  Open Question: british-flag-theorem-oq-01-oq-02-oq-01

  The parent entry (`british-flag-theorem-oq-01-oq-02`) proves the British Flag
  defect identity for an *axis-aligned box* (orthotope) in `n` dimensions: the
  alternating sum of squared distances over the `2ⁿ` vertices,

      ∑_{t ⊆ {0,…,n-1}} (-1)^{|t|} · ‖X − vertex t‖²,

  vanishes for every `n ≥ 2`. A box has mutually orthogonal edge vectors, so all
  pairwise inner products are zero.

  This file removes the orthogonality assumption. Fix a base point `c` and edge
  vectors `u₀,…,u_{n-1}` in a real inner product space `V`. The parallelepiped
  vertex indexed by `t ⊆ {0,…,n-1}` is

      vertex t = c + ∑_{i ∈ t} uᵢ,

  and for an observer `X` we study the alternating squared-distance defect

      defect = ∑_{t} (-1)^{|t|} · ‖X − vertex t‖².

  ## Why a clean defect formula exists

  Writing `w = X − c`, expanding `‖X − vertex t‖² = ‖w − ∑_{i∈t} uᵢ‖²` shows that
  `sqDist t` is a polynomial of **degree ≤ 2** in the membership indicators
  `[i ∈ t]`:

      sqDist t = ‖w‖²  −  2 ∑_{i∈t} ⟪w, uᵢ⟫  +  ∑_{i∈t} ∑_{j∈t} ⟪uᵢ, uⱼ⟫.

  The operator `g ↦ ∑_t (-1)^{|t|} g t` is (up to sign) the `n`-th iterated finite
  difference; it annihilates every monomial in the indicators that omits at least
  one coordinate. Hence:

  * **`n ≥ 3`**: every term has degree ≤ 2 < n, so the defect is **identically 0**,
    independent of the observer `X`, the base `c`, and the (arbitrary, possibly
    skew) edge vectors. This is the general defect formula requested by the open
    question — the orthotope of the parent is just the special case where the
    `⟪uᵢ,uⱼ⟫` happen to vanish.
  * **`n = 2`**: the only surviving monomial is `[0 ∈ t][1 ∈ t]`, giving the defect
    `2 ⟪u₀, u₁⟫`. For orthogonal edges this is `0`, recovering the classical
    British Flag Theorem; in general it measures the failure of orthogonality.

  ## Main results

  * `alt_sum_eq_zero_of_indep` — structural heart: if `g` does not depend on a
    coordinate `k`, the signed powerset sum `∑_t (-1)^{|t|} g t` vanishes
    (pairing `s` with `insert k s`).
  * `sqDist_expand` — the degree-≤2 inner-product expansion of `‖X − vertex t‖²`.
  * `parallelepiped_defect_eq_zero` — for `n ≥ 3`, `defect = 0`.
  * `parallelepiped_defect_two` — for `n = 2`, `defect = 2 ⟪u 0, u 1⟫`.
  * `parallelepiped_defect_two_orthogonal` — orthogonal edges (`n = 2`) ⟹ defect
    `0`, the British Flag Theorem, unifying with the parent.

  Everything is `sorry`-free and axiom-free.
-/

import Mathlib

open Finset
open scoped RealInnerProductSpace

namespace BritishFlagParallelepipedOQ010201

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The vertex of the parallelepiped with base `c` and edge vectors `u`, indexed by
    `t`: starting from `c`, add the edges `uᵢ` for `i ∈ t`. -/
def pVertex (c : V) (u : Fin n → V) (t : Finset (Fin n)) : V :=
  c + ∑ i ∈ t, u i

/-- Squared Euclidean distance from the observer `X` to the parallelepiped vertex
    indexed by `t`. -/
def sqDist (X c : V) (u : Fin n → V) (t : Finset (Fin n)) : ℝ :=
  ‖X - pVertex c u t‖ ^ 2

/-- The British Flag defect: the alternating (`(-1)^{|t|}`-weighted) sum of squared
    distances over all `2ⁿ` vertices of the parallelepiped. -/
def defect (X c : V) (u : Fin n → V) : ℝ :=
  ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * sqDist X c u t

/-! ### Structural heart: alternating powerset sums kill coordinate-independent functions -/

/-- **Structural heart.** If `g t` does not change when the coordinate `k` is
    inserted into a `k`-free set, then the signed powerset sum vanishes. The
    powerset of `univ` splits into the subsets `s ⊆ univ.erase k` and their images
    `insert k s`; the two have equal `g`-value but opposite sign `(-1)^{|·|}`, so
    they cancel in pairs. -/
theorem alt_sum_eq_zero_of_indep (k : Fin n) (g : Finset (Fin n) → ℝ)
    (hg : ∀ s : Finset (Fin n), k ∉ s → g (insert k s) = g s) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * g t = 0 := by
  classical
  set E := (univ : Finset (Fin n)).erase k with hE
  have hins : (univ : Finset (Fin n)) = insert k E := (insert_erase (mem_univ k)).symm
  have hk : k ∉ E := notMem_erase k univ
  have hinj : Set.InjOn (insert k) (E.powerset : Set (Finset (Fin n))) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_powerset] at ha hb
    have hka : k ∉ a := fun h => hk (ha h)
    have hkb : k ∉ b := fun h => hk (hb h)
    have := congrArg (·.erase k) hab
    simpa [erase_insert hka, erase_insert hkb] using this
  have hdisj : Disjoint E.powerset (E.powerset.image (insert k)) := by
    rw [Finset.disjoint_left]
    intro t ht htimg
    rw [mem_powerset] at ht
    rw [mem_image] at htimg
    obtain ⟨v, _, rfl⟩ := htimg
    exact hk (ht (mem_insert_self k v))
  rw [hins, powerset_insert, sum_union hdisj, sum_image hinj]
  -- second sum: insert k s has card |s|+1 and equal g-value, so it negates the first
  have hsecond : ∑ s ∈ E.powerset, (-1 : ℝ) ^ (insert k s).card * g (insert k s)
               = ∑ s ∈ E.powerset, -((-1 : ℝ) ^ s.card * g s) := by
    apply sum_congr rfl
    intro s hs
    rw [mem_powerset] at hs
    have hks : k ∉ s := fun h => hk (hs h)
    rw [card_insert_of_notMem hks, hg s hks, pow_succ]
    ring
  rw [hsecond, sum_neg_distrib, add_neg_cancel]

/-! ### Existence of an unused coordinate -/

/-- For `n ≥ 2` there is a coordinate distinct from any given one. -/
theorem exists_coord_ne (hn : 2 ≤ n) (i : Fin n) : ∃ k : Fin n, k ≠ i := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact _root_.exists_ne i

/-- For `n ≥ 3` there is a coordinate distinct from any two given ones. -/
theorem exists_coord_ne_two (hn : 3 ≤ n) (i j : Fin n) : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  classical
  by_contra h
  push_neg at h
  have hsub : (univ : Finset (Fin n)) ⊆ {i, j} := by
    intro k _
    rcases eq_or_ne k i with hki | hki
    · simp [hki]
    · have := h k hki
      simp [this]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at hc
  have hpair : ({i, j} : Finset (Fin n)).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  omega

/-! ### Inner-product expansion of the squared distance -/

/-- `sqDist` is a degree-≤2 polynomial in the membership indicators: it expands as
    `‖w‖² − 2 ∑_{i∈t} ⟪w,uᵢ⟫ + ∑_{i∈t} ∑_{j∈t} ⟪uᵢ,uⱼ⟫` where `w = X − c`. -/
theorem sqDist_expand (X c : V) (u : Fin n → V) (t : Finset (Fin n)) :
    sqDist X c u t
      = ‖X - c‖ ^ 2 - 2 * (∑ i ∈ t, ⟪X - c, u i⟫)
        + ∑ i ∈ t, ∑ j ∈ t, ⟪u i, u j⟫ := by
  have hsub : X - pVertex c u t = (X - c) - ∑ i ∈ t, u i := by
    simp only [pVertex]; abel
  -- expand ‖∑ uᵢ‖² = ⟪∑,∑⟫ = ∑∑⟪uᵢ,uⱼ⟫ as a standalone equation to avoid touching ‖w‖²
  have hnorm : ‖∑ i ∈ t, u i‖ ^ 2 = ∑ i ∈ t, ∑ j ∈ t, ⟪u i, u j⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  rw [sqDist, hsub, norm_sub_sq_real, inner_sum, hnorm]

/-! ### The three monomial pieces vanish -/

/-- The constant piece `‖w‖² · ∑_t (-1)^{|t|}` vanishes for `n ≥ 1`. -/
theorem const_term_zero (hn : 1 ≤ n) (r : ℝ) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * r = 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨k⟩ := this
  exact alt_sum_eq_zero_of_indep k (fun _ => r) (fun _ _ => rfl)

/-- The linear piece `∑_t (-1)^{|t|} ∑_{i∈t} a i` vanishes for `n ≥ 2`. -/
theorem linear_term_zero (hn : 2 ≤ n) (a : Fin n → ℝ) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset,
        (-1 : ℝ) ^ t.card * (∑ i ∈ t, a i) = 0 := by
  classical
  -- rewrite ∑_{i∈t} a i as a sum over univ with an indicator, push the sign in, swap
  have hrw : ∀ t : Finset (Fin n),
      (∑ i ∈ t, a i) = ∑ i, (if i ∈ t then a i else 0) := fun t => by
    rw [Finset.sum_ite_mem_eq]
  simp_rw [hrw, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  obtain ⟨k, hk⟩ := exists_coord_ne hn i
  refine alt_sum_eq_zero_of_indep k (fun t => if i ∈ t then a i else 0) ?_
  intro s hks
  have e1 : i ∈ insert k s ↔ i ∈ s := by
    simp only [mem_insert]; exact or_iff_right (fun h => hk h.symm)
  simp only [e1]

/-- The quadratic piece `∑_t (-1)^{|t|} ∑_{i∈t} ∑_{j∈t} b i j` vanishes for `n ≥ 3`. -/
theorem quadratic_term_zero (hn : 3 ≤ n) (b : Fin n → Fin n → ℝ) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset,
        (-1 : ℝ) ^ t.card * (∑ i ∈ t, ∑ j ∈ t, b i j) = 0 := by
  classical
  -- rewrite the double `∑_{i∈t}∑_{j∈t}` as a double `∑_i ∑_j` of indicators
  have hrw : ∀ t : Finset (Fin n),
      (∑ i ∈ t, ∑ j ∈ t, b i j)
        = ∑ i, ∑ j, (if i ∈ t ∧ j ∈ t then b i j else 0) := by
    intro t
    have inner : ∀ i, (∑ j ∈ t, b i j) = ∑ j, if j ∈ t then b i j else 0 :=
      fun i => (Finset.sum_ite_mem_eq t (b i)).symm
    simp_rw [inner]
    rw [← Finset.sum_ite_mem_eq t (fun i => ∑ j, if j ∈ t then b i j else 0)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ t
    · rw [if_pos hi]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ t
      · rw [if_pos hj, if_pos ⟨hi, hj⟩]
      · rw [if_neg hj, if_neg (by tauto)]
    · rw [if_neg hi, eq_comm]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg (by tauto)]
  simp_rw [hrw, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  obtain ⟨k, hki, hkj⟩ := exists_coord_ne_two hn i j
  refine alt_sum_eq_zero_of_indep k (fun t => if i ∈ t ∧ j ∈ t then b i j else 0) ?_
  intro s hks
  have e1 : i ∈ insert k s ↔ i ∈ s := by
    simp only [mem_insert]; exact or_iff_right (fun h => hki h.symm)
  have e2 : j ∈ insert k s ↔ j ∈ s := by
    simp only [mem_insert]; exact or_iff_right (fun h => hkj h.symm)
  simp only [e1, e2]

/-! ### Main theorems -/

/-- **General defect formula, `n ≥ 3`.** For any parallelepiped in a real inner
    product space with base `c`, arbitrary (possibly skew) edge vectors `u`, and
    any observer `X`, the alternating squared-distance defect over the `2ⁿ`
    vertices is identically zero whenever `n ≥ 3`. This is the requested general
    defect formula: it holds for *every* configuration, the orthotope of the parent
    being the special case in which the pairwise inner products vanish. -/
theorem parallelepiped_defect_eq_zero (hn : 3 ≤ n) (X c : V) (u : Fin n → V) :
    defect X c u = 0 := by
  unfold defect
  simp_rw [sqDist_expand, mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [const_term_zero (by omega) (‖X - c‖ ^ 2),
      quadratic_term_zero hn (fun i j => ⟪u i, u j⟫)]
  have hmid : ∑ t ∈ (univ : Finset (Fin n)).powerset,
      (-1 : ℝ) ^ t.card * (2 * ∑ i ∈ t, ⟪X - c, u i⟫) = 0 := by
    have h : ∀ t : Finset (Fin n),
        (-1 : ℝ) ^ t.card * (2 * ∑ i ∈ t, ⟪X - c, u i⟫)
          = 2 * ((-1 : ℝ) ^ t.card * ∑ i ∈ t, ⟪X - c, u i⟫) := fun t => by ring
    simp_rw [h]
    rw [← Finset.mul_sum, linear_term_zero (by omega) (fun i => ⟪X - c, u i⟫), mul_zero]
  rw [hmid]; ring

/-- Enumeration of the `n = 2` quadratic piece: the four subsets of `{0,1}` give
    `b 0 1 + b 1 0`. -/
theorem quadSum_two (b : Fin 2 → Fin 2 → ℝ) :
    ∑ t ∈ (univ : Finset (Fin 2)).powerset,
        (-1 : ℝ) ^ t.card * (∑ i ∈ t, ∑ j ∈ t, b i j)
      = b 0 1 + b 1 0 := by
  have hps : (univ : Finset (Fin 2)).powerset = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hps, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide)]
  simp only [Finset.card_empty, Finset.card_singleton, Finset.sum_empty,
    Finset.sum_singleton, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1),
    Finset.card_pair (by decide : (0 : Fin 2) ≠ 1)]
  ring

/-- **`n = 2` defect.** For a (possibly skew) parallelogram with edge vectors
    `u 0, u 1`, the alternating squared-distance defect equals `2 ⟪u 0, u 1⟫`,
    independent of the observer `X` and the base `c`. -/
theorem parallelepiped_defect_two (X c : V) (u : Fin 2 → V) :
    defect X c u = 2 * ⟪u 0, u 1⟫ := by
  unfold defect
  simp_rw [sqDist_expand, mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [const_term_zero (by omega) (‖X - c‖ ^ 2)]
  have hmid : ∑ t ∈ (univ : Finset (Fin 2)).powerset,
      (-1 : ℝ) ^ t.card * (2 * ∑ i ∈ t, ⟪X - c, u i⟫) = 0 := by
    have h : ∀ t : Finset (Fin 2),
        (-1 : ℝ) ^ t.card * (2 * ∑ i ∈ t, ⟪X - c, u i⟫)
          = 2 * ((-1 : ℝ) ^ t.card * ∑ i ∈ t, ⟪X - c, u i⟫) := fun t => by ring
    simp_rw [h]
    rw [← Finset.mul_sum, linear_term_zero (by omega) (fun i => ⟪X - c, u i⟫), mul_zero]
  rw [hmid, quadSum_two (fun i j => ⟪u i, u j⟫), real_inner_comm (u 0) (u 1)]
  ring

/-- **Recovery of the British Flag Theorem.** For `n = 2` with orthogonal edges
    (`⟪u 0, u 1⟫ = 0`) the defect vanishes — the classical British Flag Theorem,
    unifying this entry with the orthotope parent. -/
theorem parallelepiped_defect_two_orthogonal (X c : V) (u : Fin 2 → V)
    (h : ⟪u 0, u 1⟫ = 0) :
    defect X c u = 0 := by
  rw [parallelepiped_defect_two, h, mul_zero]

end BritishFlagParallelepipedOQ010201
