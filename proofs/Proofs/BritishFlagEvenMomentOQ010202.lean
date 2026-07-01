/-
  Higher-Even-Moment British Flag Defect: the 2k-th Power Alternating Sum
  Open Question: british-flag-theorem-oq-01-oq-02-oq-02

  ## Background

  The British Flag Theorem says that for a rectangle `ABCD` and any point `P`,
    |PA|² + |PC|² = |PB|² + |PD|²,
  i.e. the alternating sum of squared distances over the four corners vanishes.
  The gallery family generalizes this to the `2ⁿ` vertices of an `n`-dimensional
  parallelepiped `vertex t = c + ∑_{i ∈ t} uᵢ` and studies the signed powerset sum

      defect_m = ∑_{t ⊆ {0,…,n-1}} (-1)^{|t|} · ‖X − vertex t‖^{2m}.

  Two special cases are already in the gallery:
  * `BritishFlagParallelepipedOQ010201`  — the **second** moment (`m = 1`): vanishes
    for `n ≥ 3` (`parallelepiped_defect_eq_zero`).
  * `BritishFlagFourthMomentOQ010201`     — the **fourth** moment (`m = 2`): vanishes
    for `n ≥ 5` (`fourth_moment_defect_eq_zero`), proved by hand-expanding the square
    into six monomial pieces.

  ## What this file adds

  The **arbitrary even moment**, uniformly in `m`.  We prove

      even_moment_defect_eq_zero :  2 * m < n  →  defect_m = 0,

  i.e. `∑_t (-1)^{|t|} ‖X − vertex t‖^{2m} = 0` for every `n ≥ 2m + 1`, every base
  `c`, every (arbitrary, possibly skew) edge system `u`, and every observer `X`.
  Instantiating `m = 1, 2` recovers the parent's `n ≥ 3` and the sibling's `n ≥ 5`
  thresholds, so this single statement subsumes the whole family.

  ## Proof architecture

  Write `w = X − c` and view the displacement `X − vertex t = w − ∑_{i∈t} uᵢ` as a
  linear combination `∑_{a} indᵗ(a) · e(a)` indexed by `a ∈ Option (Fin n)`, where
  `e(none) = w`, `e(some i) = −uᵢ`, and `indᵗ` is `1` on `none` and the membership
  indicator `[i ∈ t]` on `some i`.  Then

      ‖X − vertex t‖² = ∑_{p : Option(Fin n)²} indᵗ(p.1)·indᵗ(p.2)·⟪e p.1, e p.2⟫,

  a *single* sum whose only `t`-dependence sits in the indicator factors.  Raising
  to the `m`-th power and applying `Fintype.sum_pow` turns `‖·‖^{2m}` into a sum,
  over multi-indices `π : Fin m → Option(Fin n)²`, of products of `2m` indicator
  factors times a `t`-independent inner-product coefficient.

  Each product touches at most `2m` coordinates, hence — as `2m < n` — omits some
  coordinate `k`.  As a function of `t` it therefore depends only on `t ∩ (touched
  set)`, and the parent's structural lemma `alt_sum_eq_zero_of_indep` kills its
  signed powerset sum.  Summing over `π` gives `defect_m = 0`.

  Everything is `sorry`-free and axiom-free, over an arbitrary real inner product
  space `V`.
-/
import Mathlib
import Proofs.BritishFlagParallelepipedOQ010201

open Finset
open scoped RealInnerProductSpace

namespace BritishFlagEvenMomentOQ010202

open BritishFlagParallelepipedOQ010201 (pVertex sqDist alt_sum_eq_zero_of_indep)

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Abstract vanishing principle: dependence on a proper coordinate subset -/

/-- **Structural principle.**  If `g t` depends on `t` only through `t ∩ A` for some
    *proper* subset `A ≠ univ`, then the signed powerset sum `∑_t (-1)^{|t|} g t`
    vanishes.  This packages the parent's `alt_sum_eq_zero_of_indep`: pick a
    coordinate `k ∉ A`; inserting `k` never changes `t ∩ A`, so `g` is invariant. -/
theorem alt_sum_zero_of_inter (A : Finset (Fin n)) (hA : A ≠ univ)
    (g : Finset (Fin n) → ℝ) (hg : ∀ t, g t = g (t ∩ A)) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * g t = 0 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : Fin n, k ∉ A := by
    by_contra h
    push_neg at h
    exact hA (eq_univ_of_forall h)
  refine alt_sum_eq_zero_of_indep k g ?_
  intro s hks
  rw [hg (insert k s), hg s]
  congr 1
  rw [Finset.insert_inter_of_notMem hk]

/-! ### The linear-combination model of the displacement -/

/-- Base/edge vector attached to an optional coordinate: `none ↦ X − c`, `some i ↦ −uᵢ`. -/
def evec (X c : V) (u : Fin n → V) (a : Option (Fin n)) : V :=
  a.elim (X - c) (fun i => - u i)

/-- Membership weight: `none ↦ 1`, `some i ↦ [i ∈ t]`. -/
def ind (t : Finset (Fin n)) (a : Option (Fin n)) : ℝ :=
  a.elim 1 (fun i => if i ∈ t then 1 else 0)

/-- The single-sum pairwise coefficient of a term. -/
def term (X c : V) (u : Fin n → V) (t : Finset (Fin n))
    (p : Option (Fin n) × Option (Fin n)) : ℝ :=
  ind t p.1 * ind t p.2 * ⟪evec X c u p.1, evec X c u p.2⟫

@[simp] lemma evec_none (X c : V) (u : Fin n → V) : evec X c u none = X - c := rfl
@[simp] lemma evec_some (X c : V) (u : Fin n → V) (i : Fin n) : evec X c u (some i) = - u i := rfl
@[simp] lemma ind_none (t : Finset (Fin n)) : ind t none = 1 := rfl
@[simp] lemma ind_some (t : Finset (Fin n)) (i : Fin n) :
    ind t (some i) = if i ∈ t then 1 else 0 := rfl

/-- The displacement `X − vertex t` as a weighted sum over optional coordinates. -/
theorem displacement_eq_sum (X c : V) (u : Fin n → V) (t : Finset (Fin n)) :
    X - pVertex c u t = ∑ a : Option (Fin n), ind t a • evec X c u a := by
  rw [Fintype.sum_option]
  simp only [ind_none, evec_none, ind_some, evec_some, one_smul]
  have hs : (∑ i : Fin n, (if i ∈ t then (1 : ℝ) else 0) • (- u i)) = ∑ i ∈ t, - u i := by
    have hpt : ∀ i : Fin n, (if i ∈ t then (1 : ℝ) else 0) • (- u i)
        = if i ∈ t then (- u i) else 0 := by
      intro i; split <;> simp
    simp_rw [hpt]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hs, Finset.sum_neg_distrib, pVertex]
  abel

/-- **Single-sum form of the squared distance.**  `‖X − vertex t‖²` is a sum, over
    pairs of optional coordinates, of `indᵗ(p.1)·indᵗ(p.2)·⟪e p.1, e p.2⟫`. -/
theorem sqDist_eq_sum (X c : V) (u : Fin n → V) (t : Finset (Fin n)) :
    sqDist X c u t = ∑ p : Option (Fin n) × Option (Fin n), term X c u t p := by
  rw [sqDist, ← real_inner_self_eq_norm_sq, displacement_eq_sum, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp only [term]
  ring

/-! ### The coordinates touched by a multi-index and the size bound -/

/-- The set of coordinates appearing (as a `some`) in the multi-index `π`. -/
def touched {m : ℕ} (π : Fin m → Option (Fin n) × Option (Fin n)) : Finset (Fin n) :=
  univ.biUnion (fun j => (π j).1.toFinset ∪ (π j).2.toFinset)

/-- A multi-index of length `m` touches at most `2m` coordinates. -/
theorem card_touched_le {m : ℕ} (π : Fin m → Option (Fin n) × Option (Fin n)) :
    (touched π).card ≤ 2 * m := by
  have hopt : ∀ o : Option (Fin n), o.toFinset.card ≤ 1 := by
    intro o; cases o with
    | none => simp
    | some a => simp
  unfold touched
  calc (univ.biUnion (fun j => (π j).1.toFinset ∪ (π j).2.toFinset)).card
      ≤ ∑ j, ((π j).1.toFinset ∪ (π j).2.toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin m, 2 := Finset.sum_le_sum (fun j _ =>
        (Finset.card_union_le _ _).trans
          (by have := hopt (π j).1; have := hopt (π j).2; omega))
    _ = 2 * m := by simp [Finset.sum_const, Finset.card_univ, mul_comm]

/-- For `2m < n`, a length-`m` multi-index cannot touch every coordinate. -/
theorem touched_ne_univ {m : ℕ} (hn : 2 * m < n)
    (π : Fin m → Option (Fin n) × Option (Fin n)) : touched π ≠ univ := by
  intro h
  have h1 : (touched π).card = n := by rw [h, Finset.card_univ, Fintype.card_fin]
  have h2 := card_touched_le π
  omega

/-! ### Each product factors through the touched set -/

/-- An indicator weight only sees `t` through `t ∩ A`, once its coordinate lies in `A`. -/
theorem ind_inter (t A : Finset (Fin n)) (a : Option (Fin n)) (ha : a.toFinset ⊆ A) :
    ind t a = ind (t ∩ A) a := by
  cases a with
  | none => rfl
  | some i =>
    have hiA : i ∈ A := ha (by simp)
    simp only [ind_some]
    by_cases h : i ∈ t
    · simp [h, hiA, Finset.mem_inter]
    · simp [h, Finset.mem_inter]

/-- Each factor of the product depends on `t` only through `t ∩ touched π`. -/
theorem term_inter {m : ℕ} (X c : V) (u : Fin n → V) (t : Finset (Fin n))
    (π : Fin m → Option (Fin n) × Option (Fin n)) (j : Fin m) :
    term X c u t (π j) = term X c u (t ∩ touched π) (π j) := by
  have hsub : ((π j).1.toFinset ∪ (π j).2.toFinset) ⊆ touched π := by
    unfold touched
    exact Finset.subset_biUnion_of_mem
      (fun j => (π j).1.toFinset ∪ (π j).2.toFinset) (mem_univ j)
  simp only [term]
  rw [ind_inter t (touched π) (π j).1 (Finset.subset_union_left.trans hsub),
      ind_inter t (touched π) (π j).2 (Finset.subset_union_right.trans hsub)]

/-! ### Main theorem: every even moment vanishes below the dimension -/

/-- The `2m`-th power British flag defect over the `2ⁿ` vertices of a parallelepiped. -/
def defectPow (X c : V) (u : Fin n → V) (m : ℕ) : ℝ :=
  ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * (sqDist X c u t) ^ m

/-- **Higher-even-moment British Flag Theorem.**  For any real inner product space,
    any base point `c`, any edge system `u : Fin n → V`, any observer `X`, and any
    `m` with `2m < n`, the alternating `2m`-th power distance sum over the `2ⁿ`
    parallelepiped vertices vanishes:

        ∑_{t ⊆ {0,…,n-1}} (-1)^{|t|} · ‖X − vertex t‖^{2m} = 0.

    Specializing `m = 1` recovers `parallelepiped_defect_eq_zero` (`n ≥ 3`) and
    `m = 2` recovers `fourth_moment_defect_eq_zero` (`n ≥ 5`). -/
theorem even_moment_defect_eq_zero {m : ℕ} (hn : 2 * m < n) (X c : V) (u : Fin n → V) :
    defectPow X c u m = 0 := by
  classical
  unfold defectPow
  have hexp : ∀ t : Finset (Fin n), (sqDist X c u t) ^ m
      = ∑ π : Fin m → Option (Fin n) × Option (Fin n), ∏ j, term X c u t (π j) := by
    intro t; rw [sqDist_eq_sum]; exact Fintype.sum_pow _ m
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun π _ => ?_)
  refine alt_sum_zero_of_inter (touched π) (touched_ne_univ hn π)
    (fun t => ∏ j, term X c u t (π j)) ?_
  intro t
  exact Finset.prod_congr rfl (fun j _ => term_inter X c u t π j)

/-! ### Consistency corollaries: recovering the two gallery special cases -/

/-- The even-moment defect written out as `‖X − vertex t‖^{2m}`, matching the
    informal statement. -/
theorem defectPow_eq (X c : V) (u : Fin n → V) (m : ℕ) :
    defectPow X c u m
      = ∑ t ∈ (univ : Finset (Fin n)).powerset,
          (-1 : ℝ) ^ t.card * ‖X - pVertex c u t‖ ^ (2 * m) := by
  unfold defectPow
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [sqDist, ← pow_mul]

/-- **Second moment (`m = 1`), `n ≥ 3`.**  Recovers the parallelepiped British Flag
    defect identity as a corollary of the uniform theorem. -/
theorem second_moment_zero (hn : 3 ≤ n) (X c : V) (u : Fin n → V) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * ‖X - pVertex c u t‖ ^ 2 = 0 := by
  have := even_moment_defect_eq_zero (m := 1) (by omega) X c u
  rw [defectPow_eq] at this
  simpa using this

/-- **Fourth moment (`m = 2`), `n ≥ 5`.**  Recovers the fourth-moment defect
    identity as a corollary of the uniform theorem. -/
theorem fourth_moment_zero (hn : 5 ≤ n) (X c : V) (u : Fin n → V) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * ‖X - pVertex c u t‖ ^ 4 = 0 := by
  have := even_moment_defect_eq_zero (m := 2) (by omega) X c u
  rw [defectPow_eq] at this
  simpa using this

end BritishFlagEvenMomentOQ010202
