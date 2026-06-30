/-
  British Flag Defect Identity for Orthotopes in n Dimensions
  Open Question: british-flag-theorem-oq-01-oq-02

  The British Flag Theorem says that for a rectangle `ABCD` and any point `P`,
    |PA|² + |PC|² = |PB|² + |PD|²,
  i.e. the two *diagonal* corner sums agree. The four vertices of a rectangle are
  the `2² = 4` points whose `i`-th coordinate is either `aᵢ` or `bᵢ`; the diagonal
  pairs `{A,C}` and `{B,D}` are exactly the vertices reached by an **even** /
  **odd** number of `b`-choices.

  This file generalizes that to an axis-aligned box (orthotope) in `n` dimensions.
  A vertex is indexed by the set `t ⊆ {0,…,n-1}` of coordinates taking the value
  `bᵢ` (the others take `aᵢ`); the squared distance from an observer `P` is
    sqDist t = ∑ᵢ (Pᵢ − (i ∈ t ? bᵢ : aᵢ))².
  Splitting the `2ⁿ` vertices by the parity of `t.card`, the "British flag defect"

      ∑_{|t| even} sqDist t  −  ∑_{|t| odd} sqDist t

  is **identically zero** for every `n ≥ 2`, every box `a, b`, and every point `P`.
  For `n = 2` this is precisely the British Flag Theorem.

  ## Main results

  * `alternating_sqDist_zero` : the signed sum `∑_t (-1)^{|t|} · sqDist t = 0`.
    This is the structural heart; each coordinate contributes a factor
    `∑_{s ⊆ univ.erase i} (-1)^{|s|} = 0`, which vanishes precisely because the
    box is non-degenerate (`n ≥ 2`).
  * `british_flag_orthotope` : the even-vertex sum equals the odd-vertex sum.

  ## Proof strategy

  Expand `sqDist t = ∑ᵢ fᵢ(t)` and swap the order of summation. For a fixed
  coordinate `i`, the summand depends on `t` only through the predicate `i ∈ t`,
  so the inner alternating sum factors as
    [(Pᵢ−aᵢ)² − (Pᵢ−bᵢ)²] · ∑_{s ⊆ univ \ {i}} (-1)^{|s|},
  and the second factor is `0` for `n ≥ 2` (`Finset.sum_powerset_neg_one_pow_card`).
  Everything is `sorry`-free and axiom-free.
-/

import Mathlib

open Finset

namespace BritishFlagOrthotopeOQ0102

variable {n : ℕ}

/-- The vertex of the box with corners `a` and `b` selected by `t`: coordinate `i`
    is `b i` when `i ∈ t`, and `a i` otherwise. -/
def vertex (a b : Fin n → ℝ) (t : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ t then b i else a i

/-- Squared Euclidean distance from the observer `P` to the box vertex indexed by `t`. -/
def sqDist (a b P : Fin n → ℝ) (t : Finset (Fin n)) : ℝ :=
  ∑ i, (P i - vertex a b t i) ^ 2

/-- Real-coefficient alternating sum over a powerset vanishes for a nonempty set.
    (The integer version is `Finset.sum_powerset_neg_one_pow_card_of_nonempty`.) -/
theorem real_alt_powerset_zero {α : Type*} {s : Finset α} (h : s.Nonempty) :
    ∑ u ∈ s.powerset, (-1 : ℝ) ^ u.card = 0 := by
  have hz : ∑ u ∈ s.powerset, (-1 : ℤ) ^ u.card = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty h
  calc ∑ u ∈ s.powerset, (-1 : ℝ) ^ u.card
      = ((∑ u ∈ s.powerset, (-1 : ℤ) ^ u.card : ℤ) : ℝ) := by push_cast; rfl
    _ = ((0 : ℤ) : ℝ) := by rw [hz]
    _ = 0 := by norm_num

/-- Per-coordinate vanishing: when `i` can be removed leaving a nonempty index set,
    the alternating sum of a summand depending on `t` only through `i ∈ t` is `0`. -/
theorem alt_sum_ite_eq_zero (i : Fin n) (h : (univ.erase i).Nonempty) (α β : ℝ) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * (if i ∈ t then β else α) = 0 := by
  classical
  set s := (univ : Finset (Fin n)).erase i with hs
  have hins : (univ : Finset (Fin n)) = insert i s := (insert_erase (mem_univ i)).symm
  have hi : i ∉ s := notMem_erase i univ
  rw [hins, powerset_insert]
  -- the two pieces (subsets of `s`, and their `insert i` images) are disjoint
  have hdisj : Disjoint s.powerset (s.powerset.image (insert i)) := by
    rw [Finset.disjoint_left]
    intro t ht htimg
    rw [mem_powerset] at ht
    rw [mem_image] at htimg
    obtain ⟨u, _, rfl⟩ := htimg
    exact hi (ht (mem_insert_self i u))
  rw [sum_union hdisj]
  -- left piece: every `t ⊆ s` excludes `i`, so the `ite` is `α`
  have hleft : ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card * (if i ∈ t then β else α) = 0 := by
    have : ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card * (if i ∈ t then β else α)
         = ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card * α := by
      apply sum_congr rfl
      intro t ht
      rw [mem_powerset] at ht
      have : i ∉ t := fun hit => hi (ht hit)
      rw [if_neg this]
    rw [this, ← sum_mul, real_alt_powerset_zero h, zero_mul]
  -- right piece: reindex by `insert i`, each set contains `i`, so the `ite` is `β`
  have hright : ∑ t ∈ s.powerset.image (insert i), (-1 : ℝ) ^ t.card * (if i ∈ t then β else α) = 0 := by
    rw [sum_image]
    · have : ∑ u ∈ s.powerset, (-1 : ℝ) ^ (insert i u).card * (if i ∈ insert i u then β else α)
           = ∑ u ∈ s.powerset, -((-1 : ℝ) ^ u.card * β) := by
        apply sum_congr rfl
        intro u hu
        rw [mem_powerset] at hu
        have hiu : i ∉ u := fun hit => hi (hu hit)
        rw [card_insert_of_notMem hiu, if_pos (mem_insert_self i u), pow_succ]
        ring
      rw [this, sum_neg_distrib, ← sum_mul, real_alt_powerset_zero h, zero_mul, neg_zero]
    · intro u hu v hv huv
      rw [mem_coe, mem_powerset] at hu hv
      have hiu : i ∉ u := fun hit => hi (hu hit)
      have hiv : i ∉ v := fun hit => hi (hv hit)
      have := congrArg (·.erase i) huv
      simpa [erase_insert hiu, erase_insert hiv] using this
  rw [hleft, hright, add_zero]

/-- **Structural heart.** The signed sum of squared distances over all `2ⁿ`
    vertices of the box, weighted by `(-1)^{|t|}`, is identically zero whenever
    `n ≥ 2`. -/
theorem alternating_sqDist_zero (hn : 2 ≤ n) (a b P : Fin n → ℝ) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ t.card * sqDist a b P t = 0 := by
  classical
  unfold sqDist vertex
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  have hsq : ∀ t : Finset (Fin n),
      (P i - (if i ∈ t then b i else a i)) ^ 2
        = if i ∈ t then (P i - b i) ^ 2 else (P i - a i) ^ 2 := by
    intro t; split_ifs <;> rfl
  simp_rw [hsq]
  have hne : (univ.erase i).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    omega
  exact alt_sum_ite_eq_zero i hne ((P i - a i) ^ 2) ((P i - b i) ^ 2)

/-- **British Flag defect identity in `n` dimensions.** For any axis-aligned box
    with opposite corners `a, b : Fin n → ℝ` and any observer `P`, the sum of
    squared distances to the even-parity vertices equals the sum over the
    odd-parity vertices. For `n = 2` this is the classical British Flag Theorem
    `|PA|² + |PC|² = |PB|² + |PD|²`. -/
theorem british_flag_orthotope (hn : 2 ≤ n) (a b P : Fin n → ℝ) :
    ∑ t ∈ (univ : Finset (Fin n)).powerset.filter (fun t => Even t.card), sqDist a b P t
      = ∑ t ∈ (univ : Finset (Fin n)).powerset.filter (fun t => Odd t.card), sqDist a b P t := by
  classical
  have key := alternating_sqDist_zero hn a b P
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun t => Even t.card)] at key
  -- even part: sign is +1
  have heven : ∑ t ∈ (univ : Finset (Fin n)).powerset.filter (fun t => Even t.card),
        (-1 : ℝ) ^ t.card * sqDist a b P t
      = ∑ t ∈ (univ : Finset (Fin n)).powerset.filter (fun t => Even t.card), sqDist a b P t := by
    apply sum_congr rfl
    intro t ht
    rw [mem_filter] at ht
    rw [ht.2.neg_one_pow, one_mul]
  -- odd part: sign is −1
  have hodd : ∑ t ∈ (univ : Finset (Fin n)).powerset.filter (fun t => ¬ Even t.card),
        (-1 : ℝ) ^ t.card * sqDist a b P t
      = - ∑ t ∈ (univ : Finset (Fin n)).powerset.filter (fun t => Odd t.card), sqDist a b P t := by
    rw [Finset.filter_congr (fun t _ => by rw [Nat.not_even_iff_odd])]
    rw [← Finset.sum_neg_distrib]
    apply sum_congr rfl
    intro t ht
    rw [mem_filter] at ht
    rw [ht.2.neg_one_pow]
    ring
  rw [heven, hodd] at key
  linarith
