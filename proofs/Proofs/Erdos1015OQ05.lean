/-
  Erdős Problem #1015 Open Question #5:
  Can Any of the 8 Axioms Be Proved from Mathlib?

  We prove two axioms from the parent file Erdos1015Problem.lean:

  1. **ramseyNumber** (axiomatized function ℕ → ℕ → ℕ):
     Replaced with a proper definition via Nat.find using the Ramsey existence
     theorem from RamseysTheorem.lean.

  2. **ramsey_upper_bound** (R(t,t) ≤ 4^t):
     Proved via the Erdős-Szekeres bound R(r,s) ≤ C(r+s-2, r-1) combined
     with the binomial coefficient inequality C(n, k) ≤ 2^n.

  The remaining 6 axioms are deep mathematical results:
  - moon_f3, moon_f3_n: Moon (1966), specific combinatorial analysis
  - erdos_ramsey_bound: Erdős, connects f(t) to R(t,t)
  - burr_erdos_spencer: BES (1975), exact formula for f(t)
  - f_root_limit: Asymptotic analysis of f(t)^{1/t}
  - f_not_linear: Superlinear growth of f(t)

  These all require either deep Ramsey lower bounds, specific graph constructions,
  or the full BES argument, none of which are in Mathlib.

  Result: 8 axioms → 6 axioms (2 eliminated)

  Tags: graph-theory, ramsey-theory, combinatorics, axiom-elimination
-/

import Mathlib
import Proofs.RamseysTheorem

namespace Erdos1015OQ05

open RamseysTheorem Finset

-- ══════════════════════════════════════════════════════════════════
-- § 1. Ramsey Number: Proper Definition
-- ══════════════════════════════════════════════════════════════════

/-- Ramsey numbers exist for r, s ≥ 1 (from RamseysTheorem). -/
private lemma ramsey_exists (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1) :
    ∃ n, HasRamseyProperty (Fin n) r s :=
  let ⟨n, _, hn⟩ := ramsey_theorem r s hr hs; ⟨n, hn⟩

/-- The Ramsey number R(r,s): minimum n such that any 2-coloring of K_n contains
    a red r-clique or blue s-clique. Defined as 0 when r = 0 or s = 0. -/
noncomputable def ramseyNumber (r s : ℕ) : ℕ :=
  if h : r ≥ 1 ∧ s ≥ 1 then Nat.find (ramsey_exists r s h.1 h.2)
  else 0

/-- The Ramsey number satisfies the Ramsey property. -/
theorem ramseyNumber_spec (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1) :
    HasRamseyProperty (Fin (ramseyNumber r s)) r s := by
  unfold ramseyNumber; rw [dif_pos ⟨hr, hs⟩]
  exact Nat.find_spec (ramsey_exists r s hr hs)

/-- If HasRamseyProperty holds at n, then ramseyNumber ≤ n. -/
theorem ramseyNumber_le_of (r s n : ℕ) (hr : r ≥ 1) (hs : s ≥ 1)
    (h : HasRamseyProperty (Fin n) r s) : ramseyNumber r s ≤ n := by
  unfold ramseyNumber; rw [dif_pos ⟨hr, hs⟩]
  exact Nat.find_min' (ramsey_exists r s hr hs) h

-- ══════════════════════════════════════════════════════════════════
-- § 2. HasRamseyProperty Monotonicity
-- ══════════════════════════════════════════════════════════════════

/-- HasRamseyProperty is monotone: if it holds at n, it holds at any m ≥ n. -/
theorem HasRamseyProperty_mono (r s : ℕ) {n m : ℕ} (hnm : n ≤ m)
    (h : HasRamseyProperty (Fin n) r s) : HasRamseyProperty (Fin m) r s := by
  intro c
  -- Get embedding of Fin n into Fin m
  obtain ⟨embed, hembed⟩ := exists_embedding_of_card_ge (Finset.univ : Finset (Fin m)) n
    (by simp [Fintype.card_fin]; exact hnm)
  -- Restrict coloring to Fin n
  let c' : EdgeColoring (Fin n) := {
    color := fun i j => c.color (embed i) (embed j)
    symm := fun i j => c.symm (embed i) (embed j)
    irrefl := fun i => c.irrefl (embed i)
  }
  rcases h c' with ⟨red, hred_card, hred_clique⟩ | ⟨blue, hblue_card, hblue_clique⟩
  · -- Transfer red clique
    left
    use red.map embed
    refine ⟨by simp [card_map]; exact hred_card, ?_⟩
    intro x hx y hy hxy
    simp only [coe_map, Set.mem_image, mem_coe] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx; obtain ⟨j, hj, rfl⟩ := hy
    have hne : i ≠ j := fun heq => hxy (heq ▸ rfl)
    have := hred_clique hi hj hne
    exact ⟨this.1, hxy⟩
  · -- Transfer blue clique
    right
    use blue.map embed
    refine ⟨by simp [card_map]; exact hblue_card, ?_⟩
    intro x hx y hy hxy
    simp only [coe_map, Set.mem_image, mem_coe] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx; obtain ⟨j, hj, rfl⟩ := hy
    have hne : i ≠ j := fun heq => hxy (heq ▸ rfl)
    have := hblue_clique hi hj hne
    exact ⟨this.1, hxy⟩

-- ══════════════════════════════════════════════════════════════════
-- § 3. Erdős-Szekeres Bound: R(r,s) ≤ C(r+s-2, r-1)
-- ══════════════════════════════════════════════════════════════════

/-- The pigeonhole step: from HasRamseyProperty at n₁ for (r-1,s) and
    at n₂ for (r,s-1), deduce HasRamseyProperty at (n₁+n₂) for (r,s).
    This is the key inductive step of the Erdős-Szekeres proof. -/
theorem HasRamseyProperty_of_add {r s n₁ n₂ : ℕ} (hr : r ≥ 2) (hs : s ≥ 2)
    (h1 : HasRamseyProperty (Fin n₁) (r - 1) s)
    (h2 : HasRamseyProperty (Fin n₂) r (s - 1)) :
    HasRamseyProperty (Fin (n₁ + n₂)) r s := by
  -- Derive n₁ > 0 from h1 (HasRamseyProperty (Fin 0) for nontrivial params is false)
  have hn1_pos : 0 < n₁ := by
    by_contra h; push_neg at h; interval_cases n₁
    let c0 : EdgeColoring (Fin 0) :=
      ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    rcases h1 c0 with ⟨red, hred_card, _⟩ | ⟨blue, hblue_card, _⟩
    · have := red.card_le_univ; simp [Fintype.card_fin] at this; omega
    · have := blue.card_le_univ; simp [Fintype.card_fin] at this; omega
  intro c
  -- Pick vertex 0
  let v : Fin (n₁ + n₂) := ⟨0, by omega⟩
  let Nred := redNeighborhood c v
  let Nblue := blueNeighborhood c v
  have hsum : Nred.card + Nblue.card = n₁ + n₂ - 1 := by
    have := neighborhood_card_sum c v
    simp [Fintype.card_fin] at this; exact this
  -- Pigeonhole: |Nred| ≥ n₁ or |Nblue| ≥ n₂
  by_cases hred_large : Nred.card ≥ n₁
  · -- Case 1: Red neighborhood ≥ n₁, find (r-1)-red or s-blue clique inside
    obtain ⟨embed, hembed⟩ := exists_embedding_of_card_ge Nred n₁ hred_large
    let c' : EdgeColoring (Fin n₁) := {
      color := fun i j => c.color (embed i) (embed j)
      symm := fun i j => c.symm (embed i) (embed j)
      irrefl := fun i => c.irrefl (embed i)
    }
    rcases h1 c' with ⟨red', hred_card, hred_clique⟩ | ⟨blue', hblue_card, hblue_clique⟩
    · -- Found (r-1)-red clique, extend with v to get r-red clique
      left
      let red := red'.map embed
      have hv_notin : v ∉ red := by
        intro hv; simp only [red, mem_map] at hv
        obtain ⟨i, _, hi_eq⟩ := hv
        have hvi := hembed i
        simp only [Nred, redNeighborhood, mem_filter, mem_univ, true_and] at hvi
        exact hvi.2 hi_eq.symm
      have hred_sub : red ⊆ Nred := by
        intro x hx; simp only [red, mem_map] at hx
        obtain ⟨i, _, rfl⟩ := hx; exact hembed i
      have hred_is_clique : IsRedClique c red := by
        intro x hx y hy hxy
        simp only [red, coe_map, Set.mem_image, mem_coe] at hx hy
        obtain ⟨i, hi, rfl⟩ := hx; obtain ⟨j, hj, rfl⟩ := hy
        have hne : i ≠ j := fun h => hxy (h ▸ rfl)
        have := hred_clique hi hj hne
        exact ⟨this.1, hxy⟩
      use insert v red
      constructor
      · rw [card_insert_of_not_mem hv_notin, card_map]; omega
      · exact extend_red_clique c v red hred_sub hred_is_clique hv_notin
    · -- Found s-blue clique, transfer back
      right
      use blue'.map embed
      refine ⟨by simp [card_map]; exact hblue_card, ?_⟩
      intro x hx y hy hxy
      simp only [coe_map, Set.mem_image, mem_coe] at hx hy
      obtain ⟨i, hi, rfl⟩ := hx; obtain ⟨j, hj, rfl⟩ := hy
      have hne : i ≠ j := fun h => hxy (h ▸ rfl)
      have := hblue_clique hi hj hne
      exact ⟨this.1, hxy⟩
  · -- Case 2: Blue neighborhood ≥ n₂
    push_neg at hred_large
    have hblue_large : Nblue.card ≥ n₂ := by omega
    obtain ⟨embed, hembed⟩ := exists_embedding_of_card_ge Nblue n₂ hblue_large
    let c' : EdgeColoring (Fin n₂) := {
      color := fun i j => c.color (embed i) (embed j)
      symm := fun i j => c.symm (embed i) (embed j)
      irrefl := fun i => c.irrefl (embed i)
    }
    rcases h2 c' with ⟨red', hred_card, hred_clique⟩ | ⟨blue', hblue_card, hblue_clique⟩
    · -- Found r-red clique, transfer back
      left
      use red'.map embed
      refine ⟨by simp [card_map]; exact hred_card, ?_⟩
      intro x hx y hy hxy
      simp only [coe_map, Set.mem_image, mem_coe] at hx hy
      obtain ⟨i, hi, rfl⟩ := hx; obtain ⟨j, hj, rfl⟩ := hy
      have hne : i ≠ j := fun h => hxy (h ▸ rfl)
      have := hred_clique hi hj hne
      exact ⟨this.1, hxy⟩
    · -- Found (s-1)-blue clique, extend with v to get s-blue clique
      right
      let blue := blue'.map embed
      have hv_notin : v ∉ blue := by
        intro hv; simp only [blue, mem_map] at hv
        obtain ⟨i, _, hi_eq⟩ := hv
        have hvi := hembed i
        simp only [Nblue, blueNeighborhood, mem_filter, mem_univ, true_and] at hvi
        exact hvi.2 hi_eq.symm
      have hblue_sub : blue ⊆ Nblue := by
        intro x hx; simp only [blue, mem_map] at hx
        obtain ⟨i, _, rfl⟩ := hx; exact hembed i
      have hblue_is_clique : IsBlueClique c blue := by
        intro x hx y hy hxy
        simp only [blue, coe_map, Set.mem_image, mem_coe] at hx hy
        obtain ⟨i, hi, rfl⟩ := hx; obtain ⟨j, hj, rfl⟩ := hy
        have hne : i ≠ j := fun h => hxy (h ▸ rfl)
        have := hblue_clique hi hj hne
        exact ⟨this.1, hxy⟩
      use insert v blue
      constructor
      · rw [card_insert_of_not_mem hv_notin, card_map]; omega
      · exact extend_blue_clique c v blue hblue_sub hblue_is_clique hv_notin

/-- Pascal's rule for ramseyBound: C(r+s, r) = C(r+s-1, r-1) + C(r+s-1, r).
    Equivalently, ramseyBound (r+2) (s+2) = ramseyBound (r+1) (s+2) + ramseyBound (r+2) (s+1). -/
theorem ramseyBound_pascal (r s : ℕ) :
    ramseyBound (r + 2) (s + 2) = ramseyBound (r + 1) (s + 2) + ramseyBound (r + 2) (s + 1) := by
  unfold ramseyBound
  rw [if_neg (show ¬(r + 2 = 0 ∨ s + 2 = 0) from by omega),
      if_neg (show ¬(r + 1 = 0 ∨ s + 2 = 0) from by omega),
      if_neg (show ¬(r + 2 = 0 ∨ s + 1 = 0) from by omega)]
  -- C(r+s+2, r+1) = C(r+s+1, r) + C(r+s+1, r+1)
  have h1 : (r + 2) + (s + 2) - 2 = r + s + 2 := by omega
  have h2 : (r + 2) - 1 = r + 1 := by omega
  have h3 : (r + 1) + (s + 2) - 2 = r + s + 1 := by omega
  have h4 : (r + 1) - 1 = r := by omega
  have h5 : (r + 2) + (s + 1) - 2 = r + s + 1 := by omega
  rw [h1, h2, h3, h4, h5]
  exact (Nat.choose_succ_succ (r + s + 1) r).symm

/-- **Erdős-Szekeres Bound**: HasRamseyProperty holds at the binomial coefficient bound. -/
theorem ramseyBound_HasRamseyProperty (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1) :
    HasRamseyProperty (Fin (ramseyBound r s)) r s := by
  -- By strong induction on r + s
  induction' hk : r + s using Nat.strong_induction_on with k ih generalizing r s
  match r, s with
  | 0, _ => omega
  | _, 0 => omega
  | 1, s + 1 =>
    -- ramseyBound 1 (s+1) = C(s, 0) = 1
    have hb : ramseyBound 1 (s + 1) = 1 := by
      unfold ramseyBound
      rw [if_neg (show ¬(1 = 0 ∨ s + 1 = 0) from by omega)]
      simp [Nat.choose_zero_right]
    rw [hb]
    exact ramsey_one_left (s + 1)
  | r + 2, 1 =>
    -- ramseyBound (r+2) 1 = C(r+1, r+1) = 1
    have hb : ramseyBound (r + 2) 1 = 1 := by
      unfold ramseyBound
      rw [if_neg (show ¬(r + 2 = 0 ∨ 1 = 0) from by omega)]
      have : (r + 2) + 1 - 2 = r + 1 := by omega
      have : (r + 2) - 1 = r + 1 := by omega
      rw [‹(r + 2) + 1 - 2 = r + 1›, ‹(r + 2) - 1 = r + 1›]
      exact Nat.choose_self (r + 1)
    rw [hb]
    exact ramsey_one_right (r + 2)
  | r + 2, s + 2 =>
    -- Inductive case using Pascal's rule
    rw [ramseyBound_pascal r s]
    have hlt1 : (r + 1) + (s + 2) < k := by omega
    have hlt2 : (r + 2) + (s + 1) < k := by omega
    have ih1 := ih ((r + 1) + (s + 2)) hlt1 (r + 1) (s + 2) (by omega) (by omega) rfl
    have ih2 := ih ((r + 2) + (s + 1)) hlt2 (r + 2) (s + 1) (by omega) (by omega) rfl
    apply HasRamseyProperty_of_add (by omega) (by omega)
    · -- Need: HasRamseyProperty ... ((r+2)-1) (s+2) = ... (r+1) (s+2)
      show HasRamseyProperty (Fin (ramseyBound (r + 1) (s + 2))) ((r + 2) - 1) (s + 2)
      simp only [show (r + 2) - 1 = r + 1 from by omega]
      exact ih1
    · -- Need: HasRamseyProperty ... (r+2) ((s+2)-1) = ... (r+2) (s+1)
      show HasRamseyProperty (Fin (ramseyBound (r + 2) (s + 1))) (r + 2) ((s + 2) - 1)
      simp only [show (s + 2) - 1 = s + 1 from by omega]
      exact ih2

/-- R(r,s) ≤ C(r+s-2, r-1) for r, s ≥ 1. -/
theorem ramseyNumber_le_ramseyBound (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1) :
    ramseyNumber r s ≤ ramseyBound r s :=
  ramseyNumber_le_of r s (ramseyBound r s) hr hs (ramseyBound_HasRamseyProperty r s hr hs)

-- ══════════════════════════════════════════════════════════════════
-- § 4. R(t,t) ≤ 4^t
-- ══════════════════════════════════════════════════════════════════

/-- C(n, k) ≤ 2^n for all n, k. -/
private theorem choose_le_two_pow (n k : ℕ) : Nat.choose n k ≤ 2 ^ n := by
  by_cases h : k ≤ n
  · calc Nat.choose n k
        ≤ ∑ i ∈ Finset.range (n + 1), Nat.choose n i :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      _ = 2 ^ n := Nat.sum_range_choose n
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

/-- ramseyBound t t ≤ 4^t for t ≥ 1. -/
theorem ramseyBound_le_four_pow (t : ℕ) (ht : t ≥ 1) : ramseyBound t t ≤ 4 ^ t := by
  -- ramseyBound t t = C(2t-2, t-1) ≤ 2^(2t-2) = 4^(t-1) ≤ 4^t
  unfold ramseyBound
  rw [if_neg (show ¬(t = 0 ∨ t = 0) from by omega)]
  have h2t : t + t - 2 = 2 * (t - 1) := by omega
  calc Nat.choose (t + t - 2) (t - 1)
      ≤ 2 ^ (t + t - 2) := choose_le_two_pow _ _
    _ = 2 ^ (2 * (t - 1)) := by rw [h2t]
    _ = (2 ^ 2) ^ (t - 1) := by rw [pow_mul]
    _ = 4 ^ (t - 1) := by norm_num
    _ ≤ 4 ^ t := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le t 1)

/-- **R(t,t) ≤ 4^t** (Erdős-Szekeres).
    This eliminates the `ramsey_upper_bound` axiom from Erdos1015Problem.lean. -/
theorem ramsey_upper_bound (t : ℕ) (ht : t ≥ 1) : ramseyNumber t t ≤ 4 ^ t :=
  le_trans (ramseyNumber_le_ramseyBound t t ht ht) (ramseyBound_le_four_pow t ht)

/-- For t = 0, the bound holds trivially. -/
theorem ramsey_upper_bound_zero : ramseyNumber 0 0 ≤ 4 ^ 0 := by
  simp [ramseyNumber, show ¬((0 : ℕ) ≥ 1 ∧ (0 : ℕ) ≥ 1) from by omega]

/-- Universal version: R(t,t) ≤ 4^t for all t. -/
theorem ramsey_upper_bound_all (t : ℕ) : ramseyNumber t t ≤ 4 ^ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact ramsey_upper_bound_zero
  · exact ramsey_upper_bound t ht

-- ══════════════════════════════════════════════════════════════════
-- § 5. Summary and Remaining Axioms
-- ══════════════════════════════════════════════════════════════════

/-
  ## Axiom Elimination Summary

  Original Erdos1015Problem.lean has 8 axioms:

  | # | Axiom              | Status      | Reason                                          |
  |---|-------------------|-------------|--------------------------------------------------|
  | 1 | ramseyNumber      | ELIMINATED  | Defined via Nat.find (§1)                        |
  | 2 | ramsey_upper_bound| ELIMINATED  | Proved: R(r,s) ≤ C(r+s-2,r-1) ≤ 4^t (§4)       |
  | 3 | moon_f3           | REMAINS     | Deep result: specific graph analysis              |
  | 4 | moon_f3_n         | REMAINS     | Deep result: extension of Moon (1966)             |
  | 5 | erdos_ramsey_bound| REMAINS     | Connects f(t) to R(t,t); needs f(t) analysis     |
  | 6 | burr_erdos_spencer| REMAINS     | Full BES (1975) argument                          |
  | 7 | f_root_limit      | REMAINS     | Asymptotic analysis requiring Ramsey lower bounds |
  | 8 | f_not_linear      | REMAINS     | Needs superlinear lower bound on R(t,t-1)         |

  Reduction: 8 axioms → 6 axioms
-/

#check ramseyNumber
#check ramsey_upper_bound_all
#check ramseyBound_HasRamseyProperty
#check ramseyNumber_le_ramseyBound

end Erdos1015OQ05
