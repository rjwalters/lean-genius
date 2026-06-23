/-
Erdős Problem #1014 OQ-01: Ratio Convergence for k = 3

We prove that R(3, l+1) / R(3, l) → 1 as l → ∞, resolving the k = 3 case
of Erdős Problem #1014.

The proof uses only:
  (1) The Ramsey recurrence R(k, l+1) ≤ R(k, l) + R(k-1, l+1)
  (2) The trivial value R(2, l) = l
  (3) The Kim-Shearer lower bound R(3, l) ≥ c · l²/log l
  (4) Monotonicity R(3, l) ≤ R(3, l+1)

Key insight: The recurrence gives R(3, l+1) - R(3, l) ≤ R(2, l+1) = l + 1.
Combined with the quadratic lower bound R(3, l) ≥ c · l²/log l, the ratio
R(3, l+1)/R(3, l) - 1 ≤ (l+1)/(c · l²/log l) = O(log l / l) → 0.

Previously: 6 axioms (ramseyNumber definition + 5 properties).
Now: 1 axiom (Kim-Shearer lower bound — a deep result from Kim 1995).
The Ramsey number is defined from RamseysTheorem.lean and all basic
properties are proved from the definition.

References:
- Kim (1995): R(3, l) ≥ c · l² / log l
- Shearer (1995): Improved constant in lower bound
- Mattheus-Verstraëte (2024): R(3, t) ≥ (1/4 - o(1)) · t² / log t
- Erdős [Er71], Problem 1014
-/

import Mathlib
import Proofs.RamseysTheorem

open Real RamseysTheorem Finset Classical

namespace Erdos1014OQ01

-- ══════════════════════════════════════════════════════════════════
-- § Ramsey Number Definition
-- ══════════════════════════════════════════════════════════════════

/-- Ramsey numbers exist for r, s ≥ 1. -/
private lemma ramsey_exists (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1) :
    ∃ n, HasRamseyProperty (Fin n) r s :=
  let ⟨n, _, hn⟩ := ramsey_theorem r s hr hs; ⟨n, hn⟩

/-- The Ramsey number R(r,s): minimum n such that any 2-coloring of K_n contains
    a red r-clique or blue s-clique. Defined as 0 when r = 0 or s = 0. -/
noncomputable def ramseyNumber (r s : ℕ) : ℕ :=
  if h : r ≥ 1 ∧ s ≥ 1 then Nat.find (ramsey_exists r s h.1 h.2)
  else 0

/-- The Ramsey number satisfies the Ramsey property. -/
private theorem ramseyNumber_spec (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1) :
    HasRamseyProperty (Fin (ramseyNumber r s)) r s := by
  unfold ramseyNumber; rw [dif_pos ⟨hr, hs⟩]
  exact Nat.find_spec (ramsey_exists r s hr hs)

/-- If HasRamseyProperty holds at n, then ramseyNumber ≤ n. -/
private theorem ramseyNumber_le_of (r s n : ℕ) (hr : r ≥ 1) (hs : s ≥ 1)
    (h : HasRamseyProperty (Fin n) r s) : ramseyNumber r s ≤ n := by
  unfold ramseyNumber; rw [dif_pos ⟨hr, hs⟩]
  exact Nat.find_min' (ramsey_exists r s hr hs) h

-- ══════════════════════════════════════════════════════════════════
-- § Property 1: R(k, l) ≥ 1 for k, l ≥ 1
-- ══════════════════════════════════════════════════════════════════

/-- R(k, l) ≥ 1 for k, l ≥ 1. -/
theorem ramsey_pos (k l : ℕ) (hk : k ≥ 1) (hl : l ≥ 1) :
    ramseyNumber k l ≥ 1 := by
  by_contra h
  push_neg at h
  have h0 : ramseyNumber k l = 0 := by omega
  have hspec := ramseyNumber_spec k l hk hl
  rw [h0] at hspec
  -- HasRamseyProperty (Fin 0) k l is impossible: Fin 0 is empty, can't form any clique
  let c : EdgeColoring (Fin 0) := ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  obtain (⟨red, hred, _⟩ | ⟨blue, hblue, _⟩) := hspec c
  · have := red.card_le_univ; simp [Fintype.card_fin] at this; omega
  · have := blue.card_le_univ; simp [Fintype.card_fin] at this; omega

-- ══════════════════════════════════════════════════════════════════
-- § Property 2: Monotonicity R(k, l) ≤ R(k, l+1)
-- ══════════════════════════════════════════════════════════════════

/-- Monotonicity: R(k, l) ≤ R(k, l+1). -/
theorem ramsey_monotone_right (k l : ℕ) :
    ramseyNumber k l ≤ ramseyNumber k (l + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · show ramseyNumber 0 l ≤ ramseyNumber 0 (l + 1)
    unfold ramseyNumber; simp [show ¬((0 : ℕ) ≥ 1 ∧ l ≥ 1) from by omega,
      show ¬((0 : ℕ) ≥ 1 ∧ l + 1 ≥ 1) from by omega]
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · show ramseyNumber k 0 ≤ ramseyNumber k (0 + 1)
    unfold ramseyNumber; simp [show ¬(k ≥ 1 ∧ (0 : ℕ) ≥ 1) from by omega]; omega
  · -- Main case: k ≥ 1, l ≥ 1
    -- HasRamseyProperty (Fin (R(k,l+1))) k (l+1) holds by spec
    -- From a blue (l+1)-clique, take an l-subset to get HasRamseyProperty for k l
    apply ramseyNumber_le_of k l _ hk hl
    intro c
    obtain (⟨red, hred_card, hred⟩ | ⟨blue, hblue_card, hblue⟩) :=
      ramseyNumber_spec k (l + 1) hk (by omega) c
    · left; exact ⟨red, hred_card, hred⟩
    · right
      obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_smaller_set blue l (by omega)
      exact ⟨t, ht_card, hblue.mono (Finset.coe_subset.mpr ht_sub)⟩

-- ══════════════════════════════════════════════════════════════════
-- § Property 3: R(2, l) = l for l ≥ 1
-- ══════════════════════════════════════════════════════════════════

/-- R(2, l) = l for l ≥ 1. -/
theorem ramsey_k2 (l : ℕ) (hl : l ≥ 1) : ramseyNumber 2 l = l := by
  apply le_antisymm
  · -- Upper: R(2,l) ≤ l, from ramsey_two_s
    exact ramseyNumber_le_of 2 l l (by omega) hl (fun c => ramsey_two_s l c)
  · -- Lower: R(2,l) ≥ l. For m < l, all-blue K_m has no red 2-clique and no blue l-clique.
    by_contra hlt
    push_neg at hlt
    -- ramseyNumber 2 l < l, so HasRamseyProperty (Fin (ramseyNumber 2 l)) 2 l
    -- but all-blue coloring is a counterexample
    set m := ramseyNumber 2 l with hm_def
    have hm_lt : m < l := hlt
    have hspec := ramseyNumber_spec 2 l (by omega) hl
    -- All-blue coloring of Fin m
    let c : EdgeColoring (Fin m) := {
      color := fun _ _ => false
      symm := fun _ _ => rfl
      irrefl := fun _ => rfl
    }
    obtain (⟨red, hred_card, hred⟩ | ⟨blue, hblue_card, hblue⟩) := hspec c
    · -- Red 2-clique: impossible, all edges are blue
      have hge2 : 1 < red.card := by omega
      obtain ⟨i, hi, j, hj, hne⟩ := Finset.one_lt_card.mp hge2
      have h_adj := hred hi hj hne
      -- h_adj : c.redGraph.Adj i j, which needs c.color i j = true
      -- But c.color is constantly false
      have hfalse : c.color i j = false := rfl
      exact absurd h_adj.1 (by rw [hfalse]; decide)
    · -- Blue l-clique: impossible, Fin m has only m < l elements
      have := blue.card_le_univ; simp [Fintype.card_fin] at this; omega

-- ══════════════════════════════════════════════════════════════════
-- § Property 4: Ramsey recurrence R(k, l+1) ≤ R(k, l) + R(k-1, l+1)
-- ══════════════════════════════════════════════════════════════════

/-- Transfer a clique along an embedding. -/
private theorem transfer_red_clique {n m : ℕ} (c : EdgeColoring (Fin n))
    (embed : Fin m ↪ Fin n) (s : Finset (Fin m))
    (hs : IsRedClique
      (⟨fun i j => c.color (embed i) (embed j),
        fun i j => c.symm (embed i) (embed j),
        fun i => c.irrefl (embed i)⟩ : EdgeColoring (Fin m)) s) :
    IsRedClique c (s.map embed) := by
  unfold IsRedClique at *
  intro x hx y hy hxy
  simp only [coe_map, Set.mem_image, mem_coe] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx; obtain ⟨j, hj, rfl⟩ := hy
  have hne : i ≠ j := fun h => hxy (h ▸ rfl)
  have := hs hi hj hne
  exact ⟨this.1, hxy⟩

/-- Transfer a blue clique along an embedding. -/
private theorem transfer_blue_clique {n m : ℕ} (c : EdgeColoring (Fin n))
    (embed : Fin m ↪ Fin n) (s : Finset (Fin m))
    (hs : IsBlueClique
      (⟨fun i j => c.color (embed i) (embed j),
        fun i j => c.symm (embed i) (embed j),
        fun i => c.irrefl (embed i)⟩ : EdgeColoring (Fin m)) s) :
    IsBlueClique c (s.map embed) := by
  unfold IsBlueClique at *
  intro x hx y hy hxy
  simp only [coe_map, Set.mem_image, mem_coe] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx; obtain ⟨j, hj, rfl⟩ := hy
  have hne : i ≠ j := fun h => hxy (h ▸ rfl)
  have := hs hi hj hne
  exact ⟨this.1, hxy⟩

/-- Ramsey recurrence: R(k, l+1) ≤ R(k, l) + R(k-1, l+1). -/
theorem ramsey_recurrence (k l : ℕ) (hk : k ≥ 2) (hl : l ≥ 1) :
    ramseyNumber k (l + 1) ≤ ramseyNumber k l + ramseyNumber (k - 1) (l + 1) := by
  set n1 := ramseyNumber k l
  set n2 := ramseyNumber (k - 1) (l + 1)
  apply ramseyNumber_le_of k (l + 1) (n1 + n2) (by omega) (by omega)
  have hrp1 : HasRamseyProperty (Fin n1) k l := ramseyNumber_spec k l (by omega) hl
  have hrp2 : HasRamseyProperty (Fin n2) (k - 1) (l + 1) :=
    ramseyNumber_spec (k - 1) (l + 1) (by omega) (by omega)
  have hn1_pos : n1 ≥ 1 := ramsey_pos k l (by omega) hl
  -- Prove HasRamseyProperty (Fin (n1 + n2)) k (l+1)
  intro c
  let v : Fin (n1 + n2) := ⟨0, by omega⟩
  let Nred := redNeighborhood c v
  let Nblue := blueNeighborhood c v
  have hsum : Nred.card + Nblue.card = n1 + n2 - 1 := by
    have := neighborhood_card_sum c v
    simp [Fintype.card_fin] at this; exact this
  by_cases hred_large : Nred.card ≥ n2
  · -- Case 1: |red neighborhood| ≥ R(k-1, l+1)
    obtain ⟨embed, hembed⟩ := exists_embedding_of_card_ge Nred n2 hred_large
    let c' : EdgeColoring (Fin n2) := {
      color := fun i j => c.color (embed i) (embed j)
      symm := fun i j => c.symm (embed i) (embed j)
      irrefl := fun i => c.irrefl (embed i)
    }
    rcases hrp2 c' with ⟨red', hred_card, hred_clique⟩ | ⟨blue', hblue_card, hblue_clique⟩
    · -- Red (k-1)-clique: extend with v to get k-clique
      left
      let red := red'.map embed
      have hv_notin : v ∉ red := by
        intro hv; simp only [red, mem_map] at hv
        obtain ⟨i, _, hi_eq⟩ := hv
        have := hembed i
        simp only [Nred, redNeighborhood, mem_filter, mem_univ, true_and] at this
        exact this.2 hi_eq.symm
      have hred_sub : red ⊆ Nred := by
        intro x hx; simp only [red, mem_map] at hx
        obtain ⟨i, _, rfl⟩ := hx; exact hembed i
      use insert v red
      refine ⟨?_, extend_red_clique c v red hred_sub
        (transfer_red_clique c embed red' hred_clique) hv_notin⟩
      rw [card_insert_of_not_mem hv_notin, card_map]; omega
    · -- Blue (l+1)-clique
      right; exact ⟨blue'.map embed, by rw [card_map]; exact hblue_card,
        transfer_blue_clique c embed blue' hblue_clique⟩
  · -- Case 2: |blue neighborhood| ≥ R(k, l)
    push_neg at hred_large
    have hblue_large : Nblue.card ≥ n1 := by omega
    obtain ⟨embed, hembed⟩ := exists_embedding_of_card_ge Nblue n1 hblue_large
    let c' : EdgeColoring (Fin n1) := {
      color := fun i j => c.color (embed i) (embed j)
      symm := fun i j => c.symm (embed i) (embed j)
      irrefl := fun i => c.irrefl (embed i)
    }
    rcases hrp1 c' with ⟨red', hred_card, hred_clique⟩ | ⟨blue', hblue_card, hblue_clique⟩
    · -- Red k-clique
      left; exact ⟨red'.map embed, by rw [card_map]; exact hred_card,
        transfer_red_clique c embed red' hred_clique⟩
    · -- Blue l-clique: extend with v to get (l+1)-clique
      right
      let blue := blue'.map embed
      have hv_notin : v ∉ blue := by
        intro hv; simp only [blue, mem_map] at hv
        obtain ⟨i, _, hi_eq⟩ := hv
        have := hembed i
        simp only [Nblue, blueNeighborhood, mem_filter, mem_univ, true_and] at this
        exact this.2 hi_eq.symm
      have hblue_sub : blue ⊆ Nblue := by
        intro x hx; simp only [blue, mem_map] at hx
        obtain ⟨i, _, rfl⟩ := hx; exact hembed i
      use insert v blue
      refine ⟨?_, extend_blue_clique c v blue hblue_sub
        (transfer_blue_clique c embed blue' hblue_clique) hv_notin⟩
      rw [card_insert_of_not_mem hv_notin, card_map]; omega

-- ══════════════════════════════════════════════════════════════════
-- § Remaining Axiom: Kim-Shearer Lower Bound (deep result)
-- ══════════════════════════════════════════════════════════════════

/-- Kim (1995) / Shearer (1995): There exists c > 0 such that
    R(3, l) ≥ c · l² / log l for all sufficiently large l. -/
axiom R3_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    (ramseyNumber 3 l : ℝ) ≥ c * (l : ℝ) ^ 2 / Real.log (l : ℝ)

-- ══════════════════════════════════════════════════════════════════
-- § Step 1: Linear Increment Bound from Recurrence
-- ══════════════════════════════════════════════════════════════════

/-- The Ramsey recurrence and R(2, l) = l give a linear bound on the
    increment: R(3, l+1) ≤ R(3, l) + (l + 1). -/
theorem increment_bound (l : ℕ) (hl : l ≥ 1) :
    ramseyNumber 3 (l + 1) ≤ ramseyNumber 3 l + (l + 1) := by
  have h_rec := ramsey_recurrence 3 l (by omega) hl
  have h3 : (3 : ℕ) - 1 = 2 := by omega
  rw [h3] at h_rec
  have h_k2 := ramsey_k2 (l + 1) (by omega)
  omega

-- ══════════════════════════════════════════════════════════════════
-- § Step 2: Analysis Lemma
-- ══════════════════════════════════════════════════════════════════

/-- For any c > 0 and ε > 0, eventually (l+1) · log l / (c · l²) < ε. -/
theorem eventually_ratio_small (c : ℝ) (hc : c > 0) (ε : ℝ) (hε : ε > 0) :
    ∃ L : ℕ, ∀ l : ℕ, l > L →
      ((l : ℝ) + 1) * Real.log (l : ℝ) / (c * (l : ℝ) ^ 2) < ε := by
  have ho := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)
  have hev := ho.bound (show (0 : ℝ) < c * ε / 4 by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  use ⌈N⌉₊ + 1
  intro l hl
  have hl1 : 1 < l := by omega
  have hl_pos : (0 : ℝ) < (l : ℝ) := by positivity
  have hlog_pos : 0 < Real.log (l : ℝ) := Real.log_pos (by exact_mod_cast hl1)
  have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (show 2 ≤ l by omega)
  have hl_ge_N : N ≤ (l : ℝ) := le_trans (Nat.le_ceil N) (by exact_mod_cast (show ⌈N⌉₊ ≤ l by omega))
  have hb := hN (l : ℝ) hl_ge_N
  rw [rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog_pos,
      abs_of_pos hl_pos] at hb
  have h_num : ((l : ℝ) + 1) * Real.log (l : ℝ) ≤
               ε / 2 * (c * (l : ℝ) ^ 2) :=
    calc ((l : ℝ) + 1) * Real.log (l : ℝ)
        ≤ (2 * (l : ℝ)) * Real.log (l : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hlog_pos)
      _ ≤ (2 * (l : ℝ)) * (c * ε / 4 * (l : ℝ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ε / 2 * (c * (l : ℝ) ^ 2) := by ring
  have hd : (0 : ℝ) < c * (l : ℝ) ^ 2 := by positivity
  calc ((l : ℝ) + 1) * Real.log (l : ℝ) / (c * (l : ℝ) ^ 2)
      ≤ ε / 2 := (div_le_iff₀ hd).mpr h_num
    _ < ε := by linarith

-- ══════════════════════════════════════════════════════════════════
-- § Main Theorem
-- ══════════════════════════════════════════════════════════════════

/-- **Erdős Problem #1014 for k = 3**: R(3, l+1) / R(3, l) → 1 as l → ∞. -/
theorem erdos_1014_k3_ratio_convergence :
    ∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
      |(ramseyNumber 3 (l + 1) : ℝ) / (ramseyNumber 3 l : ℝ) - 1| < ε := by
  intro ε hε
  obtain ⟨c, hc, L₁, hL₁⟩ := R3_lower_bound
  obtain ⟨L₂, hL₂⟩ := eventually_ratio_small c hc ε hε
  use max (max L₁ L₂) 2
  intro l hl
  have hl1 : l > L₁ := by omega
  have hl2 : l > L₂ := by omega
  have hl_ge1 : l ≥ 1 := by omega
  set R := (ramseyNumber 3 l : ℝ) with hR_def
  set R' := (ramseyNumber 3 (l + 1) : ℝ) with hR'_def
  have hR_pos : R > 0 := by
    simp only [hR_def]
    have := ramsey_pos 3 l (by omega) hl_ge1
    exact_mod_cast (show 0 < ramseyNumber 3 l by omega)
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have hmon : R ≤ R' := by
    simp only [hR_def, hR'_def]
    exact Nat.cast_le.mpr (ramsey_monotone_right 3 l)
  have h_diff : R' - R ≤ (l : ℝ) + 1 := by
    simp only [hR_def, hR'_def]
    have h := increment_bound l hl_ge1
    have : (ramseyNumber 3 (l + 1) : ℝ) ≤ (ramseyNumber 3 l : ℝ) + ((l : ℝ) + 1) := by
      exact_mod_cast h
    linarith
  have h_abs : |R' / R - 1| = (R' - R) / R := by
    have h_eq : R' / R - 1 = (R' - R) / R := by field_simp
    rw [abs_of_nonneg]
    · exact h_eq
    · rw [h_eq]; exact div_nonneg (by linarith) (by linarith)
  rw [h_abs]
  have hlog : Real.log (l : ℝ) > 0 := by
    apply Real.log_pos
    exact_mod_cast (show (1 : ℕ) < l by omega)
  have hlb := hL₁ l hl1
  have hcl_pos : c * (l : ℝ) ^ 2 / Real.log (l : ℝ) > 0 := by positivity
  calc (R' - R) / R
      ≤ ((l : ℝ) + 1) / R := by
        apply div_le_div_of_nonneg_right h_diff (le_of_lt hR_pos)
    _ ≤ ((l : ℝ) + 1) / (c * (l : ℝ) ^ 2 / Real.log (l : ℝ)) := by
        apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (l : ℝ) + 1) hcl_pos
        exact hlb
    _ = ((l : ℝ) + 1) * Real.log (l : ℝ) / (c * (l : ℝ) ^ 2) := by
        rw [div_div_eq_mul_div]
    _ < ε := hL₂ l hl2

end Erdos1014OQ01
