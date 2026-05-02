/-
# Hook-Length Formula for Standard Young Tableaux via LGV

## Problem: ballot-problem-oq-03-oq-01-oq-02

Formalizes the hook-length formula f^λ = n!/∏h(u) for Standard Young Tableaux
using the n×n LGV infrastructure from BallotProblemOQ03OQ02.

### Hook-Length Formula (Frame-Robinson-Thrall 1954)
For a Young diagram μ with n cells, the number of Standard Young Tableaux of
shape μ satisfies:

  card(SYT(μ)) × ∏_{u ∈ μ} h(u) = n!

where h(u) = arm(u) + leg(u) + 1 is the hook length at cell u.

### Strategy
Two-step LGV proof:
1. SYT(μ) ↔ non-intersecting lattice path tuples (Fomin/RSK bijection) [open]
2. LGV determinant = n! / hookProd μ (det factorization identity) [open]

### Progress
- hookLength, hookProd, StandardYoungTableau: defined
- hookLength_pos, hookLength_add_eq: proved
- instFintypeSYT: Fintype instance for SYT (makes Fintype.card typecheck)
- hook_length_formula_bot: proved for empty diagram
- youngLGVConfig: LGV encoding with well-formedness proved
- hook_length_formula_from_chain: conditional theorem from h_ni_syt + h_det_hook
- hook_length_formula_general: PROVED via corner recursion + hook_walk_identity
  (the main theorem is established via this corner-recursion path; the LGV
   route below remains open)

### Status
- Main theorem `hook_length_formula` is proved modulo a single remaining sorry in
  `hook_walk_identity` (the ≥10×≥10 non-rectangular case; ~300-line GNW argument).
- The alternate LGV proof path remains open. See the OPEN comment block in PART V
  for the canonical-config restatement that future work should target.
-/

import Proofs.BallotProblemOQ03OQ01OQ02Helpers

namespace HookLengthFormula

open YoungDiagram Finset LGV

-- ============================================================
-- PART XXV: Hook Walk Identity for Rectangular Young Diagrams
-- ============================================================
-- k×a rectangles have exactly ONE corner (k-1, a-1).  The sum reduces to a
-- single ratio = k*a = card(rect).  Proved by hookProd_ratio_formula +
-- telescoping products for arm and leg directions (non-circular).

/-- The k×a rectangular Young diagram: all cells (i,j) with i < k and j < a. -/
private def rectYD (k a : ℕ) : YoungDiagram where
  cells := (Finset.range k).biUnion (fun i => (Finset.range a).image (Prod.mk i))
  isLowerSet := by
    intro ⟨i', j'⟩ ⟨i, j⟩ h hmem
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
               Prod.mk.injEq] at hmem ⊢
    obtain ⟨r, hr, c, hc, h1, h2⟩ := hmem
    have h12 := Prod.mk_le_mk.mp h
    exact ⟨i', h12.1.trans_lt (h1 ▸ hr), j', h12.2.trans_lt (h2 ▸ hc), rfl, rfl⟩

private lemma mem_rectYD {k a i j : ℕ} : (i, j) ∈ rectYD k a ↔ i < k ∧ j < a := by
  simp only [YoungDiagram.mem_cells, rectYD, Finset.mem_biUnion, Finset.mem_range,
             Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨r, hr, c, hc, rfl, rfl⟩; exact ⟨hr, hc⟩
  · rintro ⟨hi, hj⟩; exact ⟨i, hi, j, hj, rfl, rfl⟩

private lemma rowLen_rectYD {k a : ℕ} {i : ℕ} (hi : i < k) : (rectYD k a).rowLen i = a := by
  apply Nat.le_antisymm
  · by_contra h
    push_neg at h
    have := YoungDiagram.mem_iff_lt_rowLen.mpr h
    rw [mem_rectYD] at this
    exact Nat.lt_irrefl a this.2
  · cases Nat.eq_zero_or_pos a with
    | inl h => simp [h]
    | inr h =>
      have := YoungDiagram.mem_iff_lt_rowLen.mp (mem_rectYD.mpr ⟨hi, Nat.sub_lt h one_pos⟩)
      omega

private lemma colLen_rectYD {k a : ℕ} {j : ℕ} (hj : j < a) : (rectYD k a).colLen j = k := by
  apply Nat.le_antisymm
  · by_contra h
    push_neg at h
    have := YoungDiagram.mem_iff_lt_colLen.mpr h
    rw [mem_rectYD] at this
    exact Nat.lt_irrefl k this.1
  · cases Nat.eq_zero_or_pos k with
    | inl h => simp [h]
    | inr h =>
      have := YoungDiagram.mem_iff_lt_colLen.mp (mem_rectYD.mpr ⟨Nat.sub_lt h one_pos, hj⟩)
      omega

private lemma card_rectYD (k a : ℕ) : (rectYD k a).card = k * a := by
  unfold YoungDiagram.card
  suffices h : (rectYD k a).cells = Finset.range k ×ˢ Finset.range a by
    rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
  ext ⟨i, j⟩
  simp [YoungDiagram.mem_cells, mem_rectYD, Finset.mem_product, Finset.mem_range]

private lemma hookLength_rectYD_lastrow {k a : ℕ} (hk : 0 < k) {s : ℕ} (hs : s < a) :
    hookLength (rectYD k a) (k - 1) s = a - s := by
  have hcell : (k - 1, s) ∈ rectYD k a := mem_rectYD.mpr ⟨Nat.sub_lt hk one_pos, hs⟩
  have heq := hookLength_add_eq (rectYD k a) hcell
  simp only [Prod.fst, Prod.snd] at heq
  rw [rowLen_rectYD (Nat.sub_lt hk one_pos), colLen_rectYD hs] at heq
  omega

private lemma hookLength_rectYD_lastcol {k a : ℕ} (ha : 0 < a) {r : ℕ} (hr : r < k) :
    hookLength (rectYD k a) r (a - 1) = k - r := by
  have hcell : (r, a - 1) ∈ rectYD k a := mem_rectYD.mpr ⟨hr, Nat.sub_lt ha one_pos⟩
  have heq := hookLength_add_eq (rectYD k a) hcell
  simp only [Prod.fst, Prod.snd] at heq
  rw [rowLen_rectYD hr, colLen_rectYD (Nat.sub_lt ha one_pos)] at heq
  omega

private lemma isCorner_rectYD {k a : ℕ} (hk : 0 < k) (ha : 0 < a) :
    isCorner (rectYD k a) (k - 1, a - 1) :=
  ⟨mem_rectYD.mpr ⟨Nat.sub_lt hk one_pos, Nat.sub_lt ha one_pos⟩,
   by simp only [Prod.fst, Prod.snd, mem_rectYD, not_and]; intro _; omega,
   by simp only [Prod.fst, Prod.snd, mem_rectYD, not_and]; intro _; omega⟩

private lemma corners_rectYD_singleton {k a : ℕ} (hk : 0 < k) (ha : 0 < a) :
    corners (rectYD k a) = {(k - 1, a - 1)} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨mem_corners.mpr (isCorner_rectYD hk ha), fun ⟨i, j⟩ hc => ?_⟩
  rw [mem_corners] at hc
  obtain ⟨hmem, hright, hbelow⟩ := hc
  simp only [Prod.fst, Prod.snd] at hright hbelow
  obtain ⟨hi, hj⟩ := mem_rectYD.mp hmem
  have hj_eq : j = a - 1 := by
    by_contra h; exact hright (mem_rectYD.mpr ⟨hi, by omega⟩)
  have hi_eq : i = k - 1 := by
    by_contra h; exact hbelow (mem_rectYD.mpr ⟨by omega, hj⟩)
  simp [Finset.mem_singleton, hi_eq, hj_eq]

/-- Telescoping product: ∏_{s<n} (m+1-s)/(m-s) = (m+1)/(m+1-n) for n ≤ m. -/
private lemma prod_telescope_gen (m n : ℕ) (h : n ≤ m) :
    ∏ s ∈ Finset.range n, ((↑(m + 1 - s) : ℚ) / ↑(m - s)) = (↑m + 1) / (↑m + 1 - ↑n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ m := Nat.le_of_succ_le h
    have hk_lt : k < m := Nat.lt_of_succ_le h
    rw [Finset.prod_range_succ, ih hk,
        show (↑(m + 1 - k) : ℚ) = ↑m + 1 - ↑k from by
          rw [Nat.cast_sub (by omega : k ≤ m + 1)]; push_cast; ring,
        show (↑(m - k) : ℚ) = ↑m - ↑k from Nat.cast_sub hk,
        show (↑m + 1 - ↑(k + 1 : ℕ) : ℚ) = ↑m - ↑k from by push_cast; ring]
    have ne1 : (↑m + 1 - (↑k : ℚ)) ≠ 0 := by
      have : (k : ℚ) < ↑m + 1 := by exact_mod_cast Nat.lt_succ_of_le hk
      linarith
    have ne2 : (↑m - (↑k : ℚ)) ≠ 0 := by
      have : (k : ℚ) < ↑m := by exact_mod_cast hk_lt
      linarith
    field_simp [ne1, ne2]; ring

/-- Arm product for rectYD: telescoping over last row gives a. -/
private lemma arm_prod_rectYD {k a : ℕ} (hk : 0 < k) (ha : 1 ≤ a) :
    ∏ s ∈ Finset.range (a - 1),
      ((hookLength (rectYD k a) (k - 1) s : ℚ) / (hookLength (rectYD k a) (k - 1) s - 1))
    = (a : ℚ) := by
  -- Step 1: substitute hookLength = a - s
  have step1 : ∏ s ∈ Finset.range (a - 1),
      ((hookLength (rectYD k a) (k - 1) s : ℚ) / (hookLength (rectYD k a) (k - 1) s - 1)) =
      ∏ s ∈ Finset.range (a - 1), ((↑(a - s) : ℚ) / (↑(a - s) - 1)) := by
    apply Finset.prod_congr rfl; intro s hs
    rw [Finset.mem_range] at hs
    rw [hookLength_rectYD_lastrow hk (by omega)]
  rw [step1]
  -- Step 2: rewrite denominators ↑(a-s)-1 = ↑(a-1-s)
  have step2 : ∏ s ∈ Finset.range (a - 1), ((↑(a - s) : ℚ) / (↑(a - s) - 1)) =
      ∏ s ∈ Finset.range (a - 1), ((↑(a - 1 + 1 - s) : ℚ) / ↑(a - 1 - s)) := by
    apply Finset.prod_congr rfl; intro s hs
    rw [Finset.mem_range] at hs
    congr 1
    · congr 1; omega
    · have h1 : (a - 1 - s : ℕ) + 1 = a - s := by omega
      have h2 : (↑(a - 1 - s) : ℚ) + 1 = ↑(a - s) := by exact_mod_cast h1
      linarith
  rw [step2, prod_telescope_gen (a - 1) (a - 1) le_rfl]
  have ha1 : (↑(a - 1) : ℚ) + 1 = ↑a := by exact_mod_cast Nat.sub_add_cancel ha
  rw [show (↑(a - 1) : ℚ) + 1 - ↑(a - 1) = 1 from by ring, div_one, ha1]

/-- Leg product for rectYD: telescoping over last col gives k. -/
private lemma leg_prod_rectYD {k a : ℕ} (hk : 1 ≤ k) (ha : 0 < a) :
    ∏ r ∈ Finset.range (k - 1),
      ((hookLength (rectYD k a) r (a - 1) : ℚ) / (hookLength (rectYD k a) r (a - 1) - 1))
    = (k : ℚ) := by
  have step1 : ∏ r ∈ Finset.range (k - 1),
      ((hookLength (rectYD k a) r (a - 1) : ℚ) / (hookLength (rectYD k a) r (a - 1) - 1)) =
      ∏ r ∈ Finset.range (k - 1), ((↑(k - r) : ℚ) / (↑(k - r) - 1)) := by
    apply Finset.prod_congr rfl; intro r hr
    rw [Finset.mem_range] at hr
    rw [hookLength_rectYD_lastcol ha (by omega)]
  rw [step1]
  have step2 : ∏ r ∈ Finset.range (k - 1), ((↑(k - r) : ℚ) / (↑(k - r) - 1)) =
      ∏ r ∈ Finset.range (k - 1), ((↑(k - 1 + 1 - r) : ℚ) / ↑(k - 1 - r)) := by
    apply Finset.prod_congr rfl; intro r hr
    rw [Finset.mem_range] at hr
    congr 1
    · congr 1; omega
    · have h1 : (k - 1 - r : ℕ) + 1 = k - r := by omega
      have h2 : (↑(k - 1 - r) : ℚ) + 1 = ↑(k - r) := by exact_mod_cast h1
      linarith
  rw [step2, prod_telescope_gen (k - 1) (k - 1) le_rfl]
  have hk1 : (↑(k - 1) : ℚ) + 1 = ↑k := by exact_mod_cast Nat.sub_add_cancel hk
  rw [show (↑(k - 1) : ℚ) + 1 - ↑(k - 1) = 1 from by ring, div_one, hk1]

/-- Hook walk identity for rectangular Young diagrams k×a.
    Proved directly by hookProd_ratio_formula + telescoping (non-circular). -/
private lemma hook_walk_identity_rectYD {k a : ℕ} (hk : 0 < k) (ha : 0 < a) :
    ∑ c ∈ (corners (rectYD k a)).attach,
      ((hookProd (rectYD k a) : ℚ) /
        hookProd (removeCorner (rectYD k a) c.val (mem_corners.mp c.prop)))
    = ((rectYD k a).card : ℚ) := by
  -- Extract the unique element from corners.attach
  have hcorners : corners (rectYD k a) = {(k - 1, a - 1)} := corners_rectYD_singleton hk ha
  have hone : (corners (rectYD k a)).attach.card = 1 := by
    rw [Finset.card_attach, hcorners, Finset.card_singleton]
  obtain ⟨c₀, hc₀_eq⟩ := Finset.card_eq_one.mp hone
  rw [hc₀_eq, Finset.sum_singleton]
  -- c₀.val = (k-1, a-1)
  have hval : c₀.val = (k - 1, a - 1) := by
    have := c₀.prop; rw [hcorners] at this; exact Finset.mem_singleton.mp this
  -- Apply hookProd_ratio_formula
  have hcorner := mem_corners.mp c₀.prop
  rw [hookProd_ratio_formula hcorner, hval]
  simp only [Prod.fst, Prod.snd]
  -- Both products telescope; result is a * k = card
  rw [arm_prod_rectYD hk ha, leg_prod_rectYD hk ha, card_rectYD]
  push_cast
  ring

private lemma hook_walk_identity (μ : YoungDiagram) (hn : 0 < μ.card) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / (hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) : ℚ))
    = (μ.card : ℚ) := by
  by_cases h2 : μ.rowLen 2 = 0
  · -- At-most-2-row case: proved non-circularly
    exact hook_walk_identity_atMostTwoRows μ h2 hn
  · -- ≥3-row: check if μ is a generalized hook shape [a, 1^b]
    by_cases hghook : ∃ (a b : ℕ) (ha : 0 < a) (hb : 0 < b), μ = gHookYD a b ha
    · obtain ⟨a, b, ha, hb, rfl⟩ := hghook
      exact hook_walk_identity_gHookYD a b ha hb
    · -- ≥3-row, non-gHookYD: check at-most-2-col
      by_cases h2c : μ.colLen 2 = 0
      · exact hook_walk_identity_atMostTwoCols μ h2c hn
      · -- ≥3-row, ≥3-col, non-gHookYD: check if exactly 3 rows
        by_cases h3 : μ.rowLen 3 = 0
        · -- Exactly 3 rows (all shapes [a,b,c] with a≥b≥c≥1, including [a,2,1])
          exact hook_walk_identity_threeRow μ h3 (Nat.pos_of_ne_zero h2)
        · -- 4+ rows: check if exactly 4 rows
          by_cases h4 : μ.rowLen 4 = 0
          · -- Exactly 4 rows: use direct computation via hookProd_ratio_formula
            exact hook_walk_identity_fourRow μ h4 (Nat.pos_of_ne_zero h3)
          · -- 5+ rows: check if exactly 5 rows
            by_cases h5 : μ.rowLen 5 = 0
            · -- Exactly 5 rows: use direct computation via hookProd_ratio_formula
              exact hook_walk_identity_fiveRow μ h5 (Nat.pos_of_ne_zero h4)
            · -- 6+ rows: check if exactly 6 rows
              by_cases h6 : μ.rowLen 6 = 0
              · -- Exactly 6 rows: use direct computation via hookProd_ratio_formula
                exact hook_walk_identity_sixRow μ h6 (Nat.pos_of_ne_zero h5)
              · -- 7+ rows: check if exactly 7 rows
                by_cases h7 : μ.rowLen 7 = 0
                · -- Exactly 7 rows: use direct computation via hookProd_ratio_formula
                  exact hook_walk_identity_sevenRow μ h7 (Nat.pos_of_ne_zero h6)
                · -- 8+ rows: check if exactly 8 rows
                  by_cases h8 : μ.rowLen 8 = 0
                  · -- Exactly 8 rows: use direct computation via hookProd_ratio_formula
                    exact hook_walk_identity_eightRow μ h8 (Nat.pos_of_ne_zero h7)
                  · -- 9+ rows: check if exactly 9 rows
                    by_cases h9 : μ.rowLen 9 = 0
                    · -- Exactly 9 rows: use direct computation via hookProd_ratio_formula
                      exact hook_walk_identity_nineRow μ h9 (Nat.pos_of_ne_zero h8)
                    · -- 10+ rows, ≥3 cols, non-gHookYD: use transpose duality if ≤9 cols
                      by_cases h9c : μ.colLen 9 = 0
                      · -- ≤9 cols: μᵀ has ≤9 rows → use hook_walk_identity_atMostNineCols
                        exact hook_walk_identity_atMostNineCols μ h9c hn
                      · -- ≥10 rows AND ≥10 cols:
                        -- Check if μ is a rectangle
                        by_cases hrect : μ = rectYD (μ.colLen 0) (μ.rowLen 0)
                        · -- Rectangle case: single corner, telescoping product proof
                          -- rowLen 0 > 0 since rowLen 9 > 0 (and rowLen is non-increasing)
                          have ha : 0 < μ.rowLen 0 :=
                            Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero h9) (μ.rowLen_anti 0 9 (by omega))
                          -- colLen 0 > 0 since colLen 9 > 0 (and colLen is non-increasing)
                          have hk : 0 < μ.colLen 0 := by
                            have hcol9 : 0 < μ.colLen 9 := Nat.pos_of_ne_zero h9c
                            have : μ.colLen 9 ≤ μ.colLen 0 := by
                              have := μ.transpose.rowLen_anti 0 9 (by omega)
                              simp only [YoungDiagram.rowLen_transpose] at this
                              exact this
                            omega
                          rw [hrect]
                          exact hook_walk_identity_rectYD hk ha
                        · -- Non-rectangular ≥10×≥10: requires GNW hook walk
                          sorry

/-- The general hook-length formula in ℚ, proved by well-founded recursion on μ.card.
    Uses card_SYT_corner_step (Part XIII) + hook_walk_identity. -/
private lemma hook_length_formula_Q (ν : YoungDiagram) :
    (Fintype.card (StandardYoungTableau ν) : ℚ) * hookProd ν = ν.card.factorial := by
  rcases Nat.eq_zero_or_pos ν.card with h0 | hpos
  · -- ν.card = 0 → ν = ⊥ (empty diagram)
    have hνbot : ν = ⊥ :=
      YoungDiagram.ext ((Finset.card_eq_zero.mp h0).trans YoungDiagram.cells_bot.symm)
    subst hνbot
    simp [Fintype.card_eq_one_iff.mpr ⟨emptyTableau,
      fun T => StandardYoungTableau.ext
        fun c => (T.entry_zero c (YoungDiagram.notMem_bot c)).trans rfl⟩,
      hookProd_empty]
  · -- ν.card > 0: corner recursion + IH
    -- Apply corner recursion: card(SYT ν) = Σ_c card(SYT(ν\c))
    have hstep := card_SYT_corner_step ν hpos
    -- IH for each corner (recursive call, terminates since removeCorner.card < ν.card)
    have hIH : ∀ (cx : { x // x ∈ corners ν }),
        (Fintype.card (StandardYoungTableau
          (removeCorner ν cx.val (mem_corners.mp cx.prop))) : ℚ) *
        hookProd (removeCorner ν cx.val (mem_corners.mp cx.prop)) =
        (ν.card - 1).factorial := fun ⟨c, hc⟩ => by
      have hrc := hook_length_formula_Q (removeCorner ν c (mem_corners.mp hc))
      rwa [removeCorner_card (mem_corners.mp hc)] at hrc
    -- Main ℚ calculation
    have hstepQ : (Fintype.card (StandardYoungTableau ν) : ℚ) =
        ∑ c ∈ (corners ν).attach,
          (Fintype.card (StandardYoungTableau
            (removeCorner ν c.val (mem_corners.mp c.prop))) : ℚ) :=
      by exact_mod_cast hstep
    calc (Fintype.card (StandardYoungTableau ν) : ℚ) * hookProd ν
        -- Step 1: substitute corner step
        = ∑ c ∈ (corners ν).attach,
            ((Fintype.card (StandardYoungTableau
              (removeCorner ν c.val (mem_corners.mp c.prop))) : ℚ) * hookProd ν) := by
            rw [hstepQ, Finset.sum_mul]
      -- Step 2: rewrite each summand via IH: card(SYT(ν\c)) = (ν.card-1)! / hookProd(ν\c)
      _ = ∑ c ∈ (corners ν).attach,
            ((ν.card - 1).factorial *
              ((hookProd ν : ℚ) /
                hookProd (removeCorner ν c.val (mem_corners.mp c.prop)))) := by
            congr 1; ext ⟨c, hc⟩
            have hne := hookProdQ_ne_zero (removeCorner ν c (mem_corners.mp hc))
            have hIH_c := hIH ⟨c, hc⟩
            field_simp [hne]
            linear_combination (hookProd ν : ℚ) * hIH_c
      -- Step 3: factor out (ν.card-1)!
      _ = (ν.card - 1).factorial * ∑ c ∈ (corners ν).attach,
            ((hookProd ν : ℚ) /
              hookProd (removeCorner ν c.val (mem_corners.mp c.prop))) := by
            rw [Finset.mul_sum]
      -- Step 4: hook_walk_identity: Σ_c ratio = ν.card
      _ = (ν.card - 1).factorial * ν.card := by
            rw [hook_walk_identity ν hpos]
      -- Step 5: (ν.card-1)! * ν.card = ν.card!
      _ = ν.card.factorial := by
            cases hcard : ν.card with
            | zero => omega
            | succ n =>
              simp only [Nat.succ_sub_one]
              push_cast [Nat.factorial_succ]
              ring
termination_by ν.card
decreasing_by
  -- The recursive call is on removeCorner ν c _ which has card = ν.card - 1 < ν.card
  simp only [removeCorner_card (mem_corners.mp (by assumption : _ ∈ corners ν))]
  omega

/-- **General Hook-Length Formula (Frame-Robinson-Thrall 1954).**
    For any Young diagram μ: card(SYT(μ)) × hookProd(μ) = μ.card!
    Proof: well-founded induction using card_SYT_corner_step + hook_walk_identity.
    The sole remaining sorry is hook_walk_identity (verified for all special cases up to
    9 rows and 9 cols; ≥10×≥10 case requires GNW hook walk proof, ~300 lines). -/
theorem hook_length_formula_general (μ : YoungDiagram) :
    Fintype.card (StandardYoungTableau μ) * hookProd μ = μ.card.factorial := by
  exact_mod_cast hook_length_formula_Q μ

/-- **Hook-Length Formula (Frame-Robinson-Thrall 1954)** — alias for `hook_length_formula_general`.
    Proved here (after the corner-recursion infrastructure is in scope) via
    `hook_length_formula_general`.  The alternate LGV proof path is documented
    as the canonical-config restatement at the top of PART V; it remains open.
    Mathematical status: proved for all shapes with ≤9 rows or ≤9 columns and
    for all rectangles; `≥10 × ≥10` non-rectangular case is the sole remaining
    sorry, pending the GNW hook-walk argument (~300 lines). -/
theorem hook_length_formula (μ : YoungDiagram) :
    Fintype.card (StandardYoungTableau μ) * hookProd μ = μ.card.factorial :=
  hook_length_formula_general μ

end HookLengthFormula
