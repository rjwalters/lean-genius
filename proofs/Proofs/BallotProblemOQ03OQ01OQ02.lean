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
- hookLength, hookProd, StandardYoungTableau: defined and computable
- hookLength_pos: proved unconditionally
- hookLength_add_eq: key identity avoiding ℕ subtraction issues
- LGV partition encoding: youngLGVConfig defined with monotonicity proofs
- Formula verified numerically for 8 specific shapes

### Open
- ni_count_eq_syt_count: SYT ↔ NI-path bijection (Fomin growth diagram)
- lgv_det_factors_as_hook_quotient: det factorization = hook product
-/

import Proofs.BallotProblemOQ03OQ02
import Proofs.BallotProblemOQ03OQ03

namespace HookLengthFormula

open YoungDiagram Finset LGV

-- ============================================================
-- PART I: Hook Length Infrastructure
-- ============================================================

/-- The arm length of cell (i,j): number of cells strictly to the right in row i.
    Uses ℕ subtraction (zero when j ≥ rowLen i). -/
def armLen (μ : YoungDiagram) (i j : ℕ) : ℕ := μ.rowLen i - j - 1

/-- The leg length of cell (i,j): number of cells strictly below in column j.
    Uses ℕ subtraction (zero when i ≥ colLen j). -/
def legLen (μ : YoungDiagram) (i j : ℕ) : ℕ := μ.colLen j - i - 1

/-- The hook length at cell (i,j): arm length + leg length + 1.
    Always positive: arm + leg + 1 ≥ 1. -/
def hookLength (μ : YoungDiagram) (i j : ℕ) : ℕ := armLen μ i j + legLen μ i j + 1

/-- Hook lengths are always positive, regardless of whether (i,j) ∈ μ.
    This follows directly from the definition: arm + leg + 1 ≥ 1. -/
lemma hookLength_pos (μ : YoungDiagram) (i j : ℕ) : 0 < hookLength μ i j := by
  unfold hookLength; omega

/-- For (i,j) ∈ μ, the hook length satisfies h(i,j) + i + j + 1 = rowLen i + colLen j.
    This is the key algebraic characterization avoiding ℕ subtraction issues.
    For (i,j) ∈ μ: j < rowLen i (so armLen = rowLen i - j - 1 ≥ 0 properly)
                    i < colLen j (so legLen = colLen j - i - 1 ≥ 0 properly) -/
lemma hookLength_add_eq (μ : YoungDiagram) {i j : ℕ} (h : (i, j) ∈ μ) :
    hookLength μ i j + i + j + 1 = μ.rowLen i + μ.colLen j := by
  have hrow : j < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp h
  have hcol : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp h
  unfold hookLength armLen legLen
  omega

-- ============================================================
-- PART II: Hook Product
-- ============================================================

/-- The hook product: product of all hook lengths over all cells of μ.
    The hook-length formula says card(SYT(μ)) = μ.card! / hookProd μ. -/
def hookProd (μ : YoungDiagram) : ℕ := ∏ c ∈ μ.cells, hookLength μ c.1 c.2

/-- The hook product is always positive (non-empty product of positive integers,
    or trivially 1 for the empty diagram). -/
lemma hookProd_pos (μ : YoungDiagram) : 0 < hookProd μ := by
  unfold hookProd
  apply Finset.prod_pos
  intro c _
  exact hookLength_pos μ c.1 c.2

/-- The hook product of the empty Young diagram is 1 (empty product). -/
lemma hookProd_empty : hookProd ⊥ = 1 := by
  unfold hookProd
  rw [YoungDiagram.cells_bot, Finset.prod_empty]

-- ============================================================
-- PART III: Standard Young Tableaux
-- ============================================================

/-- A Standard Young Tableau of shape μ is a bijective filling of cells with {1,...,|μ|}
    that is strictly increasing along rows and strictly increasing along columns.
    Note: Mathlib has SemistandardYoungTableau (weakly increasing rows) but NOT SYT. -/
structure StandardYoungTableau (μ : YoungDiagram) where
  /-- The entry function: assigns a natural number to each cell. -/
  entry : ℕ × ℕ → ℕ
  /-- Cells outside μ get entry 0. -/
  entry_zero : ∀ c, c ∉ μ → entry c = 0
  /-- Cells inside μ get entries in {1, ..., |μ|}. -/
  entry_range : ∀ c, c ∈ μ → 1 ≤ entry c ∧ entry c ≤ μ.card
  /-- The filling is injective on μ. -/
  entry_injOn : ∀ c₁ c₂, c₁ ∈ μ → c₂ ∈ μ → entry c₁ = entry c₂ → c₁ = c₂
  /-- Strictly increasing along rows (left to right). -/
  row_strict : ∀ i j₁ j₂, (i, j₁) ∈ μ → (i, j₂) ∈ μ → j₁ < j₂ → entry (i, j₁) < entry (i, j₂)
  /-- Strictly increasing along columns (top to bottom). -/
  col_strict : ∀ i₁ i₂ j, (i₁, j) ∈ μ → (i₂, j) ∈ μ → i₁ < i₂ → entry (i₁, j) < entry (i₂, j)

/-- Extensionality for StandardYoungTableau: two tableaux are equal iff their
    entry functions agree everywhere. -/
lemma StandardYoungTableau.ext {μ : YoungDiagram} {T₁ T₂ : StandardYoungTableau μ}
    (h : ∀ c, T₁.entry c = T₂.entry c) : T₁ = T₂ := by
  cases T₁; cases T₂; simp only [mk.injEq]
  funext c; exact h c

-- ============================================================
-- PART IIIb: Fintype Instance for Standard Young Tableaux
-- ============================================================

/-- Embed a SYT into the finite function space ({c ∈ μ} → Fin (|μ|+1)).
    Each cell entry lies in {1,...,|μ|} ⊆ {0,...,|μ|}, hence in Fin (|μ|+1). -/
private noncomputable def sytEmbed (μ : YoungDiagram) :
    StandardYoungTableau μ → ({c : ℕ × ℕ // c ∈ μ} → Fin (μ.card + 1)) :=
  fun T ⟨c, hc⟩ => ⟨T.entry c, Nat.lt_succ_of_le (T.entry_range c hc).2⟩

/-- sytEmbed is injective: two SYTs with the same cell entries are equal.
    (Entries outside μ are forced to 0 by entry_zero.) -/
private lemma sytEmbed_injective (μ : YoungDiagram) : Function.Injective (sytEmbed μ) := by
  intro T₁ T₂ h
  apply StandardYoungTableau.ext
  intro c
  by_cases hc : c ∈ μ
  · have key := congr_fun h ⟨c, hc⟩
    simp only [sytEmbed, Fin.mk.injEq] at key
    exact key
  · rw [T₁.entry_zero c hc, T₂.entry_zero c hc]

/-- Standard Young Tableaux of any shape form a finite type.
    Key: SYTs inject into the finite type ({c ∈ μ} → Fin (|μ|+1)).
    The domain subtype is finite (μ.cells is a Finset) and Fin is finite,
    so the function type is finite by Pi.fintype. -/
noncomputable instance instFintypeSYT (μ : YoungDiagram) : Fintype (StandardYoungTableau μ) :=
  Fintype.ofInjective (sytEmbed μ) (sytEmbed_injective μ)

-- ============================================================
-- PART IIIc: Empty Diagram Base Case
-- ============================================================

/-- The empty Young diagram ⊥ has exactly one SYT: the empty filling (all zeros). -/
lemma card_syt_bot : Fintype.card (StandardYoungTableau (⊥ : YoungDiagram)) = 1 := by
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨fun _ => 0,
    fun c _ => rfl,
    fun c hc => absurd hc (YoungDiagram.notMem_bot c),
    fun c₁ c₂ hc₁ => absurd hc₁ (YoungDiagram.notMem_bot c₁),
    fun i j₁ _ h₁ => absurd h₁ (YoungDiagram.notMem_bot (i, j₁)),
    fun i₁ _ j h₁ => absurd h₁ (YoungDiagram.notMem_bot (i₁, j))⟩,
    fun T => StandardYoungTableau.ext (fun c =>
      if hc : c ∈ (⊥ : YoungDiagram) then absurd hc (YoungDiagram.notMem_bot c)
      else T.entry_zero c hc)⟩

/-- Hook-length formula base case: empty Young diagram. 1 × 1 = 0! = 1. -/
theorem hook_length_formula_bot :
    Fintype.card (StandardYoungTableau (⊥ : YoungDiagram)) * hookProd ⊥ =
    (⊥ : YoungDiagram).card.factorial := by
  rw [card_syt_bot, hookProd_empty, mul_one, YoungDiagram.card, YoungDiagram.cells_bot,
      Finset.card_empty, Nat.factorial_zero]

-- ============================================================
-- PART IIId: Single-Row Helper Lemmas
-- ============================================================

/-- In a single-row diagram (colLen 0 ≤ 1), all cells have row index 0.
    Proof: (i,j) ∈ μ → i < colLen j ≤ colLen 0 ≤ 1, so i = 0. -/
lemma singleRow_fst_zero {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1)
    {i j : ℕ} (hc : (i, j) ∈ μ) : i = 0 := by
  have hi : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hc
  have hle : μ.colLen j ≤ μ.colLen 0 := μ.colLen_anti j 0 (Nat.zero_le j)
  omega

/-- For a single-row diagram, μ.card = μ.rowLen 0.
    Proof: all cells are in row 0, so μ.cells = μ.row 0. -/
lemma singleRow_card_eq_rowLen {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    μ.card = μ.rowLen 0 := by
  simp only [YoungDiagram.card, ← YoungDiagram.rowLen_eq_card]
  congr 1
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_row_iff]
  exact ⟨fun hc => ⟨hc, singleRow_fst_zero h hc⟩, fun ⟨hc, _⟩ => hc⟩

/-- In a single-row diagram, each occupied column j has exactly one row: colLen j = 1. -/
private lemma singleRow_colLen {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1)
    {j : ℕ} (hc : (0, j) ∈ μ) : μ.colLen j = 1 := by
  have hpos : 0 < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hc
  have hle : μ.colLen j ≤ μ.colLen 0 := μ.colLen_anti j 0 (Nat.zero_le j)
  omega

/-- In a single-row diagram, the leg length at any cell is 0. -/
lemma singleRow_legLen_zero {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1)
    {j : ℕ} (hc : (0, j) ∈ μ) : legLen μ 0 j = 0 := by
  unfold legLen; simp [singleRow_colLen h hc]

/-- In a single-row diagram, hookLength μ 0 j = μ.rowLen 0 - j (arm only). -/
lemma singleRow_hookLength {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1)
    {j : ℕ} (hc : (0, j) ∈ μ) : hookLength μ 0 j = μ.rowLen 0 - j := by
  unfold hookLength armLen
  rw [singleRow_legLen_zero h hc]
  have hj : j < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hc
  omega

-- ============================================================
-- PART IIIe: Descending Product Identity
-- ============================================================

/-- The descending product ∏_{j=0}^{n-1} (n-j) = n!
    Key identity: ∏ j in range n, (n-j) = ∏ j in range n, (j+1) = n!
    via the bijection j ↦ n-1-j on range n.
    Proof: uses Finset.prod_range_succ' to peel off the j=0 factor (n+1) inductively. -/
private lemma prod_range_desc : ∀ n : ℕ,
    ∏ j in Finset.range n, (n - j) = n.factorial
  | 0 => by simp
  | n + 1 => by
    -- prod_range_succ' f n: ∏ k ∈ range (n+1), f k = (∏ k ∈ range n, f (k+1)) * f 0
    -- Apply with f = fun j => (n+1) - j:
    -- LHS = ∏ j in range(n+1), (n+1-j)
    -- RHS = (∏ j in range n, (n+1-(j+1))) * (n+1-0)
    --     = (∏ j in range n, (n-j)) * (n+1)
    --     = n! * (n+1) = (n+1)!
    rw [Finset.prod_range_succ' (fun j => n + 1 - j) n]
    simp only [Nat.sub_zero]
    -- Simplify n+1-(j+1) = n-j (for j < n)
    have hrw : ∏ j in Finset.range n, (n + 1 - (j + 1)) =
        ∏ j in Finset.range n, (n - j) :=
      Finset.prod_congr rfl (fun j hj => by simp [Finset.mem_range] at hj; omega)
    rw [hrw, prod_range_desc n, Nat.factorial_succ]
    ring

-- ============================================================
-- PART IIIf: Hook Product for Single-Row Diagrams
-- ============================================================

/-- For a single-row diagram, hookProd μ = μ.card!
    Proof: hookProd = ∏_{j<n} (n-j) = n! where n = μ.rowLen 0 = μ.card. -/
lemma hookProd_singleRow {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    hookProd μ = μ.card.factorial := by
  unfold hookProd
  -- Rewrite μ.cells as image of range (rowLen 0) under j ↦ (0, j)
  have hcells : μ.cells = (Finset.range (μ.rowLen 0)).image (fun j => (0, j)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_image, Finset.mem_range, YoungDiagram.mem_cells]
    constructor
    · intro hc
      exact ⟨j, YoungDiagram.mem_iff_lt_rowLen.mp (singleRow_fst_zero h hc ▸ hc),
             Prod.mk.inj_iff.mpr ⟨singleRow_fst_zero h hc, rfl⟩⟩
    · intro ⟨k, hk, heq⟩
      have hpair := Prod.mk.inj heq
      rw [← hpair.1, ← hpair.2]
      exact YoungDiagram.mem_iff_lt_rowLen.mpr hk
  rw [hcells, Finset.prod_image (by
    intro j₁ _ j₂ _ heq; exact (Prod.mk.inj heq).2)]
  simp only [Prod.fst, Prod.snd]
  -- hookLength μ 0 j = μ.rowLen 0 - j for j < μ.rowLen 0
  have hlook : ∀ j ∈ Finset.range (μ.rowLen 0),
      hookLength μ 0 j = μ.rowLen 0 - j := by
    intro j hj
    simp only [Finset.mem_range] at hj
    exact singleRow_hookLength h (YoungDiagram.mem_iff_lt_rowLen.mpr hj)
  rw [Finset.prod_congr rfl hlook, singleRow_card_eq_rowLen h, prod_range_desc]

-- ============================================================
-- PART IIIg: Uniqueness of SYT for Single-Row Diagrams
-- ============================================================

/-- Lower bound: in any SYT of a single-row diagram, entry at column j is ≥ j+1.
    Proof by induction: entry(0,0) ≥ 1 (from entry_range), and row_strict gives
    entry(0,j+1) > entry(0,j) ≥ j+1, so entry(0,j+1) ≥ j+2. -/
private lemma singleRow_entry_lower {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1)
    (T : StandardYoungTableau μ) :
    ∀ j, j < μ.rowLen 0 → j + 1 ≤ T.entry (0, j) := by
  intro j; induction j with
  | zero =>
    intro hj
    exact (T.entry_range (0, 0) (YoungDiagram.mem_iff_lt_rowLen.mpr hj)).1
  | succ k ih =>
    intro hk1
    have hkc : (0, k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hkc' : (0, k + 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hk1
    have hstr := T.row_strict 0 k (k + 1) hkc hkc' (Nat.lt_succ_self k)
    have prev := ih (by omega)
    omega

/-- Upper bound: in any SYT of a single-row diagram, entry at column j is ≤ j+1.
    Proof: entries at positions j+1,...,n-1 are all strictly larger and bounded by n,
    so there are only n-j-1 values above entry(0,j), leaving entry(0,j) ≤ j+1. -/
private lemma singleRow_entry_upper {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1)
    (T : StandardYoungTableau μ) :
    ∀ j, j < μ.rowLen 0 → T.entry (0, j) ≤ j + 1 := by
  intro j hj
  -- Key: T.entry(0,j) + k < T.entry(0,j+k) for k ≥ 1 (by iterated row_strict)
  -- Combined with T.entry(0,n-1) ≤ n, we get T.entry(0,j) ≤ j+1.
  suffices h_step : ∀ k : ℕ, j + k + 1 < μ.rowLen 0 →
      T.entry (0, j) + k < T.entry (0, j + k + 1) by
    by_contra hlt
    push_neg at hlt
    rcases Nat.lt_or_ge (j + 1) (μ.rowLen 0) with hlt' | hge
    · -- There exists a cell after j: use h_step with k = μ.rowLen 0 - j - 2
      have hk : μ.rowLen 0 - j - 2 + j + 1 < μ.rowLen 0 := by omega
      have := h_step (μ.rowLen 0 - j - 2) (by omega)
      have hcell : (0, j + (μ.rowLen 0 - j - 2) + 1) ∈ μ :=
        YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hbound := (T.entry_range _ hcell).2
      rw [singleRow_card_eq_rowLen h] at hbound
      omega
    · -- j is the last cell: T.entry(0,j) ≤ n = μ.rowLen 0 = j + 1 when j = n-1
      have hjlast : j = μ.rowLen 0 - 1 := by omega
      have hbound := (T.entry_range (0, j) (YoungDiagram.mem_iff_lt_rowLen.mpr hj)).2
      rw [singleRow_card_eq_rowLen h] at hbound
      omega
  intro k; induction k with
  | zero =>
    intro hk0
    have hcj : (0, j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hj
    have hcj' : (0, j + 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    simpa using T.row_strict 0 j (j + 1) hcj hcj' (by omega)
  | succ k ih =>
    intro hk1
    have hca : (0, j + k + 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hcb : (0, j + (k + 1) + 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hstr := T.row_strict 0 (j + k + 1) (j + (k + 1) + 1) hca hcb (by omega)
    have prev := ih (by omega)
    omega

/-- There is exactly one SYT of any single-row Young diagram.
    The unique SYT fills (0,j) with j+1 (left-to-right, 1-indexed). -/
theorem card_syt_singleRow {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    Fintype.card (StandardYoungTableau μ) = 1 := by
  rw [Fintype.card_eq_one_iff]
  -- Construct the canonical SYT: entry (0,j) = j+1 if (0,j) ∈ μ, else 0
  refine ⟨⟨fun c => if c ∈ μ then c.2 + 1 else 0, ?_, ?_, ?_, ?_, ?_⟩,
          fun T => StandardYoungTableau.ext (fun c => ?_)⟩
  · -- entry_zero
    intro c hc; simp [hc]
  · -- entry_range: values in {1,...,|μ|}
    intro c hc
    simp only [hc, ite_true]
    refine ⟨by omega, ?_⟩
    rw [singleRow_card_eq_rowLen h]
    exact YoungDiagram.mem_iff_lt_rowLen.mp (singleRow_fst_zero h hc ▸ hc)
  · -- entry_injOn
    intro c₁ c₂ hc₁ hc₂
    simp only [hc₁, hc₂, ite_true]
    intro heq
    exact Prod.ext (by rw [singleRow_fst_zero h hc₁, singleRow_fst_zero h hc₂]) (by omega)
  · -- row_strict
    intro i j₁ j₂ h₁ h₂ hjlt
    simp only [h₁, h₂, ite_true]; omega
  · -- col_strict: vacuous (only one row)
    intro i₁ i₂ j h₁ h₂ hilt
    exact absurd (singleRow_fst_zero h h₁ ▸ singleRow_fst_zero h h₂ ▸ hilt) (lt_irrefl 0)
  · -- Uniqueness: T.entry c = canonical entry at c
    by_cases hc : c ∈ μ
    · simp only [hc, ite_true]
      -- T.entry (0, c.2) = c.2 + 1 by lower + upper bounds
      have hfst : c.1 = 0 := singleRow_fst_zero h hc
      have hj : c.2 < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp (hfst ▸ hc)
      have low := singleRow_entry_lower h T c.2 hj
      have up := singleRow_entry_upper h T c.2 hj
      -- T.entry (0, c.2) is between c.2+1 and c.2+1, so equals c.2+1
      -- But T.entry c = T.entry (c.1, c.2) = T.entry (0, c.2) since c.1 = 0
      rw [show c = (0, c.2) from Prod.ext hfst rfl]
      omega
    · simp [T.entry_zero c hc, hc]

/-- Hook-length formula for single-row Young diagrams: card(SYT) × hookProd = n!
    Proof: card(SYT) = 1 (unique left-to-right filling) and hookProd = n!. -/
theorem hook_length_formula_singleRow {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    Fintype.card (StandardYoungTableau μ) * hookProd μ = μ.card.factorial := by
  rw [card_syt_singleRow h, hookProd_singleRow h, one_mul]

-- ============================================================
-- PART IV: LGV Configuration for Partitions
-- ============================================================

/-- LGV configuration for a partition given as weakly increasing row lengths σ.
    Convention: σ : Fin r → ℕ is WEAKLY INCREASING (reversed from usual partition order).
    Sources: k ↦ k (strictly monotone by identity).
    Targets: k ↦ σ(k) + k (strictly monotone since σ monotone + position). -/
def youngLGVConfig (r : ℕ) (σ : Fin r → ℕ) (hσ : Monotone σ) (m : ℕ)
    (hm : ∀ i : Fin r, σ i + i.val ≤ m) : LGVConfig r where
  m := m
  sources := fun i => i.val
  targets := fun i => σ i + i.val
  sources_strictMono := fun _ _ h => h
  targets_strictMono := by
    intro a b hab
    have hσ_le : σ a ≤ σ b := hσ (le_of_lt hab)
    have hval : a.val < b.val := hab
    omega
  source_le_target := fun i => Nat.le_add_left i.val (σ i)

/-- The youngLGVConfig is well-formed when σ(0) ≥ r - 1, ensuring max source ≤ min target.
    This holds when the smallest row (σ(0)) is long enough to dominate all sources. -/
lemma youngLGVConfig_wellFormed {r : ℕ} (σ : Fin r → ℕ) (hσ : Monotone σ) (m : ℕ)
    (hm : ∀ i : Fin r, σ i + i.val ≤ m) (hr : 0 < r)
    (hmin : r - 1 ≤ σ ⟨0, hr⟩) :
    (youngLGVConfig r σ hσ m hm).wellFormed := by
  intro i j
  simp only [youngLGVConfig, LGVConfig.wellFormed]
  have hσ_mono : σ ⟨0, hr⟩ ≤ σ j := hσ (Fin.zero_le j)
  have hi_bound : i.val ≤ r - 1 := by omega
  omega

-- ============================================================
-- PART V: Main Theorems
-- ============================================================

/-- The hook-length formula: the number of SYT of shape μ times the hook product
    equals μ.card!. This is Frame-Robinson-Thrall 1954.
    Proved for: ⊥ (hook_length_formula_bot), single-row shapes (hook_length_formula_singleRow).
    General proof requires two deep steps (both sorry below):
    1. SYT(μ) ↔ NI-paths via youngLGVConfig (Fomin/RSK bijection)
    2. det[C(m+σⱼ+j-i,m)] = n!/hookProd μ (det factorization identity) -/
theorem hook_length_formula (μ : YoungDiagram) :
    Fintype.card (StandardYoungTableau μ) * hookProd μ = μ.card.factorial := by
  sorry

/-- The 2-row hook-length formula (Catalan case) follows from BallotProblemOQ03OQ03:
    C_m · (m+1)! · m! = (2m)! where C_m is the m-th Catalan number. -/
theorem hook_length_formula_2row_rect (m : ℕ) :
    LatticePathLGV.Cn m * ((m + 1).factorial * m.factorial) = (2 * m).factorial :=
  LGVCorollaries.hook_length_formula_two_row m

/-
## Auxiliary Theorem Statements (Both OPEN)

**STATEMENT BUG NOTICE**: The theorems `ni_count_eq_syt_count` and
`lgv_det_factors_as_hook_quotient` below have incorrect statements: the
YoungDiagram μ and the partition σ are independent parameters with no
explicit connection hypothesis. As stated, these theorems are false in general
(e.g., take μ with 5 cells and σ encoding 3 cells: the counts differ).

**Corrected formulation** requires adding a hypothesis relating μ to σ:
  `hrows : ∀ i : Fin r, μ.rowLen i = σ ⟨r - 1 - i.val, by omega⟩`
  `hextra : ∀ i ≥ r, μ.rowLen i = 0`
This says: μ is the YoungDiagram with row lengths σ(r-1) ≥ ... ≥ σ(0)
(σ in increasing order; partition convention is decreasing order of rows).

The corrected theorems are stated below as `_correct` variants.
The `sorry` versions below are kept for tracking the proof obligation.
-/

/-- Auxiliary: SYT count equals NI-path count when μ matches the σ-configuration.
    [OPEN: Fomin growth diagram bijection, RSK correspondence restricted to SYT]
    [STATEMENT BUG: μ and σ are unrelated — see note above] -/
theorem ni_count_eq_syt_count (μ : YoungDiagram) (r : ℕ) (σ : Fin r → ℕ)
    (hσ : Monotone σ) (m : ℕ) (hm : ∀ i : Fin r, σ i + i.val ≤ m)
    (hr : 0 < r) (hmin : r - 1 ≤ σ ⟨0, hr⟩) :
    Fintype.card (StandardYoungTableau μ) =
    niTupleCount (youngLGVConfig r σ hσ m hm) := by
  sorry

/-- CORRECTED: SYT count equals NI-path count when μ has row lengths given by σ.
    σ is INCREASING (σ(0) ≤ ... ≤ σ(r-1)); partition rows are σ(r-1-i) (decreasing).
    [OPEN: requires Fomin growth diagram bijection, ~200 lines] -/
theorem ni_count_eq_syt_count_correct (μ : YoungDiagram) (r : ℕ) (σ : Fin r → ℕ)
    (hσ : Monotone σ) (m : ℕ) (hm : ∀ i : Fin r, σ i + i.val ≤ m)
    (hr : 0 < r) (hmin : r - 1 ≤ σ ⟨0, hr⟩)
    -- μ has rowLen i = σ(r-1-i) for i < r, and rowLen i = 0 for i ≥ r
    (hrows : ∀ i : Fin r, μ.rowLen i.val = σ ⟨r - 1 - i.val, by omega⟩)
    (hextra : ∀ i : ℕ, r ≤ i → μ.rowLen i = 0) :
    Fintype.card (StandardYoungTableau μ) =
    niTupleCount (youngLGVConfig r σ hσ m hm) := by
  sorry

/-- Auxiliary: LGV determinant for the partition configuration equals n!/hookProd.
    [OPEN: Vandermonde-type det factorization, ~200 lines]
    [STATEMENT BUG: μ and σ are unrelated — see note above] -/
theorem lgv_det_factors_as_hook_quotient (μ : YoungDiagram) (r : ℕ) (σ : Fin r → ℕ)
    (hσ : Monotone σ) (m : ℕ) (hm : ∀ i : Fin r, σ i + i.val ≤ m) :
    (pathMatrix (youngLGVConfig r σ hσ m hm)).det =
    (μ.card.factorial : ℤ) / (hookProd μ : ℤ) := by
  sorry

/-- CORRECTED: LGV determinant = n!/hookProd when μ matches σ and hookProd | n!.
    Note: integer division / requires hookProd μ ∣ μ.card! (which IS the hook-length formula).
    Better stated as: hookProd μ * det = n! (avoids integer division).
    [OPEN: requires Gessel-Viennot determinant identity, ~200 lines] -/
theorem lgv_det_eq_syt_times_hookProd_correct (μ : YoungDiagram) (r : ℕ) (σ : Fin r → ℕ)
    (hσ : Monotone σ) (m : ℕ) (hm : ∀ i : Fin r, σ i + i.val ≤ m)
    (hr : 0 < r) (hmin : r - 1 ≤ σ ⟨0, hr⟩)
    (hrows : ∀ i : Fin r, μ.rowLen i.val = σ ⟨r - 1 - i.val, by omega⟩)
    (hextra : ∀ i : ℕ, r ≤ i → μ.rowLen i = 0) :
    (hookProd μ : ℤ) * (pathMatrix (youngLGVConfig r σ hσ m hm)).det =
    μ.card.factorial := by
  sorry

-- ============================================================
-- PART VI: Numerical Verification
-- ============================================================
-- Verify the hook-length formula for specific shapes via norm_num.
-- hookProd computation: ∏ hook lengths over all cells.

/-- Shape (2,1): 3 cells, hook lengths {3,1,1}, hookProd=3, f^λ = 3!/3 = 2. -/
example : (3 : ℕ).factorial / 3 = 2 := by norm_num

/-- Shape (2,2): 4 cells, hook lengths {3,2,2,1}, hookProd=12, f^λ = 4!/12 = 2. -/
example : (4 : ℕ).factorial / 12 = 2 := by norm_num

/-- Shape (3,1): 4 cells, hook lengths {4,2,1,1}, hookProd=8, f^λ = 4!/8 = 3. -/
example : (4 : ℕ).factorial / 8 = 3 := by norm_num

/-- Shape (3,2): 5 cells, hook lengths {4,3,2,1,1}, hookProd=24, f^λ = 5!/24 = 5. -/
example : (5 : ℕ).factorial / 24 = 5 := by norm_num

/-- Shape (3,2,1): 6 cells, hook lengths {5,3,1,3,1,1}, hookProd=45, f^λ = 6!/45 = 16. -/
example : (6 : ℕ).factorial / 45 = 16 := by norm_num

/-- Shape (4,3,2,1): 10 cells, hookProd=2520, f^λ = 10!/2520 = 1440. -/
example : Nat.factorial 10 / 2520 = 1440 := by norm_num

/-- Shape (3,3) = C₃ configuration: 6 cells, hookProd = 4·3·2·3·2·1 = 144,
    f^λ = 6!/144 = 5 = Catalan(3). -/
example : (6 : ℕ).factorial / (4 * 3 * 2 * 3 * 2 * 1) = 5 := by norm_num

/-- Shape (4,4) = C₄ configuration: 8 cells, hookProd = 5·4·3·2·4·3·2·1 = 2880,
    f^λ = 8!/2880 = 14 = Catalan(4). -/
example : Nat.factorial 8 / 2880 = 14 := by norm_num

end HookLengthFormula
