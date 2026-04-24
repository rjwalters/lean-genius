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
- hook_length_formula_from_chain: proves main theorem FROM the two sorry lemmas
- Formula verified numerically for 8 specific shapes

### Open (2 sorry lemmas)
- ni_count_eq_syt_count: SYT ↔ NI-path bijection (Fomin growth diagram, ~200 lines)
- lgv_det_factors_as_hook_quotient: det × hookProd = n! (Vandermonde identity, ~200 lines)
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
-- PART IIIb: Fintype Instance for StandardYoungTableau
-- ============================================================

/-- Encode a SYT as a function on cells with bounded entries.
    For c ∈ μ, the entry is in {1,...,μ.card} ⊂ {0,...,μ.card}. -/
private def sytEncode (μ : YoungDiagram) (T : StandardYoungTableau μ)
    (c : μ.cells) : Fin (μ.card + 1) :=
  ⟨T.entry c.val, Nat.lt_succ_of_le (T.entry_range c.val c.prop).2⟩

private theorem sytEncode_injective (μ : YoungDiagram) :
    Function.Injective (sytEncode μ) := by
  intro T₁ T₂ h
  apply StandardYoungTableau.ext
  intro c
  by_cases hc : c ∈ μ.cells
  · have heq := congr_fun h ⟨c, hc⟩
    simp only [sytEncode, Fin.mk.injEq] at heq
    exact heq
  · simp [T₁.entry_zero c hc, T₂.entry_zero c hc]

/-- Standard Young Tableaux of shape μ form a finite type.
    Each SYT is uniquely determined by its entries on μ.cells (0 outside μ),
    giving an injection into the Fintype (μ.cells → Fin (μ.card + 1)). -/
noncomputable instance instFintypeSYT (μ : YoungDiagram) : Fintype (StandardYoungTableau μ) :=
  Fintype.ofInjective (sytEncode μ) (sytEncode_injective μ)

-- ============================================================
-- PART IIIc: Empty Diagram Base Case
-- ============================================================

/-- The unique SYT of shape ⊥: entries are all 0 (vacuously satisfies all axioms). -/
private def emptyTableau : StandardYoungTableau (⊥ : YoungDiagram) where
  entry _ := 0
  entry_zero _ _ := rfl
  entry_range c hc := absurd hc (YoungDiagram.notMem_bot c)
  entry_injOn c₁ _ hc₁ _ _ := absurd hc₁ (YoungDiagram.notMem_bot c₁)
  row_strict i j₁ _ h _ _ := absurd h (YoungDiagram.notMem_bot (i, j₁))
  col_strict i₁ _ j h _ _ := absurd h (YoungDiagram.notMem_bot (i₁, j))

/-- Hook-length formula for ⊥: 1 × 1 = 0! = 1.
    This is the base case; every SYT of shape ⊥ equals emptyTableau. -/
theorem hook_length_formula_bot :
    Fintype.card (StandardYoungTableau (⊥ : YoungDiagram)) * hookProd ⊥ =
    (⊥ : YoungDiagram).card.factorial := by
  have hcard : Fintype.card (StandardYoungTableau (⊥ : YoungDiagram)) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨emptyTableau, fun T =>
      StandardYoungTableau.ext fun c =>
        (T.entry_zero c (YoungDiagram.notMem_bot c)).trans rfl⟩
  simp [hcard, hookProd_empty, YoungDiagram.card, YoungDiagram.cells_bot]

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
    Proof requires two deep steps:
    1. SYT(μ) ↔ NI-paths via youngLGVConfig (Fomin/RSK bijection)
    2. det[C(m+σⱼ+j-i,m)] = μ.card! / hookProd μ (det factorization) -/
theorem hook_length_formula (μ : YoungDiagram) :
    Fintype.card (StandardYoungTableau μ) * hookProd μ = μ.card.factorial := by
  sorry

/-- The 2-row hook-length formula (Catalan case) follows from BallotProblemOQ03OQ03:
    C_m · (m+1)! · m! = (2m)! where C_m is the m-th Catalan number. -/
theorem hook_length_formula_2row_rect (m : ℕ) :
    LatticePathLGV.Cn m * ((m + 1).factorial * m.factorial) = (2 * m).factorial :=
  LGVCorollaries.hook_length_formula_two_row m

/-- Auxiliary: count of SYT of shape μ equals the NI-path count with youngLGVConfig.
    This is the Fomin growth diagram bijection (RSK correspondence restricted to SYT).
    [OPEN: requires ~200 lines of bijection infrastructure] -/
theorem ni_count_eq_syt_count (μ : YoungDiagram) (r : ℕ) (σ : Fin r → ℕ)
    (hσ : Monotone σ) (m : ℕ) (hm : ∀ i : Fin r, σ i + i.val ≤ m)
    (hr : 0 < r) (hmin : r - 1 ≤ σ ⟨0, hr⟩) :
    Fintype.card (StandardYoungTableau μ) =
    niTupleCount (youngLGVConfig r σ hσ m hm) := by
  sorry

/-- Auxiliary: the LGV determinant for youngLGVConfig times hookProd equals μ.card!.
    This is the algebraic identity connecting path-count determinants to hook products.
    Cleaner than division: avoids integer division and directly implies the formula.
    [OPEN: requires Vandermonde-type determinant identity; see knowledge.md Session 2] -/
theorem lgv_det_factors_as_hook_quotient (μ : YoungDiagram) (r : ℕ) (σ : Fin r → ℕ)
    (hσ : Monotone σ) (m : ℕ) (hm : ∀ i : Fin r, σ i + i.val ≤ m) :
    (pathMatrix (youngLGVConfig r σ hσ m hm)).det * (hookProd μ : ℤ) =
    μ.card.factorial := by
  sorry

/-- The hook-length formula follows from the two auxiliary sorry lemmas + lgv_lemma_rxr.
    This demonstrates the logical chain is complete; the two remaining deep steps are:
    (1) ni_count_eq_syt_count — RSK/Fomin growth diagram bijection (~200 lines)
    (2) lgv_det_factors_as_hook_quotient — Vandermonde-type det identity (~200 lines)
    If both are resolved for a specific encoding of μ, the formula follows. -/
theorem hook_length_formula_from_chain (μ : YoungDiagram)
    (r : ℕ) (σ : Fin r → ℕ) (hσ : Monotone σ) (m : ℕ)
    (hm : ∀ i : Fin r, σ i + i.val ≤ m) (hr : 0 < r) (hmin : r - 1 ≤ σ ⟨0, hr⟩)
    (h_ni_syt : Fintype.card (StandardYoungTableau μ) =
        niTupleCount (youngLGVConfig r σ hσ m hm))
    (h_det_hook : (pathMatrix (youngLGVConfig r σ hσ m hm)).det * (hookProd μ : ℤ) =
        μ.card.factorial) :
    Fintype.card (StandardYoungTableau μ) * hookProd μ = μ.card.factorial := by
  have hwf := youngLGVConfig_wellFormed σ hσ m hm hr hmin
  have h_lgv := lgv_lemma_rxr (youngLGVConfig r σ hσ m hm) hwf
  -- h_lgv : (niTupleCount cfg : ℤ) = (pathMatrix cfg).det
  have key : (Fintype.card (StandardYoungTableau μ) : ℤ) * (hookProd μ : ℤ) =
      μ.card.factorial := by
    -- card(SYT) = niTupleCount (by h_ni_syt)
    -- niTupleCount = det (by lgv_lemma_rxr)
    -- det * hookProd = n! (by h_det_hook)
    have h1 : (Fintype.card (StandardYoungTableau μ) : ℤ) =
        (pathMatrix (youngLGVConfig r σ hσ m hm)).det := by
      rw [h_ni_syt]; exact h_lgv
    calc (Fintype.card (StandardYoungTableau μ) : ℤ) * (hookProd μ : ℤ)
        = (pathMatrix (youngLGVConfig r σ hσ m hm)).det * (hookProd μ : ℤ) := by rw [h1]
      _ = μ.card.factorial := h_det_hook
  exact_mod_cast key

-- ============================================================
-- PART VI: Hook-Length Formula for Single-Row Diagrams (Direct)
-- ============================================================

/-
  For the single-row Young diagram with n cells, we prove the hook-length formula
  **directly** (without LGV):
  - hookLength(0,j) = n - j, so hookProd = n × (n-1) × ... × 1 = n!
  - The unique SYT is entry(0,j) = j+1 (strictly increasing identity filling)
  - Hence 1 × n! = n! ✓

  This serves as a concrete verified instance of hook_length_formula.
-/

/-- The Young diagram with a single row of length n. Cells: {(0,j) | j < n}. -/
def oneRowYD (n : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens [n] (by simp [List.SortedGE])

/-- Membership in oneRowYD: (i,j) ∈ oneRowYD n ↔ i = 0 ∧ j < n -/
lemma mem_oneRowYD {n i j : ℕ} : (i, j) ∈ oneRowYD n ↔ i = 0 ∧ j < n := by
  simp only [oneRowYD, YoungDiagram.mem_ofRowLens, List.length_singleton]
  constructor
  · rintro ⟨hi, hj⟩
    have hi0 : i = 0 := by omega
    subst hi0
    exact ⟨rfl, by simpa [List.getElem_cons_zero] using hj⟩
  · rintro ⟨rfl, hj⟩
    exact ⟨by omega, by simpa [List.getElem_cons_zero] using hj⟩

/-- Card of oneRowYD n is n. -/
lemma oneRowYD_card (n : ℕ) : (oneRowYD n).card = n := by
  have hcells : (oneRowYD n).cells = (Finset.range n).image (Prod.mk 0) := by
    ext ⟨i, j⟩
    simp [YoungDiagram.mem_cells, mem_oneRowYD, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨rfl, hj⟩; exact ⟨j, hj, rfl, rfl⟩
    · rintro ⟨k, hk, rfl, rfl⟩; exact ⟨rfl, hk⟩
  unfold YoungDiagram.card
  rw [hcells, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2),
    Finset.card_range]

/-- Row length of row 0 in oneRowYD n is n. -/
lemma rowLen_oneRowYD_zero (n : ℕ) : (oneRowYD n).rowLen 0 = n := by
  apply Nat.le_antisymm
  · -- rowLen 0 ≤ n: (0, n) ∉ oneRowYD n, so n ≥ rowLen 0
    rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]
    simp [mem_oneRowYD]
  · -- n ≤ rowLen 0: (0, n-1) ∈ oneRowYD n gives n-1 < rowLen 0
    cases n with
    | zero => simp
    | succ n =>
      have := YoungDiagram.mem_iff_lt_rowLen.mp (mem_oneRowYD.mpr ⟨rfl, n.lt_succ_self⟩)
      omega

/-- Column length of column j in oneRowYD n is 1 when j < n. -/
lemma colLen_oneRowYD {n j : ℕ} (hj : j < n) : (oneRowYD n).colLen j = 1 := by
  apply Nat.le_antisymm
  · -- colLen j ≤ 1: (1, j) ∉ oneRowYD n
    rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]
    simp [mem_oneRowYD]
  · -- 1 ≤ colLen j: (0, j) ∈ oneRowYD n gives 0 < colLen j
    have h0 : 0 < (oneRowYD n).colLen j :=
      YoungDiagram.mem_iff_lt_colLen.mp (mem_oneRowYD.mpr ⟨rfl, hj⟩)
    omega

/-- Hook length at cell (0, j) in oneRowYD n is n - j. -/
lemma hookLength_oneRowYD {n j : ℕ} (hj : j < n) :
    hookLength (oneRowYD n) 0 j = n - j := by
  have hcell : (0, j) ∈ oneRowYD n := mem_oneRowYD.mpr ⟨rfl, hj⟩
  have heq := hookLength_add_eq (oneRowYD n) hcell
  rw [rowLen_oneRowYD_zero, colLen_oneRowYD hj] at heq
  omega

/-- Hook product of oneRowYD n equals n!.
    Proof: hookLength(0,j) = n-j, so hookProd = ∏ₙ(n-j) = n.descFactorial n = n! -/
theorem hookProd_oneRowYD (n : ℕ) : hookProd (oneRowYD n) = n.factorial := by
  have hcells : (oneRowYD n).cells = (Finset.range n).image (Prod.mk 0) := by
    ext ⟨i, j⟩
    simp [YoungDiagram.mem_cells, mem_oneRowYD, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨rfl, hj⟩; exact ⟨j, hj, rfl, rfl⟩
    · rintro ⟨k, hk, rfl, rfl⟩; exact ⟨rfl, hk⟩
  unfold hookProd
  rw [hcells, Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).2)]
  -- Goal: ∏ j ∈ range n, hookLength (oneRowYD n) (Prod.mk 0 j).1 (Prod.mk 0 j).2 = n!
  -- (Prod.mk 0 j).1 = 0 and (Prod.mk 0 j).2 = j definitionally:
  show ∏ j ∈ Finset.range n, hookLength (oneRowYD n) 0 j = n.factorial
  -- Rewrite hookLength(0,j) = n-j, then use descFactorial identity
  rw [Finset.prod_congr rfl (fun j hj => hookLength_oneRowYD (Finset.mem_range.mp hj)),
      ← Nat.descFactorial_eq_prod_range]
  exact Nat.descFactorial_self n

-- ========================
-- Unique SYT for single row
-- ========================

/-- The identity filling for oneRowYD n: cell (0,j) gets entry j+1. -/
private def oneRowSYT (n : ℕ) : StandardYoungTableau (oneRowYD n) where
  entry := fun c => if c.1 = 0 ∧ c.2 < n then c.2 + 1 else 0
  entry_zero := fun ⟨i, j⟩ hc => if_neg (mt mem_oneRowYD.mpr hc)
  entry_range := by
    intro ⟨i, j⟩ hc
    rw [mem_oneRowYD] at hc
    show 1 ≤ (if i = 0 ∧ j < n then j + 1 else 0) ∧
         (if i = 0 ∧ j < n then j + 1 else 0) ≤ (oneRowYD n).card
    rw [if_pos hc, oneRowYD_card]
    omega
  entry_injOn := by
    intro ⟨i₁, j₁⟩ hc₁ ⟨i₂, j₂⟩ hc₂ h
    rw [mem_oneRowYD] at hc₁ hc₂
    show (i₁, j₁) = (i₂, j₂)
    simp only [if_pos hc₁, if_pos hc₂] at h
    exact Prod.mk.inj_iff.mpr ⟨hc₁.1.trans hc₂.1.symm, by omega⟩
  row_strict := by
    intro i j₁ j₂ hc₁ hc₂ hjlt
    rw [mem_oneRowYD] at hc₁ hc₂
    show (if i = 0 ∧ j₁ < n then j₁ + 1 else 0) < (if i = 0 ∧ j₂ < n then j₂ + 1 else 0)
    rw [if_pos hc₁, if_pos hc₂]
    omega
  col_strict := by
    intro i₁ i₂ j hc₁ hc₂ hilt
    rw [mem_oneRowYD] at hc₁ hc₂
    -- hc₁.1 : i₁ = 0, hc₂.1 : i₂ = 0, but hilt : i₁ < i₂, so 0 < 0 → False
    omega

/-- Helper: entries of any SYT of a single-row diagram satisfy entry(0,j) = j+1. -/
private lemma entry_oneRow_eq (n : ℕ) (T : StandardYoungTableau (oneRowYD n))
    (j : ℕ) (hj : j < n) : T.entry (0, j) = j + 1 := by
  have hcell : (0, j) ∈ oneRowYD n := mem_oneRowYD.mpr ⟨rfl, hj⟩
  -- Lower bound: j+1 ≤ T.entry(0,j) by induction on j using row_strict
  -- (Generalize over all k < n to get a proper IH)
  have hlb : j + 1 ≤ T.entry (0, j) := by
    suffices h : ∀ k < n, k + 1 ≤ T.entry (0, k) from h j hj
    intro k
    induction k with
    | zero => intro hk0; exact (T.entry_range (0, 0) (mem_oneRowYD.mpr ⟨rfl, hk0⟩)).1
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hstep := T.row_strict 0 k (k + 1)
        (mem_oneRowYD.mpr ⟨rfl, hk'⟩) (mem_oneRowYD.mpr ⟨rfl, hk⟩) k.lt_succ_self
      linarith [ih hk']
  -- Upper bound: T.entry(0,j) ≤ j+1 using strict chain from j to n-1
  have hub : T.entry (0, j) ≤ j + 1 := by
    -- Key: T.entry(0,j) + k ≤ T.entry(0,j+k) for all k ≤ n-1-j
    have hchain : ∀ k, k ≤ n - 1 - j → T.entry (0, j) + k ≤ T.entry (0, j + k) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hk' : k ≤ n - 1 - j := by omega
        have hjk : j + k < n := by omega
        have hjk1 : j + k + 1 < n := by omega
        have hstep := T.row_strict 0 (j + k) (j + k + 1)
          (mem_oneRowYD.mpr ⟨rfl, hjk⟩) (mem_oneRowYD.mpr ⟨rfl, hjk1⟩) (by omega)
        linarith [ih hk']
    rcases Nat.eq_zero_or_pos n with hn | hn
    · omega
    · have hk := hchain (n - 1 - j) le_rfl
      have hidx : j + (n - 1 - j) = n - 1 := by omega
      rw [hidx] at hk
      have hub_last : T.entry (0, n - 1) ≤ (oneRowYD n).card :=
        (T.entry_range (0, n - 1) (mem_oneRowYD.mpr ⟨rfl, by omega⟩)).2
      rw [oneRowYD_card] at hub_last
      omega
  omega

/-- Every SYT of oneRowYD n equals oneRowSYT n. -/
private lemma oneRowSYT_unique (n : ℕ) (T : StandardYoungTableau (oneRowYD n)) :
    T = oneRowSYT n := by
  apply StandardYoungTableau.ext
  intro ⟨i, j⟩
  by_cases h : (i, j) ∈ oneRowYD n
  · -- In the diagram: T.entry(0,j) = j+1 = (oneRowSYT n).entry(0,j)
    rw [mem_oneRowYD] at h
    subst h.1
    rw [entry_oneRow_eq n T j h.2]
    -- (oneRowSYT n).entry (0,j) = if 0=0 ∧ j<n then j+1 else 0 = j+1
    show j + 1 = if (0 : ℕ) = 0 ∧ j < n then j + 1 else 0
    exact (if_pos ⟨rfl, h.2⟩).symm
  · -- Not in diagram: both entries are 0
    rw [T.entry_zero _ h]
    show (0 : ℕ) = if i = 0 ∧ j < n then j + 1 else 0
    exact (if_neg (mt mem_oneRowYD.mpr h)).symm

/-- **Hook-length formula for single-row Young diagrams.**
    card(SYT(oneRowYD n)) × hookProd(oneRowYD n) = n!
    Proved directly: unique SYT with entry(0,j)=j+1, hookProd = n! -/
theorem hook_length_formula_one_row (n : ℕ) :
    Fintype.card (StandardYoungTableau (oneRowYD n)) * hookProd (oneRowYD n) = n.factorial := by
  have hcard : Fintype.card (StandardYoungTableau (oneRowYD n)) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨oneRowSYT n, oneRowSYT_unique n⟩
  rw [hcard, one_mul, hookProd_oneRowYD]

-- ============================================================
-- PART VIb: Hook-Length Formula for Single-Column Diagrams (Direct)
-- ============================================================

/-
  For the single-column Young diagram with n cells, we prove the hook-length
  formula **directly** (without LGV):
  - hookLength(i,0) = n - i, so hookProd = n × (n-1) × ... × 1 = n!
  - The unique SYT is entry(i,0) = i+1 (strictly increasing filling down the column)
  - Hence 1 × n! = n! ✓

  This is the column-transpose of the one-row case, using col_strict instead of row_strict.
-/

/-- The Young diagram with a single column of height n. Cells: {(i,0) | i < n}. -/
def oneColYD (n : ℕ) : YoungDiagram where
  cells := (Finset.range n).image (fun i => (i, 0))
  isLowerSet := by
    intro ⟨a, b⟩ ⟨c, d⟩ h hmem
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hmem ⊢
    obtain ⟨k, hk, rfl, rfl⟩ := hmem
    simp only [Prod.mk_le_mk] at h
    exact ⟨a, lt_of_le_of_lt h.1 hk, rfl, Nat.le_zero.mp h.2⟩

/-- Membership in oneColYD: (i,j) ∈ oneColYD n ↔ i < n ∧ j = 0 -/
lemma mem_oneColYD {n i j : ℕ} : (i, j) ∈ oneColYD n ↔ i < n ∧ j = 0 := by
  simp only [YoungDiagram.mem_cells, oneColYD, Finset.mem_image, Finset.mem_range,
    Prod.mk.injEq]
  constructor
  · rintro ⟨k, hk, rfl, rfl⟩; exact ⟨hk, rfl⟩
  · rintro ⟨hi, rfl⟩; exact ⟨i, hi, rfl, rfl⟩

/-- Card of oneColYD n is n. -/
lemma oneColYD_card (n : ℕ) : (oneColYD n).card = n := by
  unfold YoungDiagram.card
  simp only [oneColYD, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
    Finset.card_range]

/-- Row length of row i in oneColYD n is 1 when i < n. -/
lemma rowLen_oneColYD {n i : ℕ} (hi : i < n) : (oneColYD n).rowLen i = 1 := by
  apply Nat.le_antisymm
  · -- rowLen i ≤ 1: (i, 1) ∉ oneColYD n (only column j=0 exists)
    rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]
    simp [mem_oneColYD]
  · -- 1 ≤ rowLen i: (i, 0) ∈ oneColYD n gives 0 < rowLen i
    have h0 : 0 < (oneColYD n).rowLen i :=
      YoungDiagram.mem_iff_lt_rowLen.mp (mem_oneColYD.mpr ⟨hi, rfl⟩)
    omega

/-- Column length of column 0 in oneColYD n is n. -/
lemma colLen_oneColYD_zero (n : ℕ) : (oneColYD n).colLen 0 = n := by
  apply Nat.le_antisymm
  · -- colLen 0 ≤ n: (n, 0) ∉ oneColYD n (i must be < n)
    rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]
    simp [mem_oneColYD]
  · -- n ≤ colLen 0: (n-1, 0) ∈ oneColYD n gives n-1 < colLen 0
    cases n with
    | zero => simp
    | succ n =>
      have := YoungDiagram.mem_iff_lt_colLen.mp (mem_oneColYD.mpr ⟨n.lt_succ_self, rfl⟩)
      omega

/-- Hook length at cell (i, 0) in oneColYD n is n - i. -/
lemma hookLength_oneColYD {n i : ℕ} (hi : i < n) :
    hookLength (oneColYD n) i 0 = n - i := by
  have hcell : (i, 0) ∈ oneColYD n := mem_oneColYD.mpr ⟨hi, rfl⟩
  have heq := hookLength_add_eq (oneColYD n) hcell
  rw [rowLen_oneColYD hi, colLen_oneColYD_zero] at heq
  -- heq : hookLength (oneColYD n) i 0 + i + 0 + 1 = 1 + n
  omega

/-- Hook product of oneColYD n equals n!.
    Proof: hookLength(i,0) = n-i, so hookProd = ∏ᵢ(n-i) = n.descFactorial n = n! -/
theorem hookProd_oneColYD (n : ℕ) : hookProd (oneColYD n) = n.factorial := by
  have hcells : (oneColYD n).cells = (Finset.range n).image (fun i => (i, 0)) := rfl
  unfold hookProd
  rw [hcells, Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).1)]
  show ∏ i ∈ Finset.range n, hookLength (oneColYD n) i 0 = n.factorial
  rw [Finset.prod_congr rfl (fun i hi => hookLength_oneColYD (Finset.mem_range.mp hi)),
      ← Nat.descFactorial_eq_prod_range]
  exact Nat.descFactorial_self n

-- ========================
-- Unique SYT for single column
-- ========================

/-- The identity filling for oneColYD n: cell (i,0) gets entry i+1. -/
private def oneColSYT (n : ℕ) : StandardYoungTableau (oneColYD n) where
  entry := fun c => if c.1 < n ∧ c.2 = 0 then c.1 + 1 else 0
  entry_zero := fun ⟨i, j⟩ hc => if_neg (mt mem_oneColYD.mpr hc)
  entry_range := by
    intro ⟨i, j⟩ hc
    rw [mem_oneColYD] at hc
    show 1 ≤ (if i < n ∧ j = 0 then i + 1 else 0) ∧
         (if i < n ∧ j = 0 then i + 1 else 0) ≤ (oneColYD n).card
    rw [if_pos hc, oneColYD_card]; omega
  entry_injOn := by
    intro ⟨i₁, j₁⟩ hc₁ ⟨i₂, j₂⟩ hc₂ h
    rw [mem_oneColYD] at hc₁ hc₂
    show (i₁, j₁) = (i₂, j₂)
    simp only [if_pos hc₁, if_pos hc₂] at h
    exact Prod.mk.inj_iff.mpr ⟨by omega, hc₁.2.trans hc₂.2.symm⟩
  row_strict := by
    intro i j₁ j₂ hc₁ hc₂ hjlt
    rw [mem_oneColYD] at hc₁ hc₂
    -- hc₁.2 : j₁ = 0, hc₂.2 : j₂ = 0, contradiction with hjlt : j₁ < j₂
    omega
  col_strict := by
    intro i₁ i₂ j hc₁ hc₂ hilt
    rw [mem_oneColYD] at hc₁ hc₂
    show (if i₁ < n ∧ j = 0 then i₁ + 1 else 0) < (if i₂ < n ∧ j = 0 then i₂ + 1 else 0)
    rw [if_pos hc₁, if_pos hc₂]; omega

/-- Helper: entries of any SYT of a single-column diagram satisfy entry(i,0) = i+1. -/
private lemma entry_oneCol_eq (n : ℕ) (T : StandardYoungTableau (oneColYD n))
    (i : ℕ) (hi : i < n) : T.entry (i, 0) = i + 1 := by
  -- Lower bound: i+1 ≤ T.entry(i,0) by induction on i using col_strict
  have hlb : i + 1 ≤ T.entry (i, 0) := by
    suffices h : ∀ k < n, k + 1 ≤ T.entry (k, 0) from h i hi
    intro k
    induction k with
    | zero => intro hk0; exact (T.entry_range (0, 0) (mem_oneColYD.mpr ⟨hk0, rfl⟩)).1
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hstep := T.col_strict k (k + 1) 0
        (mem_oneColYD.mpr ⟨hk', rfl⟩) (mem_oneColYD.mpr ⟨hk, rfl⟩) k.lt_succ_self
      linarith [ih hk']
  -- Upper bound: T.entry(i,0) ≤ i+1 via strict chain from i down to n-1
  have hub : T.entry (i, 0) ≤ i + 1 := by
    have hchain : ∀ k, k ≤ n - 1 - i → T.entry (i, 0) + k ≤ T.entry (i + k, 0) := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hk' : k ≤ n - 1 - i := by omega
        have hik : i + k < n := by omega
        have hik1 : i + k + 1 < n := by omega
        have hstep := T.col_strict (i + k) (i + k + 1) 0
          (mem_oneColYD.mpr ⟨hik, rfl⟩) (mem_oneColYD.mpr ⟨hik1, rfl⟩) (by omega)
        linarith [ih hk']
    rcases Nat.eq_zero_or_pos n with hn | hn
    · omega
    · have hk := hchain (n - 1 - i) le_rfl
      rw [show i + (n - 1 - i) = n - 1 by omega] at hk
      have hub_last : T.entry (n - 1, 0) ≤ (oneColYD n).card :=
        (T.entry_range (n - 1, 0) (mem_oneColYD.mpr ⟨by omega, rfl⟩)).2
      rw [oneColYD_card] at hub_last; omega
  omega

/-- Every SYT of oneColYD n equals oneColSYT n. -/
private lemma oneColSYT_unique (n : ℕ) (T : StandardYoungTableau (oneColYD n)) :
    T = oneColSYT n := by
  apply StandardYoungTableau.ext
  intro ⟨i, j⟩
  by_cases h : (i, j) ∈ oneColYD n
  · rw [mem_oneColYD] at h
    subst h.2
    rw [entry_oneCol_eq n T i h.1]
    exact (if_pos ⟨h.1, rfl⟩).symm
  · rw [T.entry_zero _ h]
    exact (if_neg (mt mem_oneColYD.mpr h)).symm

/-- **Hook-length formula for single-column Young diagrams.**
    card(SYT(oneColYD n)) × hookProd(oneColYD n) = n!
    Proved directly: unique SYT with entry(i,0)=i+1, hookProd = n! -/
theorem hook_length_formula_one_col (n : ℕ) :
    Fintype.card (StandardYoungTableau (oneColYD n)) * hookProd (oneColYD n) = n.factorial := by
  have hcard : Fintype.card (StandardYoungTableau (oneColYD n)) = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨oneColSYT n, oneColSYT_unique n⟩
  rw [hcard, one_mul, hookProd_oneColYD]

-- ============================================================
-- PART VIc: Hook-Length Formula for Generalized Hook Shapes [a, 1^b]
-- ============================================================

/-
  A *generalized hook shape* gHookYD a b (a ≥ 1, b ≥ 0) has:
  - Row 0 of length a  (horizontal arm)
  - Rows 1, ..., b each of length 1  (vertical leg)
  - Total cells: n = a + b

  Hook lengths:
    h(0,0) = a + b        (corner of the L)
    h(0,j) = a - j        for j = 1, ..., a-1   (arm cells)
    h(i,0) = b + 1 - i    for i = 1, ..., b      (leg cells)

  Hook product: hookProd = (a+b) · (a-1)! · b!

  SYT count: card(SYT(gHookYD a b)) = C(a+b-1, a-1)
  Bijection: SYT ↔ (a-1)-subsets of {2,...,a+b}, where the subset
  records which entries go in row 0 (positions 1,...,a-1).

  HLF: C(a+b-1, a-1) × (a+b) × (a-1)! × b! = (a+b)!

  Special cases:
  - gHookYD a 0 = oneRowYD a   (row shape, already proved)
  - gHookYD 1 b = oneColYD (b+1) (column shape, already proved)
  - gHookYD a 1 = hookShapeYD (a-1) (hook shape, already proved)
  - gHookYD a b with a≥2, b≥2: NEW cases
-/

/-- Generalized hook shape: row 0 of length a ≥ 1, rows 1..b each of length 1. -/
private def gHookYD (a b : ℕ) (ha : 0 < a) : YoungDiagram where
  cells := (Finset.range a).image (Prod.mk 0) ∪
           (Finset.Ico 1 (b + 1)).image (fun i => (i, 0))
  isLowerSet := by
    intro ⟨x, y⟩ ⟨u, v⟩ huv hmem
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image, Finset.mem_range,
               Finset.mem_Ico, Prod.mk.injEq] at hmem ⊢
    simp only [Prod.mk_le_mk] at huv
    obtain ⟨hxu, hyv⟩ := huv
    rcases hmem with ⟨k, hk, rfl, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl, rfl⟩
    · -- (u,v) = (0, k) with k < a; x ≤ 0 so x = 0; y ≤ k < a
      left; exact ⟨y, by omega, Nat.eq_zero_of_le_zero hxu |>.symm, by omega⟩
    · -- (u,v) = (k, 0) with 1 ≤ k ≤ b; y ≤ 0 so y = 0; x ≤ k ≤ b
      have hy0 : y = 0 := Nat.le_zero.mp hyv
      subst hy0
      by_cases hx0 : x = 0
      · subst hx0; left; exact ⟨0, ha, rfl, rfl⟩
      · right; exact ⟨x, ⟨Nat.pos_of_ne_zero hx0, by omega⟩, rfl, rfl⟩

private lemma mem_gHookYD {a b : ℕ} {ha : 0 < a} {i j : ℕ} :
    (i, j) ∈ gHookYD a b ha ↔ (i = 0 ∧ j < a) ∨ (1 ≤ i ∧ i ≤ b ∧ j = 0) := by
  simp only [gHookYD, YoungDiagram.mem_mk, Finset.mem_union, Finset.mem_image,
             Finset.mem_range, Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro (⟨k, hk, rfl, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl, rfl⟩)
    · left; exact ⟨rfl, hk⟩
    · right; exact ⟨hk1, by omega, rfl⟩
  · rintro (⟨rfl, hj⟩ | ⟨hi1, hi2, rfl⟩)
    · left; exact ⟨j, hj, rfl, rfl⟩
    · right; exact ⟨i, ⟨hi1, by omega⟩, rfl, rfl⟩

private lemma gHookYD_card (a b : ℕ) (ha : 0 < a) : (gHookYD a b ha).card = a + b := by
  unfold YoungDiagram.card gHookYD
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
        Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).1),
        Finset.card_range, Finset.card_Ico]
    omega
  · apply Finset.disjoint_left.mpr
    intro ⟨x, y⟩ hx hy
    simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
    obtain ⟨_, _, rfl, rfl⟩ := hx
    obtain ⟨_, ⟨h1, _⟩, rfl, _⟩ := hy
    omega

-- gHookYD a 0 = oneRowYD a
private lemma gHookYD_zero_eq_oneRowYD (a : ℕ) (ha : 0 < a) :
    gHookYD a 0 ha = oneRowYD a := by
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_mk, mem_gHookYD, mem_oneRowYD, Finset.mem_Ico]
  constructor
  · rintro (⟨rfl, hj⟩ | ⟨h1, h2, _⟩); exact ⟨rfl, hj⟩; omega
  · rintro ⟨rfl, hj⟩; left; exact ⟨rfl, hj⟩

-- gHookYD 1 b ha = oneColYD (b+1)
private lemma gHookYD_one_eq_oneColYD (b : ℕ) :
    gHookYD 1 b (Nat.one_pos) = oneColYD (b + 1) := by
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_mk, mem_gHookYD, mem_oneColYD]
  constructor
  · rintro (⟨rfl, hj⟩ | ⟨hi1, hi2, rfl⟩)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, rfl⟩
  · rintro ⟨hi, rfl⟩
    rcases Nat.eq_or_gt_of_le (Nat.zero_le i) with rfl | hpos
    · left; exact ⟨rfl, Nat.one_pos⟩
    · right; exact ⟨hpos, by omega, rfl⟩

-- Row/column lengths for gHookYD
private lemma rowLen_gHookYD_zero (a b : ℕ) (ha : 0 < a) :
    (gHookYD a b ha).rowLen 0 = a := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]
    simp [mem_gHookYD]
  · cases a with
    | zero => omega
    | succ a =>
      have := YoungDiagram.mem_iff_lt_rowLen.mp
        (mem_gHookYD.mpr (Or.inl ⟨rfl, Nat.lt_succ_self a⟩))
      omega

private lemma rowLen_gHookYD_succ (a b : ℕ) (ha : 0 < a) {i : ℕ} (hi : 0 < i) (hib : i ≤ b) :
    (gHookYD a b ha).rowLen i = 1 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]
    simp [mem_gHookYD]; omega
  · have := YoungDiagram.mem_iff_lt_rowLen.mp
      (mem_gHookYD.mpr (Or.inr ⟨hi, hib, rfl⟩))
    omega

private lemma colLen_gHookYD_zero (a b : ℕ) (ha : 0 < a) :
    (gHookYD a b ha).colLen 0 = b + 1 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]
    simp [mem_gHookYD]; omega
  · cases b with
    | zero =>
      have := YoungDiagram.mem_iff_lt_colLen.mp
        (mem_gHookYD.mpr (Or.inl ⟨rfl, ha⟩))
      omega
    | succ b =>
      have := YoungDiagram.mem_iff_lt_colLen.mp
        (mem_gHookYD.mpr (Or.inr ⟨Nat.succ_pos b, le_refl _, rfl⟩))
      omega

private lemma colLen_gHookYD_pos (a b : ℕ) (ha : 0 < a) {j : ℕ} (hj : 0 < j) (hja : j < a) :
    (gHookYD a b ha).colLen j = 1 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]
    simp [mem_gHookYD]; omega
  · have := YoungDiagram.mem_iff_lt_colLen.mp
      (mem_gHookYD.mpr (Or.inl ⟨rfl, hja⟩))
    omega

-- Hook lengths for gHookYD
private lemma hookLength_gHookYD_00 (a b : ℕ) (ha : 0 < a) :
    hookLength (gHookYD a b ha) 0 0 = a + b := by
  have hcell : (0, 0) ∈ gHookYD a b ha := mem_gHookYD.mpr (Or.inl ⟨rfl, ha⟩)
  have heq := hookLength_add_eq (gHookYD a b ha) hcell
  rw [rowLen_gHookYD_zero, colLen_gHookYD_zero] at heq; omega

private lemma hookLength_gHookYD_row (a b : ℕ) (ha : 0 < a) {j : ℕ}
    (hj : 0 < j) (hja : j < a) :
    hookLength (gHookYD a b ha) 0 j = a - j := by
  have hcell : (0, j) ∈ gHookYD a b ha := mem_gHookYD.mpr (Or.inl ⟨rfl, hja⟩)
  have heq := hookLength_add_eq (gHookYD a b ha) hcell
  rw [rowLen_gHookYD_zero, colLen_gHookYD_pos ha hj hja] at heq; omega

private lemma hookLength_gHookYD_col (a b : ℕ) (ha : 0 < a) {i : ℕ}
    (hi : 0 < i) (hib : i ≤ b) :
    hookLength (gHookYD a b ha) i 0 = b + 1 - i := by
  have hcell : (i, 0) ∈ gHookYD a b ha := mem_gHookYD.mpr (Or.inr ⟨hi, hib, rfl⟩)
  have heq := hookLength_add_eq (gHookYD a b ha) hcell
  rw [rowLen_gHookYD_succ a b ha hi hib, colLen_gHookYD_zero] at heq; omega

/-- Hook product of gHookYD a b equals (a+b) * (a-1)! * b! -/
private theorem hookProd_gHookYD (a b : ℕ) (ha : 0 < a) :
    hookProd (gHookYD a b ha) = (a + b) * (a - 1).factorial * b.factorial := by
  -- Split cells: {(0,0)} ∪ {(0,j) : 1≤j<a} ∪ {(i,0) : 1≤i≤b}
  have hcells : (gHookYD a b ha).cells =
      {(0,0)} ∪ (Finset.Ico 1 a).image (Prod.mk 0) ∪
      (Finset.Ico 1 (b+1)).image (fun i => (i, 0)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
               Finset.mem_Ico, Prod.mk.injEq, YoungDiagram.mem_cells, mem_gHookYD]
    constructor
    · rintro (⟨rfl, hj⟩ | ⟨hi, hib, rfl⟩)
      · rcases Nat.eq_or_gt_of_le (Nat.zero_le j) with rfl | hpos
        · left; left; exact ⟨rfl, rfl⟩
        · left; right; exact ⟨j, ⟨hpos, hj⟩, rfl, rfl⟩
      · right; exact ⟨i, ⟨hi, by omega⟩, rfl, rfl⟩
    · rintro ((⟨rfl, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl, rfl⟩) | ⟨k, ⟨hk1, hk2⟩, rfl, rfl⟩)
      · left; exact ⟨rfl, ha⟩
      · left; exact ⟨rfl, hk2⟩
      · right; exact ⟨hk1, by omega, rfl⟩
  -- Disjointness of the three parts
  have hdisj1 : Disjoint ({(0, 0)} : Finset (ℕ × ℕ))
      ((Finset.Ico 1 a).image (Prod.mk 0)) :=
    Finset.disjoint_left.mpr (by simp [Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq])
  have hdisj2 : Disjoint ({(0, 0)} ∪ (Finset.Ico 1 a).image (Prod.mk 0))
      ((Finset.Ico 1 (b+1)).image (fun i => (i, 0))) :=
    Finset.disjoint_left.mpr (by
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
                 Finset.mem_Ico, Prod.mk.injEq]
      intro ⟨x, y⟩ hx hy
      obtain ⟨k, ⟨hk1, _⟩, rfl, rfl⟩ := hy
      rcases hx with ⟨h1, h2⟩ | ⟨_, ⟨h1, _⟩, rfl, _⟩ <;> omega)
  -- Compute hookProd by splitting
  unfold hookProd
  rw [hcells]
  rw [Finset.prod_union hdisj2, Finset.prod_union hdisj1]
  simp only [Finset.prod_singleton]
  rw [hookLength_gHookYD_00 a b ha]
  -- Row arm product: ∏_{j=1}^{a-1} (a-j) = (a-1)!
  have hrow : ∏ j ∈ Finset.Ico 1 a,
      hookLength (gHookYD a b ha) (Prod.mk 0 j).1 (Prod.mk 0 j).2 =
      (a - 1).factorial := by
    simp only [Prod.fst, Prod.snd]
    rw [Finset.prod_image (fun p _ q _ h => (Prod.mk.inj h).2)]
    simp only [Prod.fst, Prod.snd]
    rw [Finset.prod_congr rfl (fun j hj => by
      rw [hookLength_gHookYD_row a b ha (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2])]
    -- ∏_{j∈Ico 1 a} (a-j) = ∏_{k∈range (a-1)} (a-1-k) = (a-1)!
    rw [show Finset.Ico 1 a = (Finset.range (a-1)).image (· + 1) from by
      ext k; simp [Finset.mem_Ico, Finset.mem_range]; omega]
    rw [Finset.prod_image (fun p _ q _ h => by omega)]
    rw [Finset.prod_congr rfl (fun k hk => by
      simp; omega)]
    rw [← Nat.descFactorial_eq_prod_range]
    exact Nat.descFactorial_self (a - 1)
  -- Column leg product: ∏_{i=1}^{b} (b+1-i) = b!
  have hcol : ∏ i ∈ Finset.Ico 1 (b + 1),
      hookLength (gHookYD a b ha) ((fun k => (k, 0)) i).1 ((fun k => (k, 0)) i).2 =
      b.factorial := by
    simp only [Prod.fst, Prod.snd]
    rw [Finset.prod_image (fun p _ q _ h => (Prod.mk.inj h).1)]
    simp only [Prod.fst, Prod.snd]
    rw [Finset.prod_congr rfl (fun i hi => by
      rw [hookLength_gHookYD_col a b ha (Finset.mem_Ico.mp hi).1
        (by have := (Finset.mem_Ico.mp hi).2; omega)])]
    rw [show Finset.Ico 1 (b+1) = (Finset.range b).image (· + 1) from by
      ext k; simp [Finset.mem_Ico, Finset.mem_range]; omega]
    rw [Finset.prod_image (fun p _ q _ h => by omega)]
    rw [Finset.prod_congr rfl (fun k hk => by simp; omega)]
    rw [← Nat.descFactorial_eq_prod_range]
    exact Nat.descFactorial_self b
  rw [hrow, hcol]
  ring

-- ========================
-- Corner characterization for gHookYD
-- ========================

private lemma isCorner_gHook_top (a b : ℕ) (ha : 0 < a) (ha2 : 1 < a) :
    isCorner (gHookYD a b ha) (0, a - 1) := by
  refine ⟨mem_gHookYD.mpr (Or.inl ⟨rfl, by omega⟩), ?_, ?_⟩
  · simp [mem_gHookYD]; omega
  · simp [mem_gHookYD]; omega

private lemma isCorner_gHook_bot (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    isCorner (gHookYD a b ha) (b, 0) := by
  refine ⟨mem_gHookYD.mpr (Or.inr ⟨hb, le_refl _, rfl⟩), ?_, ?_⟩
  · simp [mem_gHookYD]; omega
  · simp [mem_gHookYD]; omega

-- removeCorner identities
private lemma removeCorner_gHook_top (a b : ℕ) (ha : 0 < a) (ha2 : 1 < a)
    (hc : isCorner (gHookYD a b ha) (0, a - 1)) :
    removeCorner (gHookYD a b ha) (0, a - 1) hc = gHookYD (a - 1) b (by omega) := by
  ext ⟨i, j⟩
  rw [mem_removeCorner hc, mem_gHookYD, mem_gHookYD]
  constructor
  · rintro ⟨hmem, hne⟩
    rcases hmem with ⟨rfl, hj⟩ | ⟨hi1, hi2, rfl⟩
    · left; refine ⟨rfl, ?_⟩
      simp only [Prod.mk.injEq, true_and] at hne; omega
    · right; exact ⟨hi1, hi2, rfl⟩
  · rintro (⟨rfl, hj⟩ | ⟨hi1, hi2, rfl⟩)
    · exact ⟨Or.inl ⟨rfl, by omega⟩, by simp [Prod.mk.injEq]; omega⟩
    · exact ⟨Or.inr ⟨hi1, hi2, rfl⟩, by simp [Prod.mk.injEq]; omega⟩

private lemma removeCorner_gHook_bot (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : isCorner (gHookYD a b ha) (b, 0)) :
    removeCorner (gHookYD a b ha) (b, 0) hc = gHookYD a (b - 1) ha := by
  ext ⟨i, j⟩
  rw [mem_removeCorner hc, mem_gHookYD, mem_gHookYD]
  constructor
  · rintro ⟨hmem, hne⟩
    rcases hmem with ⟨rfl, hj⟩ | ⟨hi1, hi2, rfl⟩
    · left; exact ⟨rfl, hj⟩
    · right; refine ⟨hi1, ?_, rfl⟩
      simp only [Prod.mk.injEq, and_true] at hne; omega
  · rintro (⟨rfl, hj⟩ | ⟨hi1, hi2, rfl⟩)
    · exact ⟨Or.inl ⟨rfl, hj⟩, by simp [Prod.mk.injEq]; omega⟩
    · exact ⟨Or.inr ⟨hi1, by omega, rfl⟩, by simp [Prod.mk.injEq]; omega⟩

-- ========================
-- SYT count for gHookYD: max entry location
-- ========================

/-- In any SYT of gHookYD a b (a≥2, b≥1), the max entry a+b is at
    (0, a-1) (top-right of row 0) or (b, 0) (bottom of column 0). -/
private lemma gHook_max_at_corner (a b : ℕ) (ha2 : 1 < a) (hb : 0 < b)
    (T : StandardYoungTableau (gHookYD a b (by omega : 0 < a))) :
    T.entry (0, a - 1) = a + b ∨ T.entry (b, 0) = a + b := by
  have ha : 0 < a := by omega
  have hcard : (gHookYD a b ha).card = a + b := gHookYD_card a b ha
  -- T.entry is a bijection on cells to {1,...,n}, so surjective
  have himage_eq : (gHookYD a b ha).cells.image T.entry = Finset.Icc 1 (a + b) := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_Icc.mpr (T.entry_range c (YoungDiagram.mem_cells.mp hc) |>.imp_right
        (hcard ▸ ·))
    · rw [Finset.card_Icc]
      rw [Finset.card_image_of_injOn (fun c₁ hc₁ c₂ hc₂ h =>
        T.entry_injOn c₁ c₂ (YoungDiagram.mem_cells.mp hc₁)
          (YoungDiagram.mem_cells.mp hc₂) h)]
      simp [hcard]
  -- a+b ∈ image, so some cell maps to a+b
  have hab_in : a + b ∈ (gHookYD a b ha).cells.image T.entry := by
    rw [himage_eq]; simp
  obtain ⟨c, hc_cell, hc_eq⟩ := Finset.mem_image.mp hab_in
  have hc_mem := YoungDiagram.mem_cells.mp hc_cell
  -- c must be a corner (entry a+b means no cells to the right or below)
  have hright : (c.1, c.2 + 1) ∉ gHookYD a b ha := by
    intro h; have := T.row_strict c.1 c.2 (c.2 + 1) hc_mem h (Nat.lt_succ_self _)
    rw [hc_eq, hcard] at this; exact absurd this (Nat.lt_irrefl _)
  have hbelow : (c.1 + 1, c.2) ∉ gHookYD a b ha := by
    intro h; have := T.col_strict c.1 (c.1 + 1) c.2 hc_mem h (Nat.lt_succ_self _)
    rw [hc_eq, hcard] at this; exact absurd this (Nat.lt_irrefl _)
  -- c must be (0, a-1) or (b, 0)
  rcases mem_gHookYD.mp hc_mem with ⟨h0, hj⟩ | ⟨hi1, hi2, h0⟩
  · left
    have hja : c.2 = a - 1 := by
      simp [mem_gHookYD, h0] at hright; omega
    rw [← hc_eq]; congr 1; exact Prod.ext h0 hja
  · right
    have hib : c.1 = b := by
      simp [mem_gHookYD, h0] at hbelow; omega
    rw [← hc_eq]; congr 1; exact Prod.ext hib h0

-- ========================
-- Step lemma: SYT count recursion
-- ========================

/-- Membership in gHookYD (a-1) b implies membership in gHookYD a b. -/
private lemma mem_gHookYD_top_mono {a b : ℕ} {ha : 0 < a} {ha1 : 0 < a - 1}
    (c : ℕ × ℕ) (hc : c ∈ gHookYD (a - 1) b ha1) : c ∈ gHookYD a b ha := by
  rcases mem_gHookYD.mp hc with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
  · exact mem_gHookYD.mpr (Or.inl ⟨hi, by omega⟩)
  · exact mem_gHookYD.mpr (Or.inr ⟨hi1, hi2, rfl⟩)

/-- Membership in gHookYD a (b-1) implies membership in gHookYD a b. -/
private lemma mem_gHookYD_bot_mono {a b : ℕ} {ha : 0 < a} (hb : 0 < b)
    (c : ℕ × ℕ) (hc : c ∈ gHookYD a (b - 1) ha) : c ∈ gHookYD a b ha := by
  rcases mem_gHookYD.mp hc with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
  · exact mem_gHookYD.mpr (Or.inl ⟨hi, hj⟩)
  · exact mem_gHookYD.mpr (Or.inr ⟨hi1, by omega, rfl⟩)

/-- Corner step for gHookYD (a≥2, b≥1):
    card(SYT(gHookYD a b)) = card(SYT(gHookYD (a-1) b)) + card(SYT(gHookYD a (b-1))) -/
private lemma card_SYT_gHookYD_step (a b : ℕ) (ha2 : 1 < a) (hb : 0 < b) :
    Fintype.card (StandardYoungTableau (gHookYD a b (by omega : 0 < a))) =
    Fintype.card (StandardYoungTableau (gHookYD (a - 1) b (by omega : 0 < a - 1))) +
    Fintype.card (StandardYoungTableau (gHookYD a (b - 1) (by omega : 0 < a))) := by
  have ha : 0 < a := by omega
  have ha1 : 0 < a - 1 := by omega
  have max_loc : ∀ T : StandardYoungTableau (gHookYD a b ha),
      T.entry (0, a - 1) = a + b ∨ T.entry (b, 0) = a + b :=
    fun T => gHook_max_at_corner a b ha2 hb T
  rw [← Fintype.card_sum]
  apply Fintype.card_congr
  exact {
    toFun := fun T =>
      if hT : T.entry (0, a - 1) = a + b then
        Sum.inl {
          entry := fun c => if c ∈ gHookYD (a - 1) b ha1 then T.entry c else 0
          entry_zero := fun c hc => by simp [hc]
          entry_range := fun c hc => by
            simp only [hc, ↓reduceIte]
            have hmem := mem_gHookYD_top_mono c hc
            refine ⟨(T.entry_range c hmem).1, ?_⟩
            have hne : T.entry c ≠ a + b := fun heq =>
              absurd (T.entry_injOn c (0, a - 1) hmem
                (mem_gHookYD.mpr (Or.inl ⟨rfl, by omega⟩)) (heq.trans hT.symm))
                (by rcases mem_gHookYD.mp hc with ⟨hi, hj⟩ | ⟨hi1, _, rfl⟩
                    · intro h; exact absurd ((Prod.mk.inj h).2) (by omega)
                    · intro h; exact absurd ((Prod.mk.inj h).1) (by omega))
            have hle := (T.entry_range c hmem).2
            rw [gHookYD_card] at hle; rw [gHookYD_card]; omega
          entry_injOn := fun c₁ c₂ hc₁ hc₂ h => by
            simp only [hc₁, hc₂, ↓reduceIte] at h
            exact T.entry_injOn c₁ c₂ (mem_gHookYD_top_mono c₁ hc₁)
              (mem_gHookYD_top_mono c₂ hc₂) h
          row_strict := fun i j₁ j₂ hc₁ hc₂ hlt => by
            simp only [hc₁, hc₂, ↓reduceIte]
            exact T.row_strict i j₁ j₂ (mem_gHookYD_top_mono _ hc₁)
              (mem_gHookYD_top_mono _ hc₂) hlt
          col_strict := fun i₁ i₂ j hc₁ hc₂ hlt => by
            simp only [hc₁, hc₂, ↓reduceIte]
            exact T.col_strict i₁ i₂ j (mem_gHookYD_top_mono _ hc₁)
              (mem_gHookYD_top_mono _ hc₂) hlt }
      else
        Sum.inr {
          entry := fun c => if c ∈ gHookYD a (b - 1) ha then T.entry c else 0
          entry_zero := fun c hc => by simp [hc]
          entry_range := fun c hc => by
            simp only [hc, ↓reduceIte]
            have hmem := mem_gHookYD_bot_mono hb c hc
            have hT' := (max_loc T).resolve_left hT
            refine ⟨(T.entry_range c hmem).1, ?_⟩
            have hne : T.entry c ≠ a + b := fun heq =>
              absurd (T.entry_injOn c (b, 0) hmem
                (mem_gHookYD.mpr (Or.inr ⟨hb, le_refl _, rfl⟩)) (heq.trans hT'.symm))
                (by rcases mem_gHookYD.mp hc with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                    · intro h; exact absurd ((Prod.mk.inj h).1) (by omega)
                    · intro h; exact absurd ((Prod.mk.inj h).1) (by omega))
            have hle := (T.entry_range c hmem).2
            rw [gHookYD_card] at hle; rw [gHookYD_card]; omega
          entry_injOn := fun c₁ c₂ hc₁ hc₂ h => by
            simp only [hc₁, hc₂, ↓reduceIte] at h
            exact T.entry_injOn c₁ c₂ (mem_gHookYD_bot_mono hb c₁ hc₁)
              (mem_gHookYD_bot_mono hb c₂ hc₂) h
          row_strict := fun i j₁ j₂ hc₁ hc₂ hlt => by
            simp only [hc₁, hc₂, ↓reduceIte]
            exact T.row_strict i j₁ j₂ (mem_gHookYD_bot_mono hb _ hc₁)
              (mem_gHookYD_bot_mono hb _ hc₂) hlt
          col_strict := fun i₁ i₂ j hc₁ hc₂ hlt => by
            simp only [hc₁, hc₂, ↓reduceIte]
            exact T.col_strict i₁ i₂ j (mem_gHookYD_bot_mono hb _ hc₁)
              (mem_gHookYD_bot_mono hb _ hc₂) hlt }
    invFun := fun x => match x with
      | Sum.inl T₁ => {
          entry := fun c => if c = (0, a - 1) then a + b else T₁.entry c
          entry_zero := fun c hc => by
            have hne : c ≠ (0, a - 1) := fun h =>
              hc (h ▸ mem_gHookYD.mpr (Or.inl ⟨rfl, by omega⟩))
            rw [if_neg hne]
            exact T₁.entry_zero c fun hc₁ => hc (mem_gHookYD_top_mono c hc₁)
          entry_range := fun c hc => by
            by_cases hce : c = (0, a - 1)
            · simp only [hce, ↓reduceIte]; rw [gHookYD_card]; exact ⟨by omega, le_refl _⟩
            · rw [if_neg hce]
              have hcμ₁ : c ∈ gHookYD (a - 1) b ha1 := by
                rcases mem_gHookYD.mp hc with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, by
                    have := fun heq => hce (Prod.ext hi heq); omega⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, hi2, rfl⟩)
              have hr := T₁.entry_range c hcμ₁
              rw [gHookYD_card] at hr; rw [gHookYD_card]; omega
          entry_injOn := fun c₁ c₂ hc₁ hc₂ h => by
            simp only at h
            by_cases h₁ : c₁ = (0, a - 1) <;> by_cases h₂ : c₂ = (0, a - 1)
            · rw [h₁, h₂]
            · simp only [h₁, ↓reduceIte, if_neg h₂] at h
              have hcμ₂ : c₂ ∈ gHookYD (a - 1) b ha1 := by
                rcases mem_gHookYD.mp hc₂ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, by
                    have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, hi2, rfl⟩)
              have := (T₁.entry_range c₂ hcμ₂).2
              rw [gHookYD_card] at this; omega
            · simp only [if_neg h₁, h₂, ↓reduceIte] at h
              have hcμ₁ : c₁ ∈ gHookYD (a - 1) b ha1 := by
                rcases mem_gHookYD.mp hc₁ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, by
                    have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, hi2, rfl⟩)
              have := (T₁.entry_range c₁ hcμ₁).2
              rw [gHookYD_card] at this; omega
            · simp only [if_neg h₁, if_neg h₂] at h
              have hcμ₁ : c₁ ∈ gHookYD (a - 1) b ha1 := by
                rcases mem_gHookYD.mp hc₁ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, by
                    have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, hi2, rfl⟩)
              have hcμ₂ : c₂ ∈ gHookYD (a - 1) b ha1 := by
                rcases mem_gHookYD.mp hc₂ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, by
                    have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, hi2, rfl⟩)
              exact T₁.entry_injOn c₁ c₂ hcμ₁ hcμ₂ h
          row_strict := fun i j₁ j₂ hc₁ hc₂ hlt => by
            simp only
            split_ifs with h₁ h₂
            · have := (Prod.ext_iff.mp h₁).2; have := (Prod.ext_iff.mp h₂).2; omega
            · have hi₁ := (Prod.ext_iff.mp h₁).1; have hj₁ := (Prod.ext_iff.mp h₁).2
              rcases mem_gHookYD.mp hc₂ with ⟨_, hj₂⟩ | ⟨hi₂, _, _⟩ <;> omega
            · have hi := (Prod.ext_iff.mp h₂).1; have hj₂ := (Prod.ext_iff.mp h₂).2
              have hcμ₁ : (i, j₁) ∈ gHookYD (a - 1) b ha1 :=
                mem_gHookYD.mpr (Or.inl ⟨hi, by omega⟩)
              have := (T₁.entry_range _ hcμ₁).2; rw [gHookYD_card] at this; omega
            · have hcμ₁ : (i, j₁) ∈ gHookYD (a - 1) b ha1 := by
                rcases mem_gHookYD.mp hc₁ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, by
                    have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, hi2, rfl⟩)
              have hcμ₂ : (i, j₂) ∈ gHookYD (a - 1) b ha1 := by
                rcases mem_gHookYD.mp hc₂ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, by
                    have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, hi2, rfl⟩)
              exact T₁.row_strict i j₁ j₂ hcμ₁ hcμ₂ hlt
          col_strict := fun i₁ i₂ j hc₁ hc₂ hlt => by
            simp only
            split_ifs with h₁ h₂
            · exact absurd hlt (by
                have := (Prod.ext_iff.mp h₁).1; have := (Prod.ext_iff.mp h₂).1; omega)
            · have hja := (Prod.ext_iff.mp h₁).2; have hi₁ := (Prod.ext_iff.mp h₁).1
              -- (i₁, j) = (0, a-1); need (i₂, j) ∈ gHookYD a b with i₂ > 0 and j = a-1
              rcases mem_gHookYD.mp hc₂ with ⟨hi₂, _⟩ | ⟨_, _, hj₂⟩
              · omega  -- i₂ = 0 < i₂ impossible
              · omega  -- j = 0 but j = a-1 ≥ 1 since a ≥ 2
            · exact absurd hlt (by have := (Prod.ext_iff.mp h₂).1; omega)
            · have hcμ₁ : (i₁, j) ∈ gHookYD (a - 1) b ha1 := by
                rcases mem_gHookYD.mp hc₁ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, by
                    have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, hi2, rfl⟩)
              have hcμ₂ : (i₂, j) ∈ gHookYD (a - 1) b ha1 := by
                rcases mem_gHookYD.mp hc₂ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, by
                    have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, hi2, rfl⟩)
              exact T₁.col_strict i₁ i₂ j hcμ₁ hcμ₂ hlt }
      | Sum.inr T₂ => {
          entry := fun c => if c = (b, 0) then a + b else T₂.entry c
          entry_zero := fun c hc => by
            have hne : c ≠ (b, 0) := fun h =>
              hc (h ▸ mem_gHookYD.mpr (Or.inr ⟨hb, le_refl _, rfl⟩))
            rw [if_neg hne]
            exact T₂.entry_zero c fun hc₁ => hc (mem_gHookYD_bot_mono hb c hc₁)
          entry_range := fun c hc => by
            by_cases hce : c = (b, 0)
            · simp only [hce, ↓reduceIte]; rw [gHookYD_card]; exact ⟨by omega, le_refl _⟩
            · rw [if_neg hce]
              have hcμ₂ : c ∈ gHookYD a (b - 1) ha := by
                rcases mem_gHookYD.mp hc with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, hj⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, by
                    have := fun heq => hce (Prod.ext heq rfl); omega, rfl⟩)
              have hr := T₂.entry_range c hcμ₂
              rw [gHookYD_card] at hr; rw [gHookYD_card]; omega
          entry_injOn := fun c₁ c₂ hc₁ hc₂ h => by
            simp only at h
            by_cases h₁ : c₁ = (b, 0) <;> by_cases h₂ : c₂ = (b, 0)
            · rw [h₁, h₂]
            · simp only [h₁, ↓reduceIte, if_neg h₂] at h
              have hcμ₂ : c₂ ∈ gHookYD a (b - 1) ha := by
                rcases mem_gHookYD.mp hc₂ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, hj⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, by
                    have := fun heq => h₂ (Prod.ext heq rfl); omega, rfl⟩)
              have := (T₂.entry_range c₂ hcμ₂).2
              rw [gHookYD_card] at this; omega
            · simp only [if_neg h₁, h₂, ↓reduceIte] at h
              have hcμ₁ : c₁ ∈ gHookYD a (b - 1) ha := by
                rcases mem_gHookYD.mp hc₁ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, hj⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, by
                    have := fun heq => h₁ (Prod.ext heq rfl); omega, rfl⟩)
              have := (T₂.entry_range c₁ hcμ₁).2
              rw [gHookYD_card] at this; omega
            · simp only [if_neg h₁, if_neg h₂] at h
              have hcμ₁ : c₁ ∈ gHookYD a (b - 1) ha := by
                rcases mem_gHookYD.mp hc₁ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, hj⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, by
                    have := fun heq => h₁ (Prod.ext heq rfl); omega, rfl⟩)
              have hcμ₂ : c₂ ∈ gHookYD a (b - 1) ha := by
                rcases mem_gHookYD.mp hc₂ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, hj⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, by
                    have := fun heq => h₂ (Prod.ext heq rfl); omega, rfl⟩)
              exact T₂.entry_injOn c₁ c₂ hcμ₁ hcμ₂ h
          row_strict := fun i j₁ j₂ hc₁ hc₂ hlt => by
            simp only
            split_ifs with h₁ h₂
            · have := (Prod.ext_iff.mp h₁).2; have := (Prod.ext_iff.mp h₂).2; omega
            · have hi₁ := (Prod.ext_iff.mp h₁).1; have hj₁ := (Prod.ext_iff.mp h₁).2
              -- (i, j₁) = (b, 0), so j₁ = 0. (i, j₂) ∈ gHookYD a b with j₂ > 0.
              -- gHookYD cells with i = b: only (b, 0). So j₂ = 0, contradiction with j₁ < j₂.
              rcases mem_gHookYD.mp hc₂ with ⟨hi₂, _⟩ | ⟨_, hi₂, hj₂⟩
              · omega  -- i = 0 but i = b ≥ 1
              · omega  -- j₂ = 0 but j₂ > j₁ = 0
            · have hi := (Prod.ext_iff.mp h₂).1; have hj₂ := (Prod.ext_iff.mp h₂).2
              have hcμ₁ : (i, j₁) ∈ gHookYD a (b - 1) ha := by
                rcases mem_gHookYD.mp hc₁ with ⟨hi', hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi', hj⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, by
                    have := fun heq => h₂ (Prod.ext heq rfl); omega, rfl⟩)
              have := (T₂.entry_range _ hcμ₁).2; rw [gHookYD_card] at this; omega
            · have hcμ₁ : (i, j₁) ∈ gHookYD a (b - 1) ha := by
                rcases mem_gHookYD.mp hc₁ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, hj⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, by
                    have := fun heq => h₁ (Prod.ext heq rfl); omega, rfl⟩)
              have hcμ₂ : (i, j₂) ∈ gHookYD a (b - 1) ha := by
                rcases mem_gHookYD.mp hc₂ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, hj⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, by
                    have := fun heq => h₂ (Prod.ext heq rfl); omega, rfl⟩)
              exact T₂.row_strict i j₁ j₂ hcμ₁ hcμ₂ hlt
          col_strict := fun i₁ i₂ j hc₁ hc₂ hlt => by
            simp only
            split_ifs with h₁ h₂
            · exact absurd hlt (by
                have := (Prod.ext_iff.mp h₁).1; have := (Prod.ext_iff.mp h₂).1; omega)
            · have hi₁ := (Prod.ext_iff.mp h₁).1; have hj₁ := (Prod.ext_iff.mp h₁).2
              -- (i₁, j) = (b, 0): i₁ = b, j = 0; i₂ > b; (i₂, 0) ∉ gHookYD a b
              exact absurd (mem_gHookYD.mp hc₂)
                (by rintro (⟨hi₂, _⟩ | ⟨_, hi₂_le, _⟩) <;> omega)
            · exact absurd hlt (by have := (Prod.ext_iff.mp h₂).1; omega)
            · have hcμ₁ : (i₁, j) ∈ gHookYD a (b - 1) ha := by
                rcases mem_gHookYD.mp hc₁ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, hj⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, by
                    have := fun heq => h₁ (Prod.ext heq rfl); omega, rfl⟩)
              have hcμ₂ : (i₂, j) ∈ gHookYD a (b - 1) ha := by
                rcases mem_gHookYD.mp hc₂ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
                · exact mem_gHookYD.mpr (Or.inl ⟨hi, hj⟩)
                · exact mem_gHookYD.mpr (Or.inr ⟨hi1, by
                    have := fun heq => h₂ (Prod.ext heq rfl); omega, rfl⟩)
              exact T₂.col_strict i₁ i₂ j hcμ₁ hcμ₂ hlt }
    left_inv := fun T => by
      apply StandardYoungTableau.ext; intro c
      by_cases hT : T.entry (0, a - 1) = a + b
      · simp only [dif_pos hT]
        simp only
        split_ifs with hce hcr
        · rw [hce]; exact hT.symm
        · rfl
        · symm; apply T.entry_zero; intro hcμ
          -- c ∉ gHookYD (a-1) b and c ≠ (0,a-1) → c ∉ gHookYD a b → False
          rcases mem_gHookYD.mp hcμ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
          · exact hcr (mem_gHookYD.mpr (Or.inl ⟨hi, by
              have := fun heq => hce (Prod.ext hi heq); omega⟩))
          · exact hcr (mem_gHookYD.mpr (Or.inr ⟨hi1, hi2, rfl⟩))
      · simp only [dif_neg hT]
        simp only
        split_ifs with hce hcr
        · rw [hce]; exact ((max_loc T).resolve_left hT).symm
        · rfl
        · symm; apply T.entry_zero; intro hcμ
          rcases mem_gHookYD.mp hcμ with ⟨hi, hj⟩ | ⟨hi1, hi2, rfl⟩
          · exact hcr (mem_gHookYD.mpr (Or.inl ⟨hi, hj⟩))
          · exact hcr (mem_gHookYD.mpr (Or.inr ⟨hi1, by
              have := fun heq => hce (Prod.ext heq rfl); omega, rfl⟩))
    right_inv := fun x => by
      match x with
      | Sum.inl T₁ =>
        -- invFun (Sum.inl T₁) has entry (0, a-1) = a+b (since (0,a-1) = (0,a-1))
        have hentry_top : (if (0, a - 1) = (0, a - 1) then (a + b : ℕ) else T₁.entry (0, a - 1))
            = a + b := if_pos rfl
        simp only [dif_pos hentry_top]
        congr 1
        apply StandardYoungTableau.ext; intro c
        simp only
        split_ifs with hcr hce
        · -- c ∈ gHookYD (a-1) b and c = (0,a-1): impossible since (0,a-1) ∉ gHookYD (a-1) b
          exfalso; rw [hce] at hcr
          exact absurd hcr (by simp [mem_gHookYD]; omega)
        · rfl  -- c ∈ gHookYD (a-1) b, c ≠ (0,a-1): entry = T₁.entry c
        · -- c ∉ gHookYD (a-1) b: entry = 0 = T₁.entry c
          symm; apply T₁.entry_zero; exact hcr
      | Sum.inr T₂ =>
        -- invFun (Sum.inr T₂) has entry (0, a-1) = T₂.entry (0, a-1) < a+b
        have hne_corner : (0, a - 1) ≠ (b, 0) := by
          intro h; have := (Prod.mk.inj h).1; omega
        have hentry_ne : ¬(if (0, a - 1) = (b, 0) then (a + b : ℕ) else T₂.entry (0, a - 1))
            = a + b := by
          rw [if_neg hne_corner]
          have := (T₂.entry_range (0, a - 1)
            (mem_gHookYD.mpr (Or.inl ⟨rfl, by omega⟩))).2
          rw [gHookYD_card] at this; omega
        simp only [dif_neg hentry_ne]
        congr 1
        apply StandardYoungTableau.ext; intro c
        simp only
        split_ifs with hcr hce
        · exfalso; rw [hce] at hcr
          exact absurd hcr (by simp [mem_gHookYD]; omega)
        · rfl
        · symm; apply T₂.entry_zero; exact hcr
  }

-- ========================
-- SYT count for gHookYD: by double induction
-- ========================

/-- card(SYT(gHookYD a b)) = C(a+b-1, b).
    Proved by double induction on b (outer) and a (inner).
    Base b=0: card=1=C(a-1,0). Base a=1: card=1=C(b,b).
    Step a≥2,b≥1: corner recursion gives card(a,b)=card(a-1,b)+card(a,b-1), Pascal closes. -/
private lemma card_SYT_gHookYD (a b : ℕ) (ha : 0 < a) :
    Fintype.card (StandardYoungTableau (gHookYD a b ha)) = Nat.choose (a + b - 1) b := by
  induction b generalizing a with
  | zero =>
    rw [gHookYD_zero_eq_oneRowYD a ha]
    rw [Fintype.card_eq_one_iff.mpr ⟨oneRowSYT a, oneRowSYT_unique a⟩]
    simp [Nat.choose_zero_right]
  | succ b ihb =>
    -- Inner induction on a
    induction a with
    | zero => omega
    | succ a iha =>
      rcases Nat.eq_zero_or_pos a with rfl | ha_pos
      · -- a = 0, so a+1 = 1: gHookYD 1 (b+1) = oneColYD (b+2)
        rw [gHookYD_one_eq_oneColYD (b + 1)]
        rw [Fintype.card_eq_one_iff.mpr ⟨oneColSYT (b + 2), oneColSYT_unique (b + 2)⟩]
        simp [Nat.choose_self]
      · -- a ≥ 1, so a+1 ≥ 2: use step lemma
        have ha_succ_pos : 0 < a + 1 := Nat.succ_pos a
        have ha2 : 1 < a + 1 := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_of_succ_le_succ (Nat.succ_le_succ ha_pos))
        rw [card_SYT_gHookYD_step (a + 1) (b + 1) ha2 (Nat.succ_pos b)]
        -- After step: card(gHookYD a (b+1) ha_pos) + card(gHookYD (a+1) b ha_succ_pos)
        -- = C(a+b, b+1) + C(a+b, b)  [by iha and ihb]
        -- = C(a+b+1, b+1)  [Pascal]
        have h1 : Fintype.card (StandardYoungTableau (gHookYD a (b + 1) ha_pos)) =
            Nat.choose (a + b) (b + 1) := by
          have := iha ha_pos
          simp only [show a + (b + 1) - 1 = a + b from by omega] at this
          exact this
        have h2 : Fintype.card (StandardYoungTableau (gHookYD (a + 1) b ha_succ_pos)) =
            Nat.choose (a + b) b := by
          have := ihb (a + 1) ha_succ_pos
          simp only [show a + 1 + b - 1 = a + b from by omega] at this
          exact this
        simp only [show (a + 1) - 1 = a from Nat.succ_sub_one a]
        rw [h1, h2]
        simp only [show a + 1 + (b + 1) - 1 = a + b + 1 from by omega]
        rw [Nat.choose_succ_succ (a + b) b]
        ring

-- ========================
-- HLF for gHookYD
-- ========================

/-- **Hook-length formula for generalized hook shapes.**
    card(SYT(gHookYD a b)) × hookProd(gHookYD a b) = (a+b)!
    Proof: C(a+b-1,b) × (a+b) × (a-1)! × b! = (a+b)! via choose identity. -/
private theorem hook_length_formula_gHookYD (a b : ℕ) (ha : 0 < a) :
    Fintype.card (StandardYoungTableau (gHookYD a b ha)) * hookProd (gHookYD a b ha) =
    (gHookYD a b ha).card.factorial := by
  rw [gHookYD_card, card_SYT_gHookYD a b ha, hookProd_gHookYD a b ha]
  -- Goal: C(a+b-1, b) * ((a+b) * (a-1)! * b!) = (a+b)!
  -- Use C(n, k) * k! * (n-k)! = n! with n=a+b-1, k=b
  have hkey : Nat.choose (a + b - 1) b * b.factorial * (a - 1).factorial =
      (a + b - 1).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := a + b - 1) (k := b) (by omega)
    rw [show a + b - 1 - b = a - 1 from by omega] at h
    linarith
  calc Nat.choose (a + b - 1) b * ((a + b) * (a - 1).factorial * b.factorial)
      = Nat.choose (a + b - 1) b * b.factorial * (a - 1).factorial * (a + b) := by ring
    _ = (a + b - 1).factorial * (a + b) := by rw [hkey]
    _ = (a + b).factorial := by
        conv_rhs => rw [show a + b = a + b - 1 + 1 from by omega]
        rw [Nat.factorial_succ]; ring

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

-- ============================================================
-- PART VIII: Hook-Shape Young Diagrams (m+1, 1)
-- ============================================================
/-
  The "hook-shape" (m+1, 1) has m+2 cells: row 0 length m+1, row 1 length 1.
  Hook lengths: h(0,0)=m+2, h(0,j)=m+1-j for j=1,...,m, h(1,0)=1.
  hookProd = (m+2) × m!
  card(SYT(m+1,1)) = m+1  (entry(1,0) can be any of {2,...,m+2})
  Hook formula: (m+1) × (m+2) × m! = (m+2)!
-/

/-- The hook-shape Young diagram with row 0 of length m+1 and row 1 of length 1. -/
def hookShapeYD (m : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens [m + 1, 1] (by
    simp only [List.SortedGE, List.Sorted, List.pairwise_cons, List.mem_singleton,
               forall_eq, List.Pairwise.nil, and_true]
    omega)

lemma mem_hookShapeYD {m i j : ℕ} :
    (i, j) ∈ hookShapeYD m ↔ (i = 0 ∧ j < m + 1) ∨ (i = 1 ∧ j = 0) := by
  simp only [hookShapeYD, YoungDiagram.mem_ofRowLens,
    List.length_cons, List.length_singleton]
  constructor
  · rintro ⟨hi, hj⟩
    interval_cases i
    · left; exact ⟨rfl, by simpa [List.getElem_cons_zero] using hj⟩
    · right; exact ⟨rfl, by have := hj; simp at this; omega⟩
    · omega
  · rintro (⟨rfl, hj⟩ | ⟨rfl, rfl⟩)
    · exact ⟨by omega, by simpa [List.getElem_cons_zero] using hj⟩
    · exact ⟨by omega, by simp⟩

private lemma hookShapeYD_cells_eq (m : ℕ) :
    (hookShapeYD m).cells =
    (Finset.range (m + 1)).image (Prod.mk 0) ∪ {(1, 0)} := by
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, mem_hookShapeYD, Finset.mem_union,
    Finset.mem_image, Finset.mem_range, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, hj⟩ | ⟨rfl, rfl⟩)
    · left; exact ⟨j, hj, rfl, rfl⟩
    · right; exact ⟨rfl, rfl⟩
  · rintro (⟨k, hk, rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · left; exact ⟨rfl, hk⟩; · right; exact ⟨rfl, rfl⟩

private lemma hookShapeYD_cells_disj (m : ℕ) :
    Disjoint ((Finset.range (m + 1)).image (Prod.mk 0)) ({(1, 0)} : Finset (ℕ × ℕ)) :=
  Finset.disjoint_left.mpr (by simp [Finset.mem_image, Prod.mk.injEq])

lemma hookShapeYD_card (m : ℕ) : (hookShapeYD m).card = m + 2 := by
  unfold YoungDiagram.card
  rw [hookShapeYD_cells_eq, Finset.card_union_of_disjoint (hookShapeYD_cells_disj m),
      Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2),
      Finset.card_range, Finset.card_singleton]

lemma rowLen_hookShapeYD_zero (m : ℕ) : (hookShapeYD m).rowLen 0 = m + 1 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]; simp [mem_hookShapeYD]
  · have := YoungDiagram.mem_iff_lt_rowLen.mp
        (mem_hookShapeYD.mpr (Or.inl ⟨rfl, Nat.lt_succ_self m⟩)); omega

lemma rowLen_hookShapeYD_one (m : ℕ) : (hookShapeYD m).rowLen 1 = 1 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]; simp [mem_hookShapeYD]
  · have := YoungDiagram.mem_iff_lt_rowLen.mp
        (mem_hookShapeYD.mpr (Or.inr ⟨rfl, rfl⟩)); omega

lemma colLen_hookShapeYD_zero (m : ℕ) : (hookShapeYD m).colLen 0 = 2 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]; simp [mem_hookShapeYD]
  · have h0 := YoungDiagram.mem_iff_lt_colLen.mp
        (mem_hookShapeYD.mpr (Or.inl ⟨rfl, Nat.zero_lt_succ m⟩))
    have h1 := YoungDiagram.mem_iff_lt_colLen.mp
        (mem_hookShapeYD.mpr (Or.inr ⟨rfl, rfl⟩)); omega

lemma colLen_hookShapeYD_succ {m j : ℕ} (hj : 1 ≤ j) (hj' : j < m + 1) :
    (hookShapeYD m).colLen j = 1 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]
    simp [mem_hookShapeYD]; omega
  · have := YoungDiagram.mem_iff_lt_colLen.mp
        (mem_hookShapeYD.mpr (Or.inl ⟨rfl, hj'⟩)); omega

lemma hookLength_hookShapeYD_zero_zero (m : ℕ) :
    hookLength (hookShapeYD m) 0 0 = m + 2 := by
  have heq := hookLength_add_eq (hookShapeYD m)
      (mem_hookShapeYD.mpr (Or.inl ⟨rfl, Nat.zero_lt_succ m⟩))
  rw [rowLen_hookShapeYD_zero, colLen_hookShapeYD_zero] at heq; omega

lemma hookLength_hookShapeYD_zero_succ {m j : ℕ} (hj : j < m) :
    hookLength (hookShapeYD m) 0 (j + 1) = m - j := by
  have heq := hookLength_add_eq (hookShapeYD m)
      (mem_hookShapeYD.mpr (Or.inl ⟨rfl, by omega⟩))
  rw [rowLen_hookShapeYD_zero, colLen_hookShapeYD_succ (by omega) (by omega)] at heq; omega

lemma hookLength_hookShapeYD_one_zero (m : ℕ) :
    hookLength (hookShapeYD m) 1 0 = 1 := by
  have heq := hookLength_add_eq (hookShapeYD m)
      (mem_hookShapeYD.mpr (Or.inr ⟨rfl, rfl⟩))
  rw [rowLen_hookShapeYD_one, colLen_hookShapeYD_zero] at heq; omega

/-- hookProd(hookShapeYD m) = (m+2) × m!. -/
theorem hookProd_hookShapeYD (m : ℕ) :
    hookProd (hookShapeYD m) = (m + 2) * m.factorial := by
  unfold hookProd
  rw [hookShapeYD_cells_eq, Finset.prod_union (hookShapeYD_cells_disj m),
      Finset.prod_singleton, hookLength_hookShapeYD_one_zero, mul_one,
      Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).2)]
  show ∏ j ∈ Finset.range (m + 1), hookLength (hookShapeYD m) 0 j = (m + 2) * m.factorial
  -- Peel j=0 from the front via insert decomposition
  have hsplit : Finset.range (m + 1) = insert 0 ((Finset.range m).image (· + 1)) := by
    ext j; simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hj; rcases Nat.eq_zero_or_pos j with rfl | hpos
      · exact Or.inl rfl
      · exact Or.inr ⟨j - 1, by omega, by omega⟩
    · rintro (rfl | ⟨k, hk, rfl⟩) <;> omega
  rw [hsplit, Finset.prod_insert (by simp [Finset.mem_image]),
      hookLength_hookShapeYD_zero_zero,
      Finset.prod_image (fun a _ b _ h => by omega),
      Finset.prod_congr rfl (fun j hj =>
        hookLength_hookShapeYD_zero_succ (Finset.mem_range.mp hj)),
      ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]

-- ============================================================
-- PART VIIIb: SYT of Hook-Shape — Explicit Construction
-- ============================================================

/-
  Each SYT of hookShapeYD m is determined by where the "arm" entry sits in row 1.
  Entry(0,0) = 1 always. Entry(1,0) ∈ {2,...,m+2} freely.
  Given entry(1,0) = k+2 for k ∈ {0,...,m}:
    entry(0,j) = j+1  for j ≤ k   (values before the arm entry)
    entry(0,j) = j+2  for j > k   (values after the arm entry, skipping k+2)
    entry(1,0) = k+2
-/

/-- The k-th SYT of hookShapeYD m: entry(1,0) = k+2, row 0 fills {1,...,m+2}\{k+2}. -/
private def hookSYT (m : ℕ) (k : Fin (m + 1)) : StandardYoungTableau (hookShapeYD m) where
  entry := fun ⟨i, j⟩ =>
    if i = 0 ∧ j < m + 1 then
      if j ≤ k.val then j + 1 else j + 2
    else if i = 1 ∧ j = 0 then k.val + 2
    else 0
  entry_zero := fun ⟨i, j⟩ hc => by
    have h0 : ¬(i = 0 ∧ j < m + 1) := fun ⟨hi, hj⟩ =>
      hc (mem_hookShapeYD.mpr (Or.inl ⟨hi, hj⟩))
    have h1 : ¬(i = 1 ∧ j = 0) := fun ⟨hi, hj⟩ =>
      hc (mem_hookShapeYD.mpr (Or.inr ⟨hi, hj⟩))
    simp only [if_neg h0, if_neg h1]
  entry_range := fun ⟨i, j⟩ hc => by
    simp only [hookShapeYD_card]
    rcases mem_hookShapeYD.mp hc with ⟨rfl, hj⟩ | ⟨rfl, rfl⟩
    · simp only [if_pos ⟨rfl, hj⟩]
      split_ifs with h
      · exact ⟨by omega, by omega⟩
      · exact ⟨by omega, by push_neg at h; omega⟩
    · simp only [show ¬(1 = 0 ∧ 0 < m + 1) from by omega, if_false,
                 if_pos ⟨rfl, rfl⟩]
      exact ⟨by omega, by have := k.isLt; omega⟩
  entry_injOn := fun ⟨i₁, j₁⟩ hc₁ ⟨i₂, j₂⟩ hc₂ heq => by
    rcases mem_hookShapeYD.mp hc₁ with ⟨rfl, hj₁⟩ | ⟨rfl, rfl⟩
    · rcases mem_hookShapeYD.mp hc₂ with ⟨rfl, hj₂⟩ | ⟨rfl, rfl⟩
      · -- both in row 0
        simp only [if_pos ⟨rfl, hj₁⟩, if_pos ⟨rfl, hj₂⟩] at heq
        congr 1
        split_ifs at heq with h1 h2 <;> omega
      · -- c₁ in row 0, c₂ = (1,0)
        simp only [if_pos ⟨rfl, hj₁⟩,
          show ¬(1 = 0 ∧ 0 < m + 1) from by omega, if_false,
          if_pos ⟨rfl, rfl⟩] at heq
        split_ifs at heq with h <;> omega
    · rcases mem_hookShapeYD.mp hc₂ with ⟨rfl, hj₂⟩ | ⟨rfl, rfl⟩
      · -- c₁ = (1,0), c₂ in row 0
        simp only [show ¬(1 = 0 ∧ 0 < m + 1) from by omega, if_false,
          if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, hj₂⟩] at heq
        split_ifs at heq with h <;> omega
      · rfl
  row_strict := fun i j₁ j₂ hc₁ hc₂ hjlt => by
    rcases mem_hookShapeYD.mp hc₁ with ⟨rfl, hj₁⟩ | ⟨h₁, _⟩
    · have hj₂ := (mem_hookShapeYD.mp hc₂).resolve_right (by simp)
      simp only [if_pos ⟨rfl, hj₁⟩, if_pos ⟨rfl, hj₂.2⟩]
      split_ifs <;> omega
    · -- row 1 only has j=0, so j₁ < j₂ is impossible
      have := (mem_hookShapeYD.mp hc₁).resolve_left (by simp [h₁])
      have := (mem_hookShapeYD.mp hc₂).resolve_left (by intro ⟨h, _⟩; omega)
      omega
  col_strict := fun i₁ i₂ j hc₁ hc₂ hilt => by
    -- i₁ < i₂ with cells in hookShapeYD: must be i₁=0, i₂=1, j=0
    have h1 : i₁ = 0 ∧ j < m + 1 := by
      rcases mem_hookShapeYD.mp hc₁ with ⟨h, hj⟩ | ⟨h, _⟩
      · exact ⟨h, hj⟩
      · exact absurd h (by omega)
    have h2 : i₂ = 1 ∧ j = 0 := by
      rcases mem_hookShapeYD.mp hc₂ with ⟨h, _⟩ | ⟨h, hj⟩
      · exact absurd h (by omega)
      · exact ⟨h, hj⟩
    obtain ⟨rfl, hj⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
    simp only [if_pos ⟨rfl, hj⟩,
      show ¬(1 = 0 ∧ (0 : ℕ) < m + 1) from by omega, if_false,
      if_pos ⟨rfl, rfl⟩]
    split_ifs with h
    · omega  -- j=0 ≤ k, entry(0,0) = 1 < k+2
    · push_neg at h; omega  -- j=0 > k impossible since k ≥ 0

/-- Entry at (0,0) in any SYT of hookShapeYD m is 1. -/
private lemma hookSYT_entry_zero_zero_eq_one {m : ℕ}
    (T : StandardYoungTableau (hookShapeYD m)) : T.entry (0, 0) = 1 := by
  have hmem : ∀ j < m + 1, (0, j) ∈ hookShapeYD m :=
    fun j hj => mem_hookShapeYD.mpr (Or.inl ⟨rfl, hj⟩)
  have hmem10 : (1, 0) ∈ hookShapeYD m := mem_hookShapeYD.mpr (Or.inr ⟨rfl, rfl⟩)
  -- entry(0,0) ≥ 1
  have hlb : 1 ≤ T.entry (0, 0) :=
    (T.entry_range (0, 0) (hmem 0 (Nat.zero_lt_succ m))).1
  suffices hle : T.entry (0, 0) ≤ 1 by omega
  -- Row chain: T.entry(0,j) ≥ T.entry(0,0) + j  (by row_strict induction)
  have hrow_lb : ∀ j < m + 1, T.entry (0, 0) + j ≤ T.entry (0, j) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hstep : T.entry (0, j) < T.entry (0, j + 1) :=
        T.row_strict 0 j (j + 1) (hmem j (by omega)) (hmem (j + 1) hj)
          (Nat.lt_succ_self j)
      linarith [ih (by omega)]
  -- T.entry(0,m) ≤ m+2 (entry_range with card = m+2)
  have hub_m : T.entry (0, m) ≤ m + 2 := by
    have := (T.entry_range (0, m) (hmem m (Nat.lt_succ_self m))).2
    rwa [hookShapeYD_card] at this
  -- So T.entry(0,0) + m ≤ T.entry(0,m) ≤ m+2 → T.entry(0,0) ≤ 2
  have hub00 : T.entry (0, 0) ≤ 2 := by linarith [hrow_lb m (Nat.lt_succ_self m)]
  -- if T.entry(0,0) = 2, derive contradiction via injectivity
  by_contra h
  push_neg at h
  have heq00 : T.entry (0, 0) = 2 := by omega
  -- Upward chain: T.entry(0,j) + (m-j) ≤ T.entry(0,m)
  have hrow_ub_m : ∀ j k, j + k < m + 1 → T.entry (0, j) + k ≤ T.entry (0, j + k) := by
    intro j k hjk
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : T.entry (0, j + k) < T.entry (0, j + k + 1) :=
        T.row_strict 0 (j + k) (j + k + 1)
          (hmem (j + k) (by omega)) (hmem (j + k + 1) (by omega))
          (Nat.lt_succ_self _)
      linarith [ih (by omega)]
  -- T.entry(0,j) = j+2 for all j = 0,...,m
  have heq_row : ∀ j < m + 1, T.entry (0, j) = j + 2 := by
    intro j hj
    have hlb_j : 2 + j ≤ T.entry (0, j) := by
      have := hrow_lb j hj; rw [heq00] at this; linarith
    have hub_j : T.entry (0, j) ≤ j + 2 := by
      have hup := hrow_ub_m j (m - j) (by omega)
      rw [Nat.add_sub_cancel' (Nat.le_of_lt_succ hj)] at hup
      linarith
    omega
  -- T.entry(1,0) > T.entry(0,0) = 2 and ≤ m+2
  have hcol : T.entry (0, 0) < T.entry (1, 0) :=
    T.col_strict 0 1 0 (hmem 0 (Nat.zero_lt_succ m)) hmem10 Nat.zero_lt_one
  have hub10 : T.entry (1, 0) ≤ m + 2 := by
    have := (T.entry_range (1, 0) hmem10).2; rwa [hookShapeYD_card] at this
  have hv_lt : T.entry (1, 0) - 2 < m + 1 := by omega
  -- T.entry(0, T.entry(1,0)-2) = T.entry(1,0) (by heq_row)
  have hmatch : T.entry (0, T.entry (1, 0) - 2) = T.entry (1, 0) := by
    rw [heq_row (T.entry (1, 0) - 2) hv_lt]; omega
  -- But entry_injOn says they must be the same cell
  have hne : (0, T.entry (1, 0) - 2) ≠ (1, 0) := by simp
  exact hne (T.entry_injOn (0, T.entry (1, 0) - 2) (hmem _ hv_lt) hmem10 hmatch)

/-- Every SYT of hookShapeYD m equals hookSYT m k for k = T.entry(1,0) - 2. -/
private lemma hookSYT_unique {m : ℕ} (T : StandardYoungTableau (hookShapeYD m)) :
    ∃ k : Fin (m + 1), T = hookSYT m k := by
  have hmem : ∀ j < m + 1, (0, j) ∈ hookShapeYD m :=
    fun j hj => mem_hookShapeYD.mpr (Or.inl ⟨rfl, hj⟩)
  have hmem10 : (1, 0) ∈ hookShapeYD m := mem_hookShapeYD.mpr (Or.inr ⟨rfl, rfl⟩)
  have h00 : T.entry (0, 0) = 1 := hookSYT_entry_zero_zero_eq_one T
  -- Row bounds: j+1 ≤ entry(0,j) ≤ j+2
  have hlb : ∀ j < m + 1, j + 1 ≤ T.entry (0, j) := by
    intro j hj
    induction j with
    | zero => simp [h00]
    | succ j ih =>
      have := T.row_strict 0 j (j + 1) (hmem j (by omega)) (hmem (j + 1) hj) (Nat.lt_succ_self j)
      linarith [ih (by omega)]
  have hub : ∀ j < m + 1, T.entry (0, j) ≤ j + 2 := by
    intro j hj
    have hchain : ∀ k, j + k < m + 1 → T.entry (0, j) + k ≤ T.entry (0, j + k) := by
      intro k hjk
      induction k with
      | zero => simp
      | succ k ih =>
        have := T.row_strict 0 (j + k) (j + k + 1)
            (hmem (j + k) (by omega)) (hmem (j + k + 1) (by omega)) (Nat.lt_succ_self _)
        linarith [ih (by omega)]
    have hend : T.entry (0, m) ≤ m + 2 := by
      have := (T.entry_range (0, m) (hmem m (Nat.lt_succ_self m))).2
      rwa [hookShapeYD_card] at this
    have := hchain (m - j) (by omega)
    rw [Nat.add_sub_cancel' (Nat.le_of_lt_succ hj)] at this
    linarith
  -- Define k := T.entry(1,0) - 2
  have hcol : T.entry (0, 0) < T.entry (1, 0) :=
    T.col_strict 0 1 0 (hmem 0 (Nat.zero_lt_succ m)) hmem10 Nat.zero_lt_one
  have hub10 : T.entry (1, 0) ≤ m + 2 := by
    have := (T.entry_range (1, 0) hmem10).2; rwa [hookShapeYD_card] at this
  have hk_bound : T.entry (1, 0) - 2 < m + 1 := by linarith [h00]
  refine ⟨⟨T.entry (1, 0) - 2, hk_bound⟩, ?_⟩
  apply StandardYoungTableau.ext; intro ⟨i, j⟩
  by_cases hc : (i, j) ∈ hookShapeYD m
  · rcases mem_hookShapeYD.mp hc with ⟨rfl, hj⟩ | ⟨rfl, rfl⟩
    · -- Cell (0,j): show T.entry(0,j) = hookSYT entry
      simp only [hookSYT, if_pos ⟨rfl, hj⟩, Fin.val]
      have hne : T.entry (0, j) ≠ T.entry (1, 0) := fun h =>
        absurd (T.entry_injOn (0, j) hc hmem10 h) (by simp)
      split_ifs with hjk
      · -- j ≤ k: show T.entry(0,j) = j+1 (rule out j+2)
        have hrange : T.entry (0, j) = j + 1 ∨ T.entry (0, j) = j + 2 := by
          have := hlb j hj; have := hub j hj; omega
        rcases hrange with h | h
        · exact h
        · -- T.entry(0,j) = j+2. Chain up: entry(0,k) ≥ T.entry(1,0)
          exfalso
          have hchain_up : ∀ j', j ≤ j' → j' < m + 1 →
              T.entry (0, j) + (j' - j) ≤ T.entry (0, j') := by
            intro j' hjj' hj'
            have : ∀ n, j + n ≤ j' → j + n < m + 1 → T.entry (0, j) + n ≤ T.entry (0, j + n) := by
              intro n hn1 hn2
              induction n with
              | zero => simp
              | succ n ih =>
                have := T.row_strict 0 (j + n) (j + n + 1)
                    (hmem (j + n) (by omega)) (hmem (j + n + 1) hn2) (Nat.lt_succ_self _)
                linarith [ih (by omega) (by omega)]
            have := this (j' - j) (by omega) (by omega)
            rwa [Nat.add_sub_cancel' hjj'] at this
          have hkm : T.entry (1, 0) - 2 < m + 1 := hk_bound
          have hup := hchain_up (T.entry (1, 0) - 2) (by omega) hkm
          rw [h] at hup
          have hsimp : j + 2 + (T.entry (1, 0) - 2 - j) = T.entry (1, 0) := by omega
          rw [hsimp] at hup
          have hub_k := hub (T.entry (1, 0) - 2) hkm
          have heq : T.entry (0, T.entry (1, 0) - 2) = T.entry (1, 0) := by omega
          exact absurd (T.entry_injOn (0, T.entry (1, 0) - 2) (hmem _ hkm) hmem10 heq)
            (by simp)
      · -- j > k: show T.entry(0,j) = j+2 (rule out j+1)
        push_neg at hjk
        have hrange : T.entry (0, j) = j + 1 ∨ T.entry (0, j) = j + 2 := by
          have := hlb j hj; have := hub j hj; omega
        rcases hrange with h | h
        · -- T.entry(0,j) = j+1. Chain: entry(0,k+1) ≤ T.entry(1,0)
          exfalso
          have hchain_dn : ∀ j', j' ≤ j → j' < m + 1 →
              T.entry (0, j') + (j - j') ≤ T.entry (0, j) := by
            intro j' hj'j hj'
            have : ∀ n, j' + n ≤ j → j' + n < m + 1 → T.entry (0, j') + n ≤ T.entry (0, j' + n) := by
              intro n hn1 hn2
              induction n with
              | zero => simp
              | succ n ih =>
                have := T.row_strict 0 (j' + n) (j' + n + 1)
                    (hmem (j' + n) (by omega)) (hmem (j' + n + 1) hn2) (Nat.lt_succ_self _)
                linarith [ih (by omega) (by omega)]
            have := this (j - j') (by omega) (by omega)
            rwa [Nat.add_sub_cancel' hj'j] at this
          have hk1 := hchain_dn (T.entry (1, 0) - 1) (by omega) (by omega)
          rw [h] at hk1
          have hlb_k1 := hlb (T.entry (1, 0) - 1) (by omega)
          have heq : T.entry (0, T.entry (1, 0) - 1) = T.entry (1, 0) := by omega
          exact absurd (T.entry_injOn (0, T.entry (1, 0) - 1) (hmem _ (by omega)) hmem10 heq)
            (by simp)
        · exact h
    · -- Cell (1,0): T.entry(1,0) = k+2
      simp only [hookSYT, show ¬(1 = 0 ∧ (0 : ℕ) < m + 1) from by omega, if_false,
                 if_pos ⟨rfl, rfl⟩, Fin.val]
      omega
  · -- Not in μ: both are 0
    rw [T.entry_zero _ hc]
    simp only [hookSYT, show ¬(i = 0 ∧ j < m + 1) from fun ⟨hi, hj⟩ =>
      hc (mem_hookShapeYD.mpr (Or.inl ⟨hi, hj⟩)),
      show ¬(i = 1 ∧ j = 0) from fun ⟨hi, hj⟩ =>
      hc (mem_hookShapeYD.mpr (Or.inr ⟨hi, hj⟩)), if_false]

/-- The explicit SYTs hookSYT m k are pairwise distinct. -/
private lemma hookSYT_injective (m : ℕ) : Function.Injective (hookSYT m) := by
  intro k₁ k₂ h
  have : (hookSYT m k₁).entry (1, 0) = (hookSYT m k₂).entry (1, 0) :=
    congr_fun (congrArg StandardYoungTableau.entry h) (1, 0)
  simp only [hookSYT, show ¬(1 = 0 ∧ (0 : ℕ) < m + 1) from by omega, if_false,
             if_pos ⟨rfl, rfl⟩] at this
  exact Fin.ext (by omega)

/-- card(SYT(hookShapeYD m)) = m+1.
    Proof: hookSYT m is a bijection Fin(m+1) → SYT(hookShapeYD m). -/
theorem card_SYT_hookShapeYD (m : ℕ) :
    Fintype.card (StandardYoungTableau (hookShapeYD m)) = m + 1 := by
  have hbij : Function.Bijective (hookSYT m) :=
    ⟨hookSYT_injective m, fun T =>
      let ⟨k, hk⟩ := hookSYT_unique T; ⟨k, hk.symm⟩⟩
  have h := Fintype.card_congr (Equiv.ofBijective (hookSYT m) hbij)
  rw [Fintype.card_fin] at h
  exact h.symm

/-- **Hook-length formula for hook-shape Young diagrams.**
    card(SYT(hookShapeYD m)) × hookProd(hookShapeYD m) = (m+2)!
    Proved: hookProd = (m+2)×m!, card(SYT) = m+1, and (m+1)×(m+2)×m! = (m+2)! -/
theorem hook_length_formula_hook_shape (m : ℕ) :
    Fintype.card (StandardYoungTableau (hookShapeYD m)) * hookProd (hookShapeYD m) =
    (hookShapeYD m).card.factorial := by
  rw [hookShapeYD_card, card_SYT_hookShapeYD, hookProd_hookShapeYD]
  rw [show (m + 2).factorial = (m + 2) * (m + 1) * m.factorial by
        rw [Nat.factorial_succ, Nat.factorial_succ]; ring]
  ring

-- ============================================================
-- PART IX: Hook-Length Formula for 2-Row Rectangular Diagrams
-- ============================================================

/-
  The 2-row rectangular Young diagram twoRectYD m has 2 rows each of length m
  (total 2m cells).
    hookLength(0,j) = m - j + 1  (for j < m)
    hookLength(1,j) = m - j      (for j < m)
    hookProd        = (m+1)! × m!   [proved]
    card(SYT(m,m))  = C_m           [sorry: RSK bijection with ballot sequences]
  Hook formula: C_m × (m+1)! × m! = (2m)!
  (The numerical identity is LGVCorollaries.hook_length_formula_two_row.)
-/

/-- The 2-row rectangular Young diagram: 2 rows each of length m. -/
def twoRectYD (m : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens [m, m] (by
    simp only [List.SortedGE, List.Sorted, List.pairwise_cons, List.mem_singleton,
               forall_eq, List.Pairwise.nil, and_true])

/-- (i,j) ∈ twoRectYD m ↔ (i = 0 ∨ i = 1) ∧ j < m -/
lemma mem_twoRectYD {m i j : ℕ} :
    (i, j) ∈ twoRectYD m ↔ (i = 0 ∧ j < m) ∨ (i = 1 ∧ j < m) := by
  simp only [twoRectYD, YoungDiagram.mem_ofRowLens, List.length_cons, List.length_singleton]
  constructor
  · rintro ⟨hi, hj⟩
    interval_cases i
    · left; exact ⟨rfl, by simpa [List.getElem_cons_zero] using hj⟩
    · right; exact ⟨rfl, by simpa [List.getElem_cons_succ, List.getElem_cons_zero] using hj⟩
    · omega
  · rintro (⟨rfl, hj⟩ | ⟨rfl, hj⟩)
    · exact ⟨by omega, by simpa [List.getElem_cons_zero] using hj⟩
    · exact ⟨by omega, by simpa [List.getElem_cons_succ, List.getElem_cons_zero] using hj⟩

/-- twoRectYD has 2m cells. -/
lemma twoRectYD_card (m : ℕ) : (twoRectYD m).card = 2 * m := by
  have hcells : (twoRectYD m).cells =
      (Finset.range m).image (Prod.mk 0) ∪ (Finset.range m).image (Prod.mk 1) := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, mem_twoRectYD, Finset.mem_union, Finset.mem_image,
      Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, hj⟩ | ⟨rfl, hj⟩)
      · left; exact ⟨j, hj, rfl, rfl⟩
      · right; exact ⟨j, hj, rfl, rfl⟩
    · rintro (⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩)
      · left; exact ⟨rfl, hk⟩; · right; exact ⟨rfl, hk⟩
  unfold YoungDiagram.card
  rw [hcells, Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (by
    simp [Finset.mem_image, Prod.mk.injEq])),
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2),
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2),
    Finset.card_range, Finset.card_range]

private lemma twoRectYD_cells_eq (m : ℕ) :
    (twoRectYD m).cells =
    (Finset.range m).image (Prod.mk 0) ∪ (Finset.range m).image (Prod.mk 1) := by
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, mem_twoRectYD, Finset.mem_union, Finset.mem_image,
    Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, hj⟩ | ⟨rfl, hj⟩)
    · left; exact ⟨j, hj, rfl, rfl⟩
    · right; exact ⟨j, hj, rfl, rfl⟩
  · rintro (⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩)
    · left; exact ⟨rfl, hk⟩; · right; exact ⟨rfl, hk⟩

private lemma twoRectYD_cells_disj (m : ℕ) :
    Disjoint ((Finset.range m).image (Prod.mk 0)) ((Finset.range m).image (Prod.mk 1)) :=
  Finset.disjoint_left.mpr (by simp [Finset.mem_image, Prod.mk.injEq])

lemma rowLen_twoRectYD_zero (m : ℕ) : (twoRectYD m).rowLen 0 = m := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]; simp [mem_twoRectYD]
  · cases m with
    | zero => simp
    | succ m =>
      have h := YoungDiagram.mem_iff_lt_rowLen.mp (mem_twoRectYD.mpr (Or.inl ⟨rfl, m.lt_succ_self⟩))
      omega

lemma rowLen_twoRectYD_one (m : ℕ) : (twoRectYD m).rowLen 1 = m := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]; simp [mem_twoRectYD]
  · cases m with
    | zero => simp
    | succ m =>
      have h := YoungDiagram.mem_iff_lt_rowLen.mp (mem_twoRectYD.mpr (Or.inr ⟨rfl, m.lt_succ_self⟩))
      omega

lemma colLen_twoRectYD {m j : ℕ} (hj : j < m) : (twoRectYD m).colLen j = 2 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]; simp [mem_twoRectYD]
  · have h0 := YoungDiagram.mem_iff_lt_colLen.mp (mem_twoRectYD.mpr (Or.inl ⟨rfl, hj⟩))
    have h1 := YoungDiagram.mem_iff_lt_colLen.mp (mem_twoRectYD.mpr (Or.inr ⟨rfl, hj⟩))
    omega

/-- hookLength(0,j) = m - j + 1 (arm = m-j-1, leg = 1) -/
lemma hookLength_twoRectYD_row0 {m j : ℕ} (hj : j < m) :
    hookLength (twoRectYD m) 0 j = m - j + 1 := by
  have heq := hookLength_add_eq (twoRectYD m) (mem_twoRectYD.mpr (Or.inl ⟨rfl, hj⟩))
  rw [rowLen_twoRectYD_zero, colLen_twoRectYD hj] at heq
  omega

/-- hookLength(1,j) = m - j (arm = m-j-1, leg = 0) -/
lemma hookLength_twoRectYD_row1 {m j : ℕ} (hj : j < m) :
    hookLength (twoRectYD m) 1 j = m - j := by
  have heq := hookLength_add_eq (twoRectYD m) (mem_twoRectYD.mpr (Or.inr ⟨rfl, hj⟩))
  rw [rowLen_twoRectYD_one, colLen_twoRectYD hj] at heq
  omega

/-- hookProd(twoRectYD m) = (m+1)! × m!
    Row 0: ∏_{j<m} (m-j+1) = (m+1)!  (product 2·3·...·(m+1))
    Row 1: ∏_{j<m} (m-j)   = m!      (product 1·2·...·m) -/
theorem hookProd_twoRectYD (m : ℕ) :
    hookProd (twoRectYD m) = (m + 1).factorial * m.factorial := by
  unfold hookProd
  rw [twoRectYD_cells_eq, Finset.prod_union (twoRectYD_cells_disj m),
      Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).2),
      Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).2)]
  show (∏ j ∈ Finset.range m, hookLength (twoRectYD m) 0 j) *
       (∏ j ∈ Finset.range m, hookLength (twoRectYD m) 1 j) =
       (m + 1).factorial * m.factorial
  -- Row 0: ∏_{j<m} (m-j+1) = (m+1)!
  have hrow0 : ∏ j ∈ Finset.range m, hookLength (twoRectYD m) 0 j = (m + 1).factorial := by
    rw [Finset.prod_congr rfl (fun j hj => hookLength_twoRectYD_row0 (Finset.mem_range.mp hj)),
        Finset.prod_congr rfl (fun j hj => show m - j + 1 = (m + 1) - j from by
          have := Finset.mem_range.mp hj; omega),
        ← Nat.descFactorial_eq_prod_range]
    -- (m+1).descFactorial m = (m+1)!
    have hstep := Nat.descFactorial_succ (m + 1) m
    have hone : (m + 1) - m = 1 := by omega
    rw [hone, Nat.mul_one, Nat.descFactorial_self] at hstep
    exact hstep.symm
  -- Row 1: ∏_{j<m} (m-j) = m!
  have hrow1 : ∏ j ∈ Finset.range m, hookLength (twoRectYD m) 1 j = m.factorial := by
    rw [Finset.prod_congr rfl (fun j hj => hookLength_twoRectYD_row1 (Finset.mem_range.mp hj)),
        ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  rw [hrow0, hrow1]

/-- The Catalan number Cn m equals ballotSeqCount (m+1) m.
    Both definitions unfold to C(2m,m) - C(2m,m+1) after arithmetic simplification. -/
lemma catalan_eq_ballot (m : ℕ) :
    LatticePathLGV.Cn m = LatticePathLGV.ballotSeqCount (m + 1) m := by
  simp only [LatticePathLGV.Cn, LatticePathLGV.ballotSeqCount]
  congr 1 <;> omega

/-- card(SYT(twoRectYD m)) = C_m (the m-th Catalan number).

    Proof strategy:
    Step 1: Bijection SYT(m,m) ↔ ballot LPaths of m East + m North steps.
      - Forward: T ↦ path where step k is North iff k+1 ∈ row-0 of T
      - Column condition T(0,j) < T(1,j) ↔ ballot condition #North ≥ #East in every prefix
      - Inverse: ballot path ↦ SYT with row-0 = {positions of North steps + 1}

    Step 2: Count ballot LPaths of m East + m North = Cn m.
      - Bijection: prepend-North maps (ballot m,m) ↔ (strictly ballot m+1,m)
      - ballotSeqCount (m+1) m = Cn m [by catalan_eq_ballot, trivial definitional equality]
      - Or directly: |ballot (m,m)| = C(2m,m) - C(2m,m+1) = Cn m via reflection principle

    Key ingredients available:
      - catalan_eq_ballot: Cn m = ballotSeqCount (m+1) m (proved above)
      - ballot_via_path_count: ballot count = |pathType m m| - |pathType (m-1) (m+1)|
      - Finset.orderIsoOfFin: for extracting sorted elements of a Finset

    Estimated ~150-200 lines to formalize the bijection using Finset.orderIsoOfFin.
    [HARD: known result, needs formalization] -/
-- ============================================================
-- PART IXb: Ballot Bijection for card_SYT_twoRectYD
-- ============================================================

/-- Complement of S in Fin (2*m). -/
private abbrev compFin (m : ℕ) (S : Finset (Fin (2 * m))) : Finset (Fin (2 * m)) :=
  Finset.univ.filter (· ∉ S)

private lemma compFin_card (m : ℕ) (S : Finset (Fin (2 * m))) (hS : S.card = m) :
    (compFin m S).card = m := by
  simp only [compFin, Finset.filter_not,
    Finset.card_sdiff (Finset.subset_univ S), Finset.card_fin, hS]

/-- Row-0 entries of T, mapped to Fin(2m) by subtracting 1. Strictly monotone in j. -/
private lemma sytRow0StrictMono (m : ℕ) (T : StandardYoungTableau (twoRectYD m)) :
    StrictMono (fun j : Fin m =>
      (⟨T.entry (0, j.val) - 1, by
        have := (T.entry_range (0, j.val)
          (mem_twoRectYD.mpr (Or.inl ⟨rfl, j.isLt⟩)))
        rw [twoRectYD_card] at this; omega⟩ : Fin (2 * m))) := by
  intro j₁ j₂ hlt
  simp only [Fin.mk_lt_mk]
  have hr₁ := (T.entry_range (0, j₁.val)
    (mem_twoRectYD.mpr (Or.inl ⟨rfl, j₁.isLt⟩))).1
  have hr₂ := (T.entry_range (0, j₂.val)
    (mem_twoRectYD.mpr (Or.inl ⟨rfl, j₂.isLt⟩))).1
  have hrow := T.row_strict 0 j₁.val j₂.val
    (mem_twoRectYD.mpr (Or.inl ⟨rfl, j₁.isLt⟩))
    (mem_twoRectYD.mpr (Or.inl ⟨rfl, j₂.isLt⟩)) hlt
  omega

/-- Row-0 Finset of a SYT: the set of (entry(0,j)-1) for j < m, as a Finset of Fin(2m). -/
private noncomputable def sytRow0Set (m : ℕ) (T : StandardYoungTableau (twoRectYD m)) :
    Finset (Fin (2 * m)) :=
  Finset.univ.image (fun j : Fin m =>
    ⟨T.entry (0, j.val) - 1, by
      have := (T.entry_range (0, j.val)
        (mem_twoRectYD.mpr (Or.inl ⟨rfl, j.isLt⟩)))
      rw [twoRectYD_card] at this; omega⟩)

private lemma sytRow0Set_card (m : ℕ) (T : StandardYoungTableau (twoRectYD m)) :
    (sytRow0Set m T).card = m := by
  apply Finset.card_image_of_injective
  exact (sytRow0StrictMono m T).injective

/-- The j-th element of sytRow0Set T (in sorted order) equals T.entry(0,j) - 1. -/
private lemma sytRow0Set_orderEmb (m : ℕ) (T : StandardYoungTableau (twoRectYD m)) (j : Fin m) :
    (sytRow0Set m T).orderEmbOfFin (sytRow0Set_card m T) j =
    ⟨T.entry (0, j.val) - 1, by
      have := (T.entry_range (0, j.val)
        (mem_twoRectYD.mpr (Or.inl ⟨rfl, j.isLt⟩)))
      rw [twoRectYD_card] at this; omega⟩ := by
  apply Finset.orderEmbOfFin_unique
  · intro x; simp [sytRow0Set, Finset.mem_image]
  · exact sytRow0StrictMono m T

/-- Row-1 entries of T are the complement of sytRow0Set T. -/
private lemma sytRow1_mem_comp (m : ℕ) (T : StandardYoungTableau (twoRectYD m)) (j : Fin m) :
    (⟨T.entry (1, j.val) - 1, by
        have := (T.entry_range (1, j.val)
          (mem_twoRectYD.mpr (Or.inr ⟨rfl, j.isLt⟩)))
        rw [twoRectYD_card] at this; omega⟩ : Fin (2 * m)) ∈
    compFin m (sytRow0Set m T) := by
  simp only [compFin, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [sytRow0Set, Finset.mem_image, Finset.mem_univ, true_and]
  intro ⟨k, hk⟩
  simp only [Fin.mk.injEq] at hk
  -- If T.entry(1,j) - 1 = T.entry(0,k) - 1, then entries are equal → same cell
  have hrj := (T.entry_range (1, j.val)
    (mem_twoRectYD.mpr (Or.inr ⟨rfl, j.isLt⟩))).1
  have hrk := (T.entry_range (0, k.val)
    (mem_twoRectYD.mpr (Or.inl ⟨rfl, k.isLt⟩))).1
  have heq : T.entry (1, j.val) = T.entry (0, k.val) := by omega
  -- entry_injOn: same entry → same cell
  have hinj := T.entry_injOn (1, j.val) (0, k.val)
    (mem_twoRectYD.mpr (Or.inr ⟨rfl, j.isLt⟩))
    (mem_twoRectYD.mpr (Or.inl ⟨rfl, k.isLt⟩)) heq
  simp at hinj

/-- Row-1 is strictly monotone (shifted). -/
private lemma sytRow1StrictMono (m : ℕ) (T : StandardYoungTableau (twoRectYD m)) :
    StrictMono (fun j : Fin m =>
      (⟨T.entry (1, j.val) - 1, by
        have := (T.entry_range (1, j.val)
          (mem_twoRectYD.mpr (Or.inr ⟨rfl, j.isLt⟩)))
        rw [twoRectYD_card] at this; omega⟩ : Fin (2 * m))) := by
  intro j₁ j₂ hlt
  simp only [Fin.mk_lt_mk]
  have hr₁ := (T.entry_range (1, j₁.val)
    (mem_twoRectYD.mpr (Or.inr ⟨rfl, j₁.isLt⟩))).1
  have hr₂ := (T.entry_range (1, j₂.val)
    (mem_twoRectYD.mpr (Or.inr ⟨rfl, j₂.isLt⟩))).1
  have hrow := T.row_strict 1 j₁.val j₂.val
    (mem_twoRectYD.mpr (Or.inr ⟨rfl, j₁.isLt⟩))
    (mem_twoRectYD.mpr (Or.inr ⟨rfl, j₂.isLt⟩)) hlt
  omega

/-- The j-th element of compFin (sytRow0Set T) equals T.entry(1,j)-1. -/
private lemma sytRow1Set_orderEmb (m : ℕ) (T : StandardYoungTableau (twoRectYD m)) (j : Fin m) :
    (compFin m (sytRow0Set m T)).orderEmbOfFin
        (compFin_card m (sytRow0Set m T) (sytRow0Set_card m T)) j =
    ⟨T.entry (1, j.val) - 1, by
      have := (T.entry_range (1, j.val)
        (mem_twoRectYD.mpr (Or.inr ⟨rfl, j.isLt⟩)))
      rw [twoRectYD_card] at this; omega⟩ := by
  apply Finset.orderEmbOfFin_unique
  · intro x; exact sytRow1_mem_comp m T x
  · exact sytRow1StrictMono m T

/-- SYT satisfies the ballot condition on its row-0 Finset. -/
private lemma sytRow0Set_ballot (m : ℕ) (T : StandardYoungTableau (twoRectYD m)) (j : Fin m) :
    (sytRow0Set m T).orderEmbOfFin (sytRow0Set_card m T) j <
    (compFin m (sytRow0Set m T)).orderEmbOfFin
        (compFin_card m (sytRow0Set m T) (sytRow0Set_card m T)) j := by
  rw [sytRow0Set_orderEmb, sytRow1Set_orderEmb]
  simp only [Fin.mk_lt_mk]
  have hr₀ := (T.entry_range (0, j.val)
    (mem_twoRectYD.mpr (Or.inl ⟨rfl, j.isLt⟩))).1
  have hr₁ := (T.entry_range (1, j.val)
    (mem_twoRectYD.mpr (Or.inr ⟨rfl, j.isLt⟩))).1
  have hcol := T.col_strict 0 1 j.val
    (mem_twoRectYD.mpr (Or.inl ⟨rfl, j.isLt⟩))
    (mem_twoRectYD.mpr (Or.inr ⟨rfl, j.isLt⟩)) (by norm_num)
  omega

-- ============================================================
-- PART IXc: Inverse Map (Ballot Finset → SYT)
-- ============================================================

/-- Construct a SYT from a ballot Finset S of size m: row-0 gets sorted S, row-1 gets
    sorted complement. -/
private noncomputable def ballotSYT (m : ℕ) (S : Finset (Fin (2 * m))) (hS : S.card = m)
    (hB : ∀ j : Fin m,
      S.orderEmbOfFin hS j <
      (compFin m S).orderEmbOfFin (compFin_card m S hS) j) :
    StandardYoungTableau (twoRectYD m) where
  entry := fun c =>
    if h : c ∈ twoRectYD m then
      if c.1 = 0 then
        have hj : c.2 < m := by
          rcases mem_twoRectYD.mp h with ⟨_, hj⟩ | ⟨hi, _⟩
          · exact hj
          · simp [show c.1 = 1 from by rw [← hi]; rfl] at *
        (S.orderEmbOfFin hS ⟨c.2, hj⟩).val + 1
      else -- c.1 = 1
        have hj : c.2 < m := by
          rcases mem_twoRectYD.mp h with ⟨hi, _⟩ | ⟨_, hj⟩
          · simp [show c.1 = 0 from by rw [← hi]; rfl] at *
          · exact hj
        ((compFin m S).orderEmbOfFin (compFin_card m S hS) ⟨c.2, hj⟩).val + 1
    else 0
  entry_zero := by
    intro c hc; simp [dif_neg hc]
  entry_range := by
    intro c hc
    simp only [dif_pos hc]
    split_ifs with hi
    · have hj : c.2 < m := by
        rcases mem_twoRectYD.mp hc with ⟨_, hj⟩ | ⟨h1, _⟩
        · exact hj; · simp [show c.1 = 1 from by rw [← h1]; rfl] at hi
      constructor
      · omega
      · have := (S.orderEmbOfFin hS ⟨c.2, hj⟩).isLt
        rw [twoRectYD_card]; omega
    · have hj : c.2 < m := by
        rcases mem_twoRectYD.mp hc with ⟨h0, _⟩ | ⟨_, hj⟩
        · exact absurd (by rw [← h0]; rfl : c.1 = 0) hi
        · exact hj
      constructor
      · omega
      · have := ((compFin m S).orderEmbOfFin (compFin_card m S hS) ⟨c.2, hj⟩).isLt
        rw [twoRectYD_card]; omega
  entry_injOn := by
    intro c₁ c₂ hc₁ hc₂ heq
    simp only [dif_pos hc₁, dif_pos hc₂] at heq
    -- Both cells in twoRectYD m; each has row 0 or 1
    rcases mem_twoRectYD.mp hc₁ with ⟨h1i, h1j⟩ | ⟨h1i, h1j⟩ <;>
    rcases mem_twoRectYD.mp hc₂ with ⟨h2i, h2j⟩ | ⟨h2i, h2j⟩ <;>
    simp only [h1i, h2i, ↓reduceIte, show (0 : ℕ) ≠ 1 from Nat.zero_ne_one,
               show (1 : ℕ) ≠ 0 from Nat.one_ne_zero, not_false_eq_true] at heq ⊢
    · -- Both row 0: S[j₁]+1 = S[j₂]+1 → j₁ = j₂
      have : S.orderEmbOfFin hS ⟨c₁.2, h1j⟩ = S.orderEmbOfFin hS ⟨c₂.2, h2j⟩ := by
        ext; omega
      have := (S.orderEmbOfFin hS).injective this
      ext <;> [rw [← h1i, ← h2i]; exact congr_arg Prod.snd (Fin.ext_iff.mpr this)]
    · -- Row 0 and row 1: S[j₁]+1 = S'[j₂]+1 → S[j₁] = S'[j₂]
      exfalso
      have heqv : S.orderEmbOfFin hS ⟨c₁.2, h1j⟩ =
          (compFin m S).orderEmbOfFin (compFin_card m S hS) ⟨c₂.2, h2j⟩ := by
        ext; omega
      have hlt := hB ⟨c₁.2, h1j⟩
      rw [heqv] at hlt
      -- Now hlt: comp[j₁] < comp[j₂]? No: same element in S and S' impossible
      have hmem₁ := Finset.orderEmbOfFin_mem S hS ⟨c₁.2, h1j⟩
      have hmem₂ := Finset.orderEmbOfFin_mem (compFin m S) (compFin_card m S hS) ⟨c₂.2, h2j⟩
      simp only [compFin, Finset.mem_filter, Finset.mem_univ, true_and] at hmem₂
      rw [← heqv] at hmem₂
      exact hmem₂ hmem₁
    · -- Row 1 and row 0: symmetric
      exfalso
      have heqv : (compFin m S).orderEmbOfFin (compFin_card m S hS) ⟨c₁.2, h1j⟩ =
          S.orderEmbOfFin hS ⟨c₂.2, h2j⟩ := by
        ext; omega
      have hmem₁ := Finset.orderEmbOfFin_mem (compFin m S) (compFin_card m S hS) ⟨c₁.2, h1j⟩
      have hmem₂ := Finset.orderEmbOfFin_mem S hS ⟨c₂.2, h2j⟩
      simp only [compFin, Finset.mem_filter, Finset.mem_univ, true_and] at hmem₁
      rw [heqv] at hmem₁
      exact hmem₁ hmem₂
    · -- Both row 1: S'[j₁]+1 = S'[j₂]+1 → j₁ = j₂
      have : (compFin m S).orderEmbOfFin (compFin_card m S hS) ⟨c₁.2, h1j⟩ =
          (compFin m S).orderEmbOfFin (compFin_card m S hS) ⟨c₂.2, h2j⟩ := by
        ext; omega
      have := ((compFin m S).orderEmbOfFin (compFin_card m S hS)).injective this
      ext <;> [rw [← h1i, ← h2i]; exact congr_arg Prod.snd (Fin.ext_iff.mpr this)]
  row_strict := by
    intro i j₁ j₂ hc₁ hc₂ hjlt
    simp only [dif_pos hc₁, dif_pos hc₂]
    rcases mem_twoRectYD.mp hc₁ with ⟨hi, h1j⟩ | ⟨hi, h1j⟩ <;>
    rcases mem_twoRectYD.mp hc₂ with ⟨hi2, h2j⟩ | ⟨hi2, h2j⟩ <;>
    simp only [hi, hi2, show (0 : ℕ) ≠ 1 from Nat.zero_ne_one, not_false_eq_true, ↓reduceIte]
    all_goals try (rw [← hi, ← hi2] at hjlt ⊢)
    -- Row 0, j₁ < j₂: S[j₁] < S[j₂] by orderEmb strict mono
    · have hlt : (S.orderEmbOfFin hS ⟨j₁, h1j⟩) < S.orderEmbOfFin hS ⟨j₂, h2j⟩ := by
        apply (S.orderEmbOfFin hS).strictMono; simpa
      simp only [Fin.lt_iff_val_lt_val] at hlt; omega
    -- Row 1, j₁ < j₂: comp[j₁] < comp[j₂]
    · have hlt := ((compFin m S).orderEmbOfFin (compFin_card m S hS)).strictMono
        (show (⟨j₁, h1j⟩ : Fin m) < ⟨j₂, h2j⟩ from by simpa)
      simp only [Fin.lt_iff_val_lt_val] at hlt; omega
  col_strict := by
    intro i₁ i₂ j hc₁ hc₂ hilt
    simp only [dif_pos hc₁, dif_pos hc₂]
    -- i₁ < i₂, with i₁, i₂ ∈ {0, 1}: so i₁ = 0, i₂ = 1
    have hi₁ : i₁ = 0 := by
      rcases mem_twoRectYD.mp hc₁ with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact h; omega]
    have hi₂ : i₂ = 1 := by
      rcases mem_twoRectYD.mp hc₂ with ⟨h, _⟩ | ⟨h, _⟩ <;> [omega; exact h]
    have hj : j < m := by
      rcases mem_twoRectYD.mp hc₁ with ⟨_, h⟩ | ⟨_, h⟩; exact h; omega
    subst hi₁; subst hi₂
    simp only [show (0 : ℕ) ≠ 1 from Nat.zero_ne_one, not_false_eq_true,
               show ¬(1 : ℕ) = 0 from Nat.one_ne_zero, ↓reduceIte]
    -- S[j] + 1 < comp[j] + 1 ↔ S[j] < comp[j]: ballot condition
    have hlt := hB ⟨j, hj⟩
    simp only [Fin.lt_iff_val_lt_val] at hlt; omega

-- Bijection: SYT(m,m) ≃ {S // S.card = m ∧ ballot cond}
private noncomputable def sytBallotEquiv (m : ℕ) :
    StandardYoungTableau (twoRectYD m) ≃
    {S : Finset (Fin (2 * m)) // ∃ (hS : S.card = m),
      ∀ j : Fin m,
        S.orderEmbOfFin hS j <
        (compFin m S).orderEmbOfFin (compFin_card m S hS) j} where
  toFun T := ⟨sytRow0Set m T,
    sytRow0Set_card m T,
    sytRow0Set_ballot m T⟩
  invFun := fun ⟨S, hS, hB⟩ => ballotSYT m S hS hB
  left_inv := by
    intro T
    apply StandardYoungTableau.ext
    intro c
    by_cases hc : c ∈ twoRectYD m
    · -- c ∈ twoRectYD m: check row 0 or 1
      simp only [ballotSYT, dif_pos hc]
      rcases mem_twoRectYD.mp hc with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · -- Row 0: ballotSYT gives S[j]+1 = T.entry(0,j)-1+1 = T.entry(0,j)
        subst hi; simp only [show (0 : ℕ) ≠ 1 from Nat.zero_ne_one, ↓reduceIte, not_false_eq_true]
        rw [sytRow0Set_orderEmb]
        have hr := (T.entry_range (0, c.2) (mem_twoRectYD.mpr (Or.inl ⟨rfl, hj⟩))).1
        omega
      · -- Row 1: ballotSYT gives comp[j]+1 = T.entry(1,j)-1+1 = T.entry(1,j)
        subst hi
        have h01 : ¬(1 : ℕ) = 0 := Nat.one_ne_zero
        simp only [h01, ↓reduceIte, not_false_eq_true]
        rw [sytRow1Set_orderEmb]
        have hr := (T.entry_range (1, c.2) (mem_twoRectYD.mpr (Or.inr ⟨rfl, hj⟩))).1
        omega
    · simp [ballotSYT, dif_neg hc, T.entry_zero c hc]
  right_inv := by
    intro ⟨S, hS, hB⟩
    simp only
    ext
    apply Finset.Subset.antisymm
    · -- sytRow0Set (ballotSYT S hS hB) ⊆ S
      intro x hx
      simp only [sytRow0Set, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨j, _, hxj⟩ := hx
      simp only [ballotSYT, dif_pos (mem_twoRectYD.mpr (Or.inl ⟨rfl, j.isLt⟩)),
                 show (0 : ℕ) ≠ 1 from Nat.zero_ne_one, ↓reduceIte,
                 not_false_eq_true] at hxj
      -- x = S[j]
      have : x = S.orderEmbOfFin hS j := by ext; omega
      rw [this]; exact Finset.orderEmbOfFin_mem S hS j
    · -- S ⊆ sytRow0Set (ballotSYT S hS hB)
      intro x hx
      simp only [sytRow0Set, Finset.mem_image, Finset.mem_univ, true_and]
      -- x = S[j] for some j: use image_orderEmbOfFin_univ
      have hximg : x ∈ Finset.image (S.orderEmbOfFin hS) Finset.univ := by
        rw [Finset.image_orderEmbOfFin_univ S hS]; exact hx
      obtain ⟨j, -, hjx⟩ := Finset.mem_image.mp hximg
      refine ⟨j, ?_⟩
      -- (ballotSYT).entry(0, j) = S[j].val + 1, so entry - 1 = S[j].val
      simp only [ballotSYT, dif_pos (mem_twoRectYD.mpr (Or.inl ⟨rfl, j.isLt⟩)),
                 show (0 : ℕ) ≠ 1 from Nat.zero_ne_one, ↓reduceIte, not_false_eq_true]
      -- Need: ⟨S[j].val + 1 - 1, ...⟩ = x
      -- By hjx: S[j] = x, so S[j].val = x.val, and S[j].val + 1 - 1 = x.val
      ext
      simp only [Fin.val_mk]
      have hval : (S.orderEmbOfFin hS j).val = x.val := congr_arg Fin.val hjx
      omega

-- ============================================================
-- PART IXd: Lindstrom Reflection Bijection for Ballot Count
-- ============================================================

/-- The Lindstrom reflection at barrier k: swaps comp(S) and S across k. -/
private noncomputable def lRefl (m : ℕ) (S : Finset (Fin (2 * m)))
    (k : Fin (2 * m)) : Finset (Fin (2 * m)) :=
  (compFin m S).filter (· ≤ k) ∪ S.filter (k < ·)

/-- Complement of the reflected set. -/
private lemma compFin_lRefl {m : ℕ} (S : Finset (Fin (2 * m))) (k : Fin (2 * m)) :
    compFin m (lRefl m S k) = S.filter (· ≤ k) ∪ (compFin m S).filter (k < ·) := by
  ext x
  simp only [lRefl, compFin, mem_union, mem_filter, mem_univ, true_and]
  rcases le_or_lt x k with hle | hgt <;> rcases em (x ∈ S) with hxS | hxS
  · simp [hxS, hle, not_lt.mpr hle]
  · simp [hxS, hle, not_lt.mpr hle]
  · simp [hxS, hgt, not_le.mpr hgt]
  · simp [hxS, hgt, not_le.mpr hgt]

/-- lRefl is a set-theoretic involution at any fixed barrier k. -/
private lemma lRefl_invol {m : ℕ} (S : Finset (Fin (2 * m))) (k : Fin (2 * m)) :
    lRefl m (lRefl m S k) k = S := by
  simp only [lRefl, compFin_lRefl]
  ext x
  simp only [mem_union, mem_filter, mem_univ, true_and]
  rcases le_or_lt x k with hle | hgt <;> rcases em (x ∈ S) with hxS | hxS
  · simp [hxS, hle, not_lt.mpr hle]
  · simp [hxS, hle, not_lt.mpr hle]
  · simp [hxS, hgt, not_le.mpr hgt]
  · simp [hxS, hgt, not_le.mpr hgt]

/-- The filter of S at the j-th orderEmbOfFin element has cardinality j+1. -/
private lemma filter_le_orderEmb_eq {α : Type*} [LinearOrder α] [Fintype α]
    {n : ℕ} (S : Finset α) (hS : S.card = n) (j : Fin n) :
    (S.filter (· ≤ S.orderEmbOfFin hS j)).card = j + 1 := by
  have heq : S.filter (· ≤ S.orderEmbOfFin hS j) =
      Finset.image (S.orderEmbOfFin hS) (Finset.Iic j) := by
    ext x
    simp only [mem_filter, mem_image, mem_Iic]
    constructor
    · intro ⟨hx, hle⟩
      rw [← Finset.image_orderEmbOfFin_univ S hS] at hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, (S.orderEmbOfFin hS).le_iff_le.mp hle, rfl⟩
    · intro ⟨i, hij, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem S hS i, (S.orderEmbOfFin hS).le_iff_le.mpr hij⟩
  rw [heq, Finset.card_image_of_injective _ (S.orderEmbOfFin hS).injective, Fin.card_Iic]

/-- For a bad m-subset S with bad index j, the reflected set has m+1 elements. -/
private lemma lRefl_bad_card {m : ℕ} (S : Finset (Fin (2 * m))) (hS : S.card = m)
    (j : Fin m)
    (hbad : (compFin m S).orderEmbOfFin (compFin_card m S hS) j < S.orderEmbOfFin hS j)
    (hgood : ∀ i : Fin m, i < j →
        S.orderEmbOfFin hS i < (compFin m S).orderEmbOfFin (compFin_card m S hS) i) :
    (lRefl m S ((compFin m S).orderEmbOfFin (compFin_card m S hS) j)).card = m + 1 := by
  set k := (compFin m S).orderEmbOfFin (compFin_card m S hS) j with hk_def
  simp only [lRefl]
  have hdisj : Disjoint ((compFin m S).filter (· ≤ k)) (S.filter (k < ·)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [compFin, mem_filter, mem_univ, true_and] at hx1
    exact hx1 (mem_filter.mp hx2).1
  rw [Finset.card_union_of_disjoint hdisj]
  -- Count |comp(S).filter(≤k)| = j + 1
  have hcomp_count : ((compFin m S).filter (· ≤ k)).card = j + 1 :=
    filter_le_orderEmb_eq (compFin m S) (compFin_card m S hS) j
  -- Count |S.filter(≤k)| = j (S has no element = k since S ∩ comp(S) = ∅, and S[j] > k)
  have hS_le_count : (S.filter (· ≤ k)).card = j := by
    have heq : S.filter (· ≤ k) = Finset.image (S.orderEmbOfFin hS) (Finset.Iio j) := by
      ext x
      simp only [mem_filter, mem_image, mem_Iio]
      constructor
      · intro ⟨hx, hle⟩
        rw [← Finset.image_orderEmbOfFin_univ S hS] at hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        refine ⟨i, ?_, rfl⟩
        by_contra h
        push_neg at h
        rcases h.eq_or_lt with heq | hgt
        · rw [heq] at hbad; exact absurd hle (not_le.mpr hbad)
        · exact absurd hle (not_le.mpr
            (lt_trans hbad ((S.orderEmbOfFin hS).strictMono hgt)))
      · intro ⟨i, hi, rfl⟩
        refine ⟨Finset.orderEmbOfFin_mem S hS i, ?_⟩
        -- S[i] < comp[i] ≤ comp[j] = k, so S[i] ≤ k
        have h1 : S.orderEmbOfFin hS i < (compFin m S).orderEmbOfFin (compFin_card m S hS) i :=
          hgood i hi
        have h2 : (compFin m S).orderEmbOfFin (compFin_card m S hS) i <
                  (compFin m S).orderEmbOfFin (compFin_card m S hS) j :=
          ((compFin m S).orderEmbOfFin (compFin_card m S hS)).strictMono hi
        exact le_of_lt (lt_trans h1 h2)
    rw [heq, Finset.card_image_of_injective _ (S.orderEmbOfFin hS).injective, Fin.card_Iio]
  -- |S.filter(k<·)| = m - j
  have hS_gt_count : (S.filter (k < ·)).card = m - j := by
    have hpart : (S.filter (· ≤ k)).card + (S.filter (k < ·)).card = m := by
      have h := S.filter_card_add_filter_neg_card_eq_card (· ≤ k)
      simp only [hS] at h ⊢
      convert h using 2
      congr 1; ext x; simp [not_le]
    omega
  rw [hcomp_count, hS_gt_count]; omega

/-- The "first bad comp index" of a bad m-subset: the smallest j with comp[j] < S[j]. -/
private noncomputable def firstBad (m : ℕ) (S : Finset (Fin (2 * m))) (hS : S.card = m)
    (hbad : ∃ j : Fin m, ¬(S.orderEmbOfFin hS j <
        (compFin m S).orderEmbOfFin (compFin_card m S hS) j)) : Fin m :=
  (Finset.univ.filter (fun j : Fin m =>
      ¬(S.orderEmbOfFin hS j < (compFin m S).orderEmbOfFin (compFin_card m S hS) j))).min'
  (by obtain ⟨j, hj⟩ := hbad; exact ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩)

/-- firstBad satisfies the bad condition. -/
private lemma firstBad_is_bad (m : ℕ) (S : Finset (Fin (2 * m))) (hS : S.card = m)
    (hbad : ∃ j : Fin m, ¬(S.orderEmbOfFin hS j <
        (compFin m S).orderEmbOfFin (compFin_card m S hS) j)) :
    ¬(S.orderEmbOfFin hS (firstBad m S hS hbad) <
      (compFin m S).orderEmbOfFin (compFin_card m S hS) (firstBad m S hS hbad)) := by
  simp only [firstBad]
  have := Finset.min'_mem _ _
  exact (mem_filter.mp this).2

/-- All indices before firstBad satisfy the ballot condition. -/
private lemma before_firstBad_is_good (m : ℕ) (S : Finset (Fin (2 * m))) (hS : S.card = m)
    (hbad : ∃ j : Fin m, ¬(S.orderEmbOfFin hS j <
        (compFin m S).orderEmbOfFin (compFin_card m S hS) j))
    (i : Fin m) (hi : i < firstBad m S hS hbad) :
    S.orderEmbOfFin hS i < (compFin m S).orderEmbOfFin (compFin_card m S hS) i := by
  by_contra h
  have := Finset.min'_le _ i (mem_filter.mpr ⟨mem_univ _, h⟩)
  exact absurd hi (not_lt.mpr this)

/-- The barrier k₀ for a bad m-subset. -/
private noncomputable def badBarrier (m : ℕ) (S : Finset (Fin (2 * m))) (hS : S.card = m)
    (hbad : ∃ j : Fin m, ¬(S.orderEmbOfFin hS j <
        (compFin m S).orderEmbOfFin (compFin_card m S hS) j)) : Fin (2 * m) :=
  (compFin m S).orderEmbOfFin (compFin_card m S hS) (firstBad m S hS hbad)

/-- lRefl at badBarrier has cardinality m+1. -/
private lemma lRefl_badBarrier_card {m : ℕ} (S : Finset (Fin (2 * m))) (hS : S.card = m)
    (hbad : ∃ j : Fin m, ¬(S.orderEmbOfFin hS j <
        (compFin m S).orderEmbOfFin (compFin_card m S hS) j)) :
    (lRefl m S (badBarrier m S hS hbad)).card = m + 1 := by
  apply lRefl_bad_card S hS (firstBad m S hS hbad)
  · exact not_lt.mp (firstBad_is_bad m S hS hbad)
  · exact before_firstBad_is_good m S hS hbad

/-- The "first above-zero barrier" of an (m+1)-subset: the smallest k ∈ T with
    |T∩[0..k]| > |comp(T)∩[0..k]|. This is the inverse barrier for the Lindstrom map. -/
private noncomputable def firstAbove (m : ℕ) (T : Finset (Fin (2 * m))) (hT : T.card = m + 1) :
    Fin (2 * m) :=
  (Finset.univ.filter (fun k : Fin (2 * m) =>
      (T.filter (· ≤ k)).card > ((compFin m T).filter (· ≤ k)).card)).min'
  (by
    by_cases hm : m = 0
    · subst hm; simp [Fintype.card_fin] at hT
    · have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
      refine ⟨T.max' hTne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      simp only [gt_iff_lt]
      rw [Finset.filter_true_of_mem (fun x hx => Finset.le_max' T x hx), hT]
      have hcomp_eq : compFin m T = Tᶜ := by
        ext x; simp only [compFin, Finset.mem_filter, Finset.mem_univ, true_and,
                           Finset.mem_compl]
      have hcomp_card : (compFin m T).card = 2 * m - (m + 1) := by
        rw [hcomp_eq, Finset.card_compl, Fintype.card_fin, hT]
      calc ((compFin m T).filter (· ≤ T.max' hTne)).card
          ≤ (compFin m T).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2 * m - (m + 1) := hcomp_card
        _ < m + 1 := by omega)

private lemma firstAbove_spec {m : ℕ} (T : Finset (Fin (2 * m))) (hT : T.card = m + 1) :
    (T.filter (· ≤ firstAbove m T hT)).card >
    ((compFin m T).filter (· ≤ firstAbove m T hT)).card := by
  simp only [firstAbove]
  exact (mem_filter.mp (Finset.min'_mem _ _)).2

-- ============================================================
-- Helper lemmas for the Lindstrom reflection bijection
-- ============================================================

/-- The element firstAbove T is in T (by a parity argument).
    At firstAbove, the count flips from ≤0 to 1; this requires adding to T's count. -/
private lemma firstAbove_mem {m : ℕ} (T : Finset (Fin (2 * m))) (hT : T.card = m + 1) :
    firstAbove m T hT ∈ T := by
  set k := firstAbove m T hT with hk_def
  by_contra hkT
  have hkC : k ∈ compFin m T := by simp [compFin, hkT]
  have hspec := firstAbove_spec T hT
  rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
  · -- k = 0: T.filter(≤0) = ∅ since 0 ∉ T; comp.filter(≤0) ∋ 0
    have hempty : (T.filter (· ≤ k)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      ext x; simp only [mem_filter, Finset.not_mem_empty, iff_false]
      intro ⟨hx, hle⟩
      have hxk : x = k := Fin.le_antisymm (Fin.le_def.mpr (by
        have := Fin.le_def.mp hle; omega)) (Fin.zero_le _)
      exact hkT (hxk ▸ hx)
    have hcpos : 0 < ((compFin m T).filter (· ≤ k)).card :=
      Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hkC, le_refl k⟩⟩
    omega
  · -- k > 0: use predecessor k' = k-1
    set k' : Fin (2 * m) := ⟨k.val - 1, by omega⟩ with hk'_def
    have hk'k : k' < k := Fin.mk_lt_mk.mpr (by omega)
    -- By minimality of firstAbove, k' does not satisfy the condition
    have hbefore : (T.filter (· ≤ k')).card ≤ ((compFin m T).filter (· ≤ k')).card := by
      by_contra h; push_neg at h
      have hmem : k' ∈ Finset.univ.filter (fun k'' : Fin (2 * m) =>
          (T.filter (· ≤ k'')).card > ((compFin m T).filter (· ≤ k'')).card) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have hle : firstAbove m T hT ≤ k' := by
        simp only [firstAbove]; exact Finset.min'_le _ k' hmem
      exact absurd hle (not_le.mpr hk'k)
    -- Since k ∉ T: T.filter(≤k) = T.filter(≤k')
    have hTeq : (T.filter (· ≤ k)).card = (T.filter (· ≤ k')).card := by
      apply Finset.card_nbij id
      · intro x hx
        simp only [mem_filter, id] at hx ⊢
        exact ⟨hx.1, Fin.le_def.mpr (by
          have h := Fin.le_def.mp hx.2
          rcases Nat.lt_or_eq_of_le h with hlt | heq
          · exact Nat.lt_succ_iff.mp (by omega)
          · exact absurd (Fin.ext heq.symm ▸ hx.1) hkT)⟩
      · intro x hx; simp only [mem_filter, id] at hx ⊢
        exact ⟨hx.1, Fin.le_def.mpr (by omega)⟩
      · intros; rfl
    -- Since k ∈ comp: comp.filter(≤k) = comp.filter(≤k') ∪ {k}, card +1
    have hCsucc : ((compFin m T).filter (· ≤ k)).card =
        ((compFin m T).filter (· ≤ k')).card + 1 := by
      have heq : (compFin m T).filter (· ≤ k) = (compFin m T).filter (· ≤ k') ∪ {k} := by
        ext x; simp only [mem_union, mem_filter, mem_singleton]
        constructor
        · intro ⟨hx, hle⟩
          rcases le_or_lt x k' with h | h
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr (Fin.le_antisymm hle (Fin.le_def.mpr (by
              simp only [Fin.lt_def] at h; omega)))
        · rintro (⟨hx, hle⟩ | rfl)
          · exact ⟨hx, Fin.le_def.mpr (by simp only [k', Fin.val_mk]; omega)⟩
          · exact ⟨hkC, le_refl k⟩
      have hdisj : Disjoint ((compFin m T).filter (· ≤ k')) ({k} : Finset (Fin (2 * m))) := by
        rw [Finset.disjoint_singleton_right]
        simp only [mem_filter, not_and]
        intro _; simp only [Fin.le_def, k', Fin.val_mk]; omega
      rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
    -- |T.filter(≤k)| ≤ |comp.filter(≤k')| = |comp.filter(≤k)| - 1 < |comp.filter(≤k)|
    rw [hTeq, hCsucc] at hspec; omega

/-- At firstAbove k, the filter counts differ by exactly 1: |T.filter(≤k)| = |comp.filter(≤k)| + 1.
    This follows from the minimality of firstAbove (count flips from 0 to 1). -/
private lemma firstAbove_count_diff {m : ℕ} (T : Finset (Fin (2 * m))) (hT : T.card = m + 1) :
    (T.filter (· ≤ firstAbove m T hT)).card =
    ((compFin m T).filter (· ≤ firstAbove m T hT)).card + 1 := by
  set k := firstAbove m T hT with hk_def
  have hspec := firstAbove_spec T hT
  have hkT := firstAbove_mem T hT
  have hknotC : k ∉ compFin m T := by simp [compFin, hkT]
  rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
  · -- k = 0 ∈ T: T.filter(≤0) = {0}, comp.filter(≤0) = ∅
    have h1 : (T.filter (· ≤ k)).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨k, by ext x; simp only [mem_filter, mem_singleton];
        constructor
        · intro ⟨hx, hle⟩; exact Fin.le_antisymm (Fin.le_def.mpr (by
            have := Fin.le_def.mp hle; omega)) (Fin.zero_le _)
        · intro h; exact ⟨h ▸ hkT, le_refl k⟩⟩
    have h2 : ((compFin m T).filter (· ≤ k)).card = 0 := by
      apply Finset.card_eq_zero.mpr; ext x
      simp only [mem_filter, Finset.not_mem_empty, iff_false]
      intro ⟨hxC, hle⟩
      simp only [compFin, mem_filter, mem_univ, true_and] at hxC
      have hxk : x = k := Fin.le_antisymm (Fin.le_def.mpr (by
        have := Fin.le_def.mp hle; omega)) (Fin.zero_le _)
      exact hxC (hxk ▸ hkT)
    omega
  · -- k > 0: use k' = k-1
    set k' : Fin (2 * m) := ⟨k.val - 1, by omega⟩ with hk'_def
    have hk'k : k' < k := Fin.mk_lt_mk.mpr (by omega)
    have hbefore : (T.filter (· ≤ k')).card ≤ ((compFin m T).filter (· ≤ k')).card := by
      by_contra h; push_neg at h
      have hmem : k' ∈ Finset.univ.filter (fun k'' : Fin (2 * m) =>
          (T.filter (· ≤ k'')).card > ((compFin m T).filter (· ≤ k'')).card) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have hle : firstAbove m T hT ≤ k' := by
        simp only [firstAbove]; exact Finset.min'_le _ k' hmem
      exact absurd hle (not_le.mpr hk'k)
    -- T.filter(≤k) = T.filter(≤k') ∪ {k}, card +1 (since k ∈ T)
    have hTsucc : (T.filter (· ≤ k)).card = (T.filter (· ≤ k')).card + 1 := by
      have heq : T.filter (· ≤ k) = T.filter (· ≤ k') ∪ {k} := by
        ext x; simp only [mem_union, mem_filter, mem_singleton]
        constructor
        · intro ⟨hx, hle⟩
          rcases le_or_lt x k' with h | h
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr (Fin.le_antisymm hle (Fin.le_def.mpr (by
              simp only [Fin.lt_def] at h; omega)))
        · rintro (⟨hx, hle⟩ | rfl)
          · exact ⟨hx, Fin.le_def.mpr (by simp only [k', Fin.val_mk]; omega)⟩
          · exact ⟨hkT, le_refl k⟩
      have hdisj : Disjoint (T.filter (· ≤ k')) ({k} : Finset (Fin (2 * m))) := by
        rw [Finset.disjoint_singleton_right]; simp only [mem_filter, not_and]
        intro _; simp only [Fin.le_def, k', Fin.val_mk]; omega
      rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
    -- comp.filter(≤k) = comp.filter(≤k') (since k ∉ comp)
    have hCeq : ((compFin m T).filter (· ≤ k)).card = ((compFin m T).filter (· ≤ k')).card := by
      apply Finset.card_nbij id
      · intro x hx; simp only [mem_filter, id] at hx ⊢
        exact ⟨hx.1, Fin.le_def.mpr (by
          have h := Fin.le_def.mp hx.2
          rcases Nat.lt_or_eq_of_le h with hlt | heq
          · exact Nat.lt_succ_iff.mp (by omega)
          · exact absurd (Fin.ext heq.symm ▸ hx.1) hknotC)⟩
      · intro x hx; simp only [mem_filter, id] at hx ⊢
        exact ⟨hx.1, Fin.le_def.mpr (by omega)⟩
      · intros; rfl
    linarith

/-- lRefl at firstAbove of an (m+1)-subset has exactly m elements. -/
private lemma lRefl_firstAbove_card {m : ℕ} (T : Finset (Fin (2 * m))) (hT : T.card = m + 1) :
    (lRefl m T (firstAbove m T hT)).card = m := by
  set k := firstAbove m T hT
  simp only [lRefl]
  have hdisj : Disjoint ((compFin m T).filter (· ≤ k)) (T.filter (k < ·)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [compFin, mem_filter, mem_univ, true_and] at hx1
    exact hx1 (Finset.mem_filter.mp hx2).1
  rw [Finset.card_union_of_disjoint hdisj]
  have hdiff := firstAbove_count_diff T hT
  have hTpart : (T.filter (· ≤ k)).card + (T.filter (k < ·)).card = m + 1 := by
    have h := T.filter_card_add_filter_neg_card_eq_card (· ≤ k)
    simp only [hT] at h; convert h using 2; congr 1; ext x; simp [not_le]
  -- |comp.filter(≤k)| = |T.filter(≤k)| - 1, |T.filter(k<·)| = m+1 - |T.filter(≤k)|
  omega

/-- Below badBarrier, the ballot condition holds: comp count ≤ S count. -/
private lemma comp_filter_le_S_filter_below_barrier {m : ℕ}
    (S : Finset (Fin (2 * m))) (hS : S.card = m)
    (hbad : ∃ j : Fin m, ¬(S.orderEmbOfFin hS j <
        (compFin m S).orderEmbOfFin (compFin_card m S hS) j))
    (k : Fin (2 * m)) (hk : k < badBarrier m S hS hbad) :
    ((compFin m S).filter (· ≤ k)).card ≤ (S.filter (· ≤ k)).card := by
  set hcS := compFin_card m S hS
  -- A: set of indices i with comp(S)[i] ≤ k
  let A := Finset.univ.filter (fun i : Fin m => (compFin m S).orderEmbOfFin hcS i ≤ k)
  -- A.card = |comp(S).filter(≤k)| via orderEmbOfFin bijection
  have hA_card : A.card = ((compFin m S).filter (· ≤ k)).card := by
    apply Finset.card_nbij (fun i => (compFin m S).orderEmbOfFin hcS i)
    · intro i hi
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem _ hcS i, hi⟩
    · intro c hc
      simp only [Finset.mem_filter] at hc
      rw [← Finset.image_orderEmbOfFin_univ _ hcS] at hc
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc.1
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.2⟩, rfl⟩
    · intro i _ j _ h; exact ((compFin m S).orderEmbOfFin hcS).injective h
  -- For each i ∈ A: i < firstBad and S[i] < comp(S)[i] ≤ k, so S[i] ∈ S.filter(≤k)
  have hS_image_sub : A.image (S.orderEmbOfFin hS) ⊆ S.filter (· ≤ k) := by
    intro x hx
    simp only [A, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    refine Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem S hS i, ?_⟩
    have hi_lt : i < firstBad m S hS hbad := by
      by_contra h; push_neg at h
      have h_mono := ((compFin m S).orderEmbOfFin hcS).strictMono.monotone h
      -- comp(S)[j₀] ≤ comp(S)[i] ≤ k < badBarrier = comp(S)[j₀]
      exact absurd (le_trans h_mono hi) (not_le.mpr hk)
    exact le_of_lt (lt_of_lt_of_le (before_firstBad_is_good m S hS hbad i hi_lt) hi)
  calc ((compFin m S).filter (· ≤ k)).card
      = A.card := hA_card.symm
    _ = (A.image (S.orderEmbOfFin hS)).card :=
          (Finset.card_image_of_injective A (S.orderEmbOfFin hS).injective).symm
    _ ≤ (S.filter (· ≤ k)).card := Finset.card_le_card hS_image_sub

/-- lRefl(T, firstAbove T) is a bad m-subset: the ballot condition fails at some index. -/
private lemma lRefl_firstAbove_is_bad {m : ℕ} (T : Finset (Fin (2 * m))) (hT : T.card = m + 1) :
    ∃ j : Fin m, ¬((lRefl m T (firstAbove m T hT)).orderEmbOfFin
        (lRefl_firstAbove_card T hT) j <
      (compFin m (lRefl m T (firstAbove m T hT))).orderEmbOfFin
        (compFin_card m _ (lRefl_firstAbove_card T hT)) j) := by
  set k₁ := firstAbove m T hT with hk₁_def
  set T' := lRefl m T k₁ with hT'_def
  set hT'c := lRefl_firstAbove_card T hT
  set hcT' := compFin_card m T' hT'c
  -- At k₁: |T'.filter(≤k₁)| = |comp(T).filter(≤k₁)| < |T.filter(≤k₁)| = |comp(T').filter(≤k₁)|
  -- So comp(T') has more elements ≤ k₁ than T'.
  -- This means T'[j] > comp(T')[j] for j = |T'.filter(≤k₁)| - 1...
  -- More precisely: pick j₁ = |T'.filter(· ≤ k₁)|. Then T'[j₁] > k₁ and comp(T')[j₁] ≤ k₁.
  -- Use filter cardinalities to find the witness j.
  have hT'_le : (T'.filter (· ≤ k₁)).card = ((compFin m T).filter (· ≤ k₁)).card := by
    apply Finset.card_nbij id
    · intro x hx; simp only [mem_filter, id] at hx ⊢
      simp only [T', lRefl, mem_union, mem_filter] at hx
      exact ⟨by simp [compFin]; exact (hx.1.elim (fun h => h.1) (fun h => by
        simp [compFin] at h ⊢; exact fun hT' => h.1 hT')), hx.2⟩
    · intro x hx
      simp only [mem_filter, id] at hx ⊢
      have hxle := hx.2
      have hxC : x ∈ compFin m T := hx.1
      simp only [T', lRefl, mem_union, mem_filter]
      exact ⟨Or.inl ⟨hxC, hxle⟩, hxle⟩
    · intros; rfl
  have hcT'_le : ((compFin m T').filter (· ≤ k₁)).card = (T.filter (· ≤ k₁)).card := by
    rw [compFin_lRefl]
    apply Finset.card_nbij id
    · intro x hx; simp only [mem_union, mem_filter, id] at hx ⊢
      rcases hx.1 with h | h
      · exact ⟨h.1, h.2⟩
      · exact ⟨h.1, hx.2⟩
    · intro x hx; simp only [mem_filter, id] at hx ⊢
      simp only [mem_union, mem_filter]
      exact ⟨Or.inl ⟨hx.1, hx.2⟩, hx.2⟩
    · intros; rfl
  -- |comp(T').filter(≤k₁)| = |T.filter(≤k₁)| = |comp(T).filter(≤k₁)| + 1 = |T'.filter(≤k₁)| + 1
  have hdiff := firstAbove_count_diff T hT
  -- So |comp(T').filter(≤k₁)| > |T'.filter(≤k₁)|
  have hcount : (T'.filter (· ≤ k₁)).card < ((compFin m T').filter (· ≤ k₁)).card := by
    rw [hT'_le, hcT'_le]; omega
  -- T'[j₁] is the first element of T' above k₁, comp(T')[j₁] is still ≤ k₁
  -- Pick j₁ = |T'.filter(≤k₁)|
  have hj1_lt : (T'.filter (· ≤ k₁)).card < m := by
    have : (T'.filter (· ≤ k₁)).card ≤ T'.card := Finset.card_le_card (Finset.filter_subset _ _)
    omega
  set j₁ : Fin m := ⟨(T'.filter (· ≤ k₁)).card, hj1_lt⟩
  use j₁
  push_neg  -- Show: T'[j₁] ≥ comp(T')[j₁]... actually show ¬(T'[j₁] < comp(T')[j₁])
  -- T'[j₁] is the (j₁+1)-th element of T' in order; it's the first one > k₁
  have hT'_j1 : k₁ < T'.orderEmbOfFin hT'c j₁ := by
    -- j₁ = |T'.filter(≤k₁)|, so T'[j₁] is NOT in T'.filter(≤k₁), hence T'[j₁] > k₁
    have hmem : T'.orderEmbOfFin hT'c j₁ ∈ T' := Finset.orderEmbOfFin_mem T' hT'c j₁
    by_contra h; push_neg at h
    -- T'[j₁] ≤ k₁ means T'[j₁] ∈ T'.filter(≤k₁)
    have : T'.orderEmbOfFin hT'c j₁ ∈ T'.filter (· ≤ k₁) :=
      Finset.mem_filter.mpr ⟨hmem, h⟩
    -- T'.filter(≤k₁) has card j₁, so max index in orderEmb is j₁-1
    have := filter_le_orderEmb_eq T' hT'c j₁
    -- |T'.filter(≤k₁)| = j₁+1 > j₁ = card, contradiction
    simp only [j₁, Fin.val_mk] at this; omega
  -- comp(T')[j₁] ≤ k₁
  have hcT'_j1 : (compFin m T').orderEmbOfFin hcT' j₁ ≤ k₁ := by
    -- j₁ < |comp(T').filter(≤k₁)| (since |comp.filter(≤k₁)| = j₁+1 by hcount)
    -- So comp(T')[j₁] = the (j₁+1)-th element of comp(T'), which is ≤ k₁
    have hj1_lt_c : j₁.val < ((compFin m T').filter (· ≤ k₁)).card := by
      simp only [j₁, Fin.val_mk]; omega
    have := filter_le_orderEmb_eq (compFin m T') hcT' ⟨j₁.val, by
      have := hcT'; omega⟩
    -- |comp(T').filter(≤ comp(T')[j₁])| = j₁+1 > j₁ = |comp(T').filter(≤k₁)| - 1
    -- Actually we need: comp(T')[j₁] ≤ k₁ because j₁ < |comp.filter(≤k₁)|
    -- i.e., comp(T') has at least j₁+1 elements ≤ k₁, so the (j₁+1)-th (= comp[j₁]) is ≤ k₁
    have hj_in : (compFin m T').orderEmbOfFin hcT' j₁ ∈
        (compFin m T').filter (· ≤ k₁) := by
      rw [← Finset.image_orderEmbOfFin_univ (compFin m T') hcT'] at *
      -- comp(T').filter(≤k₁) has card > j₁, so comp(T')[j₁] is in it
      -- Use: orderEmbOfFin is increasing and its first j₁+1 elements are ≤ k₁
      -- Actually: comp(T')[j₁] ∈ comp(T').filter(≤k₁) iff comp(T')[j₁] ≤ k₁
      -- We know |comp(T').filter(≤k₁)| > j₁, so comp(T')[j₁] ≤ k₁
      by_contra h
      push_neg at h
      simp only [Finset.mem_filter, Finset.not_and] at h
      have hnotmem := h (Finset.orderEmbOfFin_mem (compFin m T') hcT' j₁)
      -- comp(T')[j₁] > k₁, so all comp(T')[i] with i ≥ j₁ are > k₁
      -- Hence |comp(T').filter(≤k₁)| ≤ j₁, contradicting hcount
      have hle_j1 : ((compFin m T').filter (· ≤ k₁)).card ≤ j₁.val := by
        apply Finset.card_le_card_of_lt
        · intro c hc
          simp only [Finset.mem_filter] at hc
          rw [← Finset.image_orderEmbOfFin_univ (compFin m T') hcT'] at hc
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc.1
          -- comp(T')[i] ≤ k₁ and comp(T')[j₁] > k₁, so i < j₁
          apply Finset.mem_Iio.mpr
          rcases lt_or_le i j₁ with h | h
          · exact h
          · exact absurd hc.2 (not_le.mpr
              (lt_of_lt_of_le hnotmem ((compFin m T').orderEmbOfFin hcT' |>.monotone h)))
      simp only [j₁, Fin.val_mk] at hle_j1; omega
    exact (Finset.mem_filter.mp hj_in).2
  -- T'[j₁] > k₁ ≥ comp(T')[j₁]
  exact not_lt.mpr (le_of_lt (lt_of_le_of_lt hcT'_j1 hT'_j1))

/-- firstAbove(lRefl S k₀) = k₀: the reflection maps badBarrier back to firstAbove.
    This is the key round-trip identity for the Lindstrom bijection. -/
private lemma firstAbove_eq_badBarrier_of_refl {m : ℕ}
    (S : Finset (Fin (2 * m))) (hS : S.card = m)
    (hbad : ∃ j : Fin m, ¬(S.orderEmbOfFin hS j <
        (compFin m S).orderEmbOfFin (compFin_card m S hS) j)) :
    firstAbove m (lRefl m S (badBarrier m S hS hbad))
      (lRefl_badBarrier_card S hS hbad) =
    badBarrier m S hS hbad := by
  set k₀ := badBarrier m S hS hbad with hk₀_def
  set T' := lRefl m S k₀
  set hT'c := lRefl_badBarrier_card S hS hbad
  have hcS := compFin_card m S hS
  -- T' = comp(S).filter(≤k₀) ∪ S.filter(k₀<·), comp(T') = S.filter(≤k₀) ∪ comp(S).filter(k₀<·)
  -- At k₀: |T'.filter(≤k₀)| = |comp(S).filter(≤k₀)| = j₀+1
  --         |comp(T').filter(≤k₀)| = |S.filter(≤k₀)| = j₀
  -- So k₀ ∈ firstAbove filter (condition holds at k₀).
  -- For k < k₀: |T'.filter(≤k)| = |comp(S).filter(≤k)| ≤ |S.filter(≤k)| = |comp(T').filter(≤k)|
  -- So k₀ is the minimum: firstAbove = k₀.
  set j₀ := firstBad m S hS hbad with hj₀_def
  have hcS_j0 : (compFin m S).orderEmbOfFin hcS j₀ = k₀ := rfl
  -- k₀ ∈ T' (k₀ ∈ comp(S) and k₀ ≤ k₀)
  have hk₀_in_T' : k₀ ∈ T' := by
    simp only [T', lRefl, mem_union, mem_filter]
    left; exact ⟨Finset.orderEmbOfFin_mem _ hcS j₀, le_refl k₀⟩
  -- At k₀: T'.filter(≤k₀) = comp(S).filter(≤k₀) and comp(T').filter(≤k₀) = S.filter(≤k₀)
  have hT'_at_k₀ : (T'.filter (· ≤ k₀)).card = ((compFin m S).filter (· ≤ k₀)).card := by
    apply Finset.card_nbij id
    · intro x hx; simp only [mem_filter, id] at hx ⊢
      have hxle := hx.2
      simp only [T', lRefl, mem_union, mem_filter] at hx
      rcases hx.1 with h | h
      · exact ⟨h.1, h.2⟩
      · exact absurd hxle (not_le.mpr h.1)
    · intro x hx; simp only [mem_filter, id] at hx ⊢
      exact ⟨by simp [T', lRefl, mem_union, mem_filter, hx.1, hx.2], hx.2⟩
    · intros; rfl
  have hcT'_at_k₀ : ((compFin m T').filter (· ≤ k₀)).card = (S.filter (· ≤ k₀)).card := by
    rw [compFin_lRefl]
    apply Finset.card_nbij id
    · intro x hx; simp only [mem_union, mem_filter, id] at hx ⊢
      rcases hx.1 with h | h
      · exact ⟨h.1, h.2⟩
      · exact ⟨h.1, hx.2⟩
    · intro x hx; simp only [mem_filter, id] at hx ⊢
      exact ⟨by simp [mem_union, mem_filter, hx.1, hx.2], hx.2⟩
    · intros; rfl
  -- |comp(S).filter(≤k₀)| = j₀+1 (by filter_le_orderEmb_eq)
  have hcomp_count : ((compFin m S).filter (· ≤ k₀)).card = j₀.val + 1 :=
    filter_le_orderEmb_eq (compFin m S) hcS j₀
  -- |S.filter(≤k₀)| = j₀ (S[i] < k₀ for i < j₀, S[i] > k₀ for i ≥ j₀)
  have hS_count : (S.filter (· ≤ k₀)).card = j₀.val := by
    have heq : S.filter (· ≤ k₀) = Finset.image (S.orderEmbOfFin hS) (Finset.Iio j₀) := by
      ext x; simp only [mem_filter, mem_image, mem_Iio]
      constructor
      · intro ⟨hx, hle⟩
        rw [← Finset.image_orderEmbOfFin_univ S hS] at hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        refine ⟨i, ?_, rfl⟩
        by_contra h; push_neg at h
        rcases h.eq_or_lt with rfl | hgt
        · -- S[j₀] ≥ k₀ (firstBad_is_bad), S[j₀] ≠ k₀ (disjoint S, comp(S))
          have hge := not_lt.mp (firstBad_is_bad m S hS hbad)
          have hneq : S.orderEmbOfFin hS j₀ ≠ k₀ := by
            intro h; rw [h] at *
            have : k₀ ∈ compFin m S := Finset.orderEmbOfFin_mem _ hcS j₀
            simp [compFin] at this; exact this (Finset.orderEmbOfFin_mem S hS j₀)
          exact absurd hle (not_le.mpr (lt_of_le_of_ne hge (Ne.symm hneq)))
        · exact absurd hle (not_le.mpr
            (lt_of_lt_of_le (lt_of_le_of_ne (not_lt.mp (firstBad_is_bad m S hS hbad))
              (by intro h; rw [h] at *
                  have : k₀ ∈ compFin m S := Finset.orderEmbOfFin_mem _ hcS j₀
                  simp [compFin] at this; exact this (Finset.orderEmbOfFin_mem S hS j₀)))
              ((S.orderEmbOfFin hS).strictMono hgt).le))
      · intro ⟨i, hi, rfl⟩
        refine ⟨Finset.orderEmbOfFin_mem S hS i, ?_⟩
        have h1 := before_firstBad_is_good m S hS hbad i hi
        have h2 := ((compFin m S).orderEmbOfFin hcS).strictMono.monotone hi.le
        rw [hcS_j0] at h2
        exact le_of_lt (lt_of_lt_of_le h1 h2)
    rw [heq, Finset.card_image_of_injective _ (S.orderEmbOfFin hS).injective, Fin.card_Iio]
  -- Combine: at k₀, T'.filter has j₀+1 and comp(T').filter has j₀ elements
  have hcond_k₀ : (T'.filter (· ≤ k₀)).card > ((compFin m T').filter (· ≤ k₀)).card := by
    rw [hT'_at_k₀, hcT'_at_k₀, hcomp_count, hS_count]; omega
  -- For k < k₀: T'.filter(≤k) = comp(S).filter(≤k) ≤ S.filter(≤k) = comp(T').filter(≤k)
  have hcond_lt : ∀ k : Fin (2 * m), k < k₀ →
      ¬(T'.filter (· ≤ k)).card > ((compFin m T').filter (· ≤ k)).card := by
    intro k hk
    -- T'.filter(≤k) = comp(S).filter(≤k) for k < k₀
    have hT'_k : (T'.filter (· ≤ k)).card = ((compFin m S).filter (· ≤ k)).card := by
      apply Finset.card_nbij id
      · intro x hx; simp only [mem_filter, id] at hx ⊢
        simp only [T', lRefl, mem_union, mem_filter] at hx
        rcases hx.1 with h | h
        · exact ⟨h.1, h.2⟩
        · exact absurd (lt_of_lt_of_le hk hx.2) (lt_irrefl _)
      · intro x hx; simp only [mem_filter, id] at hx ⊢
        exact ⟨by simp [T', lRefl, mem_union, mem_filter, hx.1, hx.2], hx.2⟩
      · intros; rfl
    -- comp(T').filter(≤k) = S.filter(≤k) for k < k₀
    have hcT'_k : ((compFin m T').filter (· ≤ k)).card = (S.filter (· ≤ k)).card := by
      rw [compFin_lRefl]
      apply Finset.card_nbij id
      · intro x hx; simp only [mem_union, mem_filter, id] at hx ⊢
        rcases hx.1 with h | h
        · exact ⟨h.1, h.2⟩
        · exact absurd (lt_of_lt_of_le hk hx.2) (lt_irrefl _)
      · intro x hx; simp only [mem_filter, id] at hx ⊢
        exact ⟨by simp [mem_union, mem_filter, hx.1, hx.2], hx.2⟩
      · intros; rfl
    rw [hT'_k, hcT'_k]
    exact not_lt.mpr (comp_filter_le_S_filter_below_barrier S hS hbad k hk)
  -- k₀ is in the firstAbove filter set and is a lower bound for it
  apply Fin.le_antisymm
  · -- firstAbove ≤ k₀: k₀ ∈ filter set
    simp only [firstAbove]
    apply Finset.min'_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcond_k₀⟩
  · -- k₀ ≤ firstAbove: firstAbove ∈ filter set, and filter set elements are ≥ k₀
    have hfA_mem : firstAbove m T' hT'c ∈
        Finset.univ.filter (fun k : Fin (2 * m) =>
          (T'.filter (· ≤ k)).card > ((compFin m T').filter (· ≤ k)).card) := by
      simp only [firstAbove]; exact Finset.min'_mem _ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfA_mem
    by_contra hlt
    push_neg at hlt
    exact absurd hfA_mem (hcond_lt _ hlt)

/-- badBarrier(lRefl T k₁) = k₁: the reflection maps firstAbove back to badBarrier. -/
private lemma badBarrier_eq_firstAbove_of_refl {m : ℕ}
    (T : Finset (Fin (2 * m))) (hT : T.card = m + 1) :
    badBarrier m (lRefl m T (firstAbove m T hT))
      (lRefl_firstAbove_card T hT) (lRefl_firstAbove_is_bad T hT) =
    firstAbove m T hT := by
  set k₁ := firstAbove m T hT with hk₁_def
  set S' := lRefl m T k₁ with hS'_def
  set hS'c := lRefl_firstAbove_card T hT
  set hbad' := lRefl_firstAbove_is_bad T hT
  set hcS' := compFin_card m S' hS'c
  -- S' = comp(T).filter(≤k₁) ∪ T.filter(k₁<·), comp(S') = T.filter(≤k₁) ∪ comp(T).filter(k₁<·)
  -- badBarrier(S') = comp(S')[firstBad(S')], where firstBad is the first j with S'[j] ≥ comp(S')[j]
  -- We show: badBarrier(S') = k₁ = firstAbove(T)
  -- The first bad index of S' is j' = |S'.filter(· < k₁)| = |comp(T).filter(· < k₁)|
  -- comp(S')[j'] ≤ k₁ and S'[j'] ≥ k₁ (approximately)
  -- We use the Lindstrom involution: lRefl(S', k₁) = T, and firstAbove(T) = k₁ (firstAbove_spec),
  -- so the bad barrier of S' (the comp(S') element that gives the reflection back) must be k₁.
  -- Strategy: show comp(S') has exactly |T.filter(≤k₁)| elements ≤ k₁ = |comp(T).filter(≤k₁)|+1
  -- and S' has |comp(T).filter(≤k₁)| elements ≤ k₁, so the bad index is j' = |comp(T).filter(≤k₁)|
  -- and comp(S')[j'] = k₁ (since k₁ ∈ T ⊆ comp(S')).
  -- First, k₁ ∈ comp(S')
  have hk₁_in_cS' : k₁ ∈ compFin m S' := by
    rw [compFin_lRefl]
    simp only [mem_union, mem_filter]
    left; exact ⟨firstAbove_mem T hT, le_refl k₁⟩
  -- comp(S')[j'] = k₁ where j' = index of k₁ in comp(S')
  -- We need: badBarrier(S') = k₁, i.e., firstBad is j' with comp(S')[j'] = k₁
  -- Key: we show lRefl(S', badBarrier S') = T using firstAbove_eq_badBarrier_of_refl for S'
  -- Actually, we use the involution: lRefl(lRefl(T, k₁), k₁) = T.
  -- The badBarrier of S' = lRefl(T, k₁) should be k₁ because applying firstAbove_eq_badBarrier_of_refl
  -- with S = T (bad, so has a bad barrier k₁... wait T might not be bad)
  -- Let's use a direct approach: show k₁ is the badBarrier.
  -- badBarrier = comp(S')[firstBad(S')]
  -- We need comp(S')[firstBad(S')] = k₁.
  -- Equivalent: show firstAbove(lRefl(S', badBarrier S')) = badBarrier S', and
  -- then use the involution lRefl(lRefl(T, k₁), k₁) = T to conclude.
  -- Actually simpler: use firstAbove_eq_badBarrier_of_refl applied to S' directly!
  -- Wait, but firstAbove_eq_badBarrier_of_refl requires hbad for the set S'.
  -- We have hbad' : ∃ j, ¬(S'[j] < comp(S')[j]). ✓
  -- And it says: firstAbove(lRefl(S', badBarrier S')) (lRefl_badBarrier_card) = badBarrier S'.
  -- But that's not directly what we want.
  -- BETTER: directly compute badBarrier(S') = k₁.
  -- badBarrier(S') = comp(S')[firstBad(S')]
  -- We need to find firstBad(S') and show comp(S')[firstBad(S')] = k₁.
  -- The j₁' = firstBad(S') satisfies: S'[j₁'] ≥ comp(S')[j₁'] and S'[i] < comp(S')[i] for i < j₁'.
  -- At k₁: |S'.filter(≤k₁)| = |comp(T).filter(≤k₁)| = j₀ (say)
  --         |comp(S').filter(≤k₁)| = |T.filter(≤k₁)| = j₀+1 (by firstAbove_count_diff)
  -- So S'[j₀] > k₁ ≥ comp(S')[j₀].
  -- And for i < j₀: by the argument of comp_filter_le_S_filter_below_barrier (applied to S'),
  --   S'[i] < comp(S')[i].
  -- Thus firstBad(S') = j₀ and comp(S')[j₀] = ? We need comp(S')[j₀] = k₁.
  -- comp(S')[j₀]: it's the (j₀+1)-th element of comp(S') in order.
  -- comp(S') = T.filter(≤k₁) ∪ comp(T).filter(k₁<·).
  -- Elements of comp(S') ≤ k₁: T.filter(≤k₁), which has j₀+1 elements.
  -- So comp(S')[j₀] = max of T.filter(≤k₁) = k₁ (since k₁ ∈ T and k₁ ≤ k₁, and k₁ is the max).
  -- Wait: comp(S')[j₀] is the (j₀+1)-th element = index j₀ in the sorted order.
  -- T.filter(≤k₁) has j₀+1 elements (= T.filter(≤k₁).card by firstAbove_count_diff for T,
  -- where j₀ = |comp(T).filter(≤k₁)| and |T.filter(≤k₁)| = j₀+1).
  -- comp(S') starts with j₀+1 elements from T.filter(≤k₁) ≤ k₁, then comp(T).filter(k₁<·) > k₁.
  -- comp(S')[j₀] is the (j₀+1)-th element = the last of T.filter(≤k₁), which is k₁ (since k₁ ∈ T ∩ filter(≤k₁) and k₁ is the max of T.filter(≤k₁)).
  -- Max of T.filter(≤k₁): since k₁ ∈ T and k₁ ≤ k₁, k₁ ∈ T.filter(≤k₁).
  -- And T.filter(≤k₁) ⊆ Iic k₁, so max is ≤ k₁. And k₁ ∈ it, so max = k₁.
  -- Therefore comp(S')[j₀] = k₁. ✓
  --
  -- This is quite involved. Let me use the involution approach instead:
  -- We know lRefl(S', k₁) = lRefl(lRefl(T, k₁), k₁) = T.
  -- And firstAbove_eq_badBarrier_of_refl says: firstAbove(lRefl(S', badBarrier S')) = badBarrier S'.
  -- But firstAbove(lRefl(S', badBarrier S')) requires lRefl to give an (m+1)-subset.
  -- This is getting circular. Let me use a direct argument.
  --
  -- DIRECT: show badBarrier(S') = k₁ by proving comp(S')[firstBad(S')] = k₁.
  -- This requires computing the firstBad of S' and showing it equals j₀ with comp(S')[j₀] = k₁.
  -- We'll use the fact that T.filter(≤k₁).max' = k₁.
  --
  -- For now, use the involution + firstAbove_eq_badBarrier_of_refl:
  -- Since lRefl(S', k₁) = T (hT card = m+1), and firstAbove of T = k₁,
  -- and firstAbove_eq_badBarrier_of_refl: firstAbove(lRefl(S', badBarrier S')) = badBarrier S',
  -- we need to show that badBarrier(S') = k₁ directly.
  -- The cleanest proof: show that badBarrier(S') is in firstAbove set of T AND is the minimum.
  -- Actually, the cleanest proof uses:
  -- k₁ = firstAbove(T) = firstAbove(lRefl(S', k₁)) = ...
  -- But we need badBarrier(S') first.
  --
  -- ALTERNATIVE: use Fin.le_antisymm
  apply Fin.le_antisymm
  · -- badBarrier(S') ≤ k₁
    -- comp(S')[j'] ≤ k₁ where j' = firstBad(S')
    -- Because j' < some threshold determined by |comp(S').filter(≤k₁)|
    -- |comp(S').filter(≤k₁)| = |T.filter(≤k₁)| > |S'.filter(≤k₁)| = |comp(T).filter(≤k₁)|
    -- So first Bad index j' ≤ |S'.filter(≤k₁)| < |comp(S').filter(≤k₁)|
    -- And comp(S')[j'] ≤ comp(S')[|comp(S').filter(≤k₁)| - 1] ≤ k₁
    simp only [badBarrier]
    -- Show: comp(S')[firstBad(S')] ≤ k₁
    -- Equivalently: firstBad(S') < |comp(S').filter(≤k₁)|
    have hcT_count : ((compFin m T).filter (· ≤ k₁)).card = (S'.filter (· ≤ k₁)).card := by
      apply Finset.card_nbij id
      · intro x hx; simp only [mem_filter, id] at hx ⊢
        simp only [S', lRefl, mem_union, mem_filter]
        exact ⟨Or.inl ⟨hx.1, hx.2⟩, hx.2⟩
      · intro x hx; simp only [mem_filter, id] at hx ⊢
        simp only [S', lRefl, mem_union, mem_filter] at hx
        rcases hx.1 with h | h
        · exact ⟨h.1, h.2⟩
        · exact absurd (lt_of_lt_of_le hx.2 (le_refl k₁)) (not_lt.mpr (le_of_lt h.1))
      · intros; rfl
    have hT_count : (T.filter (· ≤ k₁)).card = ((compFin m S').filter (· ≤ k₁)).card := by
      rw [compFin_lRefl]
      apply Finset.card_nbij id
      · intro x hx; simp only [mem_union, mem_filter, id] at hx ⊢
        exact ⟨Or.inl ⟨hx.1, hx.2⟩, hx.2⟩
      · intro x hx; simp only [mem_union, mem_filter, id] at hx ⊢
        rcases hx.1 with h | h
        · exact ⟨h.1, h.2⟩
        · exact absurd (lt_of_lt_of_le hx.2 (le_refl k₁)) (not_lt.mpr (le_of_lt h.1))
      · intros; rfl
    have hdiff := firstAbove_count_diff T hT
    -- |comp(S').filter(≤k₁)| = |T.filter(≤k₁)| = |S'.filter(≤k₁)| + 1
    have hgt : (S'.filter (· ≤ k₁)).card < ((compFin m S').filter (· ≤ k₁)).card := by
      rw [hcT_count.symm, hT_count.symm]; omega
    -- firstBad(S') ≤ |S'.filter(≤k₁)| < |comp(S').filter(≤k₁)|
    -- comp(S')[firstBad(S')] ≤ comp(S')[|comp(S').filter(≤k₁)| - 1] ≤ k₁
    -- The last inequality: comp(S')[i] ≤ k₁ for all i < |comp(S').filter(≤k₁)|
    -- (by definition of the filter).
    -- Specifically, comp(S')[firstBad(S')].val ≤ k₁.val
    have hfB_lt : (firstBad m S' hS'c hbad').val <
        ((compFin m S').filter (· ≤ k₁)).card := by
      -- firstBad is the first j with S'[j] ≥ comp(S')[j]
      -- Below firstBad: S'[i] < comp(S')[i] (ballot condition)
      -- Number of S' elements ≤ k₁ = |S'.filter(≤k₁)| = |comp(T).filter(≤k₁)| < |comp(S').filter(≤k₁)|
      -- So there exists j = |S'.filter(≤k₁)| with S'[j] > k₁ and comp(S')[j] ≤ k₁
      -- Hence firstBad ≤ |S'.filter(≤k₁)| < |comp(S').filter(≤k₁)|
      -- We use: S'[|S'.filter(≤k₁)|] > k₁ and comp(S')[|S'.filter(≤k₁)|] ≤ k₁
      -- So S'[|S'.filter(≤k₁)|] ≥ comp(S')[|S'.filter(≤k₁)|] → it's a bad index
      -- Hence firstBad ≤ |S'.filter(≤k₁)|
      have hS'card_lt : (S'.filter (· ≤ k₁)).card < m := by
        calc (S'.filter (· ≤ k₁)).card ≤ S'.card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = m := hS'c
          _ < m + 1 := lt_add_one m
      set j'' : Fin m := ⟨(S'.filter (· ≤ k₁)).card, hS'card_lt⟩
      have hbad_j'' : ¬(S'.orderEmbOfFin hS'c j'' <
          (compFin m S').orderEmbOfFin hcS' j'') := by
        -- S'[j''] > k₁: it's the first S' element after the filter cutoff
        have hS'_j'' : k₁ < S'.orderEmbOfFin hS'c j'' := by
          have hmem := Finset.orderEmbOfFin_mem S' hS'c j''
          by_contra h; push_neg at h
          have : S'.orderEmbOfFin hS'c j'' ∈ S'.filter (· ≤ k₁) :=
            Finset.mem_filter.mpr ⟨hmem, h⟩
          have := filter_le_orderEmb_eq S' hS'c j''
          simp only [j'', Fin.val_mk] at this; omega
        -- comp(S')[j''] ≤ k₁
        have hcS'_j'' : (compFin m S').orderEmbOfFin hcS' j'' ≤ k₁ := by
          have hlt : j''.val < ((compFin m S').filter (· ≤ k₁)).card := by
            simp only [j'', Fin.val_mk]; omega
          have hmem' := Finset.orderEmbOfFin_mem (compFin m S') hcS' j''
          by_contra h; push_neg at h
          -- comp(S')[j''] > k₁, so |comp(S').filter(≤k₁)| ≤ j''
          have hle_j'' : ((compFin m S').filter (· ≤ k₁)).card ≤ j''.val := by
            have hbnd := filter_le_orderEmb_eq (compFin m S') hcS' j''
            -- |comp.filter(≤comp[j''])| = j''+1, and comp[j''] > k₁
            -- So comp.filter(≤k₁) ⊆ comp.filter(≤comp[j''] - 1)
            have : ((compFin m S').filter (· ≤ k₁)).card ≤
                ((compFin m S').filter (· < (compFin m S').orderEmbOfFin hcS' j'')).card := by
              apply Finset.card_le_card; intro x hx
              simp only [mem_filter] at hx ⊢
              exact ⟨hx.1, lt_of_le_of_lt hx.2 h⟩
            have hlt_card : ((compFin m S').filter
                (· < (compFin m S').orderEmbOfFin hcS' j'')).card = j''.val := by
              have heq : (compFin m S').filter (· < (compFin m S').orderEmbOfFin hcS' j'') =
                  Finset.image ((compFin m S').orderEmbOfFin hcS') (Finset.Iio j'') := by
                ext x; simp only [mem_filter, mem_image, Finset.mem_Iio]
                constructor
                · intro ⟨hx, hlt⟩
                  rw [← Finset.image_orderEmbOfFin_univ _ hcS'] at hx
                  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
                  exact ⟨i, ((compFin m S').orderEmbOfFin hcS').strictMono.lt_iff_lt.mp hlt, rfl⟩
                · intro ⟨i, hi, rfl⟩
                  exact ⟨Finset.orderEmbOfFin_mem _ hcS' i,
                    ((compFin m S').orderEmbOfFin hcS').strictMono hi⟩
              rw [heq, Finset.card_image_of_injective _
                ((compFin m S').orderEmbOfFin hcS').injective, Fin.card_Iio]
            calc ((compFin m S').filter (· ≤ k₁)).card
                ≤ ((compFin m S').filter (· < (compFin m S').orderEmbOfFin hcS' j'')).card := this
              _ = j''.val := hlt_card
          exact absurd hlt (not_lt.mpr hle_j'')
        exact not_lt.mpr (le_of_lt (lt_of_le_of_lt hcS'_j'' hS'_j''))
      have hfB_le : (firstBad m S' hS'c hbad').val ≤ j''.val :=
        Finset.min'_le _ j'' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad_j''⟩)
      simp only [j'', Fin.val_mk] at hfB_le; omega
    -- comp(S')[firstBad] ≤ k₁ since firstBad < |comp(S').filter(≤k₁)|
    have hcS'_fB : (compFin m S').orderEmbOfFin hcS' (firstBad m S' hS'c hbad') ≤ k₁ := by
      have hlt : (firstBad m S' hS'c hbad').val < ((compFin m S').filter (· ≤ k₁)).card := hfB_lt
      -- comp(S')[firstBad] ≤ k₁ because firstBad < |comp.filter(≤k₁)|
      by_contra h; push_neg at h
      -- If comp(S')[firstBad] > k₁, then |comp.filter(≤k₁)| ≤ firstBad, contradiction
      have : ((compFin m S').filter (· ≤ k₁)).card ≤ (firstBad m S' hS'c hbad').val := by
        have hbnd := filter_le_orderEmb_eq (compFin m S') hcS' (firstBad m S' hS'c hbad')
        simp only [Fin.val_mk] at hbnd
        nlinarith [Finset.card_le_card (show (compFin m S').filter (· ≤ k₁) ⊆
          (compFin m S').filter (· ≤ (compFin m S').orderEmbOfFin hcS' (firstBad m S' hS'c hbad')) from
          Finset.filter_subset_filter _ (fun x hx => le_trans hx (le_of_lt h)))]
      omega
    exact hcS'_fB
  · -- k₁ ≤ badBarrier(S')
    -- k₁ ∈ comp(S') and comp(S')[firstBad(S')] ≥ k₁
    -- We show: firstAbove condition implies badBarrier ≥ k₁
    -- k₁ ∈ comp(S'), so there exists an index i₁ with comp(S')[i₁] = k₁
    -- If firstBad < i₁, then badBarrier = comp(S')[firstBad] < comp(S')[i₁] = k₁ (by monotonicity)
    -- But then S'[firstBad] ≥ comp(S')[firstBad] and this would contradict something...
    -- Actually: for j < i₁: comp(S')[j] < comp(S')[i₁] = k₁ and S'[j] < comp(S')[j] (if ballot before i₁)
    -- For j = i₁: comp(S')[i₁] = k₁ and S'[i₁] > k₁ (since S'[i₁] ≥ k₁ + 1)
    -- Because S'.filter(≤k₁) has fewer elements than comp(S').filter(≤k₁)...
    -- So S'[i₁-1] is the last S' element ≤ k₁ if any, and S'[i₁] > k₁.
    -- The ballot holds before i₁: S'[j] < comp(S')[j] for j < i₁.
    -- At j = i₁: S'[i₁] > k₁ = comp(S')[i₁]. Bad!
    -- So firstBad ≤ i₁, hence badBarrier = comp(S')[firstBad] ≤ comp(S')[i₁] = k₁.
    -- And also badBarrier ≥ k₁ from the previous argument... wait, that's ≤.
    -- Hmm. The previous argument gives badBarrier ≤ k₁ and this argument gives badBarrier ≤ k₁ too.
    -- I need badBarrier ≥ k₁ for this direction.
    --
    -- Wait, let me reconsider. I need k₁ ≤ badBarrier(S').
    -- badBarrier(S') = comp(S')[firstBad(S')].
    -- firstBad(S') is the MINIMUM j with S'[j] ≥ comp(S')[j].
    -- I need to show that for all j < some threshold, S'[j] < comp(S')[j].
    -- If the threshold corresponds to index i₁ where comp(S')[i₁] = k₁,
    -- then badBarrier ≥ comp(S')[firstBad] where firstBad ≥ i₁ (since ballot holds before i₁),
    -- so badBarrier ≥ comp(S')[i₁] = k₁. ✓
    --
    -- The ballot holds before i₁ (index of k₁ in comp(S')):
    -- For j < i₁: comp(S')[j] < k₁ and |S'.filter(≤comp(S')[j])| ≥ |comp(S').filter(≤comp(S')[j])|
    -- = j+1. Also |S'.filter(≤comp(S')[j])| is related to orderEmb of S'.
    -- S'[j] < comp(S')[j] because: S' has more elements ≤ k₁ than comp(S'), wait no...
    -- Actually at k₁: S'.filter(≤k₁).card < comp(S').filter(≤k₁).card (from hgt above).
    -- So the comp-elements come "first" up to k₁.
    --
    -- Hmm this is getting complex. Let me use the involution argument:
    -- lRefl(S', k₁) = T. T has m+1 elements. firstAbove(T) = k₁.
    -- By firstAbove_eq_badBarrier_of_refl applied to S' (which is bad):
    -- firstAbove(lRefl(S', badBarrier(S'))) = badBarrier(S').
    -- But lRefl(lRefl(T, k₁), k₁) = T (lRefl_invol).
    -- If badBarrier(S') = k₀ ≠ k₁, then lRefl(S', k₀) is some (m+1)-subset T₀ ≠ T.
    -- firstAbove(T₀) = k₀. But then T₀ = lRefl(S', k₀) and lRefl(T₀, k₀) = S' (involution).
    -- And T = lRefl(S', k₁). If k₀ ≠ k₁, we get T ≠ T₀ both giving lRefl(·, ·) = S'.
    -- This doesn't directly give a contradiction.
    --
    -- I think the cleanest proof is: find the index i₁ of k₁ in comp(S') and show:
    -- (a) For j < i₁: S'[j] < comp(S')[j] (ballot condition below k₁)
    -- (b) S'[i₁] > comp(S')[i₁] = k₁
    -- Hence firstBad ≤ i₁ and comp(S')[firstBad] ≤ comp(S')[i₁] = k₁.
    -- But for the ≥ direction we need firstBad = i₁.
    -- Actually from (a) we get firstBad ≥ i₁ (since ballot holds below i₁).
    -- From hbad' (which shows some bad j): firstBad ≤ some j.
    -- From (b) we get firstBad ≤ i₁.
    -- So firstBad = i₁ and badBarrier = k₁. ✓
    --
    -- Let me prove (a): S'[j] < comp(S')[j] for j < i₁.
    -- This follows from the fact that T is "ballot-good" up to k₁ in a certain sense.
    -- Using comp_filter_le_S_filter_below_barrier for T (swapped roles):
    -- T'.filter(≤k) ≤ comp(T').filter(≤k) for k < k₁ translates to:
    -- S'.filter(≤k) ≤ comp(S').filter(≤k) for k < k₁. Wait no, T' = S' here.
    -- For k < k₁:
    -- S'.filter(≤k) = comp(T).filter(≤k).card (from hcT_count argument with k)
    -- Wait, I computed hcT_count for k₁ specifically.
    --
    -- For k < k₁:
    -- S'.filter(≤k) = (lRefl T k₁).filter(≤k) = (comp(T).filter(≤k₁) ∪ T.filter(k₁<·)).filter(≤k)
    --               = comp(T).filter(≤k) (since T.filter(k₁<·).filter(≤k) = ∅ for k < k₁)
    -- comp(S').filter(≤k) = (T.filter(≤k₁) ∪ comp(T).filter(k₁<·)).filter(≤k)
    --                      = T.filter(≤k) (similarly)
    -- So S'.filter(≤k).card = comp(T).filter(≤k).card ≤ T.filter(≤k).card = comp(S').filter(≤k).card
    -- by comp_filter_le_S_filter_below_barrier applied to T... but T is not bad!
    -- We need |comp(T).filter(≤k)| ≤ |T.filter(≤k)| for k < k₁ = firstAbove(T).
    -- This is exactly the complement of firstAbove_spec for k < firstAbove: ¬(T.filter(≤k) > comp(T).filter(≤k)).
    -- = comp(T).filter(≤k).card ≥ T.filter(≤k).card? NO!
    -- firstAbove_spec says: at k₁, |T.filter(≤k₁)| > |comp(T).filter(≤k₁)|.
    -- Minimality says: for k < k₁, |T.filter(≤k)| ≤ |comp(T).filter(≤k)|.
    -- So T has FEWER elements ≤ k than comp(T) for k < k₁.
    -- Therefore |S'.filter(≤k)| = |comp(T).filter(≤k)| ≥ |T.filter(≤k)| = |comp(S').filter(≤k)|.
    -- So S' has MORE elements ≤ k than comp(S') for k < k₁. This means S' is "ballot-bad" before k₁!
    -- Wait that means the ballot condition FAILS for S' before k₁?
    -- For S' to satisfy S'[j] < comp(S')[j], we need the S'-elements to come before comp(S')-elements.
    -- But above we showed |S'.filter(≤k)| ≥ |comp(S').filter(≤k)| for k < k₁...
    -- Hmm, that means comp(S') elements come AFTER S' elements before k₁.
    -- So S'[j] < comp(S')[j] means S' elements come first... but we just showed |S'| ≥ |comp(S')| up to k₁.
    -- Wait, if |S'.filter(≤k)| ≥ |comp(S').filter(≤k)| for all k < k₁, that means each S'[j] ≤ each comp(S')[j], i.e., S'[j] ≤ comp(S')[j].
    -- For STRICT inequality: we need S'[j] < comp(S')[j] i.e. S'[j] ≠ comp(S')[j] which is always true since S' ∩ comp(S') = ∅.
    -- So S'[j] < comp(S')[j] iff |S'.filter(≤k)| > |comp(S').filter(≤k)| at k = S'[j]...
    -- Hmm, this is the connection between the pointwise condition and the filter condition.
    --
    -- Actually: S'[j] < comp(S')[j] iff |S'.filter(≤comp(S')[j])| > j (i.e., more S' elements ≤ comp(S')[j] than comp(S')[j] being the (j+1)-th).
    -- This is equivalent to |S'.filter(≤comp(S')[j])| ≥ j+1 = |comp(S').filter(≤comp(S')[j])|.
    -- So the condition S'[j] < comp(S')[j] is equivalent to |S'.filter(≤c)| ≥ j+1 at c = comp(S')[j],
    -- which holds iff |S'.filter(≤c)| ≥ |comp(S').filter(≤c)| (since |comp(S').filter(≤c)| = j+1).
    -- And we showed above: for c = comp(S')[j] ≤ k₁ (when j < i₁), |S'.filter(≤c)| ≥ |comp(S').filter(≤c)|.
    -- So S'[j] < comp(S')[j] for j < i₁. ✓
    --
    -- And at j = i₁: comp(S')[i₁] = k₁ and S'[i₁] > k₁ (since |S'.filter(≤k₁)| = |comp(T).filter(≤k₁)| = i₁, so S'[i₁] is the first S'-element after k₁, hence > k₁).
    -- So S'[i₁] > k₁ = comp(S')[i₁], meaning NOT S'[i₁] < comp(S')[i₁]. Bad index!
    -- Hence firstBad ≤ i₁ and firstBad ≥ i₁ (ballot holds strictly before i₁), so firstBad = i₁.
    -- badBarrier = comp(S')[i₁] = k₁. ✓
    --
    -- This is the complete proof sketch. Let me implement it.
    -- First find i₁ (index of k₁ in comp(S')):
    rw [← Finset.image_orderEmbOfFin_univ (compFin m S') hcS'] at hk₁_in_cS'
    obtain ⟨i₁, -, hi₁⟩ := Finset.mem_image.mp hk₁_in_cS'
    -- badBarrier(S') = comp(S')[firstBad(S')] ≥ comp(S')[i₁] = k₁
    -- (since firstBad ≥ i₁ by ballot condition before i₁)
    have hfB_ge : i₁ ≤ firstBad m S' hS'c hbad' := by
      -- For j < i₁: S'[j] < comp(S')[j], so j is not bad
      -- Equivalently: firstBad ≥ i₁
      by_contra h; push_neg at h
      -- h : firstBad < i₁, so comp(S')[firstBad] < comp(S')[i₁] = k₁
      have hfB_lt_k₁ : (compFin m S').orderEmbOfFin hcS' (firstBad m S' hS'c hbad') <
          (compFin m S').orderEmbOfFin hcS' i₁ :=
        (compFin m S').orderEmbOfFin hcS' |>.strictMono h
      rw [hi₁] at hfB_lt_k₁
      -- comp(S')[firstBad] < k₁, so |S'.filter(≤comp(S')[firstBad])| ≥ |comp(S').filter(≤comp(S')[firstBad])|
      -- = (firstBad + 1). So S'[firstBad] ≤ comp(S')[firstBad] or more precisely S'[firstBad] < ...
      -- Actually: the count at comp(S')[firstBad]:
      -- comp(S').filter(≤comp(S')[firstBad]).card = firstBad + 1 (by filter_le_orderEmb_eq)
      have hcomp_count_fB : ((compFin m S').filter (·  ≤ (compFin m S').orderEmbOfFin hcS'
          (firstBad m S' hS'c hbad'))).card = (firstBad m S' hS'c hbad').val + 1 :=
        filter_le_orderEmb_eq (compFin m S') hcS' (firstBad m S' hS'c hbad')
      -- For k < k₁, |S'.filter(≤k)| ≥ |comp(S').filter(≤k)| (shown above via T-count swap)
      -- At k = comp(S')[firstBad] < k₁:
      -- |S'.filter(≤k)| ≥ firstBad + 1 = |comp(S').filter(≤k)|
      -- So S'.filter(≤k).card ≥ firstBad + 1
      -- But |S'.filter(≤S'[firstBad])| = firstBad + 1 (filter_le_orderEmb_eq for S')
      -- So S'[firstBad] ≥ comp(S')[firstBad], contradicting firstBad_is_bad (¬(S'[firstBad] < comp(S')[firstBad]))
      -- Wait, firstBad_is_bad says ¬(S'[firstBad] < comp(S')[firstBad]), which means S'[firstBad] ≥ comp(S')[firstBad].
      -- So S'[firstBad] ≥ comp(S')[firstBad]. But we need to show S'[firstBad] < comp(S')[firstBad] to get contradiction.
      -- Wait, the ballot condition HOLDS for j < firstBad. So for j < firstBad, S'[j] < comp(S')[j]. ✓
      -- So firstBad is the FIRST bad index. For h : firstBad(S') < i₁, the ballot condition holds at firstBad.
      -- But firstBad is defined as the first BAD index (¬ < means ≥).
      -- So this is NOT a contradiction! firstBad < i₁ is allowed if S'[firstBad] ≥ comp(S')[firstBad].
      -- I was confused. Let me reconsider.
      --
      -- We want: firstBad ≥ i₁. The proof: by contradiction, assume firstBad < i₁.
      -- Then comp(S')[firstBad] < comp(S')[i₁] = k₁.
      -- S'[firstBad] ≥ comp(S')[firstBad] (firstBad is bad).
      -- Also: for k = comp(S')[firstBad] < k₁:
      --   |S'.filter(≤k)| ≥ |comp(S').filter(≤k)| (ballot condition for S' below k₁ from T)
      --   = firstBad + 1
      -- But |S'.filter(≤S'[firstBad])| = firstBad + 1 (by filter_le_orderEmb_eq for S')
      -- So S'[firstBad] ≥ k = comp(S')[firstBad].
      -- But S'[firstBad] ≥ comp(S')[firstBad] is exactly what firstBad says!
      -- And we need |S'.filter(≤comp(S')[firstBad])| ≥ firstBad + 1
      -- i.e., S'[firstBad] ≤ comp(S')[firstBad].
      -- Combined: S'[firstBad] = comp(S')[firstBad], impossible (disjoint sets).
      -- WAIT: S'[firstBad] ≥ comp(S')[firstBad] and S'[firstBad] ≤ comp(S')[firstBad] → equality.
      -- But S' ∩ comp(S') = ∅, so S'[firstBad] ≠ comp(S')[firstBad]. Contradiction!
      --
      -- Let me implement this:
      -- For k = comp(S')[firstBad] < k₁, |S'.filter(≤k)|:
      have hS'_ge : ((compFin m S').filter (· ≤ (compFin m S').orderEmbOfFin hcS'
          (firstBad m S' hS'c hbad'))).card ≤ (S'.filter (· ≤ (compFin m S').orderEmbOfFin hcS'
          (firstBad m S' hS'c hbad'))).card := by
        -- S'.filter(≤k).card = comp(T).filter(≤k).card (for k < k₁)
        -- comp(S').filter(≤k).card = T.filter(≤k).card (for k < k₁)
        -- T.filter(≤k).card ≤ comp(T).filter(≤k).card (by minimality of firstAbove of T for k < k₁)
        have hk_lt : (compFin m S').orderEmbOfFin hcS' (firstBad m S' hS'c hbad') < k₁ :=
          hfB_lt_k₁
        -- |S'.filter(≤k)| = |comp(T).filter(≤k)|
        have hS'_eq : (S'.filter (· ≤ (compFin m S').orderEmbOfFin hcS'
            (firstBad m S' hS'c hbad'))).card =
            ((compFin m T).filter (· ≤ (compFin m S').orderEmbOfFin hcS'
            (firstBad m S' hS'c hbad'))).card := by
          apply Finset.card_nbij id
          · intro x hx; simp only [mem_filter, id] at hx ⊢
            simp only [S', lRefl, mem_union, mem_filter] at hx
            rcases hx.1 with h | h
            · exact ⟨h.1, h.2⟩
            · exact absurd (lt_of_lt_of_le hk_lt hx.2) (lt_irrefl _)
          · intro x hx; simp only [mem_filter, id] at hx ⊢
            exact ⟨by simp [S', lRefl, mem_union, mem_filter, hx.1, hx.2], hx.2⟩
          · intros; rfl
        -- |comp(S').filter(≤k)| = |T.filter(≤k)|
        have hcS'_eq : ((compFin m S').filter (· ≤ (compFin m S').orderEmbOfFin hcS'
            (firstBad m S' hS'c hbad'))).card =
            (T.filter (· ≤ (compFin m S').orderEmbOfFin hcS'
            (firstBad m S' hS'c hbad'))).card := by
          rw [compFin_lRefl]
          apply Finset.card_nbij id
          · intro x hx; simp only [mem_union, mem_filter, id] at hx ⊢
            rcases hx.1 with h | h
            · exact ⟨h.1, h.2⟩
            · exact absurd (lt_of_lt_of_le hk_lt hx.2) (lt_irrefl _)
          · intro x hx; simp only [mem_filter, id] at hx ⊢
            exact ⟨by simp [mem_union, mem_filter, hx.1, hx.2], hx.2⟩
          · intros; rfl
        rw [hS'_eq, hcS'_eq]
        -- T.filter(≤k).card ≤ comp(T).filter(≤k).card for k < k₁ = firstAbove(T)
        by_contra h; push_neg at h
        have hmem : (compFin m S').orderEmbOfFin hcS' (firstBad m S' hS'c hbad') ∈
            Finset.univ.filter (fun k'' : Fin (2 * m) =>
              (T.filter (· ≤ k'')).card > ((compFin m T).filter (· ≤ k'')).card) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        have hle : firstAbove m T hT ≤
            (compFin m S').orderEmbOfFin hcS' (firstBad m S' hS'c hbad') := by
          simp only [firstAbove]; exact Finset.min'_le _ _ hmem
        exact absurd hle (not_le.mpr hk_lt)
      -- comp(S')[firstBad] = filter_le_orderEmb_eq count gives firstBad+1
      -- S'[firstBad] ≥ comp(S')[firstBad] (firstBad_is_bad)
      -- And comp(S').filter(≤comp(S')[firstBad]).card ≤ S'.filter(≤comp(S')[firstBad]).card
      -- filter_le_orderEmb_eq for S' at firstBad: S'.filter(≤S'[firstBad]).card = firstBad+1
      have hS'_fB_eq := filter_le_orderEmb_eq S' hS'c (firstBad m S' hS'c hbad')
      -- So S'.filter(≤comp[firstBad]).card ≥ S'.filter(≤S'[firstBad]).card - 1 ≥ firstBad
      -- And comp(S').filter(≤comp[firstBad]).card = firstBad + 1 ≤ S'.filter(≤comp[firstBad]).card
      -- So S'[firstBad] ≤ comp(S')[firstBad].
      -- Combined with S'[firstBad] ≥ comp(S')[firstBad] (firstBad_is_bad):
      -- S'[firstBad] = comp(S')[firstBad]. But S' ∩ comp(S') = ∅. Contradiction.
      have hfB_bad := firstBad_is_bad m S' hS'c hbad'
      have hge : (compFin m S').orderEmbOfFin hcS' (firstBad m S' hS'c hbad') ≤
          S'.orderEmbOfFin hS'c (firstBad m S' hS'c hbad') := not_lt.mp hfB_bad
      -- |comp(S').filter(≤comp[fB])| = fB + 1 ≤ |S'.filter(≤comp[fB])|
      -- So S'[fB] ≤ comp(S')[fB]: filter_le_orderEmb_eq for S' at fB says |S'.filter(≤S'[fB])| = fB+1
      -- Since ≤ is total and S'[fB] ≥ comp(S')[fB]:
      -- |S'.filter(≤comp(S')[fB])| ≤ |S'.filter(≤S'[fB])| = fB+1
      have hS'_filter_le : (S'.filter (· ≤ (compFin m S').orderEmbOfFin hcS'
          (firstBad m S' hS'c hbad'))).card ≤ (firstBad m S' hS'c hbad').val + 1 := by
        calc (S'.filter (· ≤ (compFin m S').orderEmbOfFin hcS' (firstBad m S' hS'c hbad'))).card
            ≤ (S'.filter (· ≤ S'.orderEmbOfFin hS'c (firstBad m S' hS'c hbad'))).card :=
              Finset.card_le_card (Finset.filter_subset_filter _ hge)
          _ = (firstBad m S' hS'c hbad').val + 1 := hS'_fB_eq
      -- But |comp(S').filter(≤comp(S')[fB])| = fB+1 ≤ |S'.filter(≤comp(S')[fB])| ≤ fB+1
      -- So equality and comp(S')[fB] = S'[fB] (both give filter card = fB+1).
      -- S'[fB] ∈ S' and comp(S')[fB] ∈ comp(S'), and they're equal. Contradiction.
      have heq : (compFin m S').orderEmbOfFin hcS' (firstBad m S' hS'c hbad') =
          S'.orderEmbOfFin hS'c (firstBad m S' hS'c hbad') := by
        apply le_antisymm hge
        -- Show S'[fB] ≤ comp(S')[fB] using filter count ≥ fB+1 at comp(S')[fB]
        by_contra hlt; push_neg at hlt
        -- S'[fB] < comp(S')[fB] contradicts firstBad_is_bad
        exact absurd hlt hfB_bad
      have hmemS := Finset.orderEmbOfFin_mem S' hS'c (firstBad m S' hS'c hbad')
      have hmemC := Finset.orderEmbOfFin_mem (compFin m S') hcS' (firstBad m S' hS'c hbad')
      rw [← heq] at hmemS
      simp only [compFin, Finset.mem_filter, Finset.mem_univ, true_and] at hmemC
      exact absurd hmemS hmemC
    -- Now: firstBad ≥ i₁, so comp(S')[firstBad] ≥ comp(S')[i₁] = k₁
    calc k₁ = (compFin m S').orderEmbOfFin hcS' i₁ := hi₁.symm
      _ ≤ (compFin m S').orderEmbOfFin hcS' (firstBad m S' hS'c hbad') :=
          (compFin m S').orderEmbOfFin hcS' |>.monotone hfB_ge

/-- Count of ballot Finsets of size m in Fin(2m) equals Cn m.
    Proved via the Lindstrom reflection principle:
    bad m-subsets ↔ (m+1)-subsets, so ballot = C(2m,m) - C(2m,m+1) = Cn m. -/
private lemma ballot_finset_card (m : ℕ) :
    Fintype.card {S : Finset (Fin (2 * m)) // ∃ (hS : S.card = m),
      ∀ j : Fin m,
        S.orderEmbOfFin hS j <
        (compFin m S).orderEmbOfFin (compFin_card m S hS) j} =
    LatticePathLGV.Cn m := by
  -- Delegate to standalone proved lemmas:
  -- lRefl T (firstAbove T) has cardinality m:
  have lRefl_fA_card : ∀ (T : Finset (Fin (2 * m))) (hT : T.card = m + 1),
      (lRefl m T (firstAbove m T hT)).card = m := fun T hT => lRefl_firstAbove_card T hT
  -- lRefl T (firstAbove T) is a bad m-subset:
  have lRefl_fA_bad : ∀ (T : Finset (Fin (2 * m))) (hT : T.card = m + 1),
      ∃ j : Fin m, ¬((lRefl m T (firstAbove m T hT)).orderEmbOfFin (lRefl_fA_card T hT) j <
        (compFin m (lRefl m T (firstAbove m T hT))).orderEmbOfFin
          (compFin_card m _ (lRefl_fA_card T hT)) j) := fun T hT => lRefl_firstAbove_is_bad T hT
  -- firstAbove(lRefl S k₀) = k₀ (round-trip 1):
  have fA_eq_bB : ∀ (S : Finset (Fin (2 * m))) (hS : S.card = m)
      (hbad : ∃ j : Fin m, ¬(S.orderEmbOfFin hS j <
        (compFin m S).orderEmbOfFin (compFin_card m S hS) j)),
      firstAbove m (lRefl m S (badBarrier m S hS hbad))
        (lRefl_badBarrier_card S hS hbad) =
      badBarrier m S hS hbad := fun S hS hbad => firstAbove_eq_badBarrier_of_refl S hS hbad
  -- badBarrier(lRefl T k₁) = k₁ (round-trip 2):
  have bB_eq_fA : ∀ (T : Finset (Fin (2 * m))) (hT : T.card = m + 1),
      badBarrier m (lRefl m T (firstAbove m T hT))
        (lRefl_fA_card T hT) (lRefl_fA_bad T hT) =
      firstAbove m T hT := fun T hT => badBarrier_eq_firstAbove_of_refl T hT
  -- Step 1: bad m-subsets ≃ (m+1)-subsets via Lindstrom reflection.
  have hBad : Fintype.card {S : Finset (Fin (2 * m)) // ∃ hS : S.card = m,
        ∃ j : Fin m, ¬(S.orderEmbOfFin hS j <
          (compFin m S).orderEmbOfFin (compFin_card m S hS) j)} =
      Nat.choose (2 * m) (m + 1) := by
    rw [show Nat.choose (2 * m) (m + 1) = Nat.choose (Fintype.card (Fin (2 * m))) (m + 1)
        from by simp [Fintype.card_fin]]
    rw [← Fintype.card_finset_len (m + 1)]
    apply Fintype.card_congr
    exact {
      toFun := fun ⟨S, hS, hbad⟩ =>
          ⟨lRefl m S (badBarrier m S hS hbad), lRefl_badBarrier_card S hS hbad⟩
      invFun := fun ⟨T, hT⟩ =>
          ⟨lRefl m T (firstAbove m T hT), lRefl_fA_card T hT, lRefl_fA_bad T hT⟩
      left_inv := fun ⟨S, hS, hbad⟩ =>
          Subtype.ext (by rw [fA_eq_bB S hS hbad]; exact lRefl_invol S _)
      right_inv := fun ⟨T, hT⟩ =>
          Subtype.ext (by rw [bB_eq_fA T hT]; exact lRefl_invol T _) }
  -- Step 2: partition ballot + bad = all m-subsets = C(2m,m).
  have hAll : Fintype.card {S : Finset (Fin (2 * m)) // S.card = m} =
      Nat.choose (2 * m) m := by
    rw [show Nat.choose (2 * m) m = Nat.choose (Fintype.card (Fin (2 * m))) m
        from by simp [Fintype.card_fin]]
    exact Fintype.card_finset_len m
  have hPartition :
      Fintype.card {S : Finset (Fin (2 * m)) // ∃ hS : S.card = m,
        ∀ j : Fin m, S.orderEmbOfFin hS j <
          (compFin m S).orderEmbOfFin (compFin_card m S hS) j} +
      Fintype.card {S : Finset (Fin (2 * m)) // ∃ hS : S.card = m,
        ∃ j : Fin m, ¬(S.orderEmbOfFin hS j <
          (compFin m S).orderEmbOfFin (compFin_card m S hS) j)} =
      Fintype.card {S : Finset (Fin (2 * m)) // S.card = m} := by
    rw [← Fintype.card_sum]
    apply Fintype.card_congr
    classical
    exact {
      toFun := fun x => match x with
        | Sum.inl ⟨S, hS, _⟩ => ⟨S, hS⟩
        | Sum.inr ⟨S, hS, _⟩ => ⟨S, hS⟩
      invFun := fun ⟨S, hS⟩ =>
        if h : ∀ j : Fin m, S.orderEmbOfFin hS j <
            (compFin m S).orderEmbOfFin (compFin_card m S hS) j
        then Sum.inl ⟨S, hS, h⟩
        else Sum.inr ⟨S, hS, not_forall.mp h⟩
      left_inv := by
        intro x
        rcases x with ⟨S, hS, h⟩ | ⟨S, hS, hb⟩
        · simp [dif_pos h]
        · have hnp : ¬∀ j : Fin m, S.orderEmbOfFin hS j <
              (compFin m S).orderEmbOfFin (compFin_card m S hS) j :=
            not_forall.mpr hb
          simp only [dif_neg hnp]
          congr 1; apply Subtype.ext; rfl
      right_inv := fun ⟨S, hS⟩ => by
        simp only
        split_ifs <;> rfl }
  -- Step 3: arithmetic to conclude.
  show _ = Nat.choose (2 * m) m - Nat.choose (2 * m) (m + 1)
  rw [hBad, hAll] at hPartition
  omega

theorem card_SYT_twoRectYD (m : ℕ) :
    Fintype.card (StandardYoungTableau (twoRectYD m)) = LatticePathLGV.Cn m := by
  rw [Fintype.card_congr (sytBallotEquiv m)]
  exact ballot_finset_card m

/-- **Hook-length formula for 2-row rectangular Young diagrams.**
    card(SYT(twoRectYD m)) × hookProd(twoRectYD m) = (2m)!
    Proof: C_m × (m+1)! × m! = (2m)! (LGVCorollaries.hook_length_formula_two_row). -/
theorem hook_length_formula_two_rect (m : ℕ) :
    Fintype.card (StandardYoungTableau (twoRectYD m)) * hookProd (twoRectYD m) =
    (twoRectYD m).card.factorial := by
  rw [twoRectYD_card, hookProd_twoRectYD, card_SYT_twoRectYD]
  exact LGVCorollaries.hook_length_formula_two_row m

-- Numerical verification
example : LatticePathLGV.Cn 1 * (2 * 1) = 2 := by native_decide
example : LatticePathLGV.Cn 2 * (6 * 2) = 24 := by native_decide
example : LatticePathLGV.Cn 3 * (24 * 6) = 720 := by native_decide

-- ============================================================
-- PART XI: Hook-Length Formula for General 2-Row Diagrams
-- ============================================================

/-
  The general 2-row Young diagram twoRowYD a b (a ≥ b) has shape [a, b].
    hookLength(0,j) = a-j+1  for j < b  (arm = a-j-1, leg = 1 since colLen=2)
    hookLength(0,j) = a-j    for b ≤ j < a  (arm = a-j-1, leg = 0 since colLen=1)
    hookLength(1,j) = b-j    for j < b  (arm = b-j-1, leg = 0)
    hookProd = (a+1).descFactorial b × (a-b)! × b!
    card(SYT([a,b])) = ballotSeqCount (a+1) b  [sorry: bijection via ballot subsets]
  Hook formula: ballotSeqCount (a+1) b × (a+1).descFactorial b × (a-b)! × b! = (a+b)!
-/

/-- The general 2-row Young diagram with row lengths a ≥ b ≥ 0. -/
def twoRowYD (a b : ℕ) (hab : b ≤ a) : YoungDiagram :=
  YoungDiagram.ofRowLens [a, b] (by
    simp only [List.SortedGE, List.Sorted, List.pairwise_cons, List.mem_singleton, forall_eq,
               List.Pairwise.nil, and_true]
    exact hab)

/-- Membership: (i,j) ∈ twoRowYD a b ↔ (i=0 ∧ j<a) ∨ (i=1 ∧ j<b) -/
lemma mem_twoRowYD {a b : ℕ} (hab : b ≤ a) {i j : ℕ} :
    (i, j) ∈ twoRowYD a b hab ↔ (i = 0 ∧ j < a) ∨ (i = 1 ∧ j < b) := by
  simp only [twoRowYD, YoungDiagram.mem_ofRowLens, List.length_cons, List.length_singleton]
  constructor
  · rintro ⟨hi, hj⟩
    interval_cases i
    · left; exact ⟨rfl, by simpa [List.getElem_cons_zero] using hj⟩
    · right; exact ⟨rfl, by simpa [List.getElem_cons_succ, List.getElem_cons_zero] using hj⟩
    · omega
  · rintro (⟨rfl, hj⟩ | ⟨rfl, hj⟩)
    · exact ⟨by omega, by simpa [List.getElem_cons_zero] using hj⟩
    · exact ⟨by omega, by simpa [List.getElem_cons_succ, List.getElem_cons_zero] using hj⟩

/-- twoRowYD a b has a+b cells. -/
lemma twoRowYD_card (a b : ℕ) (hab : b ≤ a) : (twoRowYD a b hab).card = a + b := by
  have hcells : (twoRowYD a b hab).cells =
      (Finset.range a).image (Prod.mk 0) ∪ (Finset.range b).image (Prod.mk 1) := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, mem_twoRowYD hab, Finset.mem_union, Finset.mem_image,
      Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, hj⟩ | ⟨rfl, hj⟩)
      · left; exact ⟨j, hj, rfl, rfl⟩
      · right; exact ⟨j, hj, rfl, rfl⟩
    · rintro (⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩)
      · left; exact ⟨rfl, hk⟩
      · right; exact ⟨rfl, hk⟩
  unfold YoungDiagram.card
  rw [hcells, Finset.card_union_of_disjoint
        (Finset.disjoint_left.mpr (by simp [Finset.mem_image, Prod.mk.injEq])),
      Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2),
      Finset.card_range, Finset.card_range]

lemma rowLen_twoRowYD_zero (a b : ℕ) (hab : b ≤ a) : (twoRowYD a b hab).rowLen 0 = a := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]
    simp [mem_twoRowYD hab]
  · cases a with
    | zero => exact Nat.zero_le _
    | succ a =>
      exact YoungDiagram.mem_iff_lt_rowLen.mp
        (mem_twoRowYD hab |>.mpr (Or.inl ⟨rfl, a.lt_succ_self⟩))

lemma rowLen_twoRowYD_one (a b : ℕ) (hab : b ≤ a) : (twoRowYD a b hab).rowLen 1 = b := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]
    simp [mem_twoRowYD hab]
  · cases b with
    | zero => simp
    | succ b =>
      exact YoungDiagram.mem_iff_lt_rowLen.mp
        (mem_twoRowYD hab |>.mpr (Or.inr ⟨rfl, b.lt_succ_self⟩))

lemma colLen_twoRowYD_lt {a b : ℕ} (hab : b ≤ a) {j : ℕ} (hj : j < b) :
    (twoRowYD a b hab).colLen j = 2 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]
    simp [mem_twoRowYD hab]
    omega
  · have h1 : 1 < (twoRowYD a b hab).colLen j :=
      YoungDiagram.mem_iff_lt_colLen.mp
        (mem_twoRowYD hab |>.mpr (Or.inr ⟨rfl, hj⟩))
    omega

lemma colLen_twoRowYD_ge {a b : ℕ} (hab : b ≤ a) {j : ℕ} (hj : b ≤ j) (hja : j < a) :
    (twoRowYD a b hab).colLen j = 1 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]
    simp [mem_twoRowYD hab]
    omega
  · have h1 : 0 < (twoRowYD a b hab).colLen j :=
      YoungDiagram.mem_iff_lt_colLen.mp
        (mem_twoRowYD hab |>.mpr (Or.inl ⟨rfl, hja⟩))
    omega

lemma hookLength_twoRowYD_row0_lt {a b : ℕ} (hab : b ≤ a) {j : ℕ} (hj : j < b) :
    hookLength (twoRowYD a b hab) 0 j = a - j + 1 := by
  unfold hookLength armLen legLen
  rw [rowLen_twoRowYD_zero a b hab, colLen_twoRowYD_lt hab hj]
  omega

lemma hookLength_twoRowYD_row0_ge {a b : ℕ} (hab : b ≤ a) {j : ℕ} (hj : b ≤ j) (hja : j < a) :
    hookLength (twoRowYD a b hab) 0 j = a - j := by
  unfold hookLength armLen legLen
  rw [rowLen_twoRowYD_zero a b hab, colLen_twoRowYD_ge hab hj hja]
  omega

lemma hookLength_twoRowYD_row1 {a b : ℕ} (hab : b ≤ a) {j : ℕ} (hj : j < b) :
    hookLength (twoRowYD a b hab) 1 j = b - j := by
  unfold hookLength armLen legLen
  rw [rowLen_twoRowYD_one a b hab, colLen_twoRowYD_lt hab hj]
  omega

private lemma twoRowYD_cells_eq' (a b : ℕ) (hab : b ≤ a) :
    (twoRowYD a b hab).cells =
    (Finset.range a).image (Prod.mk 0) ∪ (Finset.range b).image (Prod.mk 1) := by
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, mem_twoRowYD hab, Finset.mem_union, Finset.mem_image,
    Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, hj⟩ | ⟨rfl, hj⟩)
    · left; exact ⟨j, hj, rfl, rfl⟩
    · right; exact ⟨j, hj, rfl, rfl⟩
  · rintro (⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩)
    · left; exact ⟨rfl, hk⟩
    · right; exact ⟨rfl, hk⟩

private lemma twoRowYD_cells_disj' (a b : ℕ) :
    Disjoint ((Finset.range a).image (Prod.mk 0)) ((Finset.range b).image (Prod.mk 1)) :=
  Finset.disjoint_left.mpr (by simp [Finset.mem_image, Prod.mk.injEq])

/-- Hook product of twoRowYD a b equals (a+1).descFactorial b × (a-b)! × b!. -/
theorem hookProd_twoRowYD (a b : ℕ) (hab : b ≤ a) :
    hookProd (twoRowYD a b hab) =
    (a + 1).descFactorial b * (a - b).factorial * b.factorial := by
  unfold hookProd
  rw [twoRowYD_cells_eq' a b hab,
      Finset.prod_union (twoRowYD_cells_disj' a b),
      Finset.prod_image (fun x _ y _ h => (Prod.mk.inj h).2),
      Finset.prod_image (fun x _ y _ h => (Prod.mk.inj h).2)]
  -- Row 0: split range a = range b ∪ Ico b a
  have hsplit : Finset.range a = Finset.range b ∪ Finset.Ico b a := by
    rw [Finset.range_eq_Ico, ← Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
    simp [Finset.range_eq_Ico]
  have hdisj : Disjoint (Finset.range b) (Finset.Ico b a) :=
    Finset.disjoint_left.mpr (fun x hx hy =>
      absurd (Finset.mem_range.mp hx) (by simp [Finset.mem_Ico] at hy; omega))
  -- Row 0 total product
  have hrow0 : ∏ j ∈ Finset.range a, hookLength (twoRowYD a b hab) 0 j =
      (a + 1).descFactorial b * (a - b).factorial := by
    rw [hsplit, Finset.prod_union hdisj]
    -- Left part: ∏ j in range b, (a-j+1) = (a+1).descFactorial b
    have hleft : ∏ j ∈ Finset.range b, hookLength (twoRowYD a b hab) 0 j =
        (a + 1).descFactorial b := by
      rw [Finset.prod_congr rfl (fun j hj =>
            hookLength_twoRowYD_row0_lt hab (Finset.mem_range.mp hj)),
          Finset.prod_congr rfl (fun j hj =>
            show a - j + 1 = (a + 1) - j from by
              have := Finset.mem_range.mp hj; omega),
          ← Nat.descFactorial_eq_prod_range]
    -- Right part: ∏ j in Ico b a, (a-j) = (a-b)!
    have hright : ∏ j ∈ Finset.Ico b a, hookLength (twoRowYD a b hab) 0 j =
        (a - b).factorial := by
      rw [Finset.prod_congr rfl (fun j hj =>
            hookLength_twoRowYD_row0_ge hab
              (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2)]
      -- ∏ j in Ico b a, (a-j) = ∏ k in range(a-b), (a-b-k) via reindex k = j-b
      rw [show Finset.Ico b a = (Finset.range (a - b)).image (b + ·) from by
            ext x; simp [Finset.mem_Ico, Finset.mem_range, Finset.mem_image]; omega,
          Finset.prod_image (fun x _ y _ h => by omega),
          Finset.prod_congr rfl (fun k hk =>
            show a - (b + k) = (a - b) - k from by
              have := Finset.mem_range.mp hk; omega),
          ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
    rw [hleft, hright]
  -- Row 1: ∏ j in range b, (b-j) = b!
  have hrow1 : ∏ j ∈ Finset.range b, hookLength (twoRowYD a b hab) 1 j = b.factorial := by
    rw [Finset.prod_congr rfl (fun j hj =>
          hookLength_twoRowYD_row1 hab (Finset.mem_range.mp hj)),
        ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  rw [hrow0, hrow1]

-- ============================================================
-- PART XIb: Card of SYT for General 2-Row Diagrams (Corner Recursion)
-- ============================================================

/-- twoRowYD a 0 hab = oneRowYD a: both have cells {(0,j) | j < a}. -/
private lemma twoRowYD_zero_eq_oneRowYD (a : ℕ) {h : 0 ≤ a} :
    twoRowYD a 0 h = oneRowYD a := by
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, mem_twoRowYD h, mem_oneRowYD]
  omega

/-- twoRowYD a a h = twoRectYD a: both have cells {(i,j) | i∈{0,1}, j<a}. -/
private lemma twoRowYD_sq_eq_twoRectYD (a : ℕ) {h : a ≤ a} :
    twoRowYD a a h = twoRectYD a := by
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, mem_twoRowYD h, mem_twoRectYD]
  exact Iff.rfl

/-- ballotSeqCount (a+1) 0 = 1 for all a:
    C(a,a) - C(a, a+1) = 1 - 0 = 1. -/
private lemma ballotSeqCount_zero_right (a : ℕ) :
    LatticePathLGV.ballotSeqCount (a + 1) 0 = 1 := by
  simp only [LatticePathLGV.ballotSeqCount,
             show a + 1 + 0 - 1 = a from by omega,
             show a + 1 - 1 = a from by omega,
             Nat.choose_self, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self a), Nat.sub_zero]

/-- Pascal recursion for ballotSeqCount: for 0 < b < a,
    ballotSeqCount (a+1) b = ballotSeqCount a b + ballotSeqCount (a+1) (b-1).
    Both sides equal C(a+b-1, a-1) - C(a+b-1, a+1) by applying Pascal twice.
    [Arithmetic identity: provable but deferred for build speed] -/
private lemma ballotSeqCount_rec (a b : ℕ) (ha : b < a) (hb : 0 < b) :
    LatticePathLGV.ballotSeqCount (a + 1) b =
    LatticePathLGV.ballotSeqCount a b + LatticePathLGV.ballotSeqCount (a + 1) (b - 1) := by
  -- Pascal: C(a+b,a) = C(a+b-1,a-1) + C(a+b-1,a)  and  C(a+b,a+1) = C(a+b-1,a) + C(a+b-1,a+1)
  -- So LHS = C(a+b-1,a-1) - C(a+b-1,a+1) = RHS (both differences non-neg since a > b)
  simp only [LatticePathLGV.ballotSeqCount,
             show a + 1 + b - 1 = a + b from by omega,
             show a + 1 - 1 = a from by omega,
             show a + 1 + (b - 1) - 1 = a + b - 1 from by omega,
             show a + 1 + (b - 1) = a + b from by omega]
  -- Pascal identities:
  have hPas1 : Nat.choose (a + b) a =
      Nat.choose (a + b - 1) (a - 1) + Nat.choose (a + b - 1) a :=
    Nat.choose_eq_choose_pred_add (by omega) (by omega)
  have hPas2 : Nat.choose (a + b) (a + 1) =
      Nat.choose (a + b - 1) a + Nat.choose (a + b - 1) (a + 1) :=
    Nat.choose_succ_right _ _ (by omega)
  -- Monotonicity: C(a+b-1, a-1) ≥ C(a+b-1, a) ≥ C(a+b-1, a+1) since a > b.
  -- Key: choose_succ_right_eq says C(n,k+1)*(k+1) = C(n,k)*(n-k).
  -- For hge1 (k=a-1): C(n,a)*a = C(n,a-1)*b, and b < a, so C(n,a)*a ≤ C(n,a-1)*a → C(n,a) ≤ C(n,a-1).
  -- For hge2 (k=a): C(n,a+1)*(a+1) = C(n,a)*(b-1), and b-1 ≤ a+1, so C(n,a+1)*(a+1) ≤ C(n,a)*(a+1) → C(n,a+1) ≤ C(n,a).
  -- Monotonicity via choose_succ_right_eq ratio identity:
  -- C(n,k+1)*(k+1) = C(n,k)*(n-k), so C(n,k+1) ≤ C(n,k) iff n-k ≤ k+1 iff n ≤ 2k+1.
  have hge1 : Nat.choose (a + b - 1) a ≤ Nat.choose (a + b - 1) (a - 1) := by
    -- C(n,a)*a = C(n,a-1)*b via choose_succ_right_eq with k=a-1
    -- b < a, so C(n,a)*a = C(n,a-1)*b ≤ C(n,a-1)*a → C(n,a) ≤ C(n,a-1) (cancel a > 0)
    have hkey : Nat.choose (a + b - 1) a * a =
        Nat.choose (a + b - 1) (a - 1) * b := by
      have h := Nat.choose_succ_right_eq (a + b - 1) (a - 1)
      simp only [show a - 1 + 1 = a from by omega,
                 show a + b - 1 - (a - 1) = b from by omega] at h; exact h
    nlinarith [Nat.zero_le (Nat.choose (a + b - 1) (a - 1)),
               Nat.zero_le (Nat.choose (a + b - 1) a)]
  have hge2 : Nat.choose (a + b - 1) (a + 1) ≤ Nat.choose (a + b - 1) a := by
    -- C(n,a+1)*(a+1) = C(n,a)*(b-1) via choose_succ_right_eq with k=a
    -- b-1 ≤ a+1, so C(n,a+1)*(a+1) = C(n,a)*(b-1) ≤ C(n,a)*(a+1) → C(n,a+1) ≤ C(n,a)
    have hkey : Nat.choose (a + b - 1) (a + 1) * (a + 1) =
        Nat.choose (a + b - 1) a * (b - 1) := by
      have h := Nat.choose_succ_right_eq (a + b - 1) a
      simp only [show a + b - 1 - a = b - 1 from by omega] at h; exact h
    nlinarith [Nat.zero_le (Nat.choose (a + b - 1) a),
               Nat.zero_le (Nat.choose (a + b - 1) (a + 1))]
  -- Combine: (C1+C2)-(C2+C3) = C1-C3 = (C1-C2)+(C2-C3) in ℕ (since C1 ≥ C2 ≥ C3)
  rw [hPas1, hPas2]
  omega

-- ============================================================
-- PART XIa: Corner-Cell Bijection Infrastructure
-- ============================================================

-- Lift membership from twoRowYD (a-1) b to twoRowYD a b
private lemma mem_of_twoRowYD_pred {a b : ℕ} (hab : b ≤ a) (hab₁ : b ≤ a - 1) :
    ∀ c, c ∈ twoRowYD (a - 1) b hab₁ → c ∈ twoRowYD a b hab := fun c hc => by
  rcases mem_twoRowYD hab₁ |>.mp hc with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact mem_twoRowYD hab |>.mpr (Or.inl ⟨hi, by omega⟩)
  · exact mem_twoRowYD hab |>.mpr (Or.inr ⟨hi, hj⟩)

-- Lift membership from twoRowYD a (b-1) to twoRowYD a b
private lemma mem_of_twoRowYD_pred2 {a b : ℕ} (hab : b ≤ a) (hab₂ : b - 1 ≤ a) :
    ∀ c, c ∈ twoRowYD a (b - 1) hab₂ → c ∈ twoRowYD a b hab := fun c hc => by
  rcases mem_twoRowYD hab₂ |>.mp hc with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact mem_twoRowYD hab |>.mpr (Or.inl ⟨hi, hj⟩)
  · exact mem_twoRowYD hab |>.mpr (Or.inr ⟨hi, by omega⟩)

-- Restrict T : SYT(twoRowYD a b) to SYT(twoRowYD (a-1) b)
-- when max entry a+b is at corner (0, a-1)
private noncomputable def restrictSYT0 {a b : ℕ}
    (hab : b ≤ a) (hab₁ : b ≤ a - 1)
    (T : StandardYoungTableau (twoRowYD a b hab))
    (hT : T.entry (0, a - 1) = a + b) :
    StandardYoungTableau (twoRowYD (a - 1) b hab₁) where
  entry c := if c ∈ twoRowYD (a - 1) b hab₁ then T.entry c else 0
  entry_zero c hc := by simp [hc]
  entry_range c hc := by
    simp only [hc, ↓reduceIte]
    have hmem := mem_of_twoRowYD_pred hab hab₁ c hc
    refine ⟨(T.entry_range c hmem).1, ?_⟩
    have hle := (T.entry_range c hmem).2
    have hne : T.entry c ≠ a + b := by
      intro heq
      have := T.entry_injOn c (0, a - 1) hmem
        (mem_twoRowYD hab |>.mpr (Or.inl ⟨rfl, by omega⟩)) (heq.trans hT.symm)
      exact absurd (this ▸ hc) (by simp [mem_twoRowYD hab₁])
    rw [twoRowYD_card a b hab] at hle
    rw [twoRowYD_card (a - 1) b hab₁]; omega
  entry_injOn c₁ c₂ hc₁ hc₂ h := by
    simp only [hc₁, hc₂, ↓reduceIte] at h
    exact T.entry_injOn c₁ c₂
      (mem_of_twoRowYD_pred hab hab₁ c₁ hc₁) (mem_of_twoRowYD_pred hab hab₁ c₂ hc₂) h
  row_strict i j₁ j₂ hc₁ hc₂ hlt := by
    simp only [hc₁, hc₂, ↓reduceIte]
    exact T.row_strict i j₁ j₂
      (mem_of_twoRowYD_pred hab hab₁ _ hc₁) (mem_of_twoRowYD_pred hab hab₁ _ hc₂) hlt
  col_strict i₁ i₂ j hc₁ hc₂ hlt := by
    simp only [hc₁, hc₂, ↓reduceIte]
    exact T.col_strict i₁ i₂ j
      (mem_of_twoRowYD_pred hab hab₁ _ hc₁) (mem_of_twoRowYD_pred hab hab₁ _ hc₂) hlt

-- Restrict T : SYT(twoRowYD a b) to SYT(twoRowYD a (b-1))
-- when max entry a+b is at corner (1, b-1)
private noncomputable def restrictSYT1 {a b : ℕ}
    (hab : b ≤ a) (hab₂ : b - 1 ≤ a)
    (T : StandardYoungTableau (twoRowYD a b hab))
    (hT : T.entry (1, b - 1) = a + b) :
    StandardYoungTableau (twoRowYD a (b - 1) hab₂) where
  entry c := if c ∈ twoRowYD a (b - 1) hab₂ then T.entry c else 0
  entry_zero c hc := by simp [hc]
  entry_range c hc := by
    simp only [hc, ↓reduceIte]
    have hmem := mem_of_twoRowYD_pred2 hab hab₂ c hc
    refine ⟨(T.entry_range c hmem).1, ?_⟩
    have hle := (T.entry_range c hmem).2
    have hne : T.entry c ≠ a + b := by
      intro heq
      have := T.entry_injOn c (1, b - 1) hmem
        (mem_twoRowYD hab |>.mpr (Or.inr ⟨rfl, by omega⟩)) (heq.trans hT.symm)
      exact absurd (this ▸ hc) (by simp [mem_twoRowYD hab₂])
    rw [twoRowYD_card a b hab] at hle
    rw [twoRowYD_card a (b - 1) hab₂]; omega
  entry_injOn c₁ c₂ hc₁ hc₂ h := by
    simp only [hc₁, hc₂, ↓reduceIte] at h
    exact T.entry_injOn c₁ c₂
      (mem_of_twoRowYD_pred2 hab hab₂ c₁ hc₁) (mem_of_twoRowYD_pred2 hab hab₂ c₂ hc₂) h
  row_strict i j₁ j₂ hc₁ hc₂ hlt := by
    simp only [hc₁, hc₂, ↓reduceIte]
    exact T.row_strict i j₁ j₂
      (mem_of_twoRowYD_pred2 hab hab₂ _ hc₁) (mem_of_twoRowYD_pred2 hab hab₂ _ hc₂) hlt
  col_strict i₁ i₂ j hc₁ hc₂ hlt := by
    simp only [hc₁, hc₂, ↓reduceIte]
    exact T.col_strict i₁ i₂ j
      (mem_of_twoRowYD_pred2 hab hab₂ _ hc₁) (mem_of_twoRowYD_pred2 hab hab₂ _ hc₂) hlt

-- Extend T₁ : SYT(twoRowYD (a-1) b) to SYT(twoRowYD a b) by adding (0,a-1) ↦ a+b
private noncomputable def extendSYT0 {a b : ℕ}
    (hab : b ≤ a) (hab₁ : b ≤ a - 1)
    (T₁ : StandardYoungTableau (twoRowYD (a - 1) b hab₁)) :
    StandardYoungTableau (twoRowYD a b hab) where
  entry c := if c = (0, a - 1) then a + b else T₁.entry c
  entry_zero c hc := by
    have hne : c ≠ (0, a - 1) := fun h =>
      hc (h ▸ mem_twoRowYD hab |>.mpr (Or.inl ⟨rfl, by omega⟩))
    rw [if_neg hne]
    exact T₁.entry_zero c (fun hc₁ => hc (mem_of_twoRowYD_pred hab hab₁ c hc₁))
  entry_range c hc := by
    by_cases hce : c = (0, a - 1)
    · simp only [hce, ↓reduceIte]
      have ha1 : a - 1 < a := by
        rcases mem_twoRowYD hab |>.mp (hce ▸ hc) with ⟨_, h⟩ | ⟨h, _⟩
        · exact h; · exact absurd h (by norm_num)
      rw [twoRowYD_card a b hab]; exact ⟨by omega, le_refl _⟩
    · rw [if_neg hce]
      have hcμ₁ : c ∈ twoRowYD (a - 1) b hab₁ := by
        rcases mem_twoRowYD hab |>.mp hc with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inl ⟨hi,
            by have := fun heq => hce (Prod.ext hi heq); omega⟩)
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inr ⟨hi, hj⟩)
      have hr := T₁.entry_range c hcμ₁
      rw [twoRowYD_card (a - 1) b hab₁] at hr
      rw [twoRowYD_card a b hab]; exact ⟨hr.1, by omega⟩
  entry_injOn c₁ c₂ hc₁ hc₂ h := by
    simp only at h
    by_cases h₁ : c₁ = (0, a - 1) <;> by_cases h₂ : c₂ = (0, a - 1)
    · rw [h₁, h₂]
    · simp only [h₁, h₂, ↓reduceIte, if_false] at h
      have hcμ₂ : c₂ ∈ twoRowYD (a - 1) b hab₁ := by
        rcases mem_twoRowYD hab |>.mp hc₂ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inl ⟨hi,
            by have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inr ⟨hi, hj⟩)
      have := (T₁.entry_range c₂ hcμ₂).2
      rw [twoRowYD_card (a - 1) b hab₁] at this; omega
    · simp only [h₁, h₂, ↓reduceIte, if_true, if_false] at h
      have hcμ₁ : c₁ ∈ twoRowYD (a - 1) b hab₁ := by
        rcases mem_twoRowYD hab |>.mp hc₁ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inl ⟨hi,
            by have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inr ⟨hi, hj⟩)
      have := (T₁.entry_range c₁ hcμ₁).2
      rw [twoRowYD_card (a - 1) b hab₁] at this; omega
    · simp only [h₁, h₂, ↓reduceIte] at h
      have hcμ₁ : c₁ ∈ twoRowYD (a - 1) b hab₁ := by
        rcases mem_twoRowYD hab |>.mp hc₁ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inl ⟨hi,
            by have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inr ⟨hi, hj⟩)
      have hcμ₂ : c₂ ∈ twoRowYD (a - 1) b hab₁ := by
        rcases mem_twoRowYD hab |>.mp hc₂ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inl ⟨hi,
            by have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inr ⟨hi, hj⟩)
      exact T₁.entry_injOn c₁ c₂ hcμ₁ hcμ₂ h
  row_strict i j₁ j₂ hc₁ hc₂ hlt := by
    simp only
    split_ifs with h₁ h₂
    · have := (Prod.ext_iff.mp h₁).2; have := (Prod.ext_iff.mp h₂).2; omega
    · have hi₁ := (Prod.ext_iff.mp h₁).1; have hj₁ := (Prod.ext_iff.mp h₁).2
      rcases mem_twoRowYD hab |>.mp hc₂ with ⟨_, hj₂⟩ | ⟨hi₂, _⟩ <;> omega
    · have hi := (Prod.ext_iff.mp h₂).1; have hj₂ := (Prod.ext_iff.mp h₂).2
      have hcμ₁ : (i, j₁) ∈ twoRowYD (a - 1) b hab₁ :=
        mem_twoRowYD hab₁ |>.mpr (Or.inl ⟨hi, by omega⟩)
      have := (T₁.entry_range _ hcμ₁).2
      rw [twoRowYD_card (a - 1) b hab₁] at this; omega
    · have hcμ₁ : (i, j₁) ∈ twoRowYD (a - 1) b hab₁ := by
        rcases mem_twoRowYD hab |>.mp hc₁ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inl ⟨hi,
            by have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inr ⟨hi, hj⟩)
      have hcμ₂ : (i, j₂) ∈ twoRowYD (a - 1) b hab₁ := by
        rcases mem_twoRowYD hab |>.mp hc₂ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inl ⟨hi,
            by have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inr ⟨hi, hj⟩)
      exact T₁.row_strict i j₁ j₂ hcμ₁ hcμ₂ hlt
  col_strict i₁ i₂ j hc₁ hc₂ hlt := by
    simp only
    split_ifs with h₁ h₂
    · exact absurd hlt (by
        have := (Prod.ext_iff.mp h₁).1; have := (Prod.ext_iff.mp h₂).1; omega)
    · have hja := (Prod.ext_iff.mp h₁).2
      rcases mem_twoRowYD hab |>.mp hc₂ with ⟨hi₂, hj₂⟩ | ⟨_, hj₂⟩
      · have := (Prod.ext_iff.mp h₁).1; omega
      · rw [hja] at hj₂; omega
    · exact absurd hlt (by have := (Prod.ext_iff.mp h₂).1; omega)
    · have hcμ₁ : (i₁, j) ∈ twoRowYD (a - 1) b hab₁ := by
        rcases mem_twoRowYD hab |>.mp hc₁ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inl ⟨hi,
            by have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inr ⟨hi, hj⟩)
      have hcμ₂ : (i₂, j) ∈ twoRowYD (a - 1) b hab₁ := by
        rcases mem_twoRowYD hab |>.mp hc₂ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inl ⟨hi,
            by have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
        · exact mem_twoRowYD hab₁ |>.mpr (Or.inr ⟨hi, hj⟩)
      exact T₁.col_strict i₁ i₂ j hcμ₁ hcμ₂ hlt

-- Extend T₂ : SYT(twoRowYD a (b-1)) to SYT(twoRowYD a b) by adding (1,b-1) ↦ a+b
private noncomputable def extendSYT1 {a b : ℕ}
    (hab : b ≤ a) (hab₂ : b - 1 ≤ a)
    (T₂ : StandardYoungTableau (twoRowYD a (b - 1) hab₂)) :
    StandardYoungTableau (twoRowYD a b hab) where
  entry c := if c = (1, b - 1) then a + b else T₂.entry c
  entry_zero c hc := by
    have hne : c ≠ (1, b - 1) := fun h =>
      hc (h ▸ mem_twoRowYD hab |>.mpr (Or.inr ⟨rfl, by omega⟩))
    rw [if_neg hne]
    exact T₂.entry_zero c (fun hc₂ => hc (mem_of_twoRowYD_pred2 hab hab₂ c hc₂))
  entry_range c hc := by
    by_cases hce : c = (1, b - 1)
    · simp only [hce, ↓reduceIte]
      have hb1 : b - 1 < b := by
        rcases mem_twoRowYD hab |>.mp (hce ▸ hc) with ⟨h, _⟩ | ⟨_, h⟩
        · exact absurd h (by norm_num); · exact h
      rw [twoRowYD_card a b hab]; exact ⟨by omega, le_refl _⟩
    · rw [if_neg hce]
      have hcμ₂ : c ∈ twoRowYD a (b - 1) hab₂ := by
        rcases mem_twoRowYD hab |>.mp hc with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inl ⟨hi, hj⟩)
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inr ⟨hi,
            by have := fun heq => hce (Prod.ext hi heq); omega⟩)
      have hr := T₂.entry_range c hcμ₂
      rw [twoRowYD_card a (b - 1) hab₂] at hr
      rw [twoRowYD_card a b hab]; exact ⟨hr.1, by omega⟩
  entry_injOn c₁ c₂ hc₁ hc₂ h := by
    simp only at h
    by_cases h₁ : c₁ = (1, b - 1) <;> by_cases h₂ : c₂ = (1, b - 1)
    · rw [h₁, h₂]
    · simp only [h₁, h₂, ↓reduceIte, if_false] at h
      have hcμ₂ : c₂ ∈ twoRowYD a (b - 1) hab₂ := by
        rcases mem_twoRowYD hab |>.mp hc₂ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inl ⟨hi, hj⟩)
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inr ⟨hi,
            by have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
      have := (T₂.entry_range c₂ hcμ₂).2
      rw [twoRowYD_card a (b - 1) hab₂] at this; omega
    · simp only [h₁, h₂, ↓reduceIte, if_true, if_false] at h
      have hcμ₁ : c₁ ∈ twoRowYD a (b - 1) hab₂ := by
        rcases mem_twoRowYD hab |>.mp hc₁ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inl ⟨hi, hj⟩)
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inr ⟨hi,
            by have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
      have := (T₂.entry_range c₁ hcμ₁).2
      rw [twoRowYD_card a (b - 1) hab₂] at this; omega
    · simp only [h₁, h₂, ↓reduceIte] at h
      have hcμ₁ : c₁ ∈ twoRowYD a (b - 1) hab₂ := by
        rcases mem_twoRowYD hab |>.mp hc₁ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inl ⟨hi, hj⟩)
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inr ⟨hi,
            by have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
      have hcμ₂ : c₂ ∈ twoRowYD a (b - 1) hab₂ := by
        rcases mem_twoRowYD hab |>.mp hc₂ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inl ⟨hi, hj⟩)
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inr ⟨hi,
            by have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
      exact T₂.entry_injOn c₁ c₂ hcμ₁ hcμ₂ h
  row_strict i j₁ j₂ hc₁ hc₂ hlt := by
    simp only
    split_ifs with h₁ h₂
    · have := (Prod.ext_iff.mp h₁).2; have := (Prod.ext_iff.mp h₂).2; omega
    · have hi₁ := (Prod.ext_iff.mp h₁).1; have hj₁ := (Prod.ext_iff.mp h₁).2
      rcases mem_twoRowYD hab |>.mp hc₂ with ⟨_, hj₂⟩ | ⟨hi₂, hj₂⟩
      · omega
      · have := fun heq => h₂ (Prod.ext hi₁ heq); omega
    · have hi := (Prod.ext_iff.mp h₂).1; have hj₂ := (Prod.ext_iff.mp h₂).2
      have hcμ₁ : (i, j₁) ∈ twoRowYD a (b - 1) hab₂ :=
        mem_twoRowYD hab₂ |>.mpr (Or.inr ⟨hi, by omega⟩)
      have := (T₂.entry_range _ hcμ₁).2
      rw [twoRowYD_card a (b - 1) hab₂] at this; omega
    · have hcμ₁ : (i, j₁) ∈ twoRowYD a (b - 1) hab₂ := by
        rcases mem_twoRowYD hab |>.mp hc₁ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inl ⟨hi, hj⟩)
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inr ⟨hi,
            by have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
      have hcμ₂ : (i, j₂) ∈ twoRowYD a (b - 1) hab₂ := by
        rcases mem_twoRowYD hab |>.mp hc₂ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inl ⟨hi, hj⟩)
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inr ⟨hi,
            by have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
      exact T₂.row_strict i j₁ j₂ hcμ₁ hcμ₂ hlt
  col_strict i₁ i₂ j hc₁ hc₂ hlt := by
    simp only
    split_ifs with h₁ h₂
    · exact absurd hlt (by
        have := (Prod.ext_iff.mp h₁).1; have := (Prod.ext_iff.mp h₂).1; omega)
    · rcases mem_twoRowYD hab |>.mp hc₂ with ⟨_, hj₂⟩ | ⟨hi₂, hj₂⟩
      · have := (Prod.ext_iff.mp h₁).1; omega
      · have hi₁ := (Prod.ext_iff.mp h₁).1
        -- i₂ > i₁ = 1, but rows only go to 1: impossible
        omega
    · exact absurd hlt (by have := (Prod.ext_iff.mp h₂).1; omega)
    · have hcμ₁ : (i₁, j) ∈ twoRowYD a (b - 1) hab₂ := by
        rcases mem_twoRowYD hab |>.mp hc₁ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inl ⟨hi, hj⟩)
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inr ⟨hi,
            by have := fun heq => h₁ (Prod.ext hi heq); omega⟩)
      have hcμ₂ : (i₂, j) ∈ twoRowYD a (b - 1) hab₂ := by
        rcases mem_twoRowYD hab |>.mp hc₂ with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inl ⟨hi, hj⟩)
        · exact mem_twoRowYD hab₂ |>.mpr (Or.inr ⟨hi,
            by have := fun heq => h₂ (Prod.ext hi heq); omega⟩)
      exact T₂.col_strict i₁ i₂ j hcμ₁ hcμ₂ hlt

/-- Corner-cell step: for 0 < b < a,
    card(SYT([a,b])) = card(SYT([a-1,b])) + card(SYT([a,b-1])).
    The max entry a+b is at exactly one corner: (0,a-1) or (1,b-1).
    Removing it gives an equiv between SYT([a,b]) and the disjoint union. -/
private lemma card_SYT_twoRowYD_step (a b : ℕ) (ha : b < a) (hb : 0 < b) :
    Fintype.card (StandardYoungTableau (twoRowYD a b (Nat.le_of_lt ha))) =
    Fintype.card (StandardYoungTableau (twoRowYD (a - 1) b (by omega))) +
    Fintype.card (StandardYoungTableau (twoRowYD a (b - 1) (by omega))) := by
  have hab : b ≤ a := Nat.le_of_lt ha
  have hab₁ : b ≤ a - 1 := by omega
  have hab₂ : b - 1 ≤ a := by omega
  -- Max entry a+b is at corner (0,a-1) or (1,b-1)
  have hcard : (twoRowYD a b hab).card = a + b := twoRowYD_card a b hab
  have max_at_corner : ∀ T : StandardYoungTableau (twoRowYD a b hab),
      T.entry (0, a - 1) = a + b ∨ T.entry (1, b - 1) = a + b := by
    intro T
    -- T.entry is injective on cells with range ⊆ {1,...,a+b}, so surjective
    have hcells_card : (twoRowYD a b hab).cells.card = a + b := by
      unfold YoungDiagram.card at hcard; exact hcard
    have himage_card : ((twoRowYD a b hab).cells.image T.entry).card = a + b := by
      rw [Finset.card_image_of_injOn (fun c₁ hc₁ c₂ hc₂ h =>
        T.entry_injOn c₁ c₂ (YoungDiagram.mem_cells.mp hc₁)
          (YoungDiagram.mem_cells.mp hc₂) h), hcells_card]
    have himage_sub : (twoRowYD a b hab).cells.image T.entry ⊆ Finset.Icc 1 (a + b) := by
      intro k hk
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hk
      have := T.entry_range c (YoungDiagram.mem_cells.mp hc)
      rw [hcard] at this; exact Finset.mem_Icc.mpr this
    have hIcc_card : (Finset.Icc 1 (a + b)).card = a + b := by simp [Finset.card_Icc]
    have himage_eq : (twoRowYD a b hab).cells.image T.entry = Finset.Icc 1 (a + b) :=
      Finset.eq_of_subset_of_card_le himage_sub (by rw [hIcc_card, himage_card])
    have hab_in : a + b ∈ (twoRowYD a b hab).cells.image T.entry := by
      rw [himage_eq]; simp [Finset.mem_Icc]
    obtain ⟨c, hc_cell, hc_eq⟩ := Finset.mem_image.mp hab_in
    have hc_mem := YoungDiagram.mem_cells.mp hc_cell
    -- c is a corner: (c.1, c.2+1) ∉ μ
    have hright : (c.1, c.2 + 1) ∉ twoRowYD a b hab := by
      intro h
      have hlt := T.row_strict c.1 c.2 (c.2 + 1) hc_mem h (Nat.lt_succ_self _)
      rw [hc_eq, hcard] at hlt
      exact absurd hlt (Nat.lt_irrefl _)
    -- Determine which corner c is
    rcases mem_twoRowYD hab |>.mp hc_mem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · left
      have hja : c.2 = a - 1 := by
        have : ¬(0 = 0 ∧ c.2 + 1 < a) := fun ⟨_, h⟩ =>
          hright (mem_twoRowYD hab |>.mpr (Or.inl ⟨hi, h⟩))
        omega
      have : c = (0, a - 1) := Prod.ext hi hja
      rw [← this]; exact hc_eq
    · right
      have hja : c.2 = b - 1 := by
        have : ¬(1 = 1 ∧ c.2 + 1 < b) := fun ⟨_, h⟩ =>
          hright (mem_twoRowYD hab |>.mpr (Or.inr ⟨hi, h⟩))
        omega
      have : c = (1, b - 1) := Prod.ext hi hja
      rw [← this]; exact hc_eq
  -- Build the bijection SYT(a,b) ≃ SYT(a-1,b) ⊕ SYT(a,b-1)
  rw [← Fintype.card_sum]
  apply Fintype.card_congr
  exact {
    toFun := fun T =>
      if hT : T.entry (0, a - 1) = a + b then
        Sum.inl (restrictSYT0 hab hab₁ T hT)
      else
        Sum.inr (restrictSYT1 hab hab₂ T ((max_at_corner T).resolve_left hT))
    invFun := fun x => match x with
      | Sum.inl T₁ => extendSYT0 hab hab₁ T₁
      | Sum.inr T₂ => extendSYT1 hab hab₂ T₂
    left_inv := fun T => by
      apply StandardYoungTableau.ext; intro c
      by_cases hT : T.entry (0, a - 1) = a + b
      · rw [dif_pos hT]
        simp only [extendSYT0, restrictSYT0]
        split_ifs with hce hcμ
        · -- c = (0, a-1)
          exact hT.symm
        · -- c ∈ μ₁, c ≠ (0, a-1)
          rfl
        · -- c ∉ μ₁, c ≠ (0, a-1)
          apply T.entry_zero; intro hcμ_big
          rcases mem_twoRowYD hab |>.mp hcμ_big with ⟨hi, hj⟩ | ⟨hi, hj⟩
          · exact hcμ (mem_twoRowYD hab₁ |>.mpr (Or.inl ⟨hi,
              by have := fun heq => hce (Prod.ext hi heq); omega⟩))
          · exact hcμ (mem_twoRowYD hab₁ |>.mpr (Or.inr ⟨hi, hj⟩))
      · rw [dif_neg hT]
        simp only [extendSYT1, restrictSYT1]
        split_ifs with hce hcμ
        · -- c = (1, b-1)
          exact ((max_at_corner T).resolve_left hT).symm
        · -- c ∈ μ₂, c ≠ (1, b-1)
          rfl
        · -- c ∉ μ₂, c ≠ (1, b-1)
          apply T.entry_zero; intro hcμ_big
          rcases mem_twoRowYD hab |>.mp hcμ_big with ⟨hi, hj⟩ | ⟨hi, hj⟩
          · exact hcμ (mem_twoRowYD hab₂ |>.mpr (Or.inl ⟨hi, hj⟩))
          · exact hcμ (mem_twoRowYD hab₂ |>.mpr (Or.inr ⟨hi,
              by have := fun heq => hce (Prod.ext hi heq); omega⟩))
    right_inv := fun x => by
      match x with
      | Sum.inl T₁ =>
        -- Show toFun (extendSYT0 T₁) = Sum.inl T₁
        -- extendSYT0 T₁ has entry (0, a-1) = a+b, so dif_pos applies
        have h0a1 : (extendSYT0 hab hab₁ T₁).entry (0, a - 1) = a + b := by
          simp [extendSYT0]
        rw [dif_pos h0a1]
        congr 1
        apply StandardYoungTableau.ext; intro c
        simp only [restrictSYT0, extendSYT0]
        split_ifs with hcμ hce
        · -- c ∈ μ₁: entry = if c=(0,a-1) then a+b else T₁.entry c
          -- c ∈ μ₁ implies c ≠ (0,a-1), so entry = T₁.entry c
          simp only [if_neg (by
            intro h; exact absurd (h ▸ hcμ) (by simp [mem_twoRowYD hab₁]))]
        · -- c = (0,a-1): entry = a+b, but (0,a-1) ∉ μ₁: branch is else = 0
          simp only [if_pos rfl]
          -- hcμ : c ∉ μ₁, hce : c = (0, a-1)
          -- We want T₁.entry_zero applied to prove T₁.entry c = 0... wait,
          -- the "if c ∈ μ₁ then T.entry c else 0" branch: c ∉ μ₁, so = 0.
          -- But wait: the split_ifs split on c ∈ μ₁ first, then something else?
          -- The outer if is "if c ∈ μ₁ then T.entry c else 0" (from restrictSYT0)
          -- and the inner if is "if c = (0,a-1) then a+b else T₁.entry c" (from extendSYT0)
          -- Case hcμ (c ∉ μ₁) and hce (c = (0,a-1)):
          -- restrictSYT0 of extendSYT0 at c: (if c ∈ μ₁ then (extendSYT0).entry c else 0) = 0
          -- We need 0 = T₁.entry c. By T₁.entry_zero c (hcμ) — no wait, the split_ifs is wrong here
          -- Let me think: the goal here is:
          -- (if c ∈ μ₁ then (if c = (0,a-1) then a+b else T₁.entry c) else 0) = T₁.entry c
          -- c ∉ μ₁ (hcμ), c = (0,a-1) (hce): LHS = 0. RHS = T₁.entry (0,a-1).
          -- T₁.entry (0,a-1) = 0 since (0,a-1) ∉ μ₁. ✓
          exact (T₁.entry_zero c hcμ).symm
        · -- c ∉ μ₁, c ≠ (0, a-1):
          -- LHS = 0, RHS = T₁.entry c = 0 (by T₁.entry_zero)
          exact (T₁.entry_zero c hcμ).symm
      | Sum.inr T₂ =>
        have h1b1 : (extendSYT1 hab hab₂ T₂).entry (1, b - 1) = a + b := by
          simp [extendSYT1]
        have h0a1 : (extendSYT1 hab hab₂ T₂).entry (0, a - 1) ≠ a + b := by
          simp only [extendSYT1]
          rw [if_neg (by
            intro h; simp [Prod.ext_iff] at h)]
          have hcμ₂ : (0, a - 1) ∈ twoRowYD a (b - 1) hab₂ :=
            mem_twoRowYD hab₂ |>.mpr (Or.inl ⟨rfl, by omega⟩)
          have := (T₂.entry_range _ hcμ₂).2
          rw [twoRowYD_card a (b - 1) hab₂]; omega
        rw [dif_neg h0a1]
        have : (max_at_corner (extendSYT1 hab hab₂ T₂)).resolve_left h0a1 = h1b1 := by
          rfl
        congr 1
        apply StandardYoungTableau.ext; intro c
        simp only [restrictSYT1, extendSYT1]
        split_ifs with hcμ hce
        · -- c ∈ μ₂: entry = if c=(1,b-1) then a+b else T₂.entry c
          simp only [if_neg (by
            intro h; exact absurd (h ▸ hcμ) (by simp [mem_twoRowYD hab₂]))]
        · exact (T₂.entry_zero c hcμ).symm
        · exact (T₂.entry_zero c hcμ).symm
  }

/-- **Card of SYT of general 2-row shape equals ballotSeqCount.**
    card(SYT([a,b])) = ballotSeqCount(a+1, b) for all a ≥ b ≥ 0.
    Proof by strong induction on a+b:
    - b=0: shape=[a], unique SYT, ballotSeqCount(a+1,0)=1
    - b=a: twoRowYD a a = twoRectYD a, so card = Cn a = ballotSeqCount(a+1,a)
    - b<a, b>0: corner recursion + arithmetic Pascal step -/
theorem card_SYT_twoRowYD (a b : ℕ) (hab : b ≤ a) :
    Fintype.card (StandardYoungTableau (twoRowYD a b hab)) =
    LatticePathLGV.ballotSeqCount (a + 1) b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- Base: b = 0.  twoRowYD a 0 = oneRowYD a (unique SYT), ballotSeqCount (a+1) 0 = 1
    rw [twoRowYD_zero_eq_oneRowYD a, ballotSeqCount_zero_right]
    exact Fintype.card_eq_one_iff.mpr ⟨oneRowSYT a, oneRowSYT_unique a⟩
  · rcases Nat.lt_or_eq_of_le hab with ha | rfl
    · -- Step: 0 < b < a.  Corner recursion + Pascal + induction
      rw [card_SYT_twoRowYD_step a b ha hb,
          card_SYT_twoRowYD (a - 1) b (by omega),
          card_SYT_twoRowYD a (b - 1) (by omega),
          ← ballotSeqCount_rec a b ha hb]
    · -- Square: b = a.  twoRowYD a a = twoRectYD a; card = Cn a = ballotSeqCount (a+1) a
      rw [twoRowYD_sq_eq_twoRectYD a, card_SYT_twoRectYD]
      exact catalan_eq_ballot a
termination_by a + b
decreasing_by all_goals omega

/-- Algebraic identity: ballotSeqCount (a+1) b × hookProd([a,b]) = (a+b)!
    This is the numerical core of the hook-length formula for 2-row shapes. -/
private lemma two_row_hook_identity (a b : ℕ) (hab : b ≤ a) :
    LatticePathLGV.ballotSeqCount (a + 1) b *
    ((a + 1).descFactorial b * (a - b).factorial * b.factorial) =
    (a + b).factorial := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- b = 0: ballotSeqCount (a+1) 0 = 1, descFactorial b = 1, (a-0)! = a!, 0! = 1
    simp [LatticePathLGV.ballotSeqCount]
  -- b ≥ 1, a ≥ b
  -- Sub-lemma: (a+1).descFactorial b * (a-b)! * (a+1-b) = (a+1)!
  have hkey : (a + 1).descFactorial b * (a - b).factorial * (a + 1 - b) = (a + 1).factorial := by
    have h1 : (a + 1 - b).factorial * (a + 1).descFactorial b = (a + 1).factorial :=
      Nat.factorial_mul_descFactorial (by omega)
    have h2 : (a + 1 - b).factorial = (a + 1 - b) * (a - b).factorial := by
      rw [show a + 1 - b = (a - b) + 1 from by omega, Nat.factorial_succ]
    calc (a + 1).descFactorial b * (a - b).factorial * (a + 1 - b)
        = (a + 1 - b) * (a - b).factorial * (a + 1).descFactorial b := by ring
      _ = (a + 1 - b).factorial * (a + 1).descFactorial b := by rw [← h2]
      _ = (a + 1).factorial := h1
  -- ballot_formula: ballotSeqCount (a+1) b * (a+b+1) = (a+1-b) * C(a+b+1, a+1)
  have hbf : LatticePathLGV.ballotSeqCount (a + 1) b * (a + b + 1) =
      (a + 1 - b) * Nat.choose (a + b + 1) (a + 1) :=
    LatticePathLGV.ballot_formula (a + 1) b (by omega) (by omega) hb
  -- C(a+b+1, a+1) * (a+1)! * b! = (a+b+1)!
  have hcf : Nat.choose (a + b + 1) (a + 1) * (a + 1).factorial * b.factorial =
      (a + b + 1).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show a + 1 ≤ a + b + 1 by omega)
    rw [show a + b + 1 - (a + 1) = b from by omega] at this
    linarith
  -- (a+b+1)! = (a+b+1) * (a+b)!
  have hfact : (a + b + 1).factorial = (a + b + 1) * (a + b).factorial :=
    Nat.factorial_succ _
  -- Combine: S*D*F*G * ((a+1-b) * (a+b+1)) = (a+b)! * ((a+1-b) * (a+b+1))
  have hprod :
      LatticePathLGV.ballotSeqCount (a + 1) b *
      ((a + 1).descFactorial b * (a - b).factorial * b.factorial) *
      ((a + 1 - b) * (a + b + 1)) =
      (a + b).factorial * ((a + 1 - b) * (a + b + 1)) := by
    calc LatticePathLGV.ballotSeqCount (a + 1) b *
          ((a + 1).descFactorial b * (a - b).factorial * b.factorial) *
          ((a + 1 - b) * (a + b + 1))
        = LatticePathLGV.ballotSeqCount (a + 1) b * (a + b + 1) *
          ((a + 1).descFactorial b * (a - b).factorial * (a + 1 - b)) *
          b.factorial := by ring
      _ = (a + 1 - b) * Nat.choose (a + b + 1) (a + 1) *
          (a + 1).factorial * b.factorial := by rw [hbf, hkey]
      _ = (a + 1 - b) * (Nat.choose (a + b + 1) (a + 1) * (a + 1).factorial *
          b.factorial) := by ring
      _ = (a + 1 - b) * (a + b + 1).factorial := by rw [hcf]
      _ = (a + 1 - b) * ((a + b + 1) * (a + b).factorial) := by rw [hfact]
      _ = (a + b).factorial * ((a + 1 - b) * (a + b + 1)) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by omega) (by omega)) hprod

/-- **Hook-length formula for general 2-row Young diagrams.**
    For a ≥ b ≥ 0: card(SYT([a,b])) × hookProd([a,b]) = (a+b)!
    Generalizes hook_length_formula_two_rect (a=b=m case).
    [card_SYT_twoRowYD is proved by WF induction in this file] -/
theorem hook_length_formula_two_row_gen (a b : ℕ) (hab : b ≤ a) :
    Fintype.card (StandardYoungTableau (twoRowYD a b hab)) *
    hookProd (twoRowYD a b hab) =
    (twoRowYD a b hab).card.factorial := by
  rw [twoRowYD_card a b hab, hookProd_twoRowYD a b hab, card_SYT_twoRowYD a b hab]
  exact two_row_hook_identity a b hab

-- Numerical verification
example : LatticePathLGV.ballotSeqCount 3 1 * (2 * 1 * 1) = 2 := by native_decide  -- [2,1]
example : LatticePathLGV.ballotSeqCount 4 1 * (6 * 1 * 1) = 6 := by native_decide  -- [3,1]
example : LatticePathLGV.ballotSeqCount 4 2 * (3 * 1 * 2) = 24 := by native_decide -- [3,2]
example : LatticePathLGV.ballotSeqCount 5 3 * (4 * 1 * 6) = 720 := by native_decide -- [4,3]

-- ============================================================
-- PART XII: Hook-Length Formula for Arbitrary 2-Row Diagrams
-- ============================================================

/-
  Any YoungDiagram μ with rowLen 2 = 0 (at most 2 rows) equals twoRowYD a b
  where a = μ.rowLen 0 and b = μ.rowLen 1.
  Combined with hook_length_formula_two_row_gen, this gives the HLF for ALL 2-row shapes.
  This covers: ⊥ (empty), 1×n (1-row), and all 2-row shapes [a,b] with a ≥ b.
-/

/-- Any YoungDiagram with at most 2 rows equals twoRowYD (rowLen 0) (rowLen 1).
    Key idea: (i,j) ∈ μ ↔ j < rowLen i; for i ≥ 2, rowLen i ≤ rowLen 2 = 0,
    so no cells with row index ≥ 2 exist. -/
private lemma eq_twoRowYD_of_atMostTwoRows (μ : YoungDiagram) (h2 : μ.rowLen 2 = 0) :
    ∃ (hab : μ.rowLen 1 ≤ μ.rowLen 0), μ = twoRowYD (μ.rowLen 0) (μ.rowLen 1) hab := by
  have hab : μ.rowLen 1 ≤ μ.rowLen 0 := μ.rowLen_anti 0 1 (by omega)
  refine ⟨hab, ?_⟩
  apply YoungDiagram.ext
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, mem_twoRowYD hab]
  constructor
  · intro hlt
    rcases i with _ | _ | i
    · exact Or.inl ⟨rfl, hlt⟩
    · exact Or.inr ⟨rfl, hlt⟩
    · -- i+2 ≥ 2: rowLen (i+2) ≤ rowLen 2 = 0, so j < 0, contradiction
      have hzero : μ.rowLen (i + 2) = 0 :=
        Nat.le_zero.mp (calc μ.rowLen (i + 2)
              ≤ μ.rowLen 2 := μ.rowLen_anti 2 (i + 2) (by omega)
            _ = 0 := h2)
      omega
  · rintro (⟨rfl, hlt⟩ | ⟨rfl, hlt⟩) <;> exact hlt

/-- **Hook-length formula for all YoungDiagrams with at most 2 rows.**
    Any μ with rowLen 2 = 0 is characterized as twoRowYD (rowLen 0) (rowLen 1),
    so hook_length_formula_two_row_gen directly applies.
    This subsumes: ⊥ (empty), 1-row, 2-row-rectangle, and general 2-row [a,b]. -/
theorem hook_length_formula_atMostTwoRows (μ : YoungDiagram) (h2 : μ.rowLen 2 = 0) :
    Fintype.card (StandardYoungTableau μ) * hookProd μ = μ.card.factorial := by
  obtain ⟨hab, hμ⟩ := eq_twoRowYD_of_atMostTwoRows μ h2
  rw [hμ]
  exact hook_length_formula_two_row_gen (μ.rowLen 0) (μ.rowLen 1) hab

-- ============================================================
-- PART XIII: General Corner Recursion for SYT Counts
-- ============================================================

/-
  We prove the general corner recursion:
    card(SYT(μ)) = Σ_{c ∈ corners(μ)} card(SYT(μ\c))  (for non-empty μ)
  where corners(μ) are cells c with arm(c)=0 and leg(c)=0 (hookLength = 1).
  The bijection T ↦ (max-entry corner, restricted SYT) is the key tool.
-/

/-- A corner of μ: a cell c ∈ μ with no cell immediately to its right or below.
    Equivalently arm(c) = 0 and leg(c) = 0, so hookLength(μ,c) = 1. -/
private def isCorner (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∈ μ ∧ (c.1, c.2 + 1) ∉ μ ∧ (c.1 + 1, c.2) ∉ μ

/-- Finset of corner cells of μ. -/
private def corners (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  μ.cells.filter (fun c => (c.1, c.2 + 1) ∉ μ ∧ (c.1 + 1, c.2) ∉ μ)

private lemma mem_corners {μ : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ corners μ ↔ isCorner μ c := by
  simp only [corners, Finset.mem_filter, YoungDiagram.mem_cells, isCorner]

/-- Removing a corner cell preserves the lower-set property. -/
private noncomputable def removeCorner (μ : YoungDiagram) (c : ℕ × ℕ)
    (hc : isCorner μ c) : YoungDiagram where
  cells := μ.cells.erase c
  isLowerSet := by
    intro a b hab hb
    rw [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff] at hb ⊢
    obtain ⟨hb_mem, hb_ne⟩ := hb
    refine ⟨μ.isLowerSet hab hb_mem, ?_⟩
    intro ha_eq
    subst ha_eq
    obtain ⟨_, h_right, h_below⟩ := hc
    have h1 : a.1 ≤ b.1 ∧ a.2 ≤ b.2 := Prod.mk_le_mk.mp hab
    rcases Nat.lt_or_eq_of_le h1.1 with h1' | rfl
    · exact h_below (μ.isLowerSet (Prod.mk_le_mk.mpr ⟨by omega, h1.2⟩) hb_mem)
    · rcases Nat.lt_or_eq_of_le h1.2 with h2' | rfl
      · exact h_right (μ.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl _, by omega⟩) hb_mem)
      · exact hb_ne rfl

/-- Membership in removeCorner: all cells except c. -/
private lemma mem_removeCorner {μ : YoungDiagram} {c x : ℕ × ℕ} (hc : isCorner μ c) :
    x ∈ removeCorner μ c hc ↔ x ∈ μ ∧ x ≠ c := by
  simp only [removeCorner, YoungDiagram.mem_mk, Finset.mem_erase, YoungDiagram.mem_cells]
  tauto

/-- Cardinality of removeCorner is μ.card - 1. -/
private lemma removeCorner_card {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c) :
    (removeCorner μ c hc).card = μ.card - 1 := by
  simp [YoungDiagram.card, removeCorner,
    Finset.card_erase_of_mem (YoungDiagram.mem_cells.mpr hc.1)]

/-- removeCorner doesn't depend on which proof of isCorner we use.
    (The cells are just μ.cells.erase c, independent of the proof.) -/
private lemma removeCorner_proof_irrel (μ : YoungDiagram) (c : ℕ × ℕ)
    (hc₁ hc₂ : isCorner μ c) :
    removeCorner μ c hc₁ = removeCorner μ c hc₂ := by
  apply YoungDiagram.ext
  simp [removeCorner]

/-- For any SYT, its entries surject onto {1,...,μ.card}. -/
private lemma syt_entry_image {μ : YoungDiagram} (T : StandardYoungTableau μ)
    (hn : 0 < μ.card) :
    μ.cells.image T.entry = Finset.Icc 1 μ.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr (T.entry_range c (YoungDiagram.mem_cells.mp hc))
  · rw [Finset.card_Icc, Nat.add_sub_cancel,
      Finset.card_image_of_injOn (fun c₁ hc₁ c₂ hc₂ h =>
        T.entry_injOn c₁ c₂ (YoungDiagram.mem_cells.mp hc₁)
          (YoungDiagram.mem_cells.mp hc₂) h)]

/-- The unique cell of μ where T.entry achieves μ.card (the maximum). -/
private noncomputable def maxEntryCell {μ : YoungDiagram}
    (T : StandardYoungTableau μ) (hn : 0 < μ.card) : ℕ × ℕ :=
  Classical.choose (Finset.mem_image.mp
    (show μ.card ∈ μ.cells.image T.entry by
      rw [syt_entry_image T hn]; simp [Finset.mem_Icc, hn]))

private lemma maxEntryCell_spec {μ : YoungDiagram}
    (T : StandardYoungTableau μ) (hn : 0 < μ.card) :
    maxEntryCell T hn ∈ μ.cells ∧ T.entry (maxEntryCell T hn) = μ.card :=
  Classical.choose_spec (Finset.mem_image.mp
    (show μ.card ∈ μ.cells.image T.entry by
      rw [syt_entry_image T hn]; simp [Finset.mem_Icc, hn]))

private lemma maxEntryCell_mem {μ : YoungDiagram}
    (T : StandardYoungTableau μ) (hn : 0 < μ.card) :
    maxEntryCell T hn ∈ μ :=
  YoungDiagram.mem_cells.mp (maxEntryCell_spec T hn).1

private lemma maxEntryCell_entry {μ : YoungDiagram}
    (T : StandardYoungTableau μ) (hn : 0 < μ.card) :
    T.entry (maxEntryCell T hn) = μ.card :=
  (maxEntryCell_spec T hn).2

/-- The cell achieving the maximum entry is a corner (no larger entries can exist to right/below). -/
private lemma maxEntryCell_isCorner {μ : YoungDiagram}
    (T : StandardYoungTableau μ) (hn : 0 < μ.card) :
    isCorner μ (maxEntryCell T hn) := by
  set c := maxEntryCell T hn
  refine ⟨maxEntryCell_mem T hn, ?_, ?_⟩
  · intro h
    have := T.row_strict c.1 c.2 (c.2 + 1) (maxEntryCell_mem T hn) h (Nat.lt_succ_self _)
    rw [maxEntryCell_entry T hn] at this; exact Nat.lt_irrefl _ this
  · intro h
    have := T.col_strict c.1 (c.1 + 1) c.2 (maxEntryCell_mem T hn) h (Nat.lt_succ_self _)
    rw [maxEntryCell_entry T hn] at this; exact Nat.lt_irrefl _ this

private lemma maxEntryCell_in_corners {μ : YoungDiagram}
    (T : StandardYoungTableau μ) (hn : 0 < μ.card) :
    maxEntryCell T hn ∈ corners μ :=
  mem_corners.mpr (maxEntryCell_isCorner T hn)

/-- maxEntryCell is unique: if T.entry x = μ.card and x ∈ μ, then x = maxEntryCell T hn. -/
private lemma maxEntryCell_unique {μ : YoungDiagram}
    (T : StandardYoungTableau μ) (hn : 0 < μ.card)
    (x : ℕ × ℕ) (hx : x ∈ μ) (heq : T.entry x = μ.card) :
    x = maxEntryCell T hn := by
  apply T.entry_injOn x (maxEntryCell T hn) hx (maxEntryCell_mem T hn)
  rw [heq, maxEntryCell_entry T hn]

/-- Restrict a SYT to shape μ\c, given the max entry is at c. -/
private noncomputable def restrictSYT_gen {μ : YoungDiagram} (c : ℕ × ℕ)
    (hc : isCorner μ c) (T : StandardYoungTableau μ)
    (hT : T.entry c = μ.card) :
    StandardYoungTableau (removeCorner μ c hc) where
  entry x := if x ∈ removeCorner μ c hc then T.entry x else 0
  entry_zero x hx := by simp [hx]
  entry_range x hx := by
    simp only [hx, ↓reduceIte]
    obtain ⟨hxmem, hxne⟩ := (mem_removeCorner hc).mp hx
    have hne : T.entry x ≠ μ.card := by
      intro h; exact hxne (T.entry_injOn x c hxmem hc.1 (h.trans hT.symm))
    exact ⟨(T.entry_range x hxmem).1,
      by rw [removeCorner_card hc]; have := (T.entry_range x hxmem).2; omega⟩
  entry_injOn x₁ x₂ hx₁ hx₂ h := by
    simp only [hx₁, hx₂, ↓reduceIte] at h
    exact T.entry_injOn x₁ x₂ ((mem_removeCorner hc).mp hx₁).1
      ((mem_removeCorner hc).mp hx₂).1 h
  row_strict i j₁ j₂ hx₁ hx₂ hlt := by
    simp only [hx₁, hx₂, ↓reduceIte]
    exact T.row_strict i j₁ j₂ ((mem_removeCorner hc).mp hx₁).1
      ((mem_removeCorner hc).mp hx₂).1 hlt
  col_strict i₁ i₂ j hx₁ hx₂ hlt := by
    simp only [hx₁, hx₂, ↓reduceIte]
    exact T.col_strict i₁ i₂ j ((mem_removeCorner hc).mp hx₁).1
      ((mem_removeCorner hc).mp hx₂).1 hlt

/-- Extend a SYT of shape μ\c to shape μ by placing μ.card at the corner c. -/
private noncomputable def extendSYT_gen {μ : YoungDiagram} (c : ℕ × ℕ)
    (hc : isCorner μ c) (T₁ : StandardYoungTableau (removeCorner μ c hc)) :
    StandardYoungTableau μ where
  entry x := if x = c then μ.card else T₁.entry x
  entry_zero x hx := by
    have hne : x ≠ c := fun h => hx (h ▸ hc.1)
    rw [if_neg hne]
    exact T₁.entry_zero x (fun hm => (mem_removeCorner hc).mp hm |>.1 |> hx)
  entry_range x hx := by
    by_cases hxc : x = c
    · simp [hxc, hc.1]
    · rw [if_neg hxc]
      have hxrc : x ∈ removeCorner μ c hc := (mem_removeCorner hc).mpr ⟨hx, hxc⟩
      exact ⟨(T₁.entry_range x hxrc).1,
        by have := (T₁.entry_range x hxrc).2; rw [removeCorner_card hc] at this; omega⟩
  entry_injOn x₁ x₂ hx₁ hx₂ heq := by
    by_cases hx₁c : x₁ = c <;> by_cases hx₂c : x₂ = c
    · exact hx₁c.trans hx₂c.symm
    · simp [hx₁c, if_neg hx₂c] at heq
      have := (T₁.entry_range x₂ ((mem_removeCorner hc).mpr ⟨hx₂, hx₂c⟩)).2
      rw [removeCorner_card hc] at this; omega
    · simp [if_neg hx₁c, hx₂c] at heq
      have := (T₁.entry_range x₁ ((mem_removeCorner hc).mpr ⟨hx₁, hx₁c⟩)).2
      rw [removeCorner_card hc] at this; omega
    · simp only [if_neg hx₁c, if_neg hx₂c] at heq
      exact T₁.entry_injOn x₁ x₂
        ((mem_removeCorner hc).mpr ⟨hx₁, hx₁c⟩)
        ((mem_removeCorner hc).mpr ⟨hx₂, hx₂c⟩) heq
  row_strict i j₁ j₂ hx₁ hx₂ hlt := by
    by_cases hx₁c : (i, j₁) = c
    · exfalso  -- arm(c) = 0: no cell to right
      exact hc.2.1 (μ.isLowerSet
        (by simp only [← hx₁c]; exact Prod.mk_le_mk.mpr ⟨le_refl _, by omega⟩) hx₂)
    · by_cases hx₂c : (i, j₂) = c
      · rw [if_neg hx₁c, hx₂c, if_pos rfl]
        have := (T₁.entry_range _ ((mem_removeCorner hc).mpr ⟨hx₁, hx₁c⟩)).2
        rw [removeCorner_card hc] at this; omega
      · rw [if_neg hx₁c, if_neg hx₂c]
        exact T₁.row_strict i j₁ j₂
          ((mem_removeCorner hc).mpr ⟨hx₁, hx₁c⟩)
          ((mem_removeCorner hc).mpr ⟨hx₂, hx₂c⟩) hlt
  col_strict i₁ i₂ j hx₁ hx₂ hlt := by
    by_cases hx₁c : (i₁, j) = c
    · exfalso  -- leg(c) = 0: no cell below
      exact hc.2.2 (μ.isLowerSet
        (by simp only [← hx₁c]; exact Prod.mk_le_mk.mpr ⟨by omega, le_refl _⟩) hx₂)
    · by_cases hx₂c : (i₂, j) = c
      · rw [if_neg hx₁c, hx₂c, if_pos rfl]
        have := (T₁.entry_range _ ((mem_removeCorner hc).mpr ⟨hx₁, hx₁c⟩)).2
        rw [removeCorner_card hc] at this; omega
      · rw [if_neg hx₁c, if_neg hx₂c]
        exact T₁.col_strict i₁ i₂ j
          ((mem_removeCorner hc).mpr ⟨hx₁, hx₁c⟩)
          ((mem_removeCorner hc).mpr ⟨hx₂, hx₂c⟩) hlt

/-- Casting a StandardYoungTableau along a YoungDiagram equality preserves the entry function. -/
private lemma cast_syt_entry {μ₁ μ₂ : YoungDiagram} (h : μ₁ = μ₂)
    (T : StandardYoungTableau μ₁) (x : ℕ × ℕ) :
    (cast (congrArg StandardYoungTableau h) T).entry x = T.entry x := by
  subst h; rfl

/-- General corner recursion: for non-empty μ,
    card(SYT(μ)) = Σ_{c ∈ corners(μ)} card(SYT(μ\c)).
    Bijection: T ↦ (max-entry corner c, T restricted to μ\c). -/
theorem card_SYT_corner_step (μ : YoungDiagram) (hn : 0 < μ.card) :
    Fintype.card (StandardYoungTableau μ) =
    ∑ c ∈ (corners μ).attach,
      Fintype.card (StandardYoungTableau (removeCorner μ c.val
        (mem_corners.mp c.prop))) := by
  rw [← Fintype.card_sigma]
  apply Fintype.card_congr
  exact {
    toFun := fun T =>
      ⟨⟨maxEntryCell T hn, maxEntryCell_in_corners T hn⟩,
        restrictSYT_gen (maxEntryCell T hn) (maxEntryCell_isCorner T hn) T
          (maxEntryCell_entry T hn)⟩
    invFun := fun ⟨⟨c, hc_corners⟩, T₁⟩ =>
      extendSYT_gen c (mem_corners.mp hc_corners) T₁
    left_inv := fun T => by
      apply StandardYoungTableau.ext; intro x
      simp only [extendSYT_gen, restrictSYT_gen]
      split_ifs with hxc hxrc
      · -- x = maxEntryCell T hn
        rw [hxc]; exact (maxEntryCell_entry T hn).symm
      · -- x ∈ removeCorner (so x ≠ maxEntryCell)
        rfl
      · -- x ∉ removeCorner and x ≠ maxEntryCell
        apply T.entry_zero
        intro hxμ
        exact hxrc ((mem_removeCorner (maxEntryCell_isCorner T hn)).mpr
          ⟨hxμ, fun h => hxc h.symm⟩)
    right_inv := fun ⟨⟨c, hc_corners⟩, T₁⟩ => by
      simp only
      have hc := mem_corners.mp hc_corners
      -- maxEntryCell of extendSYT_gen is c (unique cell with max entry)
      have hmaxeq : maxEntryCell (extendSYT_gen c hc T₁) hn = c := by
        apply maxEntryCell_unique
        · exact hc.1
        · simp [extendSYT_gen]
      have hmax_corner := maxEntryCell_isCorner (extendSYT_gen c hc T₁) hn
      -- removeCorner with maxEntryCell = removeCorner with c (same cell, proof irrelevance)
      have hyd : removeCorner μ (maxEntryCell (extendSYT_gen c hc T₁) hn) hmax_corner =
                 removeCorner μ c hc := by
        conv_lhs => rw [hmaxeq]
        exact removeCorner_proof_irrel μ c _ _
      refine Sigma.ext (Subtype.ext hmaxeq) ?_
      -- Reduce HEq to regular equality via cast along hyd
      have hEq : cast (congrArg StandardYoungTableau hyd)
          (restrictSYT_gen (maxEntryCell (extendSYT_gen c hc T₁) hn) hmax_corner
            (extendSYT_gen c hc T₁) (maxEntryCell_entry (extendSYT_gen c hc T₁) hn)) = T₁ := by
        apply StandardYoungTableau.ext; intro x
        rw [cast_syt_entry hyd]
        simp only [restrictSYT_gen, extendSYT_gen]
        by_cases hxrc : x ∈ removeCorner μ (maxEntryCell (extendSYT_gen c hc T₁) hn) hmax_corner
        · simp only [hxrc, ↓reduceIte]
          have hxne : x ≠ c := fun heq =>
            ((mem_removeCorner hmax_corner).mp hxrc).2 (heq.trans hmaxeq.symm)
          simp only [if_neg hxne]
        · simp only [hxrc, ↓reduceIte]
          symm
          apply T₁.entry_zero
          intro hxrc'
          exact hxrc ((mem_removeCorner hmax_corner).mpr
            ⟨((mem_removeCorner hc).mp hxrc').1,
             fun h => ((mem_removeCorner hc).mp hxrc').2 (h.trans hmaxeq)⟩)
      exact (cast_heq (congrArg StandardYoungTableau hyd) _).symm.trans (heq_of_eq hEq)
  }

-- ============================================================
-- PART XIV: General Hook-Length Formula via Corner Induction
-- ============================================================

/-
  We prove the general hook-length formula by well-founded recursion on μ.card,
  using the corner recursion (card_SYT_corner_step) and the hook walk identity.

  The hook walk identity (Frame-Robinson-Thrall 1954):
    Σ_{c ∈ corners(μ)} hookProd(μ) / hookProd(μ\c) = μ.card   (in ℚ)

  For each corner c = (i,j): removing c decreases hook lengths in row(c) and
  col(c) each by 1. The sum of all such ratio products equals n = μ.card.

  Proof structure (n = μ.card):
    card(SYT(μ)) * hookProd(μ)
    = (Σ_c card(SYT(μ\c))) * hookProd(μ)         [card_SYT_corner_step]
    = Σ_c [(n-1)! * hookProd(μ)/hookProd(μ\c)]   [IH: card(SYT(μ\c))*hookProd(μ\c)=(n-1)!]
    = (n-1)! * Σ_c hookProd(μ)/hookProd(μ\c)
    = (n-1)! * n = n!                             [hook_walk_identity]
-/

/-- hookProd is nonzero in ℚ. -/
private lemma hookProdQ_ne_zero (μ : YoungDiagram) : (hookProd μ : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (hookProd_pos μ).ne'

/-- Removing a corner from a ≤2-row diagram preserves the ≤2-row property.
    Any corner c is in row 0 or row 1; removing it leaves rows 2+ unchanged (still empty). -/
private lemma removeCorner_atMostTwoRows {μ : YoungDiagram} {c : ℕ × ℕ}
    (h2 : μ.rowLen 2 = 0) (hc : isCorner μ c) :
    (removeCorner μ c hc).rowLen 2 = 0 := by
  -- If rowLen 2 > 0 then (2, 0) ∈ removeCorner, so (2, 0) ∈ μ, contradicting h2
  rcases Nat.eq_zero_or_pos ((removeCorner μ c hc).rowLen 2) with h | hpos
  · exact h
  · exfalso
    have hmem : (2, 0) ∈ removeCorner μ c hc := YoungDiagram.mem_iff_lt_rowLen.mpr hpos
    obtain ⟨hmem2, _⟩ := (mem_removeCorner hc).mp hmem
    have hlt := YoungDiagram.mem_iff_lt_rowLen.mp hmem2
    omega

/-- The hook walk identity for at-most-2-row Young diagrams.
    **Non-circular proof**: hook_length_formula_atMostTwoRows was proved without this identity,
    and removing a corner of a ≤2-row shape gives another ≤2-row shape.
    Key algebraic identity:
      HP / HPc = card(SYT(μ\c)) · HP / (N-1)!   [from HLF for μ\c]
      Σ_c HP/HPc = HP/(N-1)! · Σ_c card(SYT(μ\c))
               = HP/(N-1)! · card(SYT(μ))         [corner step]
               = N!/(N-1)! = N                     [HLF for μ] -/
private lemma hook_walk_identity_atMostTwoRows (μ : YoungDiagram) (h2 : μ.rowLen 2 = 0)
    (hpos : 0 < μ.card) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / (hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) : ℚ))
    = (μ.card : ℚ) := by
  have hHP : (hookProd μ : ℚ) ≠ 0 := hookProdQ_ne_zero μ
  have hfact : ((μ.card - 1).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  -- HLF for μ over ℚ (proved independently, without hook_walk_identity)
  have hμ : (Fintype.card (StandardYoungTableau μ) : ℚ) * hookProd μ = μ.card.factorial :=
    by exact_mod_cast hook_length_formula_atMostTwoRows μ h2
  -- HLF for each removeCorner (stays ≤2-row by removeCorner_atMostTwoRows)
  have hμc : ∀ cx : { x // x ∈ corners μ },
      (Fintype.card (StandardYoungTableau
        (removeCorner μ cx.val (mem_corners.mp cx.prop))) : ℚ) *
      (hookProd (removeCorner μ cx.val (mem_corners.mp cx.prop)) : ℚ) =
      ((μ.card - 1).factorial : ℚ) := by
    intro ⟨c, hcx⟩
    have h2c := removeCorner_atMostTwoRows h2 (mem_corners.mp hcx)
    have hlf := hook_length_formula_atMostTwoRows _ h2c
    rw [removeCorner_card (mem_corners.mp hcx)] at hlf
    exact_mod_cast hlf
  -- Corner step over ℚ
  have hstepQ : (Fintype.card (StandardYoungTableau μ) : ℚ) =
      ∑ cx ∈ (corners μ).attach,
        (Fintype.card (StandardYoungTableau
          (removeCorner μ cx.val (mem_corners.mp cx.prop))) : ℚ) :=
    by exact_mod_cast card_SYT_corner_step μ hpos
  -- μ.card! = μ.card × (μ.card − 1)! as rationals
  have hfact_succ : (μ.card.factorial : ℚ) = (μ.card : ℚ) * ((μ.card - 1).factorial : ℚ) := by
    cases hcard : μ.card with
    | zero => omega
    | succ n =>
      rw [show μ.card - 1 = n by omega, show μ.card = n + 1 from hcard, Nat.factorial_succ]
      push_cast; ring
  -- Each summand: HP/HPc = card(SYT(μ\c)) × (HP/(N-1)!)
  have hterm : ∀ cx : { x // x ∈ corners μ },
      (hookProd μ : ℚ) / (hookProd (removeCorner μ cx.val (mem_corners.mp cx.prop)) : ℚ) =
      (Fintype.card (StandardYoungTableau
        (removeCorner μ cx.val (mem_corners.mp cx.prop))) : ℚ) *
      ((hookProd μ : ℚ) / ((μ.card - 1).factorial : ℚ)) := by
    intro ⟨c, hcx⟩
    have hHPc : (hookProd (removeCorner μ c (mem_corners.mp hcx)) : ℚ) ≠ 0 :=
      hookProdQ_ne_zero _
    have hIHc := hμc ⟨c, hcx⟩
    rw [mul_div_assoc, div_eq_div_iff hHPc hfact]
    linear_combination -(hookProd μ : ℚ) * hIHc
  -- Assemble: rewrite summands, factor, apply corner step, use HLF and factorial identity
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← hstepQ, mul_div_assoc, hμ, hfact_succ]
  field_simp [hfact]

/-- The hook walk identity: sum over corners c of hookProd(μ)/hookProd(μ\c) equals μ.card.
    Proved for at-most-2-row shapes via hook_walk_identity_atMostTwoRows (non-circular).
    General (≥3-row) case: requires GNW probabilistic proof (~300 lines) or RSK (~500 lines). -/

-- ============================================================
-- Infrastructure: rowLen/colLen/hookLength changes for removeCorner
-- ============================================================

/-- For a corner c of μ, the row at row c.1 ends exactly at c.2: rowLen = c.2 + 1. -/
private lemma rowLen_of_isCorner {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c) :
    μ.rowLen c.1 = c.2 + 1 := by
  have h1 : c.2 < μ.rowLen c.1 := YoungDiagram.mem_iff_lt_rowLen.mp hc.1
  have h2 : ¬(c.2 + 1 < μ.rowLen c.1) := by
    rw [← YoungDiagram.mem_iff_lt_rowLen]; exact hc.2.1
  omega

/-- For a corner c of μ, the column at col c.2 ends exactly at c.1: colLen = c.1 + 1. -/
private lemma colLen_of_isCorner {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c) :
    μ.colLen c.2 = c.1 + 1 := by
  have h1 : c.1 < μ.colLen c.2 := YoungDiagram.mem_iff_lt_colLen.mp hc.1
  have h2 : ¬(c.1 + 1 < μ.colLen c.2) := by
    rw [← YoungDiagram.mem_iff_lt_colLen]; exact hc.2.2
  omega

/-- Removing corner c decreases rowLen at row c.1 by 1: from c.2+1 to c.2. -/
private lemma rowLen_removeCorner_self {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c) :
    (removeCorner μ c hc).rowLen c.1 = c.2 := by
  obtain ⟨i, j⟩ := c
  apply Nat.le_antisymm
  · -- rowLen ≤ j: (i, j) ∉ removeCorner (it was erased)
    have h1 : (i, j) ∉ removeCorner μ (i, j) hc := by
      rw [mem_removeCorner hc]; rintro ⟨-, hne⟩; exact hne rfl
    have h2 := YoungDiagram.mem_iff_lt_rowLen.not.mp h1
    -- h2 : ¬(j < rowLen ν i), i.e., rowLen ν i ≤ j
    omega
  · -- j ≤ rowLen: if j > 0, show (i, j-1) ∈ removeCorner
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact Nat.zero_le _
    · have hmem : (i, j - 1) ∈ removeCorner μ (i, j) hc := by
        rw [mem_removeCorner hc]
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by rw [rowLen_of_isCorner hc]; omega), ?_⟩
        rintro h; exact absurd (congr_arg Prod.snd h) (by omega)
      have := YoungDiagram.mem_iff_lt_rowLen.mp hmem
      omega

/-- Removing corner c leaves rowLen unchanged at rows r ≠ c.1. -/
private lemma rowLen_removeCorner_other {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c)
    {r : ℕ} (hr : r ≠ c.1) :
    (removeCorner μ c hc).rowLen r = μ.rowLen r := by
  obtain ⟨i, j⟩ := c
  -- hr : r ≠ i
  have mem_iff : ∀ k, (r, k) ∈ removeCorner μ (i, j) hc ↔ (r, k) ∈ μ := fun k => by
    rw [mem_removeCorner hc]
    exact ⟨And.left, fun h => ⟨h, fun heq => hr (congr_arg Prod.fst heq)⟩⟩
  apply Nat.le_antisymm
  · -- rowLen ν r ≤ rowLen μ r: boundary of μ is also not in ν
    have h1 : (r, μ.rowLen r) ∉ μ := by
      rw [YoungDiagram.mem_iff_lt_rowLen]; exact lt_irrefl _
    have h2 : (r, μ.rowLen r) ∉ removeCorner μ (i, j) hc := (mem_iff _).not.mpr h1
    have h3 := YoungDiagram.mem_iff_lt_rowLen.not.mp h2
    omega
  · -- rowLen μ r ≤ rowLen ν r: boundary of ν is also not in μ
    have h1 : (r, (removeCorner μ (i, j) hc).rowLen r) ∉ removeCorner μ (i, j) hc := by
      rw [YoungDiagram.mem_iff_lt_rowLen]; exact lt_irrefl _
    have h2 : (r, (removeCorner μ (i, j) hc).rowLen r) ∉ μ := (mem_iff _).not.mp h1
    have h3 := YoungDiagram.mem_iff_lt_rowLen.not.mp h2
    omega

/-- Removing corner c decreases colLen at col c.2 by 1: from c.1+1 to c.1. -/
private lemma colLen_removeCorner_self {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c) :
    (removeCorner μ c hc).colLen c.2 = c.1 := by
  obtain ⟨i, j⟩ := c
  apply Nat.le_antisymm
  · -- colLen ≤ i: (i, j) ∉ removeCorner
    have h1 : (i, j) ∉ removeCorner μ (i, j) hc := by
      rw [mem_removeCorner hc]; rintro ⟨-, hne⟩; exact hne rfl
    have h2 := YoungDiagram.mem_iff_lt_colLen.not.mp h1
    omega
  · -- i ≤ colLen: if i > 0, show (i-1, j) ∈ removeCorner
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact Nat.zero_le _
    · have hmem : (i - 1, j) ∈ removeCorner μ (i, j) hc := by
        rw [mem_removeCorner hc]
        refine ⟨YoungDiagram.mem_iff_lt_colLen.mpr (by rw [colLen_of_isCorner hc]; omega), ?_⟩
        rintro h; exact absurd (congr_arg Prod.fst h) (by omega)
      have := YoungDiagram.mem_iff_lt_colLen.mp hmem
      omega

/-- Removing corner c leaves colLen unchanged at columns s ≠ c.2. -/
private lemma colLen_removeCorner_other {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c)
    {s : ℕ} (hs : s ≠ c.2) :
    (removeCorner μ c hc).colLen s = μ.colLen s := by
  obtain ⟨i, j⟩ := c
  -- hs : s ≠ j
  have mem_iff : ∀ k, (k, s) ∈ removeCorner μ (i, j) hc ↔ (k, s) ∈ μ := fun k => by
    rw [mem_removeCorner hc]
    exact ⟨And.left, fun h => ⟨h, fun heq => hs (congr_arg Prod.snd heq)⟩⟩
  apply Nat.le_antisymm
  · -- colLen ν s ≤ colLen μ s
    have h1 : (μ.colLen s, s) ∉ μ := by
      rw [YoungDiagram.mem_iff_lt_colLen]; exact lt_irrefl _
    have h2 : (μ.colLen s, s) ∉ removeCorner μ (i, j) hc := (mem_iff _).not.mpr h1
    have h3 := YoungDiagram.mem_iff_lt_colLen.not.mp h2
    omega
  · -- colLen μ s ≤ colLen ν s
    have h1 : ((removeCorner μ (i, j) hc).colLen s, s) ∉ removeCorner μ (i, j) hc := by
      rw [YoungDiagram.mem_iff_lt_colLen]; exact lt_irrefl _
    have h2 : ((removeCorner μ (i, j) hc).colLen s, s) ∉ μ := (mem_iff _).not.mp h1
    have h3 := YoungDiagram.mem_iff_lt_colLen.not.mp h2
    omega

/-- For arm cells (c.1, s) with s < c.2: removing corner c decreases hookLength by 1. -/
private lemma hookLength_removeCorner_arm {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c)
    {s : ℕ} (hs : s < c.2) :
    hookLength (removeCorner μ c hc) c.1 s + 1 = hookLength μ c.1 s := by
  obtain ⟨i, j⟩ := c
  -- hs : s < j
  have hmem : (i, s) ∈ μ :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (by rw [rowLen_of_isCorner hc]; omega)
  have hcol : i < μ.colLen s := YoungDiagram.mem_iff_lt_colLen.mp hmem
  unfold hookLength armLen legLen
  rw [rowLen_removeCorner_self hc, colLen_removeCorner_other hc (ne_of_lt hs),
      rowLen_of_isCorner hc]
  omega

/-- For leg cells (r, c.2) with r < c.1: removing corner c decreases hookLength by 1. -/
private lemma hookLength_removeCorner_leg {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c)
    {r : ℕ} (hr : r < c.1) :
    hookLength (removeCorner μ c hc) r c.2 + 1 = hookLength μ r c.2 := by
  obtain ⟨i, j⟩ := c
  -- hr : r < i
  have hmem : (r, j) ∈ μ :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by rw [colLen_of_isCorner hc]; omega)
  have hrowlen : j < μ.rowLen r := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  unfold hookLength armLen legLen
  rw [colLen_removeCorner_self hc, rowLen_removeCorner_other hc (ne_of_lt hr),
      colLen_of_isCorner hc]
  omega

/-- For a corner c, hookLength μ c.1 c.2 = 1 (armLen = 0, legLen = 0). -/
private lemma hookLength_corner_eq_one {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c) :
    hookLength μ c.1 c.2 = 1 := by
  obtain ⟨i, j⟩ := c
  unfold hookLength armLen legLen
  rw [rowLen_of_isCorner hc, colLen_of_isCorner hc]
  omega

/-- For cells that are neither arm nor leg of corner c, hookLength is unchanged by removeCorner. -/
private lemma hookLength_eq_of_not_arm_leg {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c)
    {x : ℕ × ℕ} (hxμ : x ∈ μ) (hxc : x ≠ c)
    (hxarm : ¬(x.1 = c.1 ∧ x.2 < c.2))
    (hxleg : ¬(x.1 < c.1 ∧ x.2 = c.2)) :
    hookLength (removeCorner μ c hc) x.1 x.2 = hookLength μ x.1 x.2 := by
  obtain ⟨i, j⟩ := c
  obtain ⟨a, b⟩ := x
  simp only [Prod.fst, Prod.snd] at hxarm hxleg hxc ⊢
  -- Derive: a ≠ i
  have ha : a ≠ i := by
    intro heq; subst heq
    push_neg at hxarm
    have hb_lt : b < μ.rowLen a := YoungDiagram.mem_iff_lt_rowLen.mp hxμ
    rw [rowLen_of_isCorner hc] at hb_lt
    -- b < j+1, hxarm says b ≥ j (since it's not true b < j), so b = j, contradicting hxc
    exact hxc (Prod.ext rfl (by omega))
  -- Derive: b ≠ j
  have hb : b ≠ j := by
    intro heq; subst heq
    push_neg at hxleg
    have ha_lt : a < μ.colLen b := YoungDiagram.mem_iff_lt_colLen.mp hxμ
    rw [colLen_of_isCorner hc] at ha_lt
    -- a < i+1, hxleg says a ≥ i, so a = i, contradicting hxc
    exact hxc (Prod.ext (by omega) rfl)
  -- Now apply removeCorner invariance
  unfold hookLength armLen legLen
  rw [rowLen_removeCorner_other hc ha, colLen_removeCorner_other hc hb]

/-- The hookProd ratio for a corner c equals the product of h/(h-1) over arm and leg cells.
    Proof strategy (for future completion):
    1. hookProd(μ) = hookLength(μ,c) × ∏_{x∈ν.cells} hookLength(μ,x)  [mul_prod_erase]
    2. hookLength(μ,c) = 1  [hookLength_corner_eq_one]
    3. ratio = ∏_{x∈ν.cells} hookLength(μ,x)/hookLength(ν,x)  [prod_div_distrib]
    4. ν.cells = armCells ∪ legCells ∪ restCells (disjoint)
    5. On arm cells: hookLength(μ)/hookLength(ν) = h/(h-1)  [hookLength_removeCorner_arm]
    6. On leg cells: hookLength(μ)/hookLength(ν) = h/(h-1)  [hookLength_removeCorner_leg]
    7. On rest cells: hookLength(μ)/hookLength(ν) = 1  [hookLength_eq_of_not_arm_leg]
    Requires ~80 lines of Finset.prod_union decomposition. -/
private lemma hookProd_ratio_formula {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c) :
    (hookProd μ : ℚ) / hookProd (removeCorner μ c hc) =
      (∏ s ∈ Finset.range c.2, (hookLength μ c.1 s : ℚ) / (hookLength μ c.1 s - 1)) *
      (∏ r ∈ Finset.range c.1, (hookLength μ r c.2 : ℚ) / (hookLength μ r c.2 - 1)) := by
  sorry


private lemma hook_walk_identity (μ : YoungDiagram) (hn : 0 < μ.card) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / (hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) : ℚ))
    = (μ.card : ℚ) := by
  by_cases h2 : μ.rowLen 2 = 0
  · -- At-most-2-row case: proved non-circularly
    exact hook_walk_identity_atMostTwoRows μ h2 hn
  · -- ≥3-row case: requires hook walk combinatorics (GNW ~300 lines or RSK ~500 lines)
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
    The sole remaining sorry is hook_walk_identity (verified for all special cases;
    general proof requires hook walk combinatorics, ~300 lines). -/
theorem hook_length_formula_general (μ : YoungDiagram) :
    Fintype.card (StandardYoungTableau μ) * hookProd μ = μ.card.factorial := by
  exact_mod_cast hook_length_formula_Q μ

end HookLengthFormula
