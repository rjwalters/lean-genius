/-
  BallotProblemOQ03OQ01OQ02Helpers — PARTS I through XXIV
  (Hook-Length Formula infrastructure: extracted for file-size management)

  This file contains the supporting infrastructure (PARTS I-XXIV) for the
  Hook-Length Formula proof. The main proof file BallotProblemOQ03OQ01OQ02.lean
  imports this file and adds PART XXV + the dispatcher + hook_length_formula_general.
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
def emptyTableau : StandardYoungTableau (⊥ : YoungDiagram) where
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

-- hook_length_formula is proved at the end of the file via hook_length_formula_general.
-- (The theorem must be stated after its proof infrastructure is elaborated.)

/-- The 2-row hook-length formula (Catalan case) follows from BallotProblemOQ03OQ03:
    C_m · (m+1)! · m! = (2m)! where C_m is the m-th Catalan number. -/
theorem hook_length_formula_2row_rect (m : ℕ) :
    LatticePathLGV.Cn m * ((m + 1).factorial * m.factorial) = (2 * m).factorial :=
  LGVCorollaries.hook_length_formula_two_row m

/-
  ## OPEN: LGV proof path — canonical-config restatement

  Earlier revisions of this file declared two auxiliary `sorry` lemmas
  (`ni_count_eq_syt_count` and `lgv_det_factors_as_hook_quotient`) that took
  an arbitrary tuple (r, σ, m) of LGV parameters with no hypothesis tying
  them to μ.  As stated, those lemmas were not generally true: most choices
  of (r, σ, m) bear no relation to μ, so the equalities reduce to false
  numerical claims (e.g. for μ = ⊥ paired with r = 1, σ = fun _ => 5).
  They were therefore dead, unprovable scaffolding, and have been removed.

  The corrected formulation requires a canonical encoding `youngLGVConfigOf μ`
  built from μ alone:

      r       = μ.colLen 0                    -- number of non-empty rows
      σ_μ i   = μ.rowLen (r - 1 - i.val)      -- weakly-increasing reversal
      m       = σ_μ ⟨r-1, _⟩ + (r-1)           -- max source/target index

  With this canonical config the two open conjectures become:

  (A)  Fintype.card (StandardYoungTableau μ) = niTupleCount (youngLGVConfigOf μ)
       — the Fomin/RSK bijection between SYT and non-intersecting lattice
         path tuples.  ~200 lines.

  (B)  (pathMatrix (youngLGVConfigOf μ)).det * (hookProd μ : ℤ) = μ.card.factorial
       — the Lindström / Jacobi–Trudi determinant identity.  ~200 lines.

  Subtlety: the LGV well-formedness condition `r - 1 ≤ σ_μ ⟨0, _⟩` reduces to
  `r - 1 ≤ μ.rowLen (r - 1)`, i.e. the bottom row is at least as long as
  (numRows − 1).  This fails for tall/narrow shapes such as the column
  `(1,1,…,1)`.  The general statement therefore needs a transpose-duality
  case split (apply LGV to whichever of μ, μᵀ is "wide enough"), or a more
  flexible canonical config that does not require well-formedness.

  Until (A) and (B) are formalized, the main theorem `hook_length_formula`
  is established via the corner-recursion / `hook_walk_identity` path
  (`hook_length_formula_general`, end of file).  `hook_length_formula_from_chain`
  below remains a clean *conditional* statement that records the LGV chain
  abstractly and can consume any future proof of (A) and (B).
-/

/-- The hook-length formula follows abstractly from the LGV chain hypotheses
    `h_ni_syt` (SYT count = NI-path count) and `h_det_hook` (det × hookProd = n!).
    A proof of (A) and (B) above for a canonical encoding `youngLGVConfigOf μ`
    would discharge both hypotheses and yield `hook_length_formula` directly. -/
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
def gHookYD (a b : ℕ) (ha : 0 < a) : YoungDiagram where
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
def isCorner (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∈ μ ∧ (c.1, c.2 + 1) ∉ μ ∧ (c.1 + 1, c.2) ∉ μ

/-- Finset of corner cells of μ. -/
def corners (μ : YoungDiagram) : Finset (ℕ × ℕ) :=
  μ.cells.filter (fun c => (c.1, c.2 + 1) ∉ μ ∧ (c.1 + 1, c.2) ∉ μ)

lemma mem_corners {μ : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ corners μ ↔ isCorner μ c := by
  simp only [corners, Finset.mem_filter, YoungDiagram.mem_cells, isCorner]

/-- Removing a corner cell preserves the lower-set property. -/
noncomputable def removeCorner (μ : YoungDiagram) (c : ℕ × ℕ)
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
lemma mem_removeCorner {μ : YoungDiagram} {c x : ℕ × ℕ} (hc : isCorner μ c) :
    x ∈ removeCorner μ c hc ↔ x ∈ μ ∧ x ≠ c := by
  simp only [removeCorner, YoungDiagram.mem_mk, Finset.mem_erase, YoungDiagram.mem_cells]
  tauto

/-- A corner of μ distinct from c₁ remains a corner of removeCorner μ c₁. -/
private lemma isCorner_removeCorner_of_ne {μ : YoungDiagram} {c₁ c₂ : ℕ × ℕ}
    (hc₁ : isCorner μ c₁) (hc₂ : isCorner μ c₂) (hne : c₁ ≠ c₂) :
    isCorner (removeCorner μ c₁ hc₁) c₂ := by
  obtain ⟨hc₂mem, hc₂right, hc₂below⟩ := hc₂
  refine ⟨(mem_removeCorner hc₁).mpr ⟨hc₂mem, hne.symm⟩, ?_, ?_⟩
  · intro hmem
    exact hc₂right ((mem_removeCorner hc₁).mp hmem).1
  · intro hmem
    exact hc₂below ((mem_removeCorner hc₁).mp hmem).1

/-- Cardinality of removeCorner is μ.card - 1. -/
lemma removeCorner_card {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c) :
    (removeCorner μ c hc).card = μ.card - 1 := by
  simp [YoungDiagram.card, removeCorner,
    Finset.card_erase_of_mem (YoungDiagram.mem_cells.mpr hc.1)]

/-- removeCorner doesn't depend on which proof of isCorner we use.
    (The cells are just μ.cells.erase c, independent of the proof.) -/
lemma removeCorner_proof_irrel (μ : YoungDiagram) (c : ℕ × ℕ)
    (hc₁ hc₂ : isCorner μ c) :
    removeCorner μ c hc₁ = removeCorner μ c hc₂ := by
  apply YoungDiagram.ext
  simp [removeCorner]

/-- Removing two distinct corners commutes: the diagram obtained by removing
    `c` then `c'` equals the one obtained by removing `c'` then `c`.

    Why this matters for `gnwProb_exchange`: the exchange identity relates
    `H((μ\c')\c)` to `H(μ\c)` and `H(μ\c')`.  Writing the equation in either
    iteration order is equivalent thanks to this commutativity, freeing the
    proof from having to track whether `c` is removed before or after `c'`. -/
private lemma removeCorner_swap {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') :
    removeCorner (removeCorner μ c hc) c'
        (isCorner_removeCorner_of_ne hc hc' hne) =
    removeCorner (removeCorner μ c' hc') c
        (isCorner_removeCorner_of_ne hc' hc hne.symm) := by
  apply YoungDiagram.ext
  show (μ.cells.erase c).erase c' = (μ.cells.erase c').erase c
  ext x
  simp only [Finset.mem_erase]
  tauto

/-- Hook products are invariant under swapping the order of two distinct corner
    removals.  Direct corollary of `removeCorner_swap`: equal diagrams have
    equal hook products. -/
private lemma hookProd_removeCorner_swap {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') :
    hookProd (removeCorner (removeCorner μ c hc) c'
        (isCorner_removeCorner_of_ne hc hc' hne)) =
    hookProd (removeCorner (removeCorner μ c' hc') c
        (isCorner_removeCorner_of_ne hc' hc hne.symm)) := by
  rw [removeCorner_swap hc hc' hne]

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
lemma hookProdQ_ne_zero (μ : YoungDiagram) : (hookProd μ : ℚ) ≠ 0 :=
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
lemma hook_walk_identity_atMostTwoRows (μ : YoungDiagram) (h2 : μ.rowLen 2 = 0)
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

/-- Two distinct corners of μ are anti-monotone: if `c.1 < c'.1` then `c'.2 < c.2`.
    This is a structural fact: corners step strictly down-and-left in the diagram.
    Useful for identifying the unique cell `(c.1, c'.2)` that is in the arm of `c` and
    leg of `c'` (the "doubly-affected cell" in the GNW exchange argument). -/
private lemma corner_col_lt_of_row_lt {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hi : c.1 < c'.1) :
    c'.2 < c.2 := by
  -- c'.1 < μ.colLen c'.2 from c' ∈ μ
  have hc'_col : c'.1 < μ.colLen c'.2 := YoungDiagram.mem_iff_lt_colLen.mp hc'.1
  -- If c.2 ≤ c'.2, then μ.colLen c'.2 ≤ μ.colLen c.2 (colLen anti-monotone),
  -- and μ.colLen c.2 = c.1 + 1, so c'.1 < c.1 + 1, i.e., c'.1 ≤ c.1, contradicting hi.
  by_contra h_le
  push_neg at h_le -- c.2 ≤ c'.2
  have h_anti : μ.colLen c'.2 ≤ μ.colLen c.2 := by
    apply Nat.le_of_not_lt
    intro hlt
    have h1 : (μ.colLen c.2, c'.2) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have h2 : (μ.colLen c.2, c.2) ∈ μ :=
      μ.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl _, h_le⟩) h1
    exact absurd (YoungDiagram.mem_iff_lt_colLen.mp h2) (lt_irrefl _)
  rw [colLen_of_isCorner hc] at h_anti
  omega

/-- Symmetric form: if two distinct corners satisfy `c.2 < c'.2` then `c'.1 < c.1`.
    Equivalently, corners are also row-anti-monotone in column index. -/
private lemma corner_row_lt_of_col_lt {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hj : c.2 < c'.2) :
    c'.1 < c.1 := by
  by_contra h_le
  push_neg at h_le -- c.1 ≤ c'.1
  rcases lt_or_eq_of_le h_le with hlt | heq
  · exact absurd (corner_col_lt_of_row_lt hc hc' hlt) (not_lt.mpr (le_of_lt hj))
  · -- c.1 = c'.1; combined with c.2 < c'.2 and rowLen of corner ⇒ contradiction
    have hrl : μ.rowLen c.1 = c.2 + 1 := rowLen_of_isCorner hc
    have hc'_row : c'.2 < μ.rowLen c'.1 := YoungDiagram.mem_iff_lt_rowLen.mp hc'.1
    rw [← heq, hrl] at hc'_row; omega

/-- Distinct corners of μ have distinct first coordinates: each row of μ has at
    most one corner (namely the rightmost cell of the row, if any).
    Useful in the GNW exchange argument when reasoning about hookLength shifts:
    distinct corners c, c' never share a row, so the arm of c and the arm of c'
    are disjoint apart from the doubly-affected cell. -/
private lemma corners_fst_ne {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') :
    c.1 ≠ c'.1 := by
  intro heq
  -- Same row ⇒ both have rowLen at row c.1 = c.2 + 1 = c'.2 + 1, hence c = c'.
  have h1 : μ.rowLen c.1 = c.2 + 1 := rowLen_of_isCorner hc
  have h2 : μ.rowLen c'.1 = c'.2 + 1 := rowLen_of_isCorner hc'
  rw [← heq] at h2
  have hsnd : c.2 = c'.2 := by omega
  exact hne (Prod.ext heq hsnd)

/-- Distinct corners of μ have distinct second coordinates: each column of μ has
    at most one corner (namely the bottom cell of the column, if any). -/
private lemma corners_snd_ne {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') :
    c.2 ≠ c'.2 := by
  intro heq
  have h1 : μ.colLen c.2 = c.1 + 1 := colLen_of_isCorner hc
  have h2 : μ.colLen c'.2 = c'.1 + 1 := colLen_of_isCorner hc'
  rw [← heq] at h2
  have hfst : c.1 = c'.1 := by omega
  exact hne (Prod.ext hfst heq)

/-- Trichotomy for distinct corners (collapses to dichotomy): either `c` is
    strictly above-and-to-the-right of `c'`, or vice versa. The middle case
    (`c.1 = c'.1`) is impossible by `corners_fst_ne`.

    This packages the existing `corner_col_lt_of_row_lt` for use in case
    analysis without re-deriving the row-coordinate dichotomy at each call site.
    Used in the GNW exchange identity to split on the relative orientation of
    `c` and `c'`. -/
private lemma distinct_corners_dichotomy {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') :
    (c.1 < c'.1 ∧ c'.2 < c.2) ∨ (c'.1 < c.1 ∧ c.2 < c'.2) := by
  have h_fst_ne : c.1 ≠ c'.1 := corners_fst_ne hc hc' hne
  rcases lt_or_gt_of_ne h_fst_ne with hlt | hgt
  · exact Or.inl ⟨hlt, corner_col_lt_of_row_lt hc hc' hlt⟩
  · exact Or.inr ⟨hgt, corner_col_lt_of_row_lt hc' hc hgt⟩

/-- For two distinct corners `c, c'` of μ with `c.1 < c'.1`, the cell `(c.1, c'.2)`
    lies in μ. It is the unique cell in the arm of `c` and leg of `c'`, and plays
    a key role in the GNW 1979 exchange identity. -/
private lemma doubly_affected_cell_mem {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hi : c.1 < c'.1) :
    (c.1, c'.2) ∈ μ := by
  have h_col_lt : c'.2 < c.2 := corner_col_lt_of_row_lt hc hc' hi
  -- (c.1, c'.2) ≤ (c.1, c.2) = c, and c ∈ μ, so by lower-set property (c.1, c'.2) ∈ μ
  exact μ.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl _, le_of_lt h_col_lt⟩) hc.1

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

-- ============================================================
-- Double-removal hookLength shifts (Session 48)
-- For two distinct corners c, c' of μ with c.1 < c'.1 (whence c'.2 < c.2 by
-- `corner_col_lt_of_row_lt`), the lemmas in this block characterize how
-- `hookLength` shifts at each cell when both corners are removed.  The shift
-- is determined purely by x's geometric relationship to the two corners:
--   * `(c.1, c'.2)` (the doubly-affected cell)        → shift by 2
--   * arm(c) \ {(c.1, c'.2)}, leg(c), arm(c'), leg(c') \ {(c.1, c'.2)} → shift by 1
--   * everything else                                  → shift by 0.
-- These six lemmas are the core combinatorial input to `gnwProb_exchange`
-- (line 14173).  All proofs are 1-2 line consequences of the existing
-- single-removal helpers (`hookLength_removeCorner_arm`, `_leg`,
-- `hookLength_eq_of_not_arm_leg`) chained through `isCorner_removeCorner_of_ne`.
-- The iteration order is `(μ\c)\c'`; convert to `(μ\c')\c` via
-- `removeCorner_swap` if needed.
-- ============================================================

/-- **Doubly-affected cell shifts by 2.**

For two distinct corners `c, c'` of `μ` with `c.1 < c'.1` (whence `c'.2 < c.2`),
the cell `(c.1, c'.2)` is the unique cell sitting in the arm of `c` and the
leg of `c'`.  Removing both corners shifts its hook length by exactly 2:
removing `c` cuts its arm by 1, then removing `c'` (still a corner of `μ\c`)
cuts its leg by 1.

This is the cell whose hook-length asymmetry is the heart of the GNW 1979
exchange identity:
`h_μ(d) · h_{(μ\c)\c'}(d) = h(h-2)` versus
`h_{μ\c}(d) · h_{μ\c'}(d) = (h-1)²`. -/
private lemma hookLength_doubleRemove_doubly_affected
    {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') (hi : c.1 < c'.1) :
    hookLength (removeCorner (removeCorner μ c hc) c'
        (isCorner_removeCorner_of_ne hc hc' hne)) c.1 c'.2 + 2 =
      hookLength μ c.1 c'.2 := by
  have h_col_lt : c'.2 < c.2 := corner_col_lt_of_row_lt hc hc' hi
  -- Step 1 (arm of c): hookLength_{μ\c}(c.1, c'.2) + 1 = hookLength_μ(c.1, c'.2)
  have h_arm := hookLength_removeCorner_arm hc h_col_lt
  -- Step 2 (leg of c' inside μ\c): hookLength_{(μ\c)\c'}(c.1, c'.2) + 1
  --                              = hookLength_{μ\c}(c.1, c'.2)
  have hc'_in_rc : isCorner (removeCorner μ c hc) c' :=
    isCorner_removeCorner_of_ne hc hc' hne
  have h_leg := hookLength_removeCorner_leg hc'_in_rc hi
  omega

/-- **Arm of c (excluding doubly-affected): shift by 1.**

For arm-of-`c` cells `(c.1, s)` with `s < c.2` and `s ≠ c'.2`, removing both
corners shifts hook length by exactly 1: the arm-of-`c` shift accounts for
the entire change, since the cell is in neither the arm nor the leg of `c'`
(different row from `c'` and different column since `s ≠ c'.2`). -/
private lemma hookLength_doubleRemove_arm_of_c_off_d
    {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') (hi : c.1 < c'.1)
    {s : ℕ} (hs : s < c.2) (hs' : s ≠ c'.2) :
    hookLength (removeCorner (removeCorner μ c hc) c'
        (isCorner_removeCorner_of_ne hc hc' hne)) c.1 s + 1 =
      hookLength μ c.1 s := by
  -- Step 1 (arm of c): hookLength_{μ\c}(c.1, s) + 1 = hookLength_μ(c.1, s)
  have h_arm := hookLength_removeCorner_arm hc hs
  -- Step 2 (NOT arm or leg of c' in μ\c): hookLength unchanged after removing c'.
  have hc'_in_rc : isCorner (removeCorner μ c hc) c' :=
    isCorner_removeCorner_of_ne hc hc' hne
  have hxν : (c.1, s) ∈ removeCorner μ c hc := by
    rw [mem_removeCorner]
    refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by rw [rowLen_of_isCorner hc]; omega), ?_⟩
    intro h; have : s = c.2 := congr_arg Prod.snd h; omega
  have hxc' : (c.1, s) ≠ c' := fun h => by
    have : c.1 = c'.1 := congr_arg Prod.fst h; omega
  have hxarm : ¬((c.1, s).1 = c'.1 ∧ (c.1, s).2 < c'.2) := by
    rintro ⟨h1, _⟩; exact absurd h1 (Nat.ne_of_lt hi)
  have hxleg : ¬((c.1, s).1 < c'.1 ∧ (c.1, s).2 = c'.2) := by
    rintro ⟨_, h2⟩; exact hs' h2
  have h_unaff := hookLength_eq_of_not_arm_leg hc'_in_rc hxν hxc' hxarm hxleg
  -- Goal: hookLength ((μ\c)\c') c.1 s + 1 = hookLength μ c.1 s
  -- h_unaff : hookLength ((μ\c)\c') c.1 s = hookLength (μ\c) c.1 s
  -- h_arm   : hookLength (μ\c) c.1 s + 1 = hookLength μ c.1 s
  rw [h_unaff]; exact h_arm

/-- **Leg of c: shift by 1.**

For leg-of-`c` cells `(r, c.2)` with `r < c.1`, removing both corners shifts
hook length by exactly 1: the leg-of-`c` shift accounts for the entire change.
The cell is in neither arm nor leg of `c'`:
* not in arm of `c'` because `r < c.1 < c'.1`, so `r ≠ c'.1`;
* not in leg of `c'` because `c.2 ≠ c'.2` (in fact `c'.2 < c.2`). -/
private lemma hookLength_doubleRemove_leg_of_c
    {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') (hi : c.1 < c'.1)
    {r : ℕ} (hr : r < c.1) :
    hookLength (removeCorner (removeCorner μ c hc) c'
        (isCorner_removeCorner_of_ne hc hc' hne)) r c.2 + 1 =
      hookLength μ r c.2 := by
  have h_col_lt : c'.2 < c.2 := corner_col_lt_of_row_lt hc hc' hi
  have h_leg := hookLength_removeCorner_leg hc hr
  have hc'_in_rc : isCorner (removeCorner μ c hc) c' :=
    isCorner_removeCorner_of_ne hc hc' hne
  have hxν : (r, c.2) ∈ removeCorner μ c hc := by
    rw [mem_removeCorner]
    refine ⟨YoungDiagram.mem_iff_lt_colLen.mpr (by rw [colLen_of_isCorner hc]; omega), ?_⟩
    intro h; have : r = c.1 := congr_arg Prod.fst h; omega
  have hxc' : (r, c.2) ≠ c' := fun h => by
    have : c.2 = c'.2 := congr_arg Prod.snd h; omega
  have hxarm : ¬((r, c.2).1 = c'.1 ∧ (r, c.2).2 < c'.2) := by
    rintro ⟨h1, _⟩; omega
  have hxleg : ¬((r, c.2).1 < c'.1 ∧ (r, c.2).2 = c'.2) := by
    rintro ⟨_, h2⟩; omega
  have h_unaff := hookLength_eq_of_not_arm_leg hc'_in_rc hxν hxc' hxarm hxleg
  rw [h_unaff]; exact h_leg

/-- **Arm of c': shift by 1.**

For arm-of-`c'` cells `(c'.1, s)` with `s < c'.2`, removing both corners shifts
hook length by exactly 1: the arm-of-`c'` shift on `μ\c` accounts for the
entire change.  The cell is in neither arm nor leg of `c` (different row from
`c` since `c'.1 ≠ c.1`, and different column since `s < c'.2 < c.2`). -/
private lemma hookLength_doubleRemove_arm_of_c'
    {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') (hi : c.1 < c'.1)
    {s : ℕ} (hs : s < c'.2) :
    hookLength (removeCorner (removeCorner μ c hc) c'
        (isCorner_removeCorner_of_ne hc hc' hne)) c'.1 s + 1 =
      hookLength μ c'.1 s := by
  have h_col_lt : c'.2 < c.2 := corner_col_lt_of_row_lt hc hc' hi
  -- Step 1: removing c doesn't change hookLength at (c'.1, s) (not in arm/leg of c)
  have hsmem : (c'.1, s) ∈ μ :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (by rw [rowLen_of_isCorner hc']; omega)
  have hxc : (c'.1, s) ≠ c := fun h => by
    have : c'.1 = c.1 := congr_arg Prod.fst h; omega
  have hxarm : ¬((c'.1, s).1 = c.1 ∧ (c'.1, s).2 < c.2) := by
    rintro ⟨h1, _⟩; omega
  have hxleg : ¬((c'.1, s).1 < c.1 ∧ (c'.1, s).2 = c.2) := by
    rintro ⟨_, h2⟩; omega
  have h_unaff_c := hookLength_eq_of_not_arm_leg hc hsmem hxc hxarm hxleg
  -- Step 2: hookLength_{(μ\c)\c'}(c'.1, s) + 1 = hookLength_{μ\c}(c'.1, s) (arm of c' in μ\c)
  have hc'_in_rc : isCorner (removeCorner μ c hc) c' :=
    isCorner_removeCorner_of_ne hc hc' hne
  have h_arm_c' := hookLength_removeCorner_arm hc'_in_rc hs
  -- Goal: hookLength ((μ\c)\c') c'.1 s + 1 = hookLength μ c'.1 s
  -- h_arm_c' : hookLength ((μ\c)\c') c'.1 s + 1 = hookLength (μ\c) c'.1 s
  -- h_unaff_c: hookLength (μ\c) c'.1 s = hookLength μ c'.1 s
  omega

/-- **Leg of c' (excluding doubly-affected): shift by 1.**

For leg-of-`c'` cells `(r, c'.2)` with `r < c'.1` and `r ≠ c.1`, removing both
corners shifts hook length by exactly 1.  The cell is in neither arm nor leg
of `c`: not in arm of `c` because `r ≠ c.1`, and not in leg of `c` because
`c'.2 ≠ c.2` (in fact `c'.2 < c.2`).  The leg-of-`c'` shift on `μ\c` accounts
for the entire change. -/
private lemma hookLength_doubleRemove_leg_of_c'_off_d
    {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') (hi : c.1 < c'.1)
    {r : ℕ} (hr : r < c'.1) (hrc : r ≠ c.1) :
    hookLength (removeCorner (removeCorner μ c hc) c'
        (isCorner_removeCorner_of_ne hc hc' hne)) r c'.2 + 1 =
      hookLength μ r c'.2 := by
  have h_col_lt : c'.2 < c.2 := corner_col_lt_of_row_lt hc hc' hi
  -- Step 1: removing c doesn't change hookLength at (r, c'.2) (not in arm/leg of c)
  have hsmem : (r, c'.2) ∈ μ :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by rw [colLen_of_isCorner hc']; omega)
  have hxc : (r, c'.2) ≠ c := fun h => by
    have : c'.2 = c.2 := congr_arg Prod.snd h; omega
  have hxarm : ¬((r, c'.2).1 = c.1 ∧ (r, c'.2).2 < c.2) := by
    rintro ⟨h1, _⟩; exact hrc h1
  have hxleg : ¬((r, c'.2).1 < c.1 ∧ (r, c'.2).2 = c.2) := by
    rintro ⟨_, h2⟩; omega
  have h_unaff_c := hookLength_eq_of_not_arm_leg hc hsmem hxc hxarm hxleg
  -- Step 2: hookLength_{(μ\c)\c'}(r, c'.2) + 1 = hookLength_{μ\c}(r, c'.2) (leg of c' in μ\c)
  have hc'_in_rc : isCorner (removeCorner μ c hc) c' :=
    isCorner_removeCorner_of_ne hc hc' hne
  have h_leg_c' := hookLength_removeCorner_leg hc'_in_rc hr
  omega

/-- **Cells outside both arm/leg sets: hookLength unchanged.**

For cells `x ∈ μ` with `x ≠ c, c'` and `x` not in the arm or leg of either
corner, removing both corners leaves hook length unchanged.  Each removal
falls into the "unaffected" branch of `hookLength_eq_of_not_arm_leg`,
applied first to `c` on `μ`, then to `c'` on `μ\c`. -/
private lemma hookLength_doubleRemove_other
    {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c')
    {x : ℕ × ℕ} (hxμ : x ∈ μ) (hxc : x ≠ c) (hxc' : x ≠ c')
    (hxarm_c : ¬(x.1 = c.1 ∧ x.2 < c.2))
    (hxleg_c : ¬(x.1 < c.1 ∧ x.2 = c.2))
    (hxarm_c' : ¬(x.1 = c'.1 ∧ x.2 < c'.2))
    (hxleg_c' : ¬(x.1 < c'.1 ∧ x.2 = c'.2)) :
    hookLength (removeCorner (removeCorner μ c hc) c'
        (isCorner_removeCorner_of_ne hc hc' hne)) x.1 x.2 =
      hookLength μ x.1 x.2 := by
  -- Step 1: removing c doesn't change hookLength (not in arm/leg of c)
  have h_unaff_c := hookLength_eq_of_not_arm_leg hc hxμ hxc hxarm_c hxleg_c
  -- Step 2: removing c' from μ\c doesn't change hookLength (not in arm/leg of c')
  have hc'_in_rc : isCorner (removeCorner μ c hc) c' :=
    isCorner_removeCorner_of_ne hc hc' hne
  have hxν : x ∈ removeCorner μ c hc := by
    rw [mem_removeCorner]; exact ⟨hxμ, hxc⟩
  have h_unaff_c' := hookLength_eq_of_not_arm_leg hc'_in_rc hxν hxc' hxarm_c' hxleg_c'
  rw [h_unaff_c', h_unaff_c]

-- ============================================================
-- Single-removal hookLength shifts at arm/leg cells of *another* corner
-- (Session 50, prerequisites for `hookProd_doubleRemove_factor`)
--
-- These two lemmas are the *dual chain* of the S48 double-removal lemmas:
-- they state how `hookLength` shifts at the arm/leg cells of corner `c`
-- when the *other* corner `c'` is removed (rather than `c`).  Combined
-- with `hookLength_removeCorner_arm`/`_leg` for corner `c`, they give an
-- alternative derivation of S48 via the iteration order `(μ\c')\c`.
--
-- More importantly, they are the building blocks of the upcoming
-- `hookProd_doubleRemove_factor` proof: applying `hookProd_ratio_formula`
-- to corner `c` on `μ` and on `μ\c'` produces two arm/leg products that
-- are pointwise equal *except* at the doubly-affected cell `d = (c.1, c'.2)`.
-- These lemmas establish that pointwise equality at all cells off `d`.
-- ============================================================

/-- **At arm-of-`c` cells off the doubly-affected cell, removing `c'` preserves hookLength.**

For two distinct corners `c, c'` of `μ` with `c.1 < c'.1`, an arm-of-`c` cell
`(c.1, s)` with `s < c.2` and `s ≠ c'.2` is in neither arm nor leg of `c'`:
* not in arm of `c'` because `c.1 ≠ c'.1` (since `c.1 < c'.1`);
* not in leg of `c'` because the column `s ≠ c'.2`.
Therefore `hookLength_eq_of_not_arm_leg` applied to corner `c'` gives
hookLength invariance at this cell. -/
private lemma hookLength_removeCornerC'_arm_of_c_off_d
    {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hi : c.1 < c'.1)
    {s : ℕ} (hs : s < c.2) (hs' : s ≠ c'.2) :
    hookLength (removeCorner μ c' hc') c.1 s = hookLength μ c.1 s := by
  have hsmem : (c.1, s) ∈ μ :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (by rw [rowLen_of_isCorner hc]; omega)
  have hxc' : (c.1, s) ≠ c' := fun h => by
    have : c.1 = c'.1 := congr_arg Prod.fst h; omega
  have hxarm : ¬((c.1, s).1 = c'.1 ∧ (c.1, s).2 < c'.2) := by
    rintro ⟨h1, _⟩; exact absurd h1 (Nat.ne_of_lt hi)
  have hxleg : ¬((c.1, s).1 < c'.1 ∧ (c.1, s).2 = c'.2) := by
    rintro ⟨_, h2⟩; exact hs' h2
  exact hookLength_eq_of_not_arm_leg hc' hsmem hxc' hxarm hxleg

/-- **At leg-of-`c` cells, removing `c'` preserves hookLength.**

For two distinct corners `c, c'` of `μ` with `c.1 < c'.1` (whence `c'.2 < c.2`
by `corner_col_lt_of_row_lt`), a leg-of-`c` cell `(r, c.2)` with `r < c.1` is
in neither arm nor leg of `c'`:
* not in arm of `c'` because `r < c.1 < c'.1`, so `r ≠ c'.1`;
* not in leg of `c'` because `c'.2 < c.2`, so the column `c.2 ≠ c'.2`.
Therefore `hookLength_eq_of_not_arm_leg` applied to corner `c'` gives
hookLength invariance at this cell.  Note: unlike the arm case, *all*
leg-of-`c` cells are off the doubly-affected cell `d = (c.1, c'.2)`,
since `d` lies in the *arm* of `c` (row `c.1`, col `c'.2 < c.2`). -/
private lemma hookLength_removeCornerC'_leg_of_c
    {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hi : c.1 < c'.1)
    {r : ℕ} (hr : r < c.1) :
    hookLength (removeCorner μ c' hc') r c.2 = hookLength μ r c.2 := by
  have h_col_lt : c'.2 < c.2 := corner_col_lt_of_row_lt hc hc' hi
  have hsmem : (r, c.2) ∈ μ :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by rw [colLen_of_isCorner hc]; omega)
  have hxc' : (r, c.2) ≠ c' := fun h => by
    have : c.2 = c'.2 := congr_arg Prod.snd h; omega
  have hxarm : ¬((r, c.2).1 = c'.1 ∧ (r, c.2).2 < c'.2) := by
    rintro ⟨h1, _⟩; omega
  have hxleg : ¬((r, c.2).1 < c'.1 ∧ (r, c.2).2 = c'.2) := by
    rintro ⟨_, h2⟩; omega
  exact hookLength_eq_of_not_arm_leg hc' hsmem hxc' hxarm hxleg

/-- **At the doubly-affected cell `d = (c.1, c'.2)`, the hook length is at least 3.**

For two distinct corners `c, c'` of `μ` with `c.1 < c'.1` (whence `c'.2 < c.2`
by `corner_col_lt_of_row_lt`), the cell `d = (c.1, c'.2)` lies strictly in
the arm of `c` (row `c.1`, column `c'.2 < c.2`) and strictly in the leg of
`c'` (column `c'.2`, row `c.1 < c'.1`).  Algebraically,
* `armLen μ c.1 c'.2 = rowLen c.1 − c'.2 − 1 = (c.2 + 1) − c'.2 − 1 = c.2 − c'.2 ≥ 1`,
* `legLen μ c.1 c'.2 = colLen c'.2 − c.1 − 1 = (c'.1 + 1) − c.1 − 1 = c'.1 − c.1 ≥ 1`,
so `hookLength μ c.1 c'.2 = armLen + legLen + 1 ≥ 3`.

This bound is the geometric prerequisite for working with the rational
factor `(h_d − 1)² / (h_d (h_d − 2))` that appears in the GNW exchange
identity: `h_d ≥ 3` ensures `h_d − 1 ≥ 2 > 0` and `h_d − 2 ≥ 1 > 0`, so
both factors are nonzero in ℚ and ℕ subtraction is well-behaved. -/
private lemma hookLength_at_d_ge_3 {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hi : c.1 < c'.1) :
    3 ≤ hookLength μ c.1 c'.2 := by
  have h_col_lt : c'.2 < c.2 := corner_col_lt_of_row_lt hc hc' hi
  have hrowLen : μ.rowLen c.1 = c.2 + 1 := rowLen_of_isCorner hc
  have hcolLen : μ.colLen c'.2 = c'.1 + 1 := colLen_of_isCorner hc'
  unfold hookLength armLen legLen
  omega

/-- **The algebraic "easy half" of the GNW exchange identity (S52).**

For two distinct corners `c, c'` of `μ` with `c.1 < c'.1` (whence `c'.2 < c.2`
by `corner_col_lt_of_row_lt`), the four hook products satisfy
```
H(μ) · H((μ\c)\c') · (h_d - 1)² = H(μ\c) · H(μ\c') · h_d · (h_d - 2)
```
where `h_d = hookLength μ c.1 c'.2` is the hook length at the doubly-affected
cell `d = (c.1, c'.2)` (the unique cell in `arm(c) ∩ leg(c')`).

This is the multiplicative-only half of the GNW 1979 exchange identity for
`gnwProb_exchange`; the F-side "hard half" (joint K-induction on the
`gnwProb` sum) is deferred to S53+.

**Proof strategy.**  Apply `hookProd_ratio_formula` twice — to corner `c` on
`μ` and (via `isCorner_removeCorner_of_ne hc' hc hne.symm`) to corner `c`
on `μ\c'`.  The two ratio expressions share the same arm-of-`c` and
leg-of-`c` index sets `Finset.range c.2`, `Finset.range c.1` (since `c` has
the same `rowLen`/`colLen` in `μ` and `μ\c'`).  They agree pointwise off
the doubly-affected cell `d` by the S50 single-removal bridges
(`hookLength_removeCornerC'_arm_of_c_off_d`,
`hookLength_removeCornerC'_leg_of_c`).  At cell `d` itself the two arm
factors differ: `R₁`'s factor is `h_d / (h_d - 1)` while `R₂`'s factor is
`(h_d - 1) / (h_d - 2)` (using `hookLength (μ\c') c.1 c'.2 = h_d - 1` from
`hookLength_removeCorner_leg hc' hi`, since the cell lies in the leg of
`c'`).  Substituting both ratio formulas into the goal and clearing the
two non-zero d-factor denominators `(h_d - 1)`, `(h_d - 2)` (justified by
`h_d ≥ 3` from `hookLength_at_d_ge_3`) reduces the identity to a
polynomial equation discharged by `ring`.  `hookProd_removeCorner_swap`
identifies `H((μ\c')\c) = H((μ\c)\c')`. -/
private lemma hookProd_doubleRemove_factor
    {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') (hi : c.1 < c'.1) :
    (hookProd μ : ℚ) *
      (hookProd (removeCorner (removeCorner μ c hc) c'
          (isCorner_removeCorner_of_ne hc hc' hne)) : ℚ) *
      ((hookLength μ c.1 c'.2 : ℚ) - 1) ^ 2 =
    (hookProd (removeCorner μ c hc) : ℚ) *
      (hookProd (removeCorner μ c' hc') : ℚ) *
      (hookLength μ c.1 c'.2 : ℚ) * ((hookLength μ c.1 c'.2 : ℚ) - 2) := by
  -- Geometric setup
  have h_col_lt : c'.2 < c.2 := corner_col_lt_of_row_lt hc hc' hi
  have hc_in_ν₂ : isCorner (removeCorner μ c' hc') c :=
    isCorner_removeCorner_of_ne hc' hc hne.symm
  have hd_ge_3 : 3 ≤ hookLength μ c.1 c'.2 := hookLength_at_d_ge_3 hc hc' hi
  have hd_ge_3_Q : (3 : ℚ) ≤ (hookLength μ c.1 c'.2 : ℚ) := by exact_mod_cast hd_ge_3
  -- Non-zero side conditions in ℚ for the d-cell factors
  have hd_sub1_ne : (hookLength μ c.1 c'.2 : ℚ) - 1 ≠ 0 := by linarith
  have hd_sub2_ne : (hookLength μ c.1 c'.2 : ℚ) - 2 ≠ 0 := by linarith
  -- Hook products are non-zero (positive, cast to ℚ)
  have hHνc_ne : (hookProd (removeCorner μ c hc) : ℚ) ≠ 0 := hookProdQ_ne_zero _
  have hHνc'c_ne :
      (hookProd (removeCorner (removeCorner μ c' hc') c hc_in_ν₂) : ℚ) ≠ 0 :=
    hookProdQ_ne_zero _
  -- The two ratio formulas (corner c on μ, and corner c on μ\c')
  have hR1 := hookProd_ratio_formula hc
  have hR2 := hookProd_ratio_formula hc_in_ν₂
  -- removeCorner_swap: H((μ\c')\c) = H((μ\c)\c')
  have h_swap :
      hookProd (removeCorner (removeCorner μ c' hc') c hc_in_ν₂) =
      hookProd (removeCorner (removeCorner μ c hc) c'
        (isCorner_removeCorner_of_ne hc hc' hne)) :=
    (hookProd_removeCorner_swap hc hc' hne).symm
  -- d ∈ Finset.range c.2 (used by Finset.mul_prod_erase below)
  have hd_mem : c'.2 ∈ Finset.range c.2 := Finset.mem_range.mpr h_col_lt
  -- hookLength of d in μ\c' equals h_d - 1 (cell is in leg of c' since c.1 < c'.1)
  have h_d_in_ν : (hookLength (removeCorner μ c' hc') c.1 c'.2 : ℚ) =
      (hookLength μ c.1 c'.2 : ℚ) - 1 := by
    have h := hookLength_removeCorner_leg hc' hi
    have hQ : (hookLength (removeCorner μ c' hc') c.1 c'.2 : ℚ) + 1 =
        (hookLength μ c.1 c'.2 : ℚ) := by exact_mod_cast h
    linarith
  -- Pointwise: leg-of-c product is identical in μ vs μ\c' (S50 bridge)
  have h_leg_eq :
      (∏ r ∈ Finset.range c.1,
        (hookLength (removeCorner μ c' hc') r c.2 : ℚ) /
        ((hookLength (removeCorner μ c' hc') r c.2 : ℚ) - 1)) =
      (∏ r ∈ Finset.range c.1,
        (hookLength μ r c.2 : ℚ) / ((hookLength μ r c.2 : ℚ) - 1)) := by
    refine Finset.prod_congr rfl (fun r hr => ?_)
    rw [hookLength_removeCornerC'_leg_of_c hc hc' hi (Finset.mem_range.mp hr)]
  -- Pointwise: arm-of-c product over (range c.2).erase c'.2 is identical (S50 bridge)
  have h_arm_off_d_eq :
      (∏ s ∈ (Finset.range c.2).erase c'.2,
        (hookLength (removeCorner μ c' hc') c.1 s : ℚ) /
        ((hookLength (removeCorner μ c' hc') c.1 s : ℚ) - 1)) =
      (∏ s ∈ (Finset.range c.2).erase c'.2,
        (hookLength μ c.1 s : ℚ) / ((hookLength μ c.1 s : ℚ) - 1)) := by
    refine Finset.prod_congr rfl (fun s hs => ?_)
    obtain ⟨hs_ne, hs_lt⟩ := Finset.mem_erase.mp hs
    have hslt_c2 : s < c.2 := Finset.mem_range.mp hs_lt
    rw [hookLength_removeCornerC'_arm_of_c_off_d hc hc' hi hslt_c2 hs_ne]
  -- Decompose μ-arm product: extract d-factor h_d/(h_d-1)
  have h_arm_decomp_μ :
      (∏ s ∈ Finset.range c.2,
        (hookLength μ c.1 s : ℚ) / ((hookLength μ c.1 s : ℚ) - 1)) =
      ((hookLength μ c.1 c'.2 : ℚ) / ((hookLength μ c.1 c'.2 : ℚ) - 1)) *
      (∏ s ∈ (Finset.range c.2).erase c'.2,
        (hookLength μ c.1 s : ℚ) / ((hookLength μ c.1 s : ℚ) - 1)) :=
    (Finset.mul_prod_erase _ _ hd_mem).symm
  -- Decompose ν-arm product: extract d-factor (h_d-1)/(h_d-2)
  have h_arm_decomp_ν :
      (∏ s ∈ Finset.range c.2,
        (hookLength (removeCorner μ c' hc') c.1 s : ℚ) /
        ((hookLength (removeCorner μ c' hc') c.1 s : ℚ) - 1)) =
      (((hookLength μ c.1 c'.2 : ℚ) - 1) / ((hookLength μ c.1 c'.2 : ℚ) - 2)) *
      (∏ s ∈ (Finset.range c.2).erase c'.2,
        (hookLength μ c.1 s : ℚ) / ((hookLength μ c.1 s : ℚ) - 1)) := by
    have h0 :
        (∏ s ∈ Finset.range c.2,
          (hookLength (removeCorner μ c' hc') c.1 s : ℚ) /
          ((hookLength (removeCorner μ c' hc') c.1 s : ℚ) - 1)) =
        ((hookLength (removeCorner μ c' hc') c.1 c'.2 : ℚ) /
          ((hookLength (removeCorner μ c' hc') c.1 c'.2 : ℚ) - 1)) *
        (∏ s ∈ (Finset.range c.2).erase c'.2,
          (hookLength (removeCorner μ c' hc') c.1 s : ℚ) /
          ((hookLength (removeCorner μ c' hc') c.1 s : ℚ) - 1)) :=
      (Finset.mul_prod_erase _ _ hd_mem).symm
    rw [h0, h_d_in_ν, h_arm_off_d_eq]
    ring
  -- Substitute decompositions and h_leg_eq into hR1 and hR2
  rw [h_arm_decomp_μ] at hR1
  rw [h_arm_decomp_ν, h_leg_eq] at hR2
  -- Clear LHS divisions (hookProd ratios)
  rw [div_eq_iff hHνc_ne] at hR1
  rw [div_eq_iff hHνc'c_ne] at hR2
  -- Apply h_swap to make goal use H((μ\c')\c) instead of H((μ\c)\c')
  rw [← h_swap]
  -- Substitute hR1 and hR2 into the goal, then clear d-factor denominators
  rw [hR1, hR2]
  field_simp
  ring

/-- Arm cells (c.1, s) with s < c.2 belong to ν = removeCorner μ c hc. -/
private lemma arm_mem_nu {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c)
    {s : ℕ} (hs : s < c.2) : (c.1, s) ∈ removeCorner μ c hc := by
  rw [mem_removeCorner]
  constructor
  · -- (c.1, s) ∈ μ: rowLen μ c.1 = c.2 + 1 > s
    exact YoungDiagram.mem_iff_lt_rowLen.mpr (by rw [rowLen_of_isCorner hc]; omega)
  · -- (c.1, s) ≠ c: their second components differ
    intro h
    have : s = c.2 := congr_arg Prod.snd h
    omega

/-- Leg cells (r, c.2) with r < c.1 belong to ν = removeCorner μ c hc. -/
private lemma leg_mem_nu {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c)
    {r : ℕ} (hr : r < c.1) : (r, c.2) ∈ removeCorner μ c hc := by
  rw [mem_removeCorner]
  constructor
  · -- (r, c.2) ∈ μ: colLen μ c.2 = c.1 + 1 > r
    exact YoungDiagram.mem_iff_lt_colLen.mpr (by rw [colLen_of_isCorner hc]; omega)
  · -- (r, c.2) ≠ c: their first components differ
    intro h
    have : r = c.1 := congr_arg Prod.fst h
    omega

/-- The hookProd ratio for a corner c equals the product of h/(h-1) over arm and leg cells.
    Proof outline:
    1. hookProd(μ) = 1 × ∏_{x∈ν.cells} hookLength(μ,x)  [mul_prod_erase + corner = 1]
    2. ratio = ∏_{x∈ν.cells} hookLength(μ,x)/hookLength(ν,x)  [field_simp]
    3. armCells = {(i,s) : s < j} ⊆ ν.cells  [arm_mem_nu]
    4. legCells = {(r,j) : r < i} ⊆ ν.cells  [leg_mem_nu], disjoint from armCells
    5. restCells = ν.cells \ (armCells ∪ legCells): hookLength ratio = 1  [hookLength_eq_of_not_arm_leg]
    6. ∏_{arm} ratio = ∏_s hookLen(i,s)/(hookLen(i,s)-1)  [hookLength_removeCorner_arm]
    7. ∏_{leg} ratio = ∏_r hookLen(r,j)/(hookLen(r,j)-1)  [hookLength_removeCorner_leg]
    Blocked on: Finset.prod_union decomposition of ν.cells (~50 lines). -/
lemma hookProd_ratio_formula {μ : YoungDiagram} {c : ℕ × ℕ} (hc : isCorner μ c) :
    (hookProd μ : ℚ) / hookProd (removeCorner μ c hc) =
      (∏ s ∈ Finset.range c.2, (hookLength μ c.1 s : ℚ) / (hookLength μ c.1 s - 1)) *
      (∏ r ∈ Finset.range c.1, (hookLength μ r c.2 : ℚ) / (hookLength μ r c.2 - 1)) := by
  obtain ⟨i, j⟩ := c
  simp only [Prod.fst, Prod.snd]
  set ν := removeCorner μ (i, j) hc with hν_def
  -- ν.cells = μ.cells.erase (i,j) by definition
  have hν_cells : ν.cells = μ.cells.erase (i, j) := rfl
  have hcmem : (i, j) ∈ μ.cells := YoungDiagram.mem_cells.mpr hc.1
  have hcorner_one : (hookLength μ i j : ℚ) = 1 :=
    by exact_mod_cast hookLength_corner_eq_one hc
  -- hookProd μ = ∏_{x ∈ ν.cells} hookLength μ x  (corner factor = 1)
  have hμ_via_ν : (hookProd μ : ℚ) = ∏ x ∈ ν.cells, (hookLength μ x.1 x.2 : ℚ) := by
    simp only [hookProd, Nat.cast_prod]
    rw [← Finset.mul_prod_erase μ.cells (fun x => (hookLength μ x.1 x.2 : ℚ)) hcmem]
    simp only [Prod.fst, Prod.snd]
    rw [hcorner_one, one_mul, hν_cells]
  -- hookProd ν > 0
  have hνpos : 0 < (hookProd ν : ℚ) := by exact_mod_cast hookProd_pos ν
  have hν_ne : (hookProd ν : ℚ) ≠ 0 := ne_of_gt hνpos
  -- Define arm and leg cell finsets
  let armCells : Finset (ℕ × ℕ) := Finset.image (fun s => (i, s)) (Finset.range j)
  let legCells : Finset (ℕ × ℕ) := Finset.image (fun r => (r, j)) (Finset.range i)
  -- arm/leg subsets of ν.cells
  have harm_sub : armCells ⊆ ν.cells := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact YoungDiagram.mem_cells.mpr (arm_mem_nu hc (Finset.mem_range.mp hs))
  have hleg_sub : legCells ⊆ ν.cells := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact YoungDiagram.mem_cells.mpr (leg_mem_nu hc (Finset.mem_range.mp hr))
  -- arm ∩ leg = ∅ (arm cells have first coord i, leg cells have first coord < i)
  have hdisj : Disjoint armCells legCells := by
    simp only [armCells, legCells, Finset.disjoint_left, Finset.mem_image, Finset.mem_range]
    rintro _ ⟨s, _, rfl⟩ ⟨r, hr, h⟩
    simp [Prod.mk.injEq] at h
    omega
  -- Split ν.cells = armCells ∪ legCells ∪ restCells and derive ratio formula
  let restCells := ν.cells \ (armCells ∪ legCells)
  have harm_leg_sub : armCells ∪ legCells ⊆ ν.cells := Finset.union_subset harm_sub hleg_sub
  -- hookLength change: hν = hμ - 1 for arm/leg cells
  have harm_diff : ∀ s ∈ Finset.range j, (hookLength ν i s : ℚ) = (hookLength μ i s : ℚ) - 1 :=
    fun s hs => by
      have h := hookLength_removeCorner_arm hc (Finset.mem_range.mp hs)
      simp only [Prod.fst, Prod.snd] at h
      have hQ : (hookLength ν i s : ℚ) + 1 = hookLength μ i s := by exact_mod_cast h
      linarith
  have hleg_diff : ∀ r ∈ Finset.range i, (hookLength ν r j : ℚ) = (hookLength μ r j : ℚ) - 1 :=
    fun r hr => by
      have h := hookLength_removeCorner_leg hc (Finset.mem_range.mp hr)
      simp only [Prod.fst, Prod.snd] at h
      have hQ : (hookLength ν r j : ℚ) + 1 = hookLength μ r j := by exact_mod_cast h
      linarith
  have harm_ν_ne : ∀ s ∈ Finset.range j, (hookLength ν i s : ℚ) ≠ 0 :=
    fun s _ => Nat.cast_ne_zero.mpr (hookLength_pos ν i s).ne'
  have hleg_ν_ne : ∀ r ∈ Finset.range i, (hookLength ν r j : ℚ) ≠ 0 :=
    fun r _ => Nat.cast_ne_zero.mpr (hookLength_pos ν r j).ne'
  have hprod_arm_ν : (∏ s ∈ Finset.range j, (hookLength ν i s : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero harm_ν_ne
  have hprod_leg_ν : (∏ r ∈ Finset.range i, (hookLength ν r j : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero hleg_ν_ne
  -- rest cells: hookLength unchanged by removeCorner
  have hrest_inv : ∀ x ∈ restCells, hookLength ν x.1 x.2 = hookLength μ x.1 x.2 := by
    intro x hx
    obtain ⟨hxν, hxnot⟩ := Finset.mem_sdiff.mp hx
    have hxμ : x ∈ μ := ((mem_removeCorner hc).mp (YoungDiagram.mem_cells.mp hxν)).1
    have hxc : x ≠ (i, j) :=
      fun h => ((mem_removeCorner hc).mp (YoungDiagram.mem_cells.mp hxν)).2 h
    apply hookLength_eq_of_not_arm_leg hc hxμ hxc
    · intro ⟨h1, h2⟩
      exact hxnot (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨x.2, Finset.mem_range.mpr h2, Prod.ext h1.symm rfl⟩))
    · intro ⟨h1, h2⟩
      exact hxnot (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨x.1, Finset.mem_range.mpr h1, Prod.ext rfl h2.symm⟩))
  -- Key ℕ equality (avoids division): hookProd μ × ∏ hν_arm × ∏ hν_leg = hookProd ν × ∏ hμ_arm × ∏ hμ_leg
  have key_nat : hookProd μ *
      (∏ s ∈ Finset.range j, hookLength ν i s) * (∏ r ∈ Finset.range i, hookLength ν r j) =
      hookProd ν *
      (∏ s ∈ Finset.range j, hookLength μ i s) * (∏ r ∈ Finset.range i, hookLength μ r j) := by
    have h_μ : hookProd μ = ∏ x ∈ ν.cells, hookLength μ x.1 x.2 := by
      simp only [hookProd]
      rw [← Finset.mul_prod_erase μ.cells (fun x => hookLength μ x.1 x.2) hcmem]
      simp only [Prod.fst, Prod.snd, hookLength_corner_eq_one hc, one_mul, hν_cells]
    have h_ν : hookProd ν = ∏ x ∈ ν.cells, hookLength ν x.1 x.2 := rfl
    have harm_μ : ∏ s ∈ Finset.range j, hookLength μ i s =
        ∏ x ∈ armCells, hookLength μ x.1 x.2 := by
      simp only [armCells]
      rw [Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).2)]
      simp only [Prod.fst, Prod.snd]
    have harm_ν2 : ∏ s ∈ Finset.range j, hookLength ν i s =
        ∏ x ∈ armCells, hookLength ν x.1 x.2 := by
      simp only [armCells]
      rw [Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).2)]
      simp only [Prod.fst, Prod.snd]
    have hleg_μ : ∏ r ∈ Finset.range i, hookLength μ r j =
        ∏ x ∈ legCells, hookLength μ x.1 x.2 := by
      simp only [legCells]
      rw [Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).1)]
      simp only [Prod.fst, Prod.snd]
    have hleg_ν2 : ∏ r ∈ Finset.range i, hookLength ν r j =
        ∏ x ∈ legCells, hookLength ν x.1 x.2 := by
      simp only [legCells]
      rw [Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).1)]
      simp only [Prod.fst, Prod.snd]
    have hcells_eq : ν.cells = armCells ∪ legCells ∪ restCells :=
      (Finset.union_sdiff_of_subset harm_leg_sub).symm
    have hdisj_union : Disjoint (armCells ∪ legCells) restCells := disjoint_sdiff_self_right
    have hμ_split : ∏ x ∈ ν.cells, hookLength μ x.1 x.2 =
        (∏ x ∈ armCells, hookLength μ x.1 x.2) * (∏ x ∈ legCells, hookLength μ x.1 x.2) *
        (∏ x ∈ restCells, hookLength μ x.1 x.2) := by
      rw [hcells_eq, Finset.prod_union hdisj_union, Finset.prod_union hdisj]; ring
    have hν_split : ∏ x ∈ ν.cells, hookLength ν x.1 x.2 =
        (∏ x ∈ armCells, hookLength ν x.1 x.2) * (∏ x ∈ legCells, hookLength ν x.1 x.2) *
        (∏ x ∈ restCells, hookLength ν x.1 x.2) := by
      rw [hcells_eq, Finset.prod_union hdisj_union, Finset.prod_union hdisj]; ring
    rw [h_μ, h_ν, harm_μ, harm_ν2, hleg_μ, hleg_ν2, hμ_split, hν_split,
        Finset.prod_congr rfl hrest_inv]
    ring
  -- Cast ℕ equality to ℚ
  have key_Q : (hookProd μ : ℚ) * (∏ s ∈ Finset.range j, (hookLength ν i s : ℚ)) *
      (∏ r ∈ Finset.range i, (hookLength ν r j : ℚ)) =
      (hookProd ν : ℚ) * (∏ s ∈ Finset.range j, (hookLength μ i s : ℚ)) *
      (∏ r ∈ Finset.range i, (hookLength μ r j : ℚ)) := by exact_mod_cast key_nat
  have harm_prod_eq : ∏ s ∈ Finset.range j, ((hookLength μ i s : ℚ) - 1) =
      ∏ s ∈ Finset.range j, (hookLength ν i s : ℚ) :=
    Finset.prod_congr rfl (fun s hs => (harm_diff s hs).symm)
  have hleg_prod_eq : ∏ r ∈ Finset.range i, ((hookLength μ r j : ℚ) - 1) =
      ∏ r ∈ Finset.range i, (hookLength ν r j : ℚ) :=
    Finset.prod_congr rfl (fun r hr => (hleg_diff r hr).symm)
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib,
      harm_prod_eq, hleg_prod_eq, div_mul_div_comm,
      div_eq_div_iff hν_ne (mul_ne_zero hprod_arm_ν hprod_leg_ν)]
  linear_combination key_Q


-- ============================================================
-- Hook walk identity for generalized hook shapes [a, 1^b] (PART XIVb)
-- ============================================================

/-- Any corner of gHookYD a b ha (with b ≥ 1) is either (0, a-1) with a ≥ 2, or (b, 0).
    Proof: corners must be at row ends; row 0 ends at a-1, column 0 ends at b.
    When a=1: (0,0) has leg neighbor (1,0), so only (b,0) is a corner. -/
private lemma corners_gHookYD_cases (a b : ℕ) (ha : 0 < a) (hb : 0 < b) {c : ℕ × ℕ}
    (hc : isCorner (gHookYD a b ha) c) :
    (c = (0, a - 1) ∧ 1 < a) ∨ c = (b, 0) := by
  obtain ⟨i, j⟩ := c
  obtain ⟨hmem, hright, hbelow⟩ := hc
  rcases mem_gHookYD.mp hmem with ⟨hi0, hj⟩ | ⟨hi1, hi2, hj0⟩
  · -- (i, j) with i = 0, j < a
    subst hi0
    -- hright: (0, j+1) ∉ μ → j+1 ≥ a → j = a-1
    have hja : j = a - 1 := by
      have : ¬(j + 1 < a) := fun hlt =>
        hright (mem_gHookYD.mpr (Or.inl ⟨rfl, hlt⟩))
      omega
    subst hja
    left
    refine ⟨rfl, ?_⟩
    -- hbelow: (1, a-1) ∉ μ; but if a=1 then (1,0) ∈ μ (since b≥1), contradiction
    by_contra hle
    push_neg at hle
    have ha1 : a = 1 := Nat.le_antisymm hle ha
    subst ha1
    -- a-1 = 0, so (0, 0) ∈ μ and (1, 0) ∈ μ (since b ≥ 1)
    exact hbelow (mem_gHookYD.mpr (Or.inr ⟨Nat.one_pos, hb, rfl⟩))
  · -- (i, j) with 1 ≤ i ≤ b, j = 0
    subst hj0
    right
    -- hbelow: (i+1, 0) ∉ μ → i+1 > b → i = b
    have hib : i = b := by
      have : ¬(i + 1 ≤ b) := fun hle =>
        hbelow (mem_gHookYD.mpr (Or.inr ⟨by omega, hle, rfl⟩))
      omega
    exact ⟨hib, rfl⟩

/-- The hook walk identity for generalized hook shapes [a, 1^b] with b ≥ 1.
    Non-circular proof: hook_length_formula_gHookYD is proved independently,
    and removing a corner of gHookYD a b gives another gHookYD shape.
    Extends hook_walk_identity_atMostTwoRows to cover ≥3-row hook shapes. -/
lemma hook_walk_identity_gHookYD (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∑ c ∈ (corners (gHookYD a b ha)).attach,
      ((hookProd (gHookYD a b ha) : ℚ) /
       (hookProd (removeCorner (gHookYD a b ha) c.val
         (mem_corners.mp c.prop)) : ℚ))
    = ((gHookYD a b ha).card : ℚ) := by
  have hHP : (hookProd (gHookYD a b ha) : ℚ) ≠ 0 := hookProdQ_ne_zero _
  have hN : (gHookYD a b ha).card = a + b := gHookYD_card a b ha
  have hpos : 0 < (gHookYD a b ha).card := by rw [hN]; omega
  have hfact : (((gHookYD a b ha).card - 1).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  -- HLF for μ (proved independently, without hook_walk_identity)
  have hμ : (Fintype.card (StandardYoungTableau (gHookYD a b ha)) : ℚ) *
      hookProd (gHookYD a b ha) = (gHookYD a b ha).card.factorial :=
    by exact_mod_cast hook_length_formula_gHookYD a b ha
  -- Corner step: card(SYT(μ)) = Σ_c card(SYT(μ\c))
  have hstepQ : (Fintype.card (StandardYoungTableau (gHookYD a b ha)) : ℚ) =
      ∑ cx ∈ (corners (gHookYD a b ha)).attach,
        (Fintype.card (StandardYoungTableau
          (removeCorner (gHookYD a b ha) cx.val (mem_corners.mp cx.prop))) : ℚ) :=
    by exact_mod_cast card_SYT_corner_step (gHookYD a b ha) hpos
  -- HLF for each removeCorner: a corner removal gives another gHookYD shape
  have hμc : ∀ cx : { x // x ∈ corners (gHookYD a b ha) },
      (Fintype.card (StandardYoungTableau
        (removeCorner (gHookYD a b ha) cx.val (mem_corners.mp cx.prop))) : ℚ) *
      (hookProd (removeCorner (gHookYD a b ha) cx.val (mem_corners.mp cx.prop)) : ℚ) =
      (((gHookYD a b ha).card - 1).factorial : ℚ) := by
    intro ⟨c, hcx⟩
    have hcorner : isCorner (gHookYD a b ha) c := mem_corners.mp hcx
    rcases corners_gHookYD_cases a b ha hb hcorner with ⟨hceq, ha2⟩ | hceq
    · -- c = (0, a-1): removeCorner = gHookYD (a-1) b h'
      subst hceq
      rw [removeCorner_gHook_top a b ha ha2 hcorner]
      have hlf : Fintype.card (StandardYoungTableau (gHookYD (a - 1) b (by omega))) *
          hookProd (gHookYD (a - 1) b (by omega)) =
          (gHookYD (a - 1) b (by omega)).card.factorial :=
        hook_length_formula_gHookYD (a - 1) b (by omega)
      rw [gHookYD_card] at hlf
      have hfact_eq : a - 1 + b = (gHookYD a b ha).card - 1 := by rw [hN]; omega
      rw [hfact_eq] at hlf
      exact_mod_cast hlf
    · -- c = (b, 0): removeCorner = gHookYD a (b-1) ha
      subst hceq
      rw [removeCorner_gHook_bot a b ha hb hcorner]
      have hlf : Fintype.card (StandardYoungTableau (gHookYD a (b - 1) ha)) *
          hookProd (gHookYD a (b - 1) ha) =
          (gHookYD a (b - 1) ha).card.factorial :=
        hook_length_formula_gHookYD a (b - 1) ha
      rw [gHookYD_card] at hlf
      have hfact_eq : a + (b - 1) = (gHookYD a b ha).card - 1 := by rw [hN]; omega
      rw [hfact_eq] at hlf
      exact_mod_cast hlf
  -- μ.card! = μ.card × (μ.card-1)! as rationals
  have hfact_succ : ((gHookYD a b ha).card.factorial : ℚ) =
      ((gHookYD a b ha).card : ℚ) * (((gHookYD a b ha).card - 1).factorial : ℚ) := by
    cases hcard : (gHookYD a b ha).card with
    | zero => rw [hN] at hcard; omega
    | succ n =>
      rw [show (gHookYD a b ha).card - 1 = n by omega,
          show (gHookYD a b ha).card = n + 1 from hcard, Nat.factorial_succ]
      push_cast; ring
  -- Each summand: HP/HPc = card(SYT(μ\c)) × HP/(N-1)!
  have hterm : ∀ cx : { x // x ∈ corners (gHookYD a b ha) },
      (hookProd (gHookYD a b ha) : ℚ) /
      (hookProd (removeCorner (gHookYD a b ha) cx.val (mem_corners.mp cx.prop)) : ℚ) =
      (Fintype.card (StandardYoungTableau
        (removeCorner (gHookYD a b ha) cx.val (mem_corners.mp cx.prop))) : ℚ) *
      ((hookProd (gHookYD a b ha) : ℚ) / (((gHookYD a b ha).card - 1).factorial : ℚ)) := by
    intro ⟨c, hcx⟩
    have hHPc :
        (hookProd (removeCorner (gHookYD a b ha) c (mem_corners.mp hcx)) : ℚ) ≠ 0 :=
      hookProdQ_ne_zero _
    have hIHc := hμc ⟨c, hcx⟩
    rw [mul_div_assoc, div_eq_div_iff hHPc hfact]
    linear_combination -(hookProd (gHookYD a b ha) : ℚ) * hIHc
  -- Assemble: same algebra as hook_walk_identity_atMostTwoRows
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← hstepQ, mul_div_assoc, hμ, hfact_succ]
  field_simp [hfact]

-- ============================================================
-- PART XV: Transpose Duality and Hook Walk for ≤2-Column Shapes
-- ============================================================

/-
  We extend hook_walk_identity to cover shapes with at most 2 columns.
  Key tools:
  1. hookProd μ = hookProd μ.transpose  (hook lengths are symmetric under transpose)
  2. card(SYT μ) = card(SYT μ.transpose)  (bijection via T ↦ sytTranspose T)
  3. μ.colLen 2 = 0 → μ.transpose.rowLen 2 = 0  (via rowLen_transpose = colLen)
  4. hook_length_formula_atMostTwoCols: HLF for ≤2-col via transpose + atMostTwoRows
  5. hook_walk_identity_atMostTwoCols: same algebraic argument using HLF for ≤2-col
-/

/-- The cell count of μ.transpose equals that of μ (transpose is a bijection on cells). -/
private lemma card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  simp only [YoungDiagram.card, YoungDiagram.transpose,
    Equiv.finsetCongr_apply, Finset.card_map]

/-- Hook length at (i,j) in μ equals hook length at (j,i) in μ.transpose.
    Follows from rowLen_transpose (rowLen of μ.transpose at row j = colLen of μ at col j)
    and colLen_transpose, combined with the arithmetic definition of hookLength. -/
private lemma hookLength_transpose (μ : YoungDiagram) (i j : ℕ) :
    hookLength μ i j = hookLength μ.transpose j i := by
  unfold hookLength armLen legLen
  rw [YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose]
  omega

/-- The hook product is invariant under transposition:  ∏_{c ∈ μ} h(c) = ∏_{c ∈ μ.transpose} h(c).
    Proof: μ.transpose.cells = μ.cells.image Prod.swap (bijection), and h(j,i,μ.transpose) = h(i,j,μ). -/
private lemma hookProd_transpose (μ : YoungDiagram) : hookProd μ = hookProd μ.transpose := by
  simp only [hookProd]
  have hcells : μ.transpose.cells = μ.cells.image Prod.swap := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose,
      Finset.mem_image, Prod.exists]
    exact ⟨fun h => ⟨j, i, h, rfl⟩, fun ⟨a, b, hab, heq⟩ => by
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact hab⟩
  rw [hcells, Finset.prod_image (fun x _ y _ h => Prod.swap_injective h)]
  apply Finset.prod_congr rfl
  intro ⟨i, j⟩ _
  exact (hookLength_transpose μ i j).symm

/-- The transpose of a Standard Young Tableau: if T : SYT(μ), then sytTranspose T : SYT(μ.transpose).
    The entry at cell (i,j) of the transposed tableau is the entry of T at (j,i).
    Row-strict in μ.transpose ↔ col-strict in μ (and vice versa). -/
private def sytTranspose {μ : YoungDiagram} (T : StandardYoungTableau μ) :
    StandardYoungTableau μ.transpose where
  entry c := T.entry c.swap
  entry_zero c hc := T.entry_zero c.swap
    (by rwa [YoungDiagram.mem_transpose, Prod.swap_swap] at hc)
  entry_range c hc := by
    have hmem : c.swap ∈ μ := YoungDiagram.mem_transpose.mp hc
    have hrange := T.entry_range c.swap hmem
    exact ⟨hrange.1, hrange.2.trans_eq (card_transpose μ).symm⟩
  entry_injOn c₁ c₂ hc₁ hc₂ heq :=
    Prod.swap_injective (T.entry_injOn c₁.swap c₂.swap
      (YoungDiagram.mem_transpose.mp hc₁) (YoungDiagram.mem_transpose.mp hc₂) heq)
  row_strict i j₁ j₂ h₁ h₂ hlt :=
    T.col_strict j₁ j₂ i
      (YoungDiagram.mem_transpose.mp h₁) (YoungDiagram.mem_transpose.mp h₂) hlt
  col_strict i₁ i₂ j h₁ h₂ hlt :=
    T.row_strict j i₁ i₂
      (YoungDiagram.mem_transpose.mp h₁) (YoungDiagram.mem_transpose.mp h₂) hlt

/-- sytTranspose is injective: if two transposed tableaux agree, the originals agree. -/
private lemma sytTranspose_injective {μ : YoungDiagram} :
    Function.Injective (@sytTranspose μ) := by
  intro T₁ T₂ h
  apply StandardYoungTableau.ext
  funext c
  have : (sytTranspose T₁).entry c.swap = (sytTranspose T₂).entry c.swap :=
    congrFun (congrArg StandardYoungTableau.entry h) c.swap
  change T₁.entry c.swap.swap = T₂.entry c.swap.swap at this
  rwa [Prod.swap_swap, Prod.swap_swap] at this

/-- The number of SYT of shape μ equals the number of SYT of shape μ.transpose.
    Proof: sytTranspose is injective, and applying it to μ.transpose gives
    SYT(μ.transpose.transpose) ≃ SYT(μ) via transpose_transpose. -/
private lemma card_SYT_transpose (μ : YoungDiagram) :
    Fintype.card (StandardYoungTableau μ) = Fintype.card (StandardYoungTableau μ.transpose) := by
  apply le_antisymm
  · exact Fintype.card_le_of_injective sytTranspose sytTranspose_injective
  · have hle : Fintype.card (StandardYoungTableau μ.transpose) ≤
               Fintype.card (StandardYoungTableau μ.transpose.transpose) :=
      Fintype.card_le_of_injective sytTranspose sytTranspose_injective
    rw [YoungDiagram.transpose_transpose] at hle
    exact hle

/-- Removing a corner from a ≤2-column diagram preserves the ≤2-column property.
    Mirror of removeCorner_atMostTwoRows: colLen 2 = 0 iff no cell in column 2;
    removing a cell can only shrink the diagram. -/
private lemma removeCorner_atMostTwoCols {μ : YoungDiagram} {c : ℕ × ℕ}
    (h2 : μ.colLen 2 = 0) (hc : isCorner μ c) :
    (removeCorner μ c hc).colLen 2 = 0 := by
  rcases Nat.eq_zero_or_pos ((removeCorner μ c hc).colLen 2) with h | hpos
  · exact h
  · exfalso
    have hmem : (0, 2) ∈ removeCorner μ c hc :=
      YoungDiagram.mem_iff_lt_colLen.mpr hpos
    obtain ⟨hmem2, _⟩ := (mem_removeCorner hc).mp hmem
    have hlt := YoungDiagram.mem_iff_lt_colLen.mp hmem2
    omega

/-- **Hook-length formula for all YoungDiagrams with at most 2 columns.**
    Proof: transpose reduces this to hook_length_formula_atMostTwoRows via:
    - μ.colLen 2 = 0 → μ.transpose.rowLen 2 = 0
    - hookProd μ = hookProd μ.transpose
    - card(SYT μ) = card(SYT μ.transpose)
    - μ.card = μ.transpose.card -/
private theorem hook_length_formula_atMostTwoCols (μ : YoungDiagram) (h2 : μ.colLen 2 = 0) :
    Fintype.card (StandardYoungTableau μ) * hookProd μ = μ.card.factorial := by
  have h2t : μ.transpose.rowLen 2 = 0 := by rw [YoungDiagram.rowLen_transpose]; exact h2
  have hT := hook_length_formula_atMostTwoRows μ.transpose h2t
  rw [← card_SYT_transpose, ← hookProd_transpose, ← card_transpose] at hT
  exact hT

/-- The hook walk identity for at-most-2-column Young diagrams.
    Non-circular proof: hook_length_formula_atMostTwoCols proved without hook_walk_identity,
    and removing a corner of a ≤2-col shape gives another ≤2-col shape.
    Identical algebraic structure to hook_walk_identity_atMostTwoRows. -/
lemma hook_walk_identity_atMostTwoCols (μ : YoungDiagram) (h2 : μ.colLen 2 = 0)
    (hpos : 0 < μ.card) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / (hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) : ℚ))
    = (μ.card : ℚ) := by
  have hHP : (hookProd μ : ℚ) ≠ 0 := hookProdQ_ne_zero μ
  have hfact : ((μ.card - 1).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  -- HLF for μ (proved independently, without hook_walk_identity)
  have hμ : (Fintype.card (StandardYoungTableau μ) : ℚ) * hookProd μ = μ.card.factorial :=
    by exact_mod_cast hook_length_formula_atMostTwoCols μ h2
  -- HLF for each removeCorner (stays ≤2-col by removeCorner_atMostTwoCols)
  have hμc : ∀ cx : { x // x ∈ corners μ },
      (Fintype.card (StandardYoungTableau
        (removeCorner μ cx.val (mem_corners.mp cx.prop))) : ℚ) *
      (hookProd (removeCorner μ cx.val (mem_corners.mp cx.prop)) : ℚ) =
      ((μ.card - 1).factorial : ℚ) := by
    intro ⟨c, hcx⟩
    have h2c := removeCorner_atMostTwoCols h2 (mem_corners.mp hcx)
    have hlf := hook_length_formula_atMostTwoCols _ h2c
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

-- ============================================================
-- PART XVI: Hook Walk Identity for [a, 2, 1] Shapes (a ≥ 3)
-- ============================================================
/-
  For a ≥ 3, the [a, 2, 1] Young diagram has:
  - n = a + 3 cells
  - Row 0: length a, Row 1: length 2, Row 2: length 1
  - 3 corners: (0, a-1), (1, 1), (2, 0)

  hook_walk_identity is proved directly via hookProd_ratio_formula:
    R(0,a-1) = (a+2)·a·(a-2)/[(a+1)·(a-1)]
    R(1,1)   = 3·a / [2·(a-1)]
    R(2,0)   = 3·(a+2) / [2·(a+1)]
    Sum      = a+3  (verified by ring)
-/

private def a21YD (a : ℕ) (ha : 3 ≤ a) : YoungDiagram where
  cells := (Finset.range a).image (Prod.mk 0) ∪
           (Finset.range 2).image (Prod.mk 1) ∪
           ({(2, 0)} : Finset (ℕ × ℕ))
  isLowerSet := by
    intro ⟨x, y⟩ ⟨u, v⟩ huv hmem
    simp only [Prod.mk_le_mk] at huv
    obtain ⟨hxu, hyv⟩ := huv
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image, Finset.mem_range,
               Finset.mem_singleton, Prod.mk.injEq] at hmem ⊢
    rcases hmem with ((⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩) | ⟨rfl, rfl⟩)
    · -- (u,v) = (0,k), k < a; x ≤ 0, y ≤ k
      left; left; exact ⟨y, by omega, (Nat.le_zero.mp hxu).symm, by omega⟩
    · -- (u,v) = (1,k), k < 2; x ≤ 1, y ≤ k < 2
      rcases Nat.eq_or_gt_of_le (Nat.zero_le x) with rfl | hxp
      · left; left; exact ⟨y, by omega, rfl, rfl⟩
      · left; right; exact ⟨y, by omega, by omega, rfl⟩
    · -- (u,v) = (2,0); y = 0
      have hy0 : y = 0 := Nat.le_zero.mp hyv
      subst hy0
      interval_cases x
      · left; left; exact ⟨0, by omega, rfl, rfl⟩
      · left; right; exact ⟨0, by omega, rfl, rfl⟩
      · right; rfl

private lemma mem_a21YD {a : ℕ} {ha : 3 ≤ a} {i j : ℕ} :
    (i, j) ∈ a21YD a ha ↔ (i = 0 ∧ j < a) ∨ (i = 1 ∧ j < 2) ∨ (i = 2 ∧ j = 0) := by
  simp only [a21YD, YoungDiagram.mem_mk, Finset.mem_union, Finset.mem_image,
             Finset.mem_range, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ((⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩) | ⟨rfl, rfl⟩)
    · left; exact ⟨rfl, hk⟩
    · right; left; exact ⟨rfl, hk⟩
    · right; right; exact ⟨rfl, rfl⟩
  · rintro (⟨rfl, hj⟩ | ⟨rfl, hj⟩ | ⟨rfl, rfl⟩)
    · left; left; exact ⟨j, hj, rfl, rfl⟩
    · left; right; exact ⟨j, hj, rfl, rfl⟩
    · right; rfl

private lemma a21YD_card (a : ℕ) (ha : 3 ≤ a) : (a21YD a ha).card = a + 3 := by
  unfold YoungDiagram.card a21YD
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
        Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
        Finset.card_singleton, Finset.card_range, Finset.card_range]; omega
  · apply Finset.disjoint_left.mpr
    intro ⟨x, y⟩ hx hy
    simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
    obtain ⟨_, _, rfl, rfl⟩ := hx; simp at hy
  · apply Finset.disjoint_left.mpr
    intro ⟨x, y⟩ hx hy
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range,
               Finset.mem_singleton, Prod.mk.injEq] at hx hy
    rcases hx with (⟨k, _, rfl, rfl⟩ | ⟨k, _, rfl, rfl⟩)
    · obtain ⟨rfl, rfl⟩ := hy; omega
    · obtain ⟨rfl, rfl⟩ := hy; omega

-- Row lengths
private lemma rowLen_a21YD_zero (a : ℕ) (ha : 3 ≤ a) : (a21YD a ha).rowLen 0 = a := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]; simp [mem_a21YD]
  · cases a with
    | zero => omega
    | succ a =>
      have := YoungDiagram.mem_iff_lt_rowLen.mp
        (mem_a21YD.mpr (Or.inl ⟨rfl, Nat.lt_succ_self a⟩))
      omega

private lemma rowLen_a21YD_one (a : ℕ) (ha : 3 ≤ a) : (a21YD a ha).rowLen 1 = 2 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]; simp [mem_a21YD]; omega
  · have := YoungDiagram.mem_iff_lt_rowLen.mp
      (mem_a21YD.mpr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
    omega

private lemma rowLen_a21YD_two (a : ℕ) (ha : 3 ≤ a) : (a21YD a ha).rowLen 2 = 1 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]; simp [mem_a21YD]; omega
  · have := YoungDiagram.mem_iff_lt_rowLen.mp
      (mem_a21YD.mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    omega

private lemma rowLen_a21YD_ge_three (a : ℕ) (ha : 3 ≤ a) {i : ℕ} (hi : 3 ≤ i) :
    (a21YD a ha).rowLen i = 0 := by
  rw [← not_lt, ← YoungDiagram.mem_iff_lt_rowLen]
  simp [mem_a21YD]; omega

-- Column lengths
private lemma colLen_a21YD_zero (a : ℕ) (ha : 3 ≤ a) : (a21YD a ha).colLen 0 = 3 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]; simp [mem_a21YD]; omega
  · have := YoungDiagram.mem_iff_lt_colLen.mp
      (mem_a21YD.mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    omega

private lemma colLen_a21YD_one (a : ℕ) (ha : 3 ≤ a) : (a21YD a ha).colLen 1 = 2 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]; simp [mem_a21YD]; omega
  · have := YoungDiagram.mem_iff_lt_colLen.mp
      (mem_a21YD.mpr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
    omega

private lemma colLen_a21YD_mid {a : ℕ} (ha : 3 ≤ a) {j : ℕ} (hj2 : 2 ≤ j) (hja : j < a) :
    (a21YD a ha).colLen j = 1 := by
  apply Nat.le_antisymm
  · rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]; simp [mem_a21YD]; omega
  · have := YoungDiagram.mem_iff_lt_colLen.mp
      (mem_a21YD.mpr (Or.inl ⟨rfl, hja⟩))
    omega

private lemma colLen_a21YD_ge_a {a : ℕ} (ha : 3 ≤ a) {j : ℕ} (hja : a ≤ j) :
    (a21YD a ha).colLen j = 0 := by
  rw [← not_lt, ← YoungDiagram.mem_iff_lt_colLen]
  simp [mem_a21YD]; omega

-- Hook lengths
private lemma hookLength_a21YD_00 (a : ℕ) (ha : 3 ≤ a) :
    hookLength (a21YD a ha) 0 0 = a + 2 := by
  have hcell : (0, 0) ∈ a21YD a ha := mem_a21YD.mpr (Or.inl ⟨rfl, by omega⟩)
  have heq := hookLength_add_eq (a21YD a ha) hcell
  rw [rowLen_a21YD_zero, colLen_a21YD_zero] at heq; omega

private lemma hookLength_a21YD_01 (a : ℕ) (ha : 3 ≤ a) :
    hookLength (a21YD a ha) 0 1 = a := by
  have hcell : (0, 1) ∈ a21YD a ha := mem_a21YD.mpr (Or.inl ⟨rfl, by omega⟩)
  have heq := hookLength_add_eq (a21YD a ha) hcell
  rw [rowLen_a21YD_zero, colLen_a21YD_one] at heq; omega

private lemma hookLength_a21YD_0j {a : ℕ} (ha : 3 ≤ a) {j : ℕ} (hj2 : 2 ≤ j) (hja : j < a) :
    hookLength (a21YD a ha) 0 j = a - j := by
  have hcell : (0, j) ∈ a21YD a ha := mem_a21YD.mpr (Or.inl ⟨rfl, hja⟩)
  have heq := hookLength_add_eq (a21YD a ha) hcell
  rw [rowLen_a21YD_zero, colLen_a21YD_mid ha hj2 hja] at heq; omega

private lemma hookLength_a21YD_10 (a : ℕ) (ha : 3 ≤ a) :
    hookLength (a21YD a ha) 1 0 = 3 := by
  have hcell : (1, 0) ∈ a21YD a ha := mem_a21YD.mpr (Or.inr (Or.inl ⟨rfl, by omega⟩))
  have heq := hookLength_add_eq (a21YD a ha) hcell
  rw [rowLen_a21YD_one, colLen_a21YD_zero] at heq; omega

private lemma hookLength_a21YD_11 (a : ℕ) (ha : 3 ≤ a) :
    hookLength (a21YD a ha) 1 1 = 1 := by
  have hcell : (1, 1) ∈ a21YD a ha := mem_a21YD.mpr (Or.inr (Or.inl ⟨rfl, by omega⟩))
  have heq := hookLength_add_eq (a21YD a ha) hcell
  rw [rowLen_a21YD_one, colLen_a21YD_one] at heq; omega

private lemma hookLength_a21YD_20 (a : ℕ) (ha : 3 ≤ a) :
    hookLength (a21YD a ha) 2 0 = 1 := by
  have hcell : (2, 0) ∈ a21YD a ha := mem_a21YD.mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have heq := hookLength_add_eq (a21YD a ha) hcell
  rw [rowLen_a21YD_two, colLen_a21YD_zero] at heq; omega

-- Corners
private lemma isCorner_a21YD_top (a : ℕ) (ha : 3 ≤ a) :
    isCorner (a21YD a ha) (0, a - 1) := by
  refine ⟨mem_a21YD.mpr (Or.inl ⟨rfl, by omega⟩), ?_, ?_⟩
  · simp [mem_a21YD]; omega
  · simp [mem_a21YD]; omega

private lemma isCorner_a21YD_mid (a : ℕ) (ha : 3 ≤ a) :
    isCorner (a21YD a ha) (1, 1) := by
  refine ⟨mem_a21YD.mpr (Or.inr (Or.inl ⟨rfl, by omega⟩)), ?_, ?_⟩
  · simp [mem_a21YD]; omega
  · simp [mem_a21YD]; omega

private lemma isCorner_a21YD_bot (a : ℕ) (ha : 3 ≤ a) :
    isCorner (a21YD a ha) (2, 0) := by
  refine ⟨mem_a21YD.mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_, ?_⟩
  · simp [mem_a21YD]; omega
  · simp [mem_a21YD]; omega

private lemma corners_a21YD_cases (a : ℕ) (ha : 3 ≤ a) {c : ℕ × ℕ}
    (hc : isCorner (a21YD a ha) c) :
    c = (0, a - 1) ∨ c = (1, 1) ∨ c = (2, 0) := by
  obtain ⟨i, j⟩ := c
  obtain ⟨hmem, hright, hbelow⟩ := hc
  rcases mem_a21YD.mp hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · subst hi
    left
    have hja : j = a - 1 := by
      have : ¬(j + 1 < a) := fun hlt => hright (mem_a21YD.mpr (Or.inl ⟨rfl, hlt⟩))
      omega
    rw [hja]
  · subst hi
    right; left
    have hj1 : j = 1 := by
      have : ¬(j + 1 < 2) := fun hlt => hright (mem_a21YD.mpr (Or.inr (Or.inl ⟨rfl, hlt⟩)))
      omega
    rw [hj1]
  · subst hi; subst hj
    right; right; rfl

private lemma corners_a21YD (a : ℕ) (ha : 3 ≤ a) :
    corners (a21YD a ha) = {(0, a - 1), (1, 1), (2, 0)} := by
  ext ⟨i, j⟩
  simp only [mem_corners, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · intro hc
    rcases corners_a21YD_cases a ha hc with rfl | rfl | rfl
    · left; exact ⟨rfl, rfl⟩
    · right; left; exact ⟨rfl, rfl⟩
    · right; right; exact ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact isCorner_a21YD_top a ha
    · exact isCorner_a21YD_mid a ha
    · exact isCorner_a21YD_bot a ha

-- Telescoping product: ∏_{k ∈ Ico 1 (n+1)} (k+1)/k = n+1
private lemma tele_prod (n : ℕ) :
    ∏ k ∈ Finset.Ico 1 (n + 1), ((k : ℚ) + 1) / (k : ℚ) = (n : ℚ) + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnotin : n + 1 ∉ Finset.Ico 1 (n + 1) := by simp [Finset.mem_Ico]
    rw [show Finset.Ico 1 (n + 1 + 1) = insert (n + 1) (Finset.Ico 1 (n + 1)) from by
      ext k; simp [Finset.mem_Ico]; omega]
    rw [Finset.prod_insert hnotin, ih]
    have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
    field_simp
    push_cast; ring

-- Tail arm product for corner (0, a-1): ∏_{s ∈ Ico 2 (a-1)} (a-s)/(a-s-1) = a-2
private lemma tail_prod_a21YD (a : ℕ) (ha : 3 ≤ a) :
    ∏ s ∈ Finset.Ico 2 (a - 1), ((a : ℚ) - s) / ((a : ℚ) - s - 1) = (a : ℚ) - 2 := by
  -- Rewrite RHS as tele_prod(a-3)
  have ha3_cast : (a - 3 : ℕ : ℚ) + 1 = (a : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 3 ≤ a)]; push_cast; ring
  rw [← ha3_cast, ← tele_prod (a - 3)]
  -- Bijection: s ↦ a-1-s from Ico 2 (a-1) to Ico 1 (a-3+1)
  apply Finset.prod_bij' (fun s _ => a - 1 - s) (fun k _ => a - 1 - k)
  · intro s hs; simp only [Finset.mem_Ico] at hs ⊢; omega
  · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
  · intro s hs; simp only [Finset.mem_Ico] at hs; omega
  · intro k hk; simp only [Finset.mem_Ico] at hk; omega
  · intro s hs
    simp only [Finset.mem_Ico] at hs
    have hle : s + 1 ≤ a := by omega
    have hcast : (a - 1 - s : ℕ : ℚ) = (a : ℚ) - s - 1 := by
      rw [show a - 1 - s = a - (s + 1) from by omega, Nat.cast_sub hle]
      push_cast; ring
    rw [hcast]; ring

/-- The hook walk identity for [a, 2, 1] shapes (a ≥ 3).
    Non-circular proof: computed directly via hookProd_ratio_formula.
    The three corner ratios sum to a+3 by ring arithmetic. -/
private lemma hook_walk_identity_a21YD (a : ℕ) (ha : 3 ≤ a) :
    ∑ c ∈ (corners (a21YD a ha)).attach,
      ((hookProd (a21YD a ha) : ℚ) /
       (hookProd (removeCorner (a21YD a ha) c.val (mem_corners.mp c.prop)) : ℚ))
    = ((a21YD a ha).card : ℚ) := by
  -- Setup
  set μ := a21YD a ha with hμ_def
  rw [a21YD_card]
  -- isCorner witnesses
  have h_top := isCorner_a21YD_top a ha
  have h_mid := isCorner_a21YD_mid a ha
  have h_bot := isCorner_a21YD_bot a ha
  -- Corners identification and distinctness
  have hcorners : corners μ = {(0, a - 1), (1, 1), (2, 0)} := corners_a21YD a ha
  have hd01 : (0, a - 1) ≠ (1, 1) := by simp [Prod.mk.injEq]
  have hd02 : (0, a - 1) ≠ (2, 0) := by simp [Prod.mk.injEq]
  have hd12 : (1, 1) ≠ (2, 0) := by simp [Prod.mk.injEq]
  -- Compute each ratio via hookProd_ratio_formula
  -- R_top: ratio at corner (0, a-1)
  have hR_top : (hookProd μ : ℚ) / hookProd (removeCorner μ (0, a - 1) h_top) =
      ((a : ℚ) + 2) * a * ((a : ℚ) - 2) / (((a : ℚ) + 1) * ((a : ℚ) - 1)) := by
    rw [hookProd_ratio_formula h_top]
    simp only [Prod.fst, Prod.snd, Finset.prod_empty, mul_one]
    -- arm product = ∏_{s ∈ range(a-1)} h(0,s)/(h(0,s)-1)
    -- Split: {0} ∪ {1} ∪ Ico 2 (a-1)
    have hsplit : Finset.range (a - 1) = {0} ∪ {1} ∪ Finset.Ico 2 (a - 1) := by
      ext k; simp [Finset.mem_Ico, Finset.mem_range]; omega
    have hdisj1 : Disjoint ({0} : Finset ℕ) {1} := by simp
    have hdisj2 : Disjoint ({0} ∪ {1} : Finset ℕ) (Finset.Ico 2 (a - 1)) := by
      simp [Finset.disjoint_left, Finset.mem_Ico]; omega
    rw [hsplit, Finset.prod_union hdisj2, Finset.prod_union hdisj1,
        Finset.prod_singleton, Finset.prod_singleton]
    simp only [hookLength_a21YD_00, hookLength_a21YD_01]
    -- Rewrite tail product: convert hookLength terms to (a-s:ℚ) form, then apply tail_prod_a21YD
    have htail : ∏ s ∈ Finset.Ico 2 (a - 1),
        ((hookLength (a21YD a ha) 0 s : ℚ) / ((hookLength (a21YD a ha) 0 s : ℚ) - 1)) =
        (a : ℚ) - 2 := by
      rw [show ∏ s ∈ Finset.Ico 2 (a - 1),
              ((hookLength (a21YD a ha) 0 s : ℚ) / ((hookLength (a21YD a ha) 0 s : ℚ) - 1)) =
              ∏ s ∈ Finset.Ico 2 (a - 1), ((a : ℚ) - s) / ((a : ℚ) - s - 1) from
          Finset.prod_congr rfl (fun s hs => by
            simp only [Finset.mem_Ico] at hs
            rw [hookLength_a21YD_0j ha (by omega) (by omega)]
            push_cast [Nat.cast_sub (show s ≤ a by omega)])]
      exact tail_prod_a21YD a ha
    rw [htail]
    have ha1 : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    have ha2 : (1 : ℚ) ≤ (a : ℚ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ a)]; linarith
    push_cast [Nat.cast_sub (by omega : 2 ≤ a), Nat.cast_sub (by omega : 1 ≤ a)]
    field_simp
    ring
  -- R_mid: ratio at corner (1, 1)
  have hR_mid : (hookProd μ : ℚ) / hookProd (removeCorner μ (1, 1) h_mid) =
      3 * (a : ℚ) / (2 * ((a : ℚ) - 1)) := by
    rw [hookProd_ratio_formula h_mid]
    simp only [Prod.fst, Prod.snd,
               Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    simp only [hookLength_a21YD_10, hookLength_a21YD_01]
    push_cast [Nat.cast_sub (by omega : 1 ≤ a)]
    field_simp; ring
  -- R_bot: ratio at corner (2, 0)
  have hR_bot : (hookProd μ : ℚ) / hookProd (removeCorner μ (2, 0) h_bot) =
      3 * ((a : ℚ) + 2) / (2 * ((a : ℚ) + 1)) := by
    rw [hookProd_ratio_formula h_bot]
    simp only [Prod.fst, Prod.snd, Finset.prod_empty, one_mul]
    -- leg product = ∏_{r ∈ range 2} h(r,0)/(h(r,0)-1)
    rw [show Finset.range 2 = {0} ∪ {1} from by ext k; simp; omega]
    rw [Finset.prod_union (by simp), Finset.prod_singleton, Finset.prod_singleton]
    simp only [hookLength_a21YD_00, hookLength_a21YD_10]
    field_simp; ring
  -- Rewrite each summand using its ratio value
  have hterm : ∀ cx : {x // x ∈ corners μ},
      (hookProd μ : ℚ) /
      hookProd (removeCorner μ cx.val (mem_corners.mp cx.prop)) =
      if cx.val = (0, a - 1) then ((a : ℚ) + 2) * a * ((a : ℚ) - 2) / (((a : ℚ) + 1) * ((a : ℚ) - 1))
      else if cx.val = (1, 1) then 3 * (a : ℚ) / (2 * ((a : ℚ) - 1))
      else 3 * ((a : ℚ) + 2) / (2 * ((a : ℚ) + 1)) := by
    intro ⟨c, hcx⟩
    rcases corners_a21YD_cases a ha (mem_corners.mp hcx) with rfl | rfl | rfl
    · rw [removeCorner_proof_irrel _ _ (mem_corners.mp hcx) h_top, hR_top]
      simp
    · rw [removeCorner_proof_irrel _ _ (mem_corners.mp hcx) h_mid, hR_mid]
      simp [show (1, 1) ≠ (0, a - 1) from by simp [Prod.mk.injEq]]
    · rw [removeCorner_proof_irrel _ _ (mem_corners.mp hcx) h_bot, hR_bot]
      simp [show (2, 0) ≠ (0, a - 1) from by simp [Prod.mk.injEq],
            show (2, 0) ≠ (1, 1) from by simp [Prod.mk.injEq]]
  simp_rw [hterm]
  -- Convert from sum over attach to sum over corners μ, then substitute hcorners
  rw [Finset.sum_attach]
  rw [hcorners]
  rw [show (({(0, a - 1), (1, 1), (2, 0)} : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ)) =
      insert (0, a - 1) (insert (1, 1) {(2, 0)}) from rfl]
  rw [Finset.sum_insert (by simp [Prod.mk.injEq]; omega),
      Finset.sum_insert (by simp [Prod.mk.injEq]),
      Finset.sum_singleton]
  -- Each term evaluates to its ratio value
  simp only [if_true, show (0, a - 1) = (0, a - 1) from rfl,
             show (1, 1) ≠ (0, a - 1) from by simp [Prod.mk.injEq],
             show (2, 0) ≠ (0, a - 1) from by simp [Prod.mk.injEq],
             show (2, 0) ≠ (1, 1) from by simp [Prod.mk.injEq],
             ite_true, ite_false]
  -- Sum = a+3
  push_cast [Nat.cast_sub (by omega : 2 ≤ a), Nat.cast_sub (by omega : 1 ≤ a)]
  field_simp
  ring

-- ============================================================
-- PART XIVc: Hook walk identity for exactly-3-row Young diagrams
-- Direct computation: no HLF needed (avoids circularity)
-- ============================================================

/-
  For a 3-row Young diagram μ with row lengths a = rowLen 0 ≥ b = rowLen 1 ≥ c = rowLen 2 ≥ 1
  and rowLen 3 = 0, we prove the hook walk identity directly:

    ∑_{corner ∈ corners μ} HP(μ)/HP(μ\corner) = a + b + c

  The corners are exactly:
    • (2, c-1)          always (since c ≥ 1 and rowLen 3 = 0)
    • (1, b-1)          iff b > c
    • (0, a-1)          iff a > b

  For each corner (i₀, j₀), hookProd_ratio_formula gives:
    HP(μ)/HP(μ\corner) = ∏_{s<j₀} h(i₀,s)/(h(i₀,s)−1) × ∏_{r<i₀} h(r,j₀)/(h(r,j₀)−1)

  Since colLen(s) = 3 for s < c, = 2 for c ≤ s < b, = 1 for b ≤ s < a (from rowLen 3=0),
  the hook lengths are: h(i,j) = rowLen(i) + colLen(j) − i − j − 1. Each arm/leg product
  telescopes to a simple fraction. The sum of all ratios equals a+b+c = μ.card.

  This is NON-CIRCULAR: hookProd_ratio_formula is proved without HLF, and the product
  computations are pure arithmetic about hook lengths.
-/

/-- colLen(s) = 3 for s < rowLen 2, when rowLen 3 = 0.
    Proof: (2,s) ∈ μ (so 3 rows contribute) and (3,s) ∉ μ (rowLen 3 = 0). -/
private lemma threeRow_colLen_lt {μ : YoungDiagram} {s : ℕ}
    (h3 : μ.rowLen 3 = 0) (hs : s < μ.rowLen 2) : μ.colLen s = 3 := by
  apply Nat.le_antisymm
  · -- colLen ≤ 3: (3,s) ∉ μ (since rowLen 3 = 0)
    by_contra hlt
    push_neg at hlt
    have h3s : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h3s
    omega
  · -- colLen ≥ 3: (2,s) ∈ μ
    exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs)

/-- colLen(s) = 2 for rowLen 2 ≤ s < rowLen 1, when rowLen 3 = 0. -/
private lemma threeRow_colLen_mid {μ : YoungDiagram} {s : ℕ}
    (h3 : μ.rowLen 3 = 0) (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    μ.colLen s = 2 := by
  apply Nat.le_antisymm
  · -- colLen ≤ 2: (2,s) ∉ μ (rowLen 2 ≤ s)
    by_contra hlt
    push_neg at hlt
    have h2s : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h2s; omega
  · -- colLen ≥ 2: (1,s) ∈ μ
    exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- hookLength μ 2 s = rowLen 2 − s when (2,s) ∈ μ and rowLen 3 = 0. -/
private lemma threeRow_hookLen_row2 {μ : YoungDiagram} {s : ℕ}
    (h3 : μ.rowLen 3 = 0) (hmem : (2, s) ∈ μ) :
    hookLength μ 2 s = μ.rowLen 2 - s := by
  have hs : s < μ.rowLen 2 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [threeRow_colLen_lt h3 hs] at key
  omega

/-- hookLength μ 1 s = rowLen 1 − s + 1 when (1,s) ∈ μ, s < rowLen 2, and rowLen 3 = 0. -/
private lemma threeRow_hookLen_row1_lt {μ : YoungDiagram} {s : ℕ}
    (h3 : μ.rowLen 3 = 0) (hmem : (1, s) ∈ μ) (hs : s < μ.rowLen 2) :
    hookLength μ 1 s = μ.rowLen 1 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [threeRow_colLen_lt h3 hs] at key
  have hs1 : s < μ.rowLen 1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  omega

/-- hookLength μ 1 s = rowLen 1 − s when (1,s) ∈ μ, rowLen 2 ≤ s, and rowLen 3 = 0. -/
private lemma threeRow_hookLen_row1_ge {μ : YoungDiagram} {s : ℕ}
    (h3 : μ.rowLen 3 = 0) (hmem : (1, s) ∈ μ) (hs : μ.rowLen 2 ≤ s) :
    hookLength μ 1 s = μ.rowLen 1 - s := by
  have hs1 : s < μ.rowLen 1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [threeRow_colLen_mid h3 hs hs1] at key
  omega

/-- hookLength μ 0 s = rowLen 0 − s + 2 when (0,s) ∈ μ, s < rowLen 2, rowLen 3 = 0. -/
private lemma threeRow_hookLen_row0_lt {μ : YoungDiagram} {s : ℕ}
    (h3 : μ.rowLen 3 = 0) (hmem : (0, s) ∈ μ) (hs : s < μ.rowLen 2) :
    hookLength μ 0 s = μ.rowLen 0 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [threeRow_colLen_lt h3 hs] at key
  have hs0 : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  omega

/-- hookLength μ 0 s = rowLen 0 − s + 1 when (0,s) ∈ μ, rowLen 2 ≤ s < rowLen 1, rowLen 3 = 0. -/
private lemma threeRow_hookLen_row0_mid {μ : YoungDiagram} {s : ℕ}
    (h3 : μ.rowLen 3 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 2 ≤ s)
    (hs_lt : s < μ.rowLen 1) :
    hookLength μ 0 s = μ.rowLen 0 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [threeRow_colLen_mid h3 hs_ge hs_lt] at key
  have hs0 : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  omega

/-- hookLength μ 0 s = rowLen 0 − s when (0,s) ∈ μ, rowLen 1 ≤ s, rowLen 3 = 0. -/
private lemma threeRow_hookLen_row0_ge {μ : YoungDiagram} {s : ℕ}
    (h3 : μ.rowLen 3 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 1 ≤ s) :
    hookLength μ 0 s = μ.rowLen 0 - s := by
  have hs0 : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  have hcl : μ.colLen s = 1 := by
    apply Nat.le_antisymm
    · by_contra hlt; push_neg at hlt
      have h1s : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
      have := YoungDiagram.mem_iff_lt_rowLen.mp h1s; omega
    · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs0)
  rw [hcl] at key; omega

/-- Telescoping product identity: ∏_{s=0}^{m-1} (K−s)/(K−s−1) = K/(K−m)
    for K > m (so all denominators are positive). -/
private lemma prod_div_telescope (K m : ℕ) (hKm : m < K) :
    ∏ s ∈ Finset.range m, ((K : ℚ) - s) / ((K : ℚ) - s - 1) =
    (K : ℚ) / ((K : ℚ) - m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hKm' : m < K := Nat.lt_of_succ_lt hKm
    rw [Finset.prod_range_succ, ih hKm']
    have hd1 : (K : ℚ) - ↑m - 1 ≠ 0 := by
      have : m + 1 < K := hKm; exact_mod_cast (by push_cast; omega)
    have hd2 : (K : ℚ) - (↑m + 1) ≠ 0 := by
      have : m + 1 < K := hKm; exact_mod_cast (by push_cast; omega)
    have hd3 : (K : ℚ) - ↑m ≠ 0 := by
      have : m < K := hKm'; exact_mod_cast (by push_cast; omega)
    push_cast
    field_simp [hd1, hd2, hd3]
    ring

/-- For the arm of corner (2, c−1) of a 3-row shape, the product telescopes to rowLen 2.
    ∏_{s ∈ range(c−1)} h(2,s)/(h(2,s)−1) = c    where h(2,s) = c−s. -/
private lemma threeRow_arm_row2 (μ : YoungDiagram) (h3 : μ.rowLen 3 = 0)
    (hc : isCorner μ (2, μ.rowLen 2 - 1)) :
    ∏ s ∈ Finset.range (μ.rowLen 2 - 1),
      ((hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1)) =
    (μ.rowLen 2 : ℚ) := by
  set c := μ.rowLen 2
  have hc_pos : 0 < c := hc.1 |>.1 |> YoungDiagram.mem_iff_lt_rowLen.mp |> (by simp)
  have hconv : ∀ s ∈ Finset.range (c - 1),
      (hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1) =
      ((c : ℚ) - s) / ((c : ℚ) - s - 1) := by
    intro s hs
    have hsc : s < c - 1 := Finset.mem_range.mp hs
    have hmem : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [threeRow_hookLen_row2 h3 hmem]
    push_cast
    congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv]
  have hcm : c - 1 < c := Nat.sub_lt hc_pos Nat.one_pos
  rw [prod_div_telescope c (c - 1) hcm]
  push_cast
  simp [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hc_pos))]

/-- corner (2, c−1) is always a corner of a 3-row shape with c > 0. -/
private lemma threeRow_corner_bot {μ : YoungDiagram} (h3 : μ.rowLen 3 = 0)
    (h2 : 0 < μ.rowLen 2) : isCorner μ (2, μ.rowLen 2 - 1) := by
  refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega),
          fun h => ?_, fun h => ?_⟩
  · have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega
  · have h3s := YoungDiagram.mem_iff_lt_rowLen.mp h
    omega

/-- Corners of a 3-row shape are classified: each is (0,a−1) if a>b, (1,b−1) if b>c, (2,c−1). -/
private lemma threeRow_corner_cases {μ : YoungDiagram} (h3 : μ.rowLen 3 = 0)
    (h2 : 0 < μ.rowLen 2) {cell : ℕ × ℕ} (hc : isCorner μ cell) :
    (cell = (0, μ.rowLen 0 - 1) ∧ μ.rowLen 1 < μ.rowLen 0) ∨
    (cell = (1, μ.rowLen 1 - 1) ∧ μ.rowLen 2 < μ.rowLen 1) ∨
    cell = (2, μ.rowLen 2 - 1) := by
  obtain ⟨hmem, hright, hbelow⟩ := hc
  obtain ⟨i, j⟩ := cell
  simp only [Prod.fst, Prod.snd] at *
  have hi_lt_3 : i < 3 := by
    by_contra hlt; push_neg at hlt
    have := YoungDiagram.rowLen_mono hlt
    rw [h3] at this
    have := YoungDiagram.mem_iff_lt_rowLen.mp hmem; omega
  have hj : j = μ.rowLen i - 1 := by
    have hlt : j < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp hmem
    have : ¬(j + 1 < μ.rowLen i) := fun h => hright (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    omega
  interval_cases i
  · left; refine ⟨by simpa, ?_⟩
    by_contra h; push_neg at h
    have : (1, μ.rowLen 0 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    exact hbelow (by rwa [hj])
  · right; left; refine ⟨by simpa, ?_⟩
    by_contra h; push_neg at h
    have : (2, μ.rowLen 1 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    exact hbelow (by rwa [hj])
  · right; right; simpa

/-- (1, b-1) is a corner of a 3-row shape when rowLen 2 < rowLen 1. -/
private lemma threeRow_corner_mid {μ : YoungDiagram} (h3 : μ.rowLen 3 = 0)
    (hbc : μ.rowLen 2 < μ.rowLen 1) : isCorner μ (1, μ.rowLen 1 - 1) := by
  refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
  · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
  · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)

/-- (0, a-1) is a corner of a 3-row shape when rowLen 1 < rowLen 0. -/
private lemma threeRow_corner_top {μ : YoungDiagram} (h3 : μ.rowLen 3 = 0)
    (hab : μ.rowLen 1 < μ.rowLen 0) : isCorner μ (0, μ.rowLen 0 - 1) := by
  refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
  · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
  · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)

/-- A 3-row YoungDiagram has card = rowLen 0 + rowLen 1 + rowLen 2. -/
private lemma threeRow_card {μ : YoungDiagram} (h3 : μ.rowLen 3 = 0) :
    μ.card = μ.rowLen 0 + μ.rowLen 1 + μ.rowLen 2 := by
  have hrows_zero : ∀ i, 3 ≤ i → μ.rowLen i = 0 := fun i hi =>
    Nat.le_zero.mp (h3 ▸ μ.rowLen_anti 3 i hi)
  unfold YoungDiagram.card
  have hcells : μ.cells =
      (Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
      (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
      (Finset.range (μ.rowLen 2)).image (Prod.mk 2) := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
               Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · intro hlt
      have hi3 : i < 3 := by
        by_contra hge; push_neg at hge
        exact absurd hlt (by rw [hrows_zero i hge]; omega)
      interval_cases i
      · left; left; exact ⟨j, hlt, rfl, rfl⟩
      · left; right; exact ⟨j, hlt, rfl, rfl⟩
      · right; exact ⟨j, hlt, rfl, rfl⟩
    · rintro ((⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩)
      all_goals exact hk
  have hd1 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0))
                       ((Finset.range (μ.rowLen 1)).image (Prod.mk 1)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      obtain ⟨_, _, rfl, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨_, _, h, _⟩ := Finset.mem_image.mp hy
      exact absurd h (by norm_num)
  have hd2 : Disjoint
      ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
       (Finset.range (μ.rowLen 1)).image (Prod.mk 1))
      ((Finset.range (μ.rowLen 2)).image (Prod.mk 2)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  rw [hcells, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_range, Finset.card_range, Finset.card_range]

/-- Arm product for corner (1, b-1) telescopes to (b+1)(b-c)/(b-c+1). -/
private lemma threeRow_arm_row1 {μ : YoungDiagram} (h3 : μ.rowLen 3 = 0)
    (hbc : μ.rowLen 2 < μ.rowLen 1) :
    ∏ s ∈ Finset.range (μ.rowLen 1 - 1),
      ((hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1)) =
    ((μ.rowLen 1 : ℚ) + 1) * ((μ.rowLen 1 : ℚ) - μ.rowLen 2) /
    ((μ.rowLen 1 : ℚ) - μ.rowLen 2 + 1) := by
  set b := μ.rowLen 1; set cv := μ.rowLen 2
  have hcb : cv ≤ b := Nat.le_of_lt hbc
  have hsplit : Finset.range (b - 1) = Finset.range cv ∪ Finset.Ico cv (b - 1) := by
    ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range cv) (Finset.Ico cv (b - 1)) :=
    Finset.disjoint_left.mpr fun _ hk => by
      simp only [Finset.mem_range, Finset.mem_Ico] at hk ⊢; omega
  rw [hsplit, Finset.prod_union hdisj]
  have hconv1 : ∀ s ∈ Finset.range cv,
      (hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1) =
      ((b : ℚ) + 1 - s) / ((b : ℚ) + 1 - s - 1) := fun s hs => by
    have hsc : s < cv := Finset.mem_range.mp hs
    rw [threeRow_hookLen_row1_lt h3 (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)) hsc]
    push_cast [Nat.cast_sub (show s ≤ b by omega)]; ring
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (b + 1) cv (by omega)]
  have hconv2 : ∀ s ∈ Finset.Ico cv (b - 1),
      (hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1) =
      ((b : ℚ) - s) / ((b : ℚ) - s - 1) := fun s hs => by
    have hs_mem := Finset.mem_Ico.mp hs
    rw [threeRow_hookLen_row1_ge h3 (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
        (by omega : μ.rowLen 2 ≤ s)]
    push_cast [Nat.cast_sub (show s ≤ b - 1 by omega)]; ring
  rw [Finset.prod_congr rfl hconv2, Finset.prod_Ico_eq_prod_range]
  have hconv2b : ∀ k ∈ Finset.range (b - 1 - cv),
      ((b : ℚ) - ↑(cv + k)) / ((b : ℚ) - ↑(cv + k) - 1) =
      (↑(b - cv) - ↑k) / (↑(b - cv) - ↑k - 1) := fun k _ => by
    push_cast [Nat.cast_sub hcb]; ring
  rw [Finset.prod_congr rfl hconv2b, prod_div_telescope (b - cv) (b - 1 - cv) (by omega)]
  have hbc1 : (b : ℚ) - cv + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < (b : ℤ) - cv + 1 by omega)
  push_cast [Nat.cast_sub hcb, Nat.cast_sub (show b - 1 - cv ≤ b - cv by omega)]
  field_simp [hbc1]; push_cast [Nat.cast_sub hcb]; ring

/-- Arm product for corner (0, a-1) telescopes to (a+2)(a-c+1)(a-b)/[(a-c+2)(a-b+1)]. -/
private lemma threeRow_arm_row0 {μ : YoungDiagram} (h3 : μ.rowLen 3 = 0)
    (h2 : 0 < μ.rowLen 2) (hab : μ.rowLen 1 < μ.rowLen 0) :
    ∏ s ∈ Finset.range (μ.rowLen 0 - 1),
      ((hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1)) =
    ((μ.rowLen 0 : ℚ) + 2) * ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 1) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 1) /
    (((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 2) * ((μ.rowLen 0 : ℚ) - μ.rowLen 1 + 1)) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set cv := μ.rowLen 2
  have hba : b ≤ a := Nat.le_of_lt hab
  have hcb : cv ≤ b := μ.rowLen_anti 1 2 (by omega)
  have hsplit : Finset.range (a - 1) =
      Finset.range cv ∪ Finset.Ico cv b ∪ Finset.Ico b (a - 1) := by
    ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj1 : Disjoint (Finset.range cv) (Finset.Ico cv b) :=
    Finset.disjoint_left.mpr fun _ hk => by
      simp only [Finset.mem_range, Finset.mem_Ico] at hk ⊢; omega
  have hdisj2 : Disjoint (Finset.range cv ∪ Finset.Ico cv b) (Finset.Ico b (a - 1)) :=
    Finset.disjoint_left.mpr fun _ hk => by
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico] at hk ⊢; omega
  rw [hsplit, Finset.prod_union hdisj2, Finset.prod_union hdisj1]
  have hconv1 : ∀ s ∈ Finset.range cv,
      (hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1) =
      ((a : ℚ) + 2 - s) / ((a : ℚ) + 2 - s - 1) := fun s hs => by
    have hsc : s < cv := Finset.mem_range.mp hs
    rw [threeRow_hookLen_row0_lt h3 (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)) hsc]
    push_cast [Nat.cast_sub (show s ≤ a by omega)]; ring
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (a + 2) cv (by omega)]
  have hconv2 : ∀ s ∈ Finset.Ico cv b,
      (hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1) =
      ((a : ℚ) + 1 - s) / ((a : ℚ) + 1 - s - 1) := fun s hs => by
    have hs_mem := Finset.mem_Ico.mp hs
    rw [threeRow_hookLen_row0_mid h3 (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
        hs_mem.1 hs_mem.2]
    push_cast [Nat.cast_sub (show s ≤ a by omega)]; ring
  rw [Finset.prod_congr rfl hconv2, Finset.prod_Ico_eq_prod_range]
  have hconv2b : ∀ k ∈ Finset.range (b - cv),
      ((a : ℚ) + 1 - ↑(cv + k)) / ((a : ℚ) + 1 - ↑(cv + k) - 1) =
      (↑(a - cv + 1) - ↑k) / (↑(a - cv + 1) - ↑k - 1) := fun k _ => by
    push_cast [Nat.cast_sub (Nat.le_trans hcb hba)]; ring
  rw [Finset.prod_congr rfl hconv2b, prod_div_telescope (a - cv + 1) (b - cv) (by omega)]
  have hconv3 : ∀ s ∈ Finset.Ico b (a - 1),
      (hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1) =
      ((a : ℚ) - s) / ((a : ℚ) - s - 1) := fun s hs => by
    have hs_mem := Finset.mem_Ico.mp hs
    rw [threeRow_hookLen_row0_ge h3 (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
        hs_mem.1]
    push_cast [Nat.cast_sub (show s ≤ a - 1 by omega)]; ring
  rw [Finset.prod_congr rfl hconv3, Finset.prod_Ico_eq_prod_range]
  have hconv3b : ∀ k ∈ Finset.range (a - 1 - b),
      ((a : ℚ) - ↑(b + k)) / ((a : ℚ) - ↑(b + k) - 1) =
      (↑(a - b) - ↑k) / (↑(a - b) - ↑k - 1) := fun k _ => by
    push_cast [Nat.cast_sub hba]; ring
  rw [Finset.prod_congr rfl hconv3b, prod_div_telescope (a - b) (a - 1 - b) (by omega)]
  have hd1 : (a : ℚ) - cv + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < (a : ℤ) - cv + 2 by omega)
  have hd2 : (a : ℚ) - b + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < (a : ℤ) - b + 1 by omega)
  push_cast [Nat.cast_sub (Nat.le_trans hcb hba), Nat.cast_sub hba, Nat.cast_sub hcb,
             Nat.cast_sub (show b - cv ≤ a - cv + 1 by omega),
             Nat.cast_sub (show a - 1 - b ≤ a - b by omega)]
  field_simp [hd1, hd2]; ring

/-- The hook walk identity for exactly-3-row Young diagrams.
    Direct computation via hookProd_ratio_formula and telescoping — no HLF used.
    This proof is NON-CIRCULAR: it does not call hook_length_formula_Q or hook_walk_identity.
    Covers ALL 3-row shapes including [a,2,1], [a,b,c] with a≥b≥c≥1. -/
lemma hook_walk_identity_threeRow (μ : YoungDiagram)
    (h3 : μ.rowLen 3 = 0) (h2 : 0 < μ.rowLen 2) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / (hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) : ℚ))
    = (μ.card : ℚ) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set cv := μ.rowLen 2
  have hcb : cv ≤ b := μ.rowLen_anti 1 2 (by omega)
  have hba : b ≤ a := μ.rowLen_anti 0 1 (by omega)
  have hbot : isCorner μ (2, cv - 1) := threeRow_corner_bot h3 h2
  have hcard : (μ.card : ℚ) = (a : ℚ) + b + cv := by
    exact_mod_cast threeRow_card h3
  rw [hcard]
  let ratio : ℕ × ℕ → ℚ := fun x =>
    if hx : isCorner μ x then (hookProd μ : ℚ) / hookProd (removeCorner μ x hx) else 0
  have hconvert : ∑ c ∈ (corners μ).attach,
        ((hookProd μ : ℚ) / hookProd (removeCorner μ c.val (mem_corners.mp c.prop))) =
      ∑ x ∈ corners μ, ratio x := by
    rw [← Finset.sum_attach (f := ratio)]
    apply Finset.sum_congr rfl
    intro cx _
    exact dif_pos (mem_corners.mp cx.2)
  have hsub : corners μ ⊆ ({(2, cv - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases threeRow_corner_cases h3 h2 (mem_corners.mp hx) with ⟨heq, _⟩ | ⟨heq, _⟩ | heq
    · right; right; exact heq
    · right; left; exact heq
    · left; exact heq
  have hext : ∑ x ∈ corners μ, ratio x =
      ∑ x ∈ ({(2, cv - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)), ratio x := by
    apply Finset.sum_subset hsub
    intro x _ hxnc
    exact dif_neg (mt mem_corners.mpr hxnc)
  have hR2 : ratio (2, cv - 1) =
      (cv : ℚ) * ((a : ℚ) - cv + 3) / ((a : ℚ) - cv + 2) *
      ((b : ℚ) - cv + 2) / ((b : ℚ) - cv + 1) := by
    simp only [ratio, dif_pos hbot]
    rw [hookProd_ratio_formula hbot]
    simp only [Prod.fst, Prod.snd]
    rw [threeRow_arm_row2 μ h3 hbot]
    rw [show Finset.range 2 = {0, 1} from by ext k; simp only [Finset.mem_range,
          Finset.mem_insert, Finset.mem_singleton]; omega]
    rw [Finset.prod_insert (by simp), Finset.prod_singleton]
    have hcv1 : cv - 1 < cv := Nat.sub_lt h2 Nat.one_pos
    have hmem0 : (0, cv - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem1 : (1, cv - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [threeRow_hookLen_row0_lt h3 hmem0 hcv1, threeRow_hookLen_row1_lt h3 hmem1 hcv1]
    push_cast [Nat.cast_sub (show 1 ≤ cv from h2),
               Nat.cast_sub (show cv - 1 ≤ a by omega),
               Nat.cast_sub (show cv - 1 ≤ b by omega)]
    ring
  have hR1 : ratio (1, b - 1) =
      ((b : ℚ) + 1) * ((b : ℚ) - cv) / ((b : ℚ) - cv + 1) *
      ((a : ℚ) - b + 2) / ((a : ℚ) - b + 1) := by
    by_cases hbc : cv < b
    · have hmid : isCorner μ (1, b - 1) := threeRow_corner_mid h3 hbc
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [threeRow_arm_row1 h3 hbc,
          Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      have hmem0 : (0, b - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [threeRow_hookLen_row0_mid h3 hmem0 (by omega : cv ≤ b - 1) (by omega : b - 1 < b)]
      push_cast [Nat.cast_sub (show 1 ≤ b by omega),
                 Nat.cast_sub (show b - 1 ≤ a by omega),
                 Nat.cast_sub hcb.le]
      ring
    · have hbc_eq : b = cv := Nat.le_antisymm (not_lt.mp hbc) hcb
      have hnotcorner : ¬ isCorner μ (1, b - 1) := by
        intro ⟨_, _, hbelow⟩
        apply hbelow
        exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      simp only [ratio, dif_neg hnotcorner]
      have : (b : ℚ) - cv = 0 := by rw [hbc_eq]; ring
      rw [this]; ring
  have hR0 : ratio (0, a - 1) =
      ((a : ℚ) + 2) * ((a : ℚ) - cv + 1) * ((a : ℚ) - b) /
      (((a : ℚ) - cv + 2) * ((a : ℚ) - b + 1)) := by
    by_cases hab : b < a
    · have htop : isCorner μ (0, a - 1) := threeRow_corner_top h3 hab
      simp only [ratio, dif_pos htop]
      rw [hookProd_ratio_formula htop]
      simp only [Prod.fst, Prod.snd, Finset.prod_range_zero, mul_one]
      rw [threeRow_arm_row0 h3 h2 hab]
      ring
    · have hba_eq : a = b := Nat.le_antisymm (not_lt.mp hab) hba
      have hnotcorner : ¬ isCorner μ (0, a - 1) := by
        intro ⟨_, _, hbelow⟩
        apply hbelow
        exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      simp only [ratio, dif_neg hnotcorner]
      have : (a : ℚ) - b = 0 := by rw [hba_eq]; ring
      rw [this]; ring
  rw [hconvert, hext]
  have hd1 : (2, cv - 1) ∉ ({(1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hd2 : (1, b - 1) ∉ ({(0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  rw [show ({(2, cv - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) =
      insert (2, cv - 1) (insert (1, b - 1) {(0, a - 1)}) from rfl,
      Finset.sum_insert hd1, Finset.sum_insert hd2, Finset.sum_singleton,
      hR2, hR1, hR0]
  have hd_cv2 : (a : ℚ) - cv + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < (a : ℤ) - cv + 2 by omega)
  have hd_bc1 : (b : ℚ) - cv + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < (b : ℤ) - cv + 1 by omega)
  have hd_ab1 : (a : ℚ) - b + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < (a : ℤ) - b + 1 by omega)
  push_cast [Nat.cast_sub (Nat.le_trans hcb hba), Nat.cast_sub hcb, Nat.cast_sub hba]
  field_simp [hd_cv2, hd_bc1, hd_ab1]
  ring

-- ============================================================
-- PART XVIII: Hook Walk Identity for 4-Row Shapes
-- ============================================================
/-
  For a 4-row Young diagram [a,b,c,d] (a≥b≥c≥d≥1, rowLen 4 = 0):
  - n = a+b+c+d cells
  - Corners: (3,d-1) always; (2,c-1) when c>d; (1,b-1) when b>c; (0,a-1) when a>b
  - hook_walk_identity proved by direct ratio computation via hookProd_ratio_formula
  - Ratios close with field_simp; ring (same algebraic pattern as threeRow)
-/

/-- colLen(s) = 4 for s < rowLen 3 in a 4-row shape (rowLen 4 = 0). -/
private lemma fourRow_colLen_lt {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hs : s < μ.rowLen 3) : μ.colLen s = 4 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h4s : (4, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h4s
    omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs)

/-- colLen(s) = 3 for rowLen 3 ≤ s < rowLen 2 in a 4-row shape. -/
private lemma fourRow_colLen_mid1 {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    μ.colLen s = 3 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h3s : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h3s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 2 for rowLen 2 ≤ s < rowLen 1 in a 4-row shape. -/
private lemma fourRow_colLen_mid2 {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    μ.colLen s = 2 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h2s : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h2s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- hookLength μ 3 s = rowLen 3 − s for (3,s) ∈ μ and rowLen 4 = 0. -/
private lemma fourRow_hookLen_row3 {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hmem : (3, s) ∈ μ) :
    hookLength μ 3 s = μ.rowLen 3 - s := by
  have hs : s < μ.rowLen 3 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [fourRow_colLen_lt h4 hs] at key; omega

/-- hookLength μ 2 s = rowLen 2 − s + 1 for s < rowLen 3 in a 4-row shape. -/
private lemma fourRow_hookLen_row2_lt {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hmem : (2, s) ∈ μ) (hs : s < μ.rowLen 3) :
    hookLength μ 2 s = μ.rowLen 2 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [fourRow_colLen_lt h4 hs] at key
  have hs2 : s < μ.rowLen 2 := YoungDiagram.mem_iff_lt_rowLen.mp hmem; omega

/-- hookLength μ 2 s = rowLen 2 − s for rowLen 3 ≤ s < rowLen 2 in a 4-row shape. -/
private lemma fourRow_hookLen_row2_ge {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hmem : (2, s) ∈ μ) (hs : μ.rowLen 3 ≤ s) :
    hookLength μ 2 s = μ.rowLen 2 - s := by
  have hs2 : s < μ.rowLen 2 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [fourRow_colLen_mid1 h4 hs hs2] at key; omega

/-- hookLength μ 1 s = rowLen 1 − s + 2 for s < rowLen 3 in a 4-row shape. -/
private lemma fourRow_hookLen_row1_lt {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hmem : (1, s) ∈ μ) (hs : s < μ.rowLen 3) :
    hookLength μ 1 s = μ.rowLen 1 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [fourRow_colLen_lt h4 hs] at key
  have hs1 : s < μ.rowLen 1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem; omega

/-- hookLength μ 1 s = rowLen 1 − s + 1 for rowLen 3 ≤ s < rowLen 2 in a 4-row shape. -/
private lemma fourRow_hookLen_row1_mid {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    hookLength μ 1 s = μ.rowLen 1 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [fourRow_colLen_mid1 h4 hs_ge hs_lt] at key
  have hs1 : s < μ.rowLen 1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem; omega

/-- hookLength μ 1 s = rowLen 1 − s for rowLen 2 ≤ s < rowLen 1 in a 4-row shape. -/
private lemma fourRow_hookLen_row1_ge {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hmem : (1, s) ∈ μ) (hs : μ.rowLen 2 ≤ s) :
    hookLength μ 1 s = μ.rowLen 1 - s := by
  have hs1 : s < μ.rowLen 1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [fourRow_colLen_mid2 h4 hs hs1] at key; omega

/-- hookLength μ 0 s = rowLen 0 − s + 3 for s < rowLen 3 in a 4-row shape. -/
private lemma fourRow_hookLen_row0_lt {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hmem : (0, s) ∈ μ) (hs : s < μ.rowLen 3) :
    hookLength μ 0 s = μ.rowLen 0 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [fourRow_colLen_lt h4 hs] at key
  have hs0 : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem; omega

/-- hookLength μ 0 s = rowLen 0 − s + 2 for rowLen 3 ≤ s < rowLen 2 in a 4-row shape. -/
private lemma fourRow_hookLen_row0_mid1 {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    hookLength μ 0 s = μ.rowLen 0 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [fourRow_colLen_mid1 h4 hs_ge hs_lt] at key
  have hs0 : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem; omega

/-- hookLength μ 0 s = rowLen 0 − s + 1 for rowLen 2 ≤ s < rowLen 1 in a 4-row shape. -/
private lemma fourRow_hookLen_row0_mid2 {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    hookLength μ 0 s = μ.rowLen 0 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [fourRow_colLen_mid2 h4 hs_ge hs_lt] at key
  have hs0 : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem; omega

/-- hookLength μ 0 s = rowLen 0 − s for rowLen 1 ≤ s < rowLen 0 in a 4-row shape. -/
private lemma fourRow_hookLen_row0_ge {μ : YoungDiagram} {s : ℕ}
    (h4 : μ.rowLen 4 = 0) (hmem : (0, s) ∈ μ) (hs : μ.rowLen 1 ≤ s) :
    hookLength μ 0 s = μ.rowLen 0 - s := by
  have hs0 : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  have hcl : μ.colLen s = 1 := by
    apply Nat.le_antisymm
    · by_contra hlt; push_neg at hlt
      have h1s : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
      have := YoungDiagram.mem_iff_lt_rowLen.mp h1s; omega
    · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs0)
  rw [hcl] at key; omega

/-- corner (3, d-1) always exists in a 4-row shape (rowLen 3 > 0, rowLen 4 = 0). -/
private lemma fourRow_corner_bot {μ : YoungDiagram} (h4 : μ.rowLen 4 = 0)
    (h3 : 0 < μ.rowLen 3) : isCorner μ (3, μ.rowLen 3 - 1) := by
  refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega),
          fun h => ?_, fun h => ?_⟩
  · have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega
  · have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega

/-- Corners of a 4-row shape are classified into at most 4 positions. -/
private lemma fourRow_corner_cases {μ : YoungDiagram} (h4 : μ.rowLen 4 = 0)
    (h3 : 0 < μ.rowLen 3) {cell : ℕ × ℕ} (hc : isCorner μ cell) :
    (cell = (0, μ.rowLen 0 - 1) ∧ μ.rowLen 1 < μ.rowLen 0) ∨
    (cell = (1, μ.rowLen 1 - 1) ∧ μ.rowLen 2 < μ.rowLen 1) ∨
    (cell = (2, μ.rowLen 2 - 1) ∧ μ.rowLen 3 < μ.rowLen 2) ∨
    cell = (3, μ.rowLen 3 - 1) := by
  obtain ⟨hmem, hright, hbelow⟩ := hc
  obtain ⟨i, j⟩ := cell
  simp only [Prod.fst, Prod.snd] at *
  have hi_lt_4 : i < 4 := by
    by_contra hlt; push_neg at hlt
    have := (μ.rowLen_anti 4 i hlt).trans_eq h4
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp hmem) (by omega)
  have hj : j = μ.rowLen i - 1 := by
    have hlt : j < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp hmem
    have : ¬(j + 1 < μ.rowLen i) := fun h => hright (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    omega
  interval_cases i
  · left; refine ⟨by simpa, ?_⟩
    by_contra h; push_neg at h
    exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega) |> hj ▸ id)
  · right; left; refine ⟨by simpa, ?_⟩
    by_contra h; push_neg at h
    exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega) |> hj ▸ id)
  · right; right; left; refine ⟨by simpa, ?_⟩
    by_contra h; push_neg at h
    exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega) |> hj ▸ id)
  · right; right; right; simpa

/-- A 4-row YoungDiagram has card = rowLen 0 + rowLen 1 + rowLen 2 + rowLen 3. -/
private lemma fourRow_card {μ : YoungDiagram} (h4 : μ.rowLen 4 = 0) :
    μ.card = μ.rowLen 0 + μ.rowLen 1 + μ.rowLen 2 + μ.rowLen 3 := by
  have hrows_zero : ∀ i, 4 ≤ i → μ.rowLen i = 0 := fun i hi =>
    Nat.le_zero.mp (h4 ▸ μ.rowLen_anti 4 i hi)
  unfold YoungDiagram.card
  have hcells : μ.cells =
      (Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
      (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
      (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
      (Finset.range (μ.rowLen 3)).image (Prod.mk 3) := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
               Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · intro hlt
      have hi4 : i < 4 := by
        by_contra hge; push_neg at hge
        exact absurd hlt (by rw [hrows_zero i hge]; omega)
      interval_cases i
      · left; left; left; exact ⟨j, hlt, rfl, rfl⟩
      · left; left; right; exact ⟨j, hlt, rfl, rfl⟩
      · left; right; exact ⟨j, hlt, rfl, rfl⟩
      · right; exact ⟨j, hlt, rfl, rfl⟩
    · rintro (((⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩)
      all_goals exact hk
  have hd1 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0))
                       ((Finset.range (μ.rowLen 1)).image (Prod.mk 1)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      obtain ⟨_, _, rfl, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨_, _, h, _⟩ := Finset.mem_image.mp hy; exact absurd h (by norm_num)
  have hd2 : Disjoint
      ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
       (Finset.range (μ.rowLen 1)).image (Prod.mk 1))
      ((Finset.range (μ.rowLen 2)).image (Prod.mk 2)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd3 : Disjoint
      ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
       (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
       (Finset.range (μ.rowLen 2)).image (Prod.mk 2))
      ((Finset.range (μ.rowLen 3)).image (Prod.mk 3)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  rw [hcells, Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
      Finset.card_union_of_disjoint hd1,
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_range, Finset.card_range, Finset.card_range, Finset.card_range]

/-- Arm product for corner (3, d-1) telescopes to d.
    ∏_{s ∈ range(d-1)} h(3,s)/(h(3,s)-1) = d, where h(3,s) = d-s. -/
private lemma fourRow_arm_row3 (μ : YoungDiagram) (h4 : μ.rowLen 4 = 0)
    (hd : isCorner μ (3, μ.rowLen 3 - 1)) :
    ∏ s ∈ Finset.range (μ.rowLen 3 - 1),
      ((hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1)) =
    (μ.rowLen 3 : ℚ) := by
  set d := μ.rowLen 3
  have hd_pos : 0 < d := by
    have := YoungDiagram.mem_iff_lt_rowLen.mp hd.1; omega
  have hconv : ∀ s ∈ Finset.range (d - 1),
      (hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1) =
      ((d : ℚ) - s) / ((d : ℚ) - s - 1) := by
    intro s hs
    have hsc : s < d - 1 := Finset.mem_range.mp hs
    have hmem : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row3 h4 hmem]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv]
  rw [prod_div_telescope d (d - 1) (Nat.sub_lt hd_pos Nat.one_pos)]
  push_cast; simp [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd_pos))]

/-- Arm product for corner (2, c-1) in a 4-row shape:
    ∏_{s=0}^{c-2} h(2,s)/(h(2,s)-1) = (c+1)(c-d)/(c-d+1). -/
private lemma fourRow_arm_row2 {μ : YoungDiagram} (h4 : μ.rowLen 4 = 0)
    (hcd : μ.rowLen 3 < μ.rowLen 2) :
    ∏ s ∈ Finset.range (μ.rowLen 2 - 1),
      ((hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1)) =
    ((μ.rowLen 2 : ℚ) + 1) * ((μ.rowLen 2 : ℚ) - μ.rowLen 3) /
    ((μ.rowLen 2 : ℚ) - μ.rowLen 3 + 1) := by
  set c := μ.rowLen 2; set d := μ.rowLen 3
  -- Split range(c-1) into [0,d) and [d, c-1)
  rw [show Finset.range (c - 1) = Finset.range d ∪ Finset.Ico d (c - 1) from by
    ext s; simp [Finset.mem_Ico]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- First product: s ∈ [0,d), h(2,s) = c-s+1
  have hconv1 : ∀ s ∈ Finset.range d,
      (hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1) =
      ((c : ℚ) + 1 - s) / ((c : ℚ) + 1 - s - 1) := by
    intro s hs
    have hsd : s < d := Finset.mem_range.mp hs
    have hmem : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row2_lt h4 hmem (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (c + 1) d (by omega)]
  -- Second product: s ∈ [d, c-1), h(2,s) = c-s
  have hconv2 : ∀ s ∈ Finset.Ico d (c - 1),
      (hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1) =
      ((c : ℚ) - s) / ((c : ℚ) - s - 1) := by
    intro s hs
    have ⟨hsd, hsc⟩ := Finset.mem_Ico.mp hs
    have hmem : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row2_ge h4 hmem (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  -- Reindex [d, c-1) to [0, c-d-1) for prod_div_telescope
  rw [show Finset.Ico d (c - 1) = (Finset.range (c - 1 - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2' : ∀ t ∈ Finset.range (c - 1 - d),
      (hookLength μ 2 (t + d) : ℚ) / ((hookLength μ 2 (t + d) : ℚ) - 1) =
      ((c : ℚ) - d - t) / ((c : ℚ) - d - t - 1) := by
    intro t ht
    have htm : t < c - 1 - d := Finset.mem_range.mp ht
    have hmem : (2, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row2_ge h4 hmem (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2', prod_div_telescope (c - d) (c - 1 - d) (by omega)]
  -- Combine: (c+1)/(c-d+1) × (c-d)/1 = (c+1)(c-d)/(c-d+1)
  push_cast [Nat.cast_sub hcd.le, Nat.cast_sub (show 1 ≤ c - d by omega)]
  have hd1 : (c : ℚ) - d + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  field_simp [hd1]; ring

/-- Arm product for corner (1, b-1) in a 4-row shape:
    ∏_{s=0}^{b-2} h(1,s)/(h(1,s)-1) = (b+2)(b-d+1)(b-c)/((b-d+2)(b-c+1)). -/
private lemma fourRow_arm_row1 {μ : YoungDiagram} (h4 : μ.rowLen 4 = 0)
    (hbc : μ.rowLen 2 < μ.rowLen 1) :
    ∏ s ∈ Finset.range (μ.rowLen 1 - 1),
      ((hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1)) =
    ((μ.rowLen 1 : ℚ) + 2) * ((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 1) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 2) /
    (((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 2) * ((μ.rowLen 1 : ℚ) - μ.rowLen 2 + 1)) := by
  set b := μ.rowLen 1; set c := μ.rowLen 2; set d := μ.rowLen 3
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  -- Split range(b-1) into [0,d), [d,c), [c,b-1)
  rw [show Finset.range (b - 1) = Finset.range d ∪ Finset.Ico d c ∪ Finset.Ico c (b - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- Product 1: [0,d), h(1,s) = b-s+2
  have hconv1 : ∀ s ∈ Finset.range d,
      (hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1) =
      ((b : ℚ) + 2 - s) / ((b : ℚ) + 2 - s - 1) := by
    intro s hs
    have hsd : s < d := Finset.mem_range.mp hs
    have hmem : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row1_lt h4 hmem (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (b + 2) d (by omega)]
  -- Product 2: [d, c), h(1,s) = b-s+1
  have hconv2 : ∀ s ∈ Finset.Ico d c,
      (hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1) =
      ((b : ℚ) + 1 - s) / ((b : ℚ) + 1 - s - 1) := by
    intro s hs
    have ⟨hsd, hsc⟩ := Finset.mem_Ico.mp hs
    have hmem : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row1_mid h4 hmem hsd hsc]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2' : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 1 (t + d) : ℚ) / ((hookLength μ 1 (t + d) : ℚ) - 1) =
      ((b : ℚ) - d + 1 - t) / ((b : ℚ) - d + 1 - t - 1) := by
    intro t ht
    have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (1, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row1_mid h4 hmem (by omega) (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2', prod_div_telescope (b - d + 1) (c - d) (by omega)]
  -- Product 3: [c, b-1), h(1,s) = b-s
  have hconv3 : ∀ s ∈ Finset.Ico c (b - 1),
      (hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1) =
      ((b : ℚ) - s) / ((b : ℚ) - s - 1) := by
    intro s hs
    have ⟨hsc, hsb⟩ := Finset.mem_Ico.mp hs
    have hmem : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row1_ge h4 hmem hsc]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [show Finset.Ico c (b - 1) = (Finset.range (b - 1 - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3' : ∀ t ∈ Finset.range (b - 1 - c),
      (hookLength μ 1 (t + c) : ℚ) / ((hookLength μ 1 (t + c) : ℚ) - 1) =
      ((b : ℚ) - c - t) / ((b : ℚ) - c - t - 1) := by
    intro t ht
    have htm : t < b - 1 - c := Finset.mem_range.mp ht
    have hmem : (1, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row1_ge h4 hmem (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3', prod_div_telescope (b - c) (b - 1 - c) (by omega)]
  -- Combine all three telescope products
  push_cast [Nat.cast_sub hdc, Nat.cast_sub hbc.le, Nat.cast_sub (show 1 ≤ b - c by omega)]
  have hne1 : (b : ℚ) - d + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne2 : (b : ℚ) - c + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  field_simp [hne1, hne2]; ring

/-- Arm product for corner (0, a-1) in a 4-row shape:
    ∏_{s=0}^{a-2} h(0,s)/(h(0,s)-1) = (a+3)(a-d+2)(a-c+1)(a-b)/((a-d+3)(a-c+2)(a-b+1)). -/
private lemma fourRow_arm_row0 {μ : YoungDiagram} (h4 : μ.rowLen 4 = 0)
    (h3 : 0 < μ.rowLen 3) (hab : μ.rowLen 1 < μ.rowLen 0) :
    ∏ s ∈ Finset.range (μ.rowLen 0 - 1),
      ((hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1)) =
    ((μ.rowLen 0 : ℚ) + 3) * ((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 2) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 1) * ((μ.rowLen 0 : ℚ) - μ.rowLen 1) /
    (((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 3) * ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 2) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 1 + 1)) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set c := μ.rowLen 2; set d := μ.rowLen 3
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  -- Split range(a-1) into [0,d), [d,c), [c,b), [b,a-1)
  rw [show Finset.range (a - 1) = Finset.range d ∪ Finset.Ico d c ∪
      Finset.Ico c b ∪ Finset.Ico b (a - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- Product 1: [0,d), h(0,s) = a-s+3
  have hconv1 : ∀ s ∈ Finset.range d,
      (hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1) =
      ((a : ℚ) + 3 - s) / ((a : ℚ) + 3 - s - 1) := by
    intro s hs
    have hmem : (0, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row0_lt h4 hmem (by exact_mod_cast Finset.mem_range.mp hs)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (a + 3) d (by omega)]
  -- Product 2: [d, c), h(0,s) = a-s+2
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 0 (t + d) : ℚ) / ((hookLength μ 0 (t + d) : ℚ) - 1) =
      ((a : ℚ) - d + 2 - t) / ((a : ℚ) - d + 2 - t - 1) := by
    intro t ht
    have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (0, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row0_mid1 h4 hmem (by omega) (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (a - d + 2) (c - d) (by omega)]
  -- Product 3: [c, b), h(0,s) = a-s+1
  rw [show Finset.Ico c b = (Finset.range (b - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (b - c),
      (hookLength μ 0 (t + c) : ℚ) / ((hookLength μ 0 (t + c) : ℚ) - 1) =
      ((a : ℚ) - c + 1 - t) / ((a : ℚ) - c + 1 - t - 1) := by
    intro t ht
    have htm : t < b - c := Finset.mem_range.mp ht
    have hmem : (0, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row0_mid2 h4 hmem (by omega) (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (a - c + 1) (b - c) (by omega)]
  -- Product 4: [b, a-1), h(0,s) = a-s
  rw [show Finset.Ico b (a - 1) = (Finset.range (a - 1 - b)).image (· + b) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (a - 1 - b),
      (hookLength μ 0 (t + b) : ℚ) / ((hookLength μ 0 (t + b) : ℚ) - 1) =
      ((a : ℚ) - b - t) / ((a : ℚ) - b - t - 1) := by
    intro t ht
    have htm : t < a - 1 - b := Finset.mem_range.mp ht
    have hmem : (0, t + b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fourRow_hookLen_row0_ge h4 hmem (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (a - b) (a - 1 - b) (by omega)]
  push_cast [Nat.cast_sub hdc, Nat.cast_sub hcb, Nat.cast_sub hab.le,
             Nat.cast_sub (show 1 ≤ a - b by omega)]
  have hne1 : (a : ℚ) - d + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne2 : (a : ℚ) - c + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne3 : (a : ℚ) - b + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  field_simp [hne1, hne2, hne3]; ring

/-- The hook walk identity for exactly-4-row Young diagrams.
    Direct computation via hookProd_ratio_formula and telescoping — no HLF used.
    NON-CIRCULAR: does not call hook_length_formula_Q or hook_walk_identity. -/
lemma hook_walk_identity_fourRow (μ : YoungDiagram)
    (h4 : μ.rowLen 4 = 0) (h3 : 0 < μ.rowLen 3) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / (hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) : ℚ))
    = (μ.card : ℚ) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set c := μ.rowLen 2; set d := μ.rowLen 3
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  have hba : b ≤ a := μ.rowLen_anti 0 1 (by omega)
  have hbot : isCorner μ (3, d - 1) := fourRow_corner_bot h4 h3
  have hcard : (μ.card : ℚ) = (a : ℚ) + b + c + d := by
    exact_mod_cast fourRow_card h4
  rw [hcard]
  let ratio : ℕ × ℕ → ℚ := fun x =>
    if hx : isCorner μ x then (hookProd μ : ℚ) / hookProd (removeCorner μ x hx) else 0
  have hconvert : ∑ cc ∈ (corners μ).attach,
        ((hookProd μ : ℚ) / hookProd (removeCorner μ cc.val (mem_corners.mp cc.prop))) =
      ∑ x ∈ corners μ, ratio x := by
    rw [← Finset.sum_attach (f := ratio)]
    apply Finset.sum_congr rfl
    intro cx _; exact dif_pos (mem_corners.mp cx.2)
  have hsub : corners μ ⊆ ({(3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases fourRow_corner_cases h4 h3 (mem_corners.mp hx) with ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | heq
    · right; right; right; exact heq
    · right; right; left; exact heq
    · right; left; exact heq
    · left; exact heq
  have hext : ∑ x ∈ corners μ, ratio x =
      ∑ x ∈ ({(3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)), ratio x := by
    apply Finset.sum_subset hsub
    intro x _ hxnc; exact dif_neg (mt mem_corners.mpr hxnc)
  -- Compute ratio for corner (3, d-1)
  have hR3 : ratio (3, d - 1) =
      (d : ℚ) * ((a : ℚ) - d + 4) / ((a : ℚ) - d + 3) *
      ((b : ℚ) - d + 3) / ((b : ℚ) - d + 2) *
      ((c : ℚ) - d + 2) / ((c : ℚ) - d + 1) := by
    simp only [ratio, dif_pos hbot]
    rw [hookProd_ratio_formula hbot]
    simp only [Prod.fst, Prod.snd]
    rw [fourRow_arm_row3 μ h4 hbot]
    -- Leg: rows 0,1,2 at column d-1
    have hd1 : d - 1 < d := Nat.sub_lt h3 Nat.one_pos
    have hmem0 : (0, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem1 : (1, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem2 : (2, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [show Finset.range 3 = {0, 1, 2} from by ext k; simp; omega]
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
        Finset.prod_singleton]
    rw [fourRow_hookLen_row0_lt h4 hmem0 hd1,
        fourRow_hookLen_row1_lt h4 hmem1 hd1,
        fourRow_hookLen_row2_lt h4 hmem2 hd1]
    push_cast [Nat.cast_sub (show 1 ≤ d from h3),
               Nat.cast_sub (show d - 1 ≤ a by omega),
               Nat.cast_sub (show d - 1 ≤ b by omega),
               Nat.cast_sub (show d - 1 ≤ c by omega)]
    ring
  -- Compute ratio for corner (2, c-1) [when c > d]
  have hR2 : ratio (2, c - 1) =
      ((c : ℚ) + 1) * ((c : ℚ) - d) / ((c : ℚ) - d + 1) *
      ((a : ℚ) - c + 3) / ((a : ℚ) - c + 2) *
      ((b : ℚ) - c + 2) / ((b : ℚ) - c + 1) := by
    by_cases hcd : d < c
    · have hmid : isCorner μ (2, c - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [fourRow_arm_row2 h4 hcd]
      -- Leg: rows 0 and 1 at column c-1 (which is in zone [d, c))
      have hc1 : c - 1 < c := Nat.sub_lt (by omega) Nat.one_pos
      have hdc1 : d ≤ c - 1 := by omega
      have hmem0 : (0, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 2 = {0, 1} from by ext k; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_singleton]
      -- h(0, c-1): zone [d, c), so h = a-(c-1)+2 = a-c+3
      rw [fourRow_hookLen_row0_mid1 h4 hmem0 hdc1 (by omega)]
      -- h(1, c-1): zone [d, c), so h = b-(c-1)+1 = b-c+2
      rw [fourRow_hookLen_row1_mid h4 hmem1 hdc1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ c by omega),
                 Nat.cast_sub (show c - 1 ≤ a by omega),
                 Nat.cast_sub (show c - 1 ≤ b by omega),
                 Nat.cast_sub hcd.le]
      ring
    · -- c = d: corner (2, c-1) doesn't exist; ratio = 0
      have hcd_eq : c = d := Nat.le_antisymm (not_lt.mp hcd) hdc
      have hnotcorner : ¬ isCorner μ (2, c - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (c : ℚ) - d = 0 := by rw [hcd_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (1, b-1) [when b > c]
  have hR1 : ratio (1, b - 1) =
      ((b : ℚ) + 2) * ((b : ℚ) - d + 1) * ((b : ℚ) - c) /
      (((b : ℚ) - d + 2) * ((b : ℚ) - c + 1)) *
      ((a : ℚ) - b + 2) / ((a : ℚ) - b + 1) := by
    by_cases hbc : c < b
    · have hmid : isCorner μ (1, b - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [fourRow_arm_row1 h4 hbc]
      -- Leg: row 0 at column b-1
      have hmem0 : (0, b - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      -- h(0, b-1): b-1 ≥ c, b-1 < b ≤ a; zone [c, b)
      rw [fourRow_hookLen_row0_mid2 h4 hmem0 (by omega) (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ b by omega),
                 Nat.cast_sub (show b - 1 ≤ a by omega),
                 Nat.cast_sub hbc.le, Nat.cast_sub (show d ≤ b by omega)]
      ring
    · have hbc_eq : b = c := Nat.le_antisymm (not_lt.mp hbc) hcb
      have hnotcorner : ¬ isCorner μ (1, b - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (b : ℚ) - c = 0 := by rw [hbc_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (0, a-1) [when a > b]
  have hR0 : ratio (0, a - 1) =
      ((a : ℚ) + 3) * ((a : ℚ) - d + 2) * ((a : ℚ) - c + 1) * ((a : ℚ) - b) /
      (((a : ℚ) - d + 3) * ((a : ℚ) - c + 2) * ((a : ℚ) - b + 1)) := by
    by_cases hab : b < a
    · have htop : isCorner μ (0, a - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos htop]
      rw [hookProd_ratio_formula htop]
      simp only [Prod.fst, Prod.snd, Finset.prod_range_zero, mul_one]
      rw [fourRow_arm_row0 h4 h3 hab]
      push_cast [Nat.cast_sub hab.le, Nat.cast_sub hcb, Nat.cast_sub hdc]
      ring
    · have hab_eq : a = b := Nat.le_antisymm (not_lt.mp hab) hba
      have hnotcorner : ¬ isCorner μ (0, a - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (a : ℚ) - b = 0 := by rw [hab_eq]; ring
      rw [this]; ring
  rw [hconvert, hext]
  -- Sum over 4 corners using distinctness
  have hne31 : (3, d - 1) ∉ ({(2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hne21 : (2, c - 1) ∉ ({(1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hne10 : (1, b - 1) ∉ ({(0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  rw [show ({(3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) =
      insert (3, d - 1) (insert (2, c - 1) (insert (1, b - 1) {(0, a - 1)})) from rfl,
      Finset.sum_insert hne31, Finset.sum_insert hne21,
      Finset.sum_insert hne10, Finset.sum_singleton,
      hR3, hR2, hR1, hR0]
  -- Close with field_simp + ring using nonzero denominators
  have hne_ad3 : (a : ℚ) - d + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne_bd2 : (b : ℚ) - d + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne_cd1 : (c : ℚ) - d + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  have hne_ac2 : (a : ℚ) - c + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne_bc1 : (b : ℚ) - c + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  have hne_ab1 : (a : ℚ) - b + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  push_cast [Nat.cast_sub hdc, Nat.cast_sub hcb, Nat.cast_sub hba,
             Nat.cast_sub (show d ≤ b by omega), Nat.cast_sub (show d ≤ a by omega),
             Nat.cast_sub (show c ≤ a by omega)]
  field_simp [hne_ad3, hne_bd2, hne_cd1, hne_ac2, hne_bc1, hne_ab1]
  ring

-- PART XIX: Hook Walk Identity for 5-Row Shapes
-- ============================================================
/-
  For a 5-row Young diagram [a,b,c,d,e] (a≥b≥c≥d≥e≥1, rowLen 5 = 0):
  - n = a+b+c+d+e cells
  - Corners: (4,e-1) always; (3,d-1) when d>e; (2,c-1) when c>d; (1,b-1) when b>c; (0,a-1) when a>b
  - hook_walk_identity proved by direct ratio computation via hookProd_ratio_formula
  - Ratios close with field_simp; ring (same algebraic pattern as threeRow/fourRow)
-/

/-- colLen(s) = 5 for s < rowLen 4 in a 5-row shape (rowLen 5 = 0). -/
private lemma fiveRow_colLen_lt {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hs : s < μ.rowLen 4) : μ.colLen s = 5 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h5s : (5, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h5s
    omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs)

/-- colLen(s) = 4 for rowLen 4 ≤ s < rowLen 3 in a 5-row shape. -/
private lemma fiveRow_colLen_mid1 {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    μ.colLen s = 4 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h4s : (4, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h4s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 3 for rowLen 3 ≤ s < rowLen 2 in a 5-row shape. -/
private lemma fiveRow_colLen_mid2 {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    μ.colLen s = 3 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h3s : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h3s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 2 for rowLen 2 ≤ s < rowLen 1 in a 5-row shape. -/
private lemma fiveRow_colLen_mid3 {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    μ.colLen s = 2 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h2s : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h2s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- hookLength μ 4 s = rowLen 4 − s for (4,s) ∈ μ and rowLen 5 = 0. -/
private lemma fiveRow_hookLen_row4 {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (4, s) ∈ μ) :
    hookLength μ 4 s = μ.rowLen 4 - s := by
  have hs : s < μ.rowLen 4 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_lt h5 hs] at key; omega

/-- hookLength μ 3 s = rowLen 3 − s + 1 for s < rowLen 4 in a 5-row shape. -/
private lemma fiveRow_hookLen_row3_lt {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (3, s) ∈ μ) (hs : s < μ.rowLen 4) :
    hookLength μ 3 s = μ.rowLen 3 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_lt h5 hs] at key; omega

/-- hookLength μ 3 s = rowLen 3 − s for rowLen 4 ≤ s in a 5-row shape. -/
private lemma fiveRow_hookLen_row3_ge {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (3, s) ∈ μ) (hs : μ.rowLen 4 ≤ s) :
    hookLength μ 3 s = μ.rowLen 3 - s := by
  have hs_lt : s < μ.rowLen 3 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_mid1 h5 hs hs_lt] at key; omega

/-- hookLength μ 2 s = rowLen 2 − s + 2 for s < rowLen 4 in a 5-row shape. -/
private lemma fiveRow_hookLen_row2_lt {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (2, s) ∈ μ) (hs : s < μ.rowLen 4) :
    hookLength μ 2 s = μ.rowLen 2 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_lt h5 hs] at key; omega

/-- hookLength μ 2 s = rowLen 2 − s + 1 for rowLen 4 ≤ s < rowLen 3 in a 5-row shape. -/
private lemma fiveRow_hookLen_row2_mid1 {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s)
    (hs_lt : s < μ.rowLen 3) : hookLength μ 2 s = μ.rowLen 2 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_mid1 h5 hs_ge hs_lt] at key; omega

/-- hookLength μ 2 s = rowLen 2 − s for rowLen 3 ≤ s in a 5-row shape. -/
private lemma fiveRow_hookLen_row2_ge {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (2, s) ∈ μ) (hs : μ.rowLen 3 ≤ s) :
    hookLength μ 2 s = μ.rowLen 2 - s := by
  have hs_lt : s < μ.rowLen 2 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_mid2 h5 hs hs_lt] at key; omega

/-- hookLength μ 1 s = rowLen 1 − s + 3 for s < rowLen 4 in a 5-row shape. -/
private lemma fiveRow_hookLen_row1_lt {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (1, s) ∈ μ) (hs : s < μ.rowLen 4) :
    hookLength μ 1 s = μ.rowLen 1 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_lt h5 hs] at key; omega

/-- hookLength μ 1 s = rowLen 1 − s + 2 for rowLen 4 ≤ s < rowLen 3 in a 5-row shape. -/
private lemma fiveRow_hookLen_row1_mid1 {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s)
    (hs_lt : s < μ.rowLen 3) : hookLength μ 1 s = μ.rowLen 1 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_mid1 h5 hs_ge hs_lt] at key; omega

/-- hookLength μ 1 s = rowLen 1 − s + 1 for rowLen 3 ≤ s < rowLen 2 in a 5-row shape. -/
private lemma fiveRow_hookLen_row1_mid2 {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 3 ≤ s)
    (hs_lt : s < μ.rowLen 2) : hookLength μ 1 s = μ.rowLen 1 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_mid2 h5 hs_ge hs_lt] at key; omega

/-- hookLength μ 1 s = rowLen 1 − s for rowLen 2 ≤ s in a 5-row shape. -/
private lemma fiveRow_hookLen_row1_ge {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (1, s) ∈ μ) (hs : μ.rowLen 2 ≤ s) :
    hookLength μ 1 s = μ.rowLen 1 - s := by
  have hs_lt : s < μ.rowLen 1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_mid3 h5 hs hs_lt] at key; omega

/-- hookLength μ 0 s = rowLen 0 − s + 4 for s < rowLen 4 in a 5-row shape. -/
private lemma fiveRow_hookLen_row0_lt {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (0, s) ∈ μ) (hs : s < μ.rowLen 4) :
    hookLength μ 0 s = μ.rowLen 0 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_lt h5 hs] at key; omega

/-- hookLength μ 0 s = rowLen 0 − s + 3 for rowLen 4 ≤ s < rowLen 3 in a 5-row shape. -/
private lemma fiveRow_hookLen_row0_mid1 {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s)
    (hs_lt : s < μ.rowLen 3) : hookLength μ 0 s = μ.rowLen 0 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_mid1 h5 hs_ge hs_lt] at key; omega

/-- hookLength μ 0 s = rowLen 0 − s + 2 for rowLen 3 ≤ s < rowLen 2 in a 5-row shape. -/
private lemma fiveRow_hookLen_row0_mid2 {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 3 ≤ s)
    (hs_lt : s < μ.rowLen 2) : hookLength μ 0 s = μ.rowLen 0 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_mid2 h5 hs_ge hs_lt] at key; omega

/-- hookLength μ 0 s = rowLen 0 − s + 1 for rowLen 2 ≤ s < rowLen 1 in a 5-row shape. -/
private lemma fiveRow_hookLen_row0_mid3 {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 2 ≤ s)
    (hs_lt : s < μ.rowLen 1) : hookLength μ 0 s = μ.rowLen 0 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [fiveRow_colLen_mid3 h5 hs_ge hs_lt] at key; omega

/-- hookLength μ 0 s = rowLen 0 − s for rowLen 1 ≤ s in a 5-row shape. -/
private lemma fiveRow_hookLen_row0_ge {μ : YoungDiagram} {s : ℕ}
    (h5 : μ.rowLen 5 = 0) (hmem : (0, s) ∈ μ) (hs : μ.rowLen 1 ≤ s) :
    hookLength μ 0 s = μ.rowLen 0 - s := by
  have hs_lt : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  -- colLen s = 1 since s ≥ rowLen 1 and s < rowLen 0
  have hcol1 : μ.colLen s = 1 := by
    apply Nat.le_antisymm
    · by_contra hlt; push_neg at hlt
      have h1s : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
      exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h1s) (by omega)
    · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)
  rw [hcol1] at key; omega

/-- The bottom-row corner (4, rowLen 4 - 1) always exists in a 5-row shape. -/
private lemma fiveRow_corner_bot {μ : YoungDiagram} (h5 : μ.rowLen 5 = 0)
    (h4 : 0 < μ.rowLen 4) : isCorner μ (4, μ.rowLen 4 - 1) := by
  refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega),
          fun h => ?_, fun h => ?_⟩
  · have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega
  · have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega

/-- Corners of a 5-row shape are classified into at most 5 positions. -/
private lemma fiveRow_corner_cases {μ : YoungDiagram} (h5 : μ.rowLen 5 = 0)
    (h4 : 0 < μ.rowLen 4) {cell : ℕ × ℕ} (hc : isCorner μ cell) :
    (cell = (0, μ.rowLen 0 - 1) ∧ μ.rowLen 1 < μ.rowLen 0) ∨
    (cell = (1, μ.rowLen 1 - 1) ∧ μ.rowLen 2 < μ.rowLen 1) ∨
    (cell = (2, μ.rowLen 2 - 1) ∧ μ.rowLen 3 < μ.rowLen 2) ∨
    (cell = (3, μ.rowLen 3 - 1) ∧ μ.rowLen 4 < μ.rowLen 3) ∨
    cell = (4, μ.rowLen 4 - 1) := by
  obtain ⟨hmem, hright, hbelow⟩ := hc
  obtain ⟨i, j⟩ := cell
  simp only [Prod.fst, Prod.snd] at *
  have hi_lt_5 : i < 5 := by
    by_contra hlt; push_neg at hlt
    have := (μ.rowLen_anti 5 i hlt).trans_eq h5
    exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp hmem) (by omega)
  have hj : j = μ.rowLen i - 1 := by
    have hlt : j < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp hmem
    have : ¬(j + 1 < μ.rowLen i) := fun h => hright (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    omega
  interval_cases i
  · left; refine ⟨by simpa, ?_⟩
    by_contra h; push_neg at h
    exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega) |> hj ▸ id)
  · right; left; refine ⟨by simpa, ?_⟩
    by_contra h; push_neg at h
    exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega) |> hj ▸ id)
  · right; right; left; refine ⟨by simpa, ?_⟩
    by_contra h; push_neg at h
    exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega) |> hj ▸ id)
  · right; right; right; left; refine ⟨by simpa, ?_⟩
    by_contra h; push_neg at h
    exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega) |> hj ▸ id)
  · right; right; right; right; simpa

/-- A 5-row YoungDiagram has card = rowLen 0 + rowLen 1 + rowLen 2 + rowLen 3 + rowLen 4. -/
private lemma fiveRow_card {μ : YoungDiagram} (h5 : μ.rowLen 5 = 0) :
    μ.card = μ.rowLen 0 + μ.rowLen 1 + μ.rowLen 2 + μ.rowLen 3 + μ.rowLen 4 := by
  have hrows_zero : ∀ i, 5 ≤ i → μ.rowLen i = 0 := fun i hi =>
    Nat.le_zero.mp (h5 ▸ μ.rowLen_anti 5 i hi)
  unfold YoungDiagram.card
  have hcells : μ.cells =
      (Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
      (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
      (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
      (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
      (Finset.range (μ.rowLen 4)).image (Prod.mk 4) := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
               Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · intro hlt
      have hi5 : i < 5 := by
        by_contra hge; push_neg at hge
        exact absurd hlt (by rw [hrows_zero i hge]; omega)
      interval_cases i
      · left; left; left; left; exact ⟨j, hlt, rfl, rfl⟩
      · left; left; left; right; exact ⟨j, hlt, rfl, rfl⟩
      · left; left; right; exact ⟨j, hlt, rfl, rfl⟩
      · left; right; exact ⟨j, hlt, rfl, rfl⟩
      · right; exact ⟨j, hlt, rfl, rfl⟩
    · rintro ((((⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) |
               ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩)
      all_goals exact hk
  have hd1 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0))
                       ((Finset.range (μ.rowLen 1)).image (Prod.mk 1)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      obtain ⟨_, _, rfl, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨_, _, h, _⟩ := Finset.mem_image.mp hy; exact absurd h (by norm_num)
  have hd2 : Disjoint
      ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
       (Finset.range (μ.rowLen 1)).image (Prod.mk 1))
      ((Finset.range (μ.rowLen 2)).image (Prod.mk 2)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd3 : Disjoint
      ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
       (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
       (Finset.range (μ.rowLen 2)).image (Prod.mk 2))
      ((Finset.range (μ.rowLen 3)).image (Prod.mk 3)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd4 : Disjoint
      ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
       (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
       (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
       (Finset.range (μ.rowLen 3)).image (Prod.mk 3))
      ((Finset.range (μ.rowLen 4)).image (Prod.mk 4)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
               ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  rw [hcells, Finset.card_union_of_disjoint hd4, Finset.card_union_of_disjoint hd3,
      Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_range, Finset.card_range, Finset.card_range, Finset.card_range,
      Finset.card_range]

/-- Arm product for corner (4, e-1) telescopes to e.
    ∏_{s ∈ range(e-1)} h(4,s)/(h(4,s)-1) = e, where h(4,s) = e-s. -/
private lemma fiveRow_arm_row4 (μ : YoungDiagram) (h5 : μ.rowLen 5 = 0)
    (he : isCorner μ (4, μ.rowLen 4 - 1)) :
    ∏ s ∈ Finset.range (μ.rowLen 4 - 1),
      ((hookLength μ 4 s : ℚ) / ((hookLength μ 4 s : ℚ) - 1)) =
    (μ.rowLen 4 : ℚ) := by
  set e := μ.rowLen 4
  have he_pos : 0 < e := by
    have := YoungDiagram.mem_iff_lt_rowLen.mp he.1; omega
  have hconv : ∀ s ∈ Finset.range (e - 1),
      (hookLength μ 4 s : ℚ) / ((hookLength μ 4 s : ℚ) - 1) =
      ((e : ℚ) - s) / ((e : ℚ) - s - 1) := by
    intro s hs
    have hsc : s < e - 1 := Finset.mem_range.mp hs
    have hmem : (4, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row4 h5 hmem]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv]
  rw [prod_div_telescope e (e - 1) (Nat.sub_lt he_pos Nat.one_pos)]
  push_cast; simp [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp he_pos))]

/-- Arm product for corner (3, d-1) in a 5-row shape:
    ∏_{s=0}^{d-2} h(3,s)/(h(3,s)-1) = (d+1)(d-e)/(d-e+1). -/
private lemma fiveRow_arm_row3 {μ : YoungDiagram} (h5 : μ.rowLen 5 = 0)
    (hde : μ.rowLen 4 < μ.rowLen 3) :
    ∏ s ∈ Finset.range (μ.rowLen 3 - 1),
      ((hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1)) =
    ((μ.rowLen 3 : ℚ) + 1) * ((μ.rowLen 3 : ℚ) - μ.rowLen 4) /
    ((μ.rowLen 3 : ℚ) - μ.rowLen 4 + 1) := by
  set d := μ.rowLen 3; set e := μ.rowLen 4
  -- Split range(d-1) into [0,e) and [e, d-1)
  rw [show Finset.range (d - 1) = Finset.range e ∪ Finset.Ico e (d - 1) from by
    ext s; simp [Finset.mem_Ico]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- First product: s ∈ [0,e), h(3,s) = d-s+1 → (d+1-s)/(d+1-s-1)
  have hconv1 : ∀ s ∈ Finset.range e,
      (hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1) =
      ((d : ℚ) + 1 - s) / ((d : ℚ) + 1 - s - 1) := by
    intro s hs
    have hse : s < e := Finset.mem_range.mp hs
    have hmem : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row3_lt h5 hmem hse]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (d + 1) e (by omega)]
  -- Second product: s ∈ [e, d-1), reindex t = s-e, h(3,t+e) = d-e-t
  have hconv2 : ∀ s ∈ Finset.Ico e (d - 1),
      (hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1) =
      ((d : ℚ) - s) / ((d : ℚ) - s - 1) := by
    intro s hs
    have ⟨hse, hsd⟩ := Finset.mem_Ico.mp hs
    have hmem : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row3_ge h5 hmem hse]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [show Finset.Ico e (d - 1) = (Finset.range (d - 1 - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2' : ∀ t ∈ Finset.range (d - 1 - e),
      (hookLength μ 3 (t + e) : ℚ) / ((hookLength μ 3 (t + e) : ℚ) - 1) =
      ((d : ℚ) - e - t) / ((d : ℚ) - e - t - 1) := by
    intro t ht
    have htm : t < d - 1 - e := Finset.mem_range.mp ht
    have hmem : (3, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row3_ge h5 hmem (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2', prod_div_telescope (d - e) (d - 1 - e) (by omega)]
  push_cast [Nat.cast_sub hde.le, Nat.cast_sub (show 1 ≤ d - e by omega)]
  have hne : (d : ℚ) - e + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - e + 1 by omega)
  field_simp [hne]; ring

/-- Arm product for corner (2, c-1) in a 5-row shape:
    ∏_{s=0}^{c-2} h(2,s)/(h(2,s)-1) = (c+2)(c-e+1)(c-d)/((c-e+2)(c-d+1)). -/
private lemma fiveRow_arm_row2 {μ : YoungDiagram} (h5 : μ.rowLen 5 = 0)
    (hdc : μ.rowLen 3 < μ.rowLen 2) :
    ∏ s ∈ Finset.range (μ.rowLen 2 - 1),
      ((hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1)) =
    ((μ.rowLen 2 : ℚ) + 2) * ((μ.rowLen 2 : ℚ) - μ.rowLen 4 + 1) *
    ((μ.rowLen 2 : ℚ) - μ.rowLen 3) /
    (((μ.rowLen 2 : ℚ) - μ.rowLen 4 + 2) * ((μ.rowLen 2 : ℚ) - μ.rowLen 3 + 1)) := by
  set c := μ.rowLen 2; set d := μ.rowLen 3; set e := μ.rowLen 4
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  -- Split range(c-1) into [0,e), [e,d), [d, c-1)
  rw [show Finset.range (c - 1) = Finset.range e ∪ Finset.Ico e d ∪ Finset.Ico d (c - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- Product 1: [0,e), h(2,s) = c-s+2 → (c+2-s)/(c+2-s-1)
  have hconv1 : ∀ s ∈ Finset.range e,
      (hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1) =
      ((c : ℚ) + 2 - s) / ((c : ℚ) + 2 - s - 1) := by
    intro s hs
    have hse : s < e := Finset.mem_range.mp hs
    have hmem : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row2_lt h5 hmem hse]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (c + 2) e (by omega)]
  -- Product 2: [e, d), h(2,t+e) = c-e+1-t → prod_div_telescope (c-e+1) (d-e)
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 2 (t + e) : ℚ) / ((hookLength μ 2 (t + e) : ℚ) - 1) =
      ((c : ℚ) - e + 1 - t) / ((c : ℚ) - e + 1 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (2, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row2_mid1 h5 hmem (by omega) (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (c - e + 1) (d - e) (by omega)]
  -- Product 3: [d, c-1), h(2,t+d) = c-d-t → prod_div_telescope (c-d) (c-1-d)
  rw [show Finset.Ico d (c - 1) = (Finset.range (c - 1 - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (c - 1 - d),
      (hookLength μ 2 (t + d) : ℚ) / ((hookLength μ 2 (t + d) : ℚ) - 1) =
      ((c : ℚ) - d - t) / ((c : ℚ) - d - t - 1) := by
    intro t ht
    have htm : t < c - 1 - d := Finset.mem_range.mp ht
    have hmem : (2, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row2_ge h5 hmem (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (c - d) (c - 1 - d) (by omega)]
  push_cast [Nat.cast_sub hed, Nat.cast_sub hdc.le, Nat.cast_sub (show 1 ≤ c - d by omega)]
  have hne1 : (c : ℚ) - e + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - e + 2 by omega)
  have hne2 : (c : ℚ) - d + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  field_simp [hne1, hne2]; ring

/-- Arm product for corner (1, b-1) in a 5-row shape:
    ∏_{s=0}^{b-2} h(1,s)/(h(1,s)-1) = (b+3)(b-e+2)(b-d+1)(b-c)/((b-e+3)(b-d+2)(b-c+1)). -/
private lemma fiveRow_arm_row1 {μ : YoungDiagram} (h5 : μ.rowLen 5 = 0)
    (hcb : μ.rowLen 2 < μ.rowLen 1) :
    ∏ s ∈ Finset.range (μ.rowLen 1 - 1),
      ((hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1)) =
    ((μ.rowLen 1 : ℚ) + 3) * ((μ.rowLen 1 : ℚ) - μ.rowLen 4 + 2) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 1) * ((μ.rowLen 1 : ℚ) - μ.rowLen 2) /
    (((μ.rowLen 1 : ℚ) - μ.rowLen 4 + 3) * ((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 2) *
     ((μ.rowLen 1 : ℚ) - μ.rowLen 2 + 1)) := by
  set b := μ.rowLen 1; set c := μ.rowLen 2; set d := μ.rowLen 3; set e := μ.rowLen 4
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  -- Split range(b-1) into [0,e), [e,d), [d,c), [c, b-1)
  rw [show Finset.range (b - 1) = Finset.range e ∪ Finset.Ico e d ∪
      Finset.Ico d c ∪ Finset.Ico c (b - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- Product 1: [0,e), h(1,s) = b-s+3
  have hconv1 : ∀ s ∈ Finset.range e,
      (hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1) =
      ((b : ℚ) + 3 - s) / ((b : ℚ) + 3 - s - 1) := by
    intro s hs
    have hse : s < e := Finset.mem_range.mp hs
    have hmem : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row1_lt h5 hmem hse]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (b + 3) e (by omega)]
  -- Product 2: [e, d), h(1,t+e) = b-e+2-t
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 1 (t + e) : ℚ) / ((hookLength μ 1 (t + e) : ℚ) - 1) =
      ((b : ℚ) - e + 2 - t) / ((b : ℚ) - e + 2 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (1, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row1_mid1 h5 hmem (by omega) (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (b - e + 2) (d - e) (by omega)]
  -- Product 3: [d, c), h(1,t+d) = b-d+1-t
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 1 (t + d) : ℚ) / ((hookLength μ 1 (t + d) : ℚ) - 1) =
      ((b : ℚ) - d + 1 - t) / ((b : ℚ) - d + 1 - t - 1) := by
    intro t ht
    have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (1, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row1_mid2 h5 hmem (by omega) (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (b - d + 1) (c - d) (by omega)]
  -- Product 4: [c, b-1), h(1,t+c) = b-c-t
  rw [show Finset.Ico c (b - 1) = (Finset.range (b - 1 - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (b - 1 - c),
      (hookLength μ 1 (t + c) : ℚ) / ((hookLength μ 1 (t + c) : ℚ) - 1) =
      ((b : ℚ) - c - t) / ((b : ℚ) - c - t - 1) := by
    intro t ht
    have htm : t < b - 1 - c := Finset.mem_range.mp ht
    have hmem : (1, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row1_ge h5 hmem (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (b - c) (b - 1 - c) (by omega)]
  push_cast [Nat.cast_sub hed, Nat.cast_sub hdc, Nat.cast_sub hcb.le,
             Nat.cast_sub (show 1 ≤ b - c by omega)]
  have hne1 : (b : ℚ) - e + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - e + 3 by omega)
  have hne2 : (b : ℚ) - d + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne3 : (b : ℚ) - c + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  field_simp [hne1, hne2, hne3]; ring

/-- Arm product for corner (0, a-1) in a 5-row shape:
    ∏_{s=0}^{a-2} h(0,s)/(h(0,s)-1) = (a+4)(a-e+3)(a-d+2)(a-c+1)(a-b)/
                                         ((a-e+4)(a-d+3)(a-c+2)(a-b+1)). -/
private lemma fiveRow_arm_row0 {μ : YoungDiagram} (h5 : μ.rowLen 5 = 0)
    (h4 : 0 < μ.rowLen 4) (hab : μ.rowLen 1 < μ.rowLen 0) :
    ∏ s ∈ Finset.range (μ.rowLen 0 - 1),
      ((hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1)) =
    ((μ.rowLen 0 : ℚ) + 4) * ((μ.rowLen 0 : ℚ) - μ.rowLen 4 + 3) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 2) * ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 1) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 1) /
    (((μ.rowLen 0 : ℚ) - μ.rowLen 4 + 4) * ((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 3) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 2) * ((μ.rowLen 0 : ℚ) - μ.rowLen 1 + 1)) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set c := μ.rowLen 2
  set d := μ.rowLen 3; set e := μ.rowLen 4
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  -- Split range(a-1) into [0,e), [e,d), [d,c), [c,b), [b, a-1)
  rw [show Finset.range (a - 1) = Finset.range e ∪ Finset.Ico e d ∪
      Finset.Ico d c ∪ Finset.Ico c b ∪ Finset.Ico b (a - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- Product 1: [0,e), h(0,s) = a-s+4
  have hconv1 : ∀ s ∈ Finset.range e,
      (hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1) =
      ((a : ℚ) + 4 - s) / ((a : ℚ) + 4 - s - 1) := by
    intro s hs
    have hse : s < e := Finset.mem_range.mp hs
    have hmem : (0, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row0_lt h5 hmem hse]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (a + 4) e (by omega)]
  -- Product 2: [e, d), h(0,t+e) = a-e+3-t
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 0 (t + e) : ℚ) / ((hookLength μ 0 (t + e) : ℚ) - 1) =
      ((a : ℚ) - e + 3 - t) / ((a : ℚ) - e + 3 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (0, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row0_mid1 h5 hmem (by omega) (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (a - e + 3) (d - e) (by omega)]
  -- Product 3: [d, c), h(0,t+d) = a-d+2-t
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 0 (t + d) : ℚ) / ((hookLength μ 0 (t + d) : ℚ) - 1) =
      ((a : ℚ) - d + 2 - t) / ((a : ℚ) - d + 2 - t - 1) := by
    intro t ht
    have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (0, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row0_mid2 h5 hmem (by omega) (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (a - d + 2) (c - d) (by omega)]
  -- Product 4: [c, b), h(0,t+c) = a-c+1-t
  rw [show Finset.Ico c b = (Finset.range (b - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (b - c),
      (hookLength μ 0 (t + c) : ℚ) / ((hookLength μ 0 (t + c) : ℚ) - 1) =
      ((a : ℚ) - c + 1 - t) / ((a : ℚ) - c + 1 - t - 1) := by
    intro t ht
    have htm : t < b - c := Finset.mem_range.mp ht
    have hmem : (0, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row0_mid3 h5 hmem (by omega) (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (a - c + 1) (b - c) (by omega)]
  -- Product 5: [b, a-1), h(0,t+b) = a-b-t
  rw [show Finset.Ico b (a - 1) = (Finset.range (a - 1 - b)).image (· + b) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (a - 1 - b),
      (hookLength μ 0 (t + b) : ℚ) / ((hookLength μ 0 (t + b) : ℚ) - 1) =
      ((a : ℚ) - b - t) / ((a : ℚ) - b - t - 1) := by
    intro t ht
    have htm : t < a - 1 - b := Finset.mem_range.mp ht
    have hmem : (0, t + b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [fiveRow_hookLen_row0_ge h5 hmem (by omega)]
    push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (a - b) (a - 1 - b) (by omega)]
  push_cast [Nat.cast_sub hed, Nat.cast_sub hdc, Nat.cast_sub hcb, Nat.cast_sub hab.le,
             Nat.cast_sub (show 1 ≤ a - b by omega)]
  have hne1 : (a : ℚ) - e + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - e + 4 by omega)
  have hne2 : (a : ℚ) - d + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne3 : (a : ℚ) - c + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne4 : (a : ℚ) - b + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4]; ring

/-- The hook walk identity for exactly-5-row Young diagrams.
    Direct computation via hookProd_ratio_formula and telescoping — no HLF used.
    NON-CIRCULAR: does not call hook_length_formula_Q or hook_walk_identity. -/
lemma hook_walk_identity_fiveRow (μ : YoungDiagram)
    (h5 : μ.rowLen 5 = 0) (h4 : 0 < μ.rowLen 4) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / (hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) : ℚ))
    = (μ.card : ℚ) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set c := μ.rowLen 2
  set d := μ.rowLen 3; set e := μ.rowLen 4
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  have hba : b ≤ a := μ.rowLen_anti 0 1 (by omega)
  have hbot : isCorner μ (4, e - 1) := fiveRow_corner_bot h5 h4
  have hcard : (μ.card : ℚ) = (a : ℚ) + b + c + d + e := by
    exact_mod_cast fiveRow_card h5
  rw [hcard]
  let ratio : ℕ × ℕ → ℚ := fun x =>
    if hx : isCorner μ x then (hookProd μ : ℚ) / hookProd (removeCorner μ x hx) else 0
  have hconvert : ∑ cc ∈ (corners μ).attach,
        ((hookProd μ : ℚ) / hookProd (removeCorner μ cc.val (mem_corners.mp cc.prop))) =
      ∑ x ∈ corners μ, ratio x := by
    rw [← Finset.sum_attach (f := ratio)]
    apply Finset.sum_congr rfl
    intro cx _; exact dif_pos (mem_corners.mp cx.2)
  have hsub : corners μ ⊆
      ({(4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases fiveRow_corner_cases h5 h4 (mem_corners.mp hx) with
      ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | heq
    · right; right; right; right; exact heq
    · right; right; right; left; exact heq
    · right; right; left; exact heq
    · right; left; exact heq
    · left; exact heq
  have hext : ∑ x ∈ corners μ, ratio x =
      ∑ x ∈ ({(4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
              Finset (ℕ × ℕ)), ratio x := by
    apply Finset.sum_subset hsub
    intro x _ hxnc; exact dif_neg (mt mem_corners.mpr hxnc)
  -- Compute ratio for corner (4, e-1)
  have hR4 : ratio (4, e - 1) =
      (e : ℚ) * ((d : ℚ) - e + 2) / ((d : ℚ) - e + 1) *
      ((c : ℚ) - e + 3) / ((c : ℚ) - e + 2) *
      ((b : ℚ) - e + 4) / ((b : ℚ) - e + 3) *
      ((a : ℚ) - e + 5) / ((a : ℚ) - e + 4) := by
    simp only [ratio, dif_pos hbot]
    rw [hookProd_ratio_formula hbot]
    simp only [Prod.fst, Prod.snd]
    rw [fiveRow_arm_row4 μ h5 hbot]
    -- Leg: rows 0,1,2,3 at column e-1 (zone s < e)
    have he1 : e - 1 < e := Nat.sub_lt h4 Nat.one_pos
    have hmem0 : (0, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem1 : (1, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem2 : (2, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem3 : (3, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [show Finset.range 4 = {0, 1, 2, 3} from by ext k; simp; omega]
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
        Finset.prod_insert (by simp), Finset.prod_singleton]
    rw [fiveRow_hookLen_row0_lt h5 hmem0 he1,
        fiveRow_hookLen_row1_lt h5 hmem1 he1,
        fiveRow_hookLen_row2_lt h5 hmem2 he1,
        fiveRow_hookLen_row3_lt h5 hmem3 he1]
    push_cast [Nat.cast_sub (show 1 ≤ e from h4),
               Nat.cast_sub (show e - 1 ≤ a by omega),
               Nat.cast_sub (show e - 1 ≤ b by omega),
               Nat.cast_sub (show e - 1 ≤ c by omega),
               Nat.cast_sub (show e - 1 ≤ d by omega)]
    ring
  -- Compute ratio for corner (3, d-1) [when d > e]
  have hR3 : ratio (3, d - 1) =
      ((d : ℚ) + 1) * ((d : ℚ) - e) / ((d : ℚ) - e + 1) *
      ((c : ℚ) - d + 2) / ((c : ℚ) - d + 1) *
      ((b : ℚ) - d + 3) / ((b : ℚ) - d + 2) *
      ((a : ℚ) - d + 4) / ((a : ℚ) - d + 3) := by
    by_cases hde : e < d
    · have hmid : isCorner μ (3, d - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [fiveRow_arm_row3 h5 hde]
      -- Leg: rows 0,1,2 at column d-1 (zone [e,d))
      have hd1 : d - 1 < d := Nat.sub_lt (by omega) Nat.one_pos
      have hed1 : e ≤ d - 1 := by omega
      have hmem0 : (0, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 3 = {0, 1, 2} from by ext k; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [fiveRow_hookLen_row0_mid1 h5 hmem0 hed1 (by omega),
          fiveRow_hookLen_row1_mid1 h5 hmem1 hed1 (by omega),
          fiveRow_hookLen_row2_mid1 h5 hmem2 hed1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ d from by omega),
                 Nat.cast_sub (show d - 1 ≤ a by omega),
                 Nat.cast_sub (show d - 1 ≤ b by omega),
                 Nat.cast_sub (show d - 1 ≤ c by omega),
                 Nat.cast_sub hde.le]
      ring
    · -- d = e: corner (3, d-1) doesn't exist; ratio = 0
      have hde_eq : d = e := Nat.le_antisymm (not_lt.mp hde) hed
      have hnotcorner : ¬ isCorner μ (3, d - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (d : ℚ) - e = 0 := by rw [hde_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (2, c-1) [when c > d]
  have hR2 : ratio (2, c - 1) =
      ((c : ℚ) + 2) * ((c : ℚ) - e + 1) * ((c : ℚ) - d) /
      (((c : ℚ) - e + 2) * ((c : ℚ) - d + 1)) *
      ((b : ℚ) - c + 2) / ((b : ℚ) - c + 1) *
      ((a : ℚ) - c + 3) / ((a : ℚ) - c + 2) := by
    by_cases hdc' : d < c
    · have hmid : isCorner μ (2, c - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [fiveRow_arm_row2 h5 hdc']
      -- Leg: rows 0,1 at column c-1 (zone [d,c))
      have hc1 : c - 1 < c := Nat.sub_lt (by omega) Nat.one_pos
      have hdc1 : d ≤ c - 1 := by omega
      have hmem0 : (0, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 2 = {0, 1} from by ext k; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [fiveRow_hookLen_row0_mid2 h5 hmem0 hdc1 (by omega),
          fiveRow_hookLen_row1_mid2 h5 hmem1 hdc1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ c by omega),
                 Nat.cast_sub (show c - 1 ≤ a by omega),
                 Nat.cast_sub (show c - 1 ≤ b by omega),
                 Nat.cast_sub hdc'.le, Nat.cast_sub hed]
      ring
    · -- c = d: corner (2, c-1) doesn't exist; ratio = 0
      have hdc_eq : c = d := Nat.le_antisymm (not_lt.mp hdc') hdc
      have hnotcorner : ¬ isCorner μ (2, c - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (c : ℚ) - d = 0 := by rw [hdc_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (1, b-1) [when b > c]
  have hR1 : ratio (1, b - 1) =
      ((b : ℚ) + 3) * ((b : ℚ) - e + 2) * ((b : ℚ) - d + 1) * ((b : ℚ) - c) /
      (((b : ℚ) - e + 3) * ((b : ℚ) - d + 2) * ((b : ℚ) - c + 1)) *
      ((a : ℚ) - b + 2) / ((a : ℚ) - b + 1) := by
    by_cases hcb' : c < b
    · have hmid : isCorner μ (1, b - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [fiveRow_arm_row1 h5 hcb']
      -- Leg: row 0 at column b-1 (zone [c,b))
      have hmem0 : (0, b - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      rw [fiveRow_hookLen_row0_mid3 h5 hmem0 (by omega) (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ b by omega),
                 Nat.cast_sub (show b - 1 ≤ a by omega),
                 Nat.cast_sub hcb'.le, Nat.cast_sub hdc, Nat.cast_sub hed]
      ring
    · -- b = c: corner (1, b-1) doesn't exist; ratio = 0
      have hbc_eq : b = c := Nat.le_antisymm (not_lt.mp hcb') hcb
      have hnotcorner : ¬ isCorner μ (1, b - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (b : ℚ) - c = 0 := by rw [hbc_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (0, a-1) [when a > b]
  have hR0 : ratio (0, a - 1) =
      ((a : ℚ) + 4) * ((a : ℚ) - e + 3) * ((a : ℚ) - d + 2) * ((a : ℚ) - c + 1) *
      ((a : ℚ) - b) /
      (((a : ℚ) - e + 4) * ((a : ℚ) - d + 3) * ((a : ℚ) - c + 2) *
       ((a : ℚ) - b + 1)) := by
    by_cases hab : b < a
    · have htop : isCorner μ (0, a - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos htop]
      rw [hookProd_ratio_formula htop]
      simp only [Prod.fst, Prod.snd, Finset.prod_range_zero, mul_one]
      rw [fiveRow_arm_row0 h5 h4 hab]
      push_cast [Nat.cast_sub hab.le, Nat.cast_sub hcb, Nat.cast_sub hdc, Nat.cast_sub hed]
      ring
    · -- a = b: corner (0, a-1) doesn't exist; ratio = 0
      have hab_eq : a = b := Nat.le_antisymm (not_lt.mp hab) hba
      have hnotcorner : ¬ isCorner μ (0, a - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (a : ℚ) - b = 0 := by rw [hab_eq]; ring
      rw [this]; ring
  rw [hconvert, hext]
  -- Sum over 5 corners using distinctness
  have hne43 : (4, e - 1) ∉ ({(3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
      Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne32 : (3, d - 1) ∉ ({(2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hne21 : (2, c - 1) ∉ ({(1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hne10 : (1, b - 1) ∉ ({(0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  rw [show ({(4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) =
      insert (4, e - 1) (insert (3, d - 1) (insert (2, c - 1) (insert (1, b - 1)
        {(0, a - 1)}))) from rfl,
      Finset.sum_insert hne43, Finset.sum_insert hne32,
      Finset.sum_insert hne21, Finset.sum_insert hne10, Finset.sum_singleton,
      hR4, hR3, hR2, hR1, hR0]
  -- Close with field_simp + ring
  have hne_de1 : (d : ℚ) - e + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < d - e + 1 by omega)
  have hne_ce2 : (c : ℚ) - e + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - e + 2 by omega)
  have hne_be3 : (b : ℚ) - e + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - e + 3 by omega)
  have hne_ae4 : (a : ℚ) - e + 4 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - e + 4 by omega)
  have hne_cd1 : (c : ℚ) - d + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  have hne_bd2 : (b : ℚ) - d + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne_ad3 : (a : ℚ) - d + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne_bc1 : (b : ℚ) - c + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  have hne_ac2 : (a : ℚ) - c + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne_ab1 : (a : ℚ) - b + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  push_cast [Nat.cast_sub hed, Nat.cast_sub hdc, Nat.cast_sub hcb, Nat.cast_sub hba,
             Nat.cast_sub (show e ≤ c by omega), Nat.cast_sub (show e ≤ b by omega),
             Nat.cast_sub (show e ≤ a by omega), Nat.cast_sub (show d ≤ b by omega),
             Nat.cast_sub (show d ≤ a by omega), Nat.cast_sub (show c ≤ a by omega)]
  field_simp [hne_de1, hne_ce2, hne_be3, hne_ae4, hne_cd1, hne_bd2,
              hne_ad3, hne_bc1, hne_ac2, hne_ab1]
  ring


-- ============================================================
-- PART XX: Hook Walk Identity for 6-Row Shapes
-- ============================================================
/-
  For a 6-row Young diagram [a,b,c,d,e,f] (a≥b≥c≥d≥e≥f≥1, rowLen 6 = 0):
  - n = a+b+c+d+e+f cells
  - Corners: (5,f-1) always; (4,e-1) when e>f; (3,d-1) when d>e;
             (2,c-1) when c>d; (1,b-1) when b>c; (0,a-1) when a>b
  - hook_walk_identity proved by direct ratio computation (same pattern as fiveRow)
-/

/-- colLen(s) = 6 for s < rowLen 5 in a 6-row shape. -/
private lemma sixRow_colLen_lt {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hs : s < μ.rowLen 5) : μ.colLen s = 6 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h6s : (6, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h6s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs)

/-- colLen(s) = 5 for rowLen 5 ≤ s < rowLen 4 in a 6-row shape. -/
private lemma sixRow_colLen_mid1 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    μ.colLen s = 5 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h5s : (5, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h5s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 4 for rowLen 4 ≤ s < rowLen 3 in a 6-row shape. -/
private lemma sixRow_colLen_mid2 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    μ.colLen s = 4 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h4s : (4, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h4s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 3 for rowLen 3 ≤ s < rowLen 2 in a 6-row shape. -/
private lemma sixRow_colLen_mid3 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    μ.colLen s = 3 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h3s : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h3s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 2 for rowLen 2 ≤ s < rowLen 1 in a 6-row shape. -/
private lemma sixRow_colLen_mid4 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    μ.colLen s = 2 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h2s : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h2s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

-- hookLen lemmas: h(r,s) = rowLen(r) + colLen(s) - r - s - 1

/-- h(5,s) = rowLen 5 - s for (5,s)∈μ. -/
private lemma sixRow_hookLen_row5 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (5, s) ∈ μ) :
    hookLength μ 5 s = μ.rowLen 5 - s := by
  have hs : s < μ.rowLen 5 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_lt h6 hs] at key; omega

/-- h(4,s) = rowLen 4 - s + 1 for s < rowLen 5. -/
private lemma sixRow_hookLen_row4_lt {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (4, s) ∈ μ) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 4 s = μ.rowLen 4 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_lt h6 hs_lt] at key; omega

/-- h(4,s) = rowLen 4 - s for rowLen 5 ≤ s. -/
private lemma sixRow_hookLen_row4_ge {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (4, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) :
    hookLength μ 4 s = μ.rowLen 4 - s := by
  have hs_lt : s < μ.rowLen 4 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid1 h6 hs_ge hs_lt] at key; omega

/-- h(3,s) = rowLen 3 - s + 2 for s < rowLen 5. -/
private lemma sixRow_hookLen_row3_lt {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (3, s) ∈ μ) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 3 s = μ.rowLen 3 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_lt h6 hs_lt] at key; omega

/-- h(3,s) = rowLen 3 - s + 1 for rowLen 5 ≤ s < rowLen 4. -/
private lemma sixRow_hookLen_row3_mid1 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (3, s) ∈ μ)
    (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 3 s = μ.rowLen 3 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid1 h6 hs_ge hs_lt] at key; omega

/-- h(3,s) = rowLen 3 - s for rowLen 4 ≤ s. -/
private lemma sixRow_hookLen_row3_ge {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (3, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s) :
    hookLength μ 3 s = μ.rowLen 3 - s := by
  have hs_lt : s < μ.rowLen 3 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid2 h6 hs_ge hs_lt] at key; omega

/-- h(2,s) = rowLen 2 - s + 3 for s < rowLen 5. -/
private lemma sixRow_hookLen_row2_lt {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (2, s) ∈ μ) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 2 s = μ.rowLen 2 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_lt h6 hs_lt] at key; omega

/-- h(2,s) = rowLen 2 - s + 2 for rowLen 5 ≤ s < rowLen 4. -/
private lemma sixRow_hookLen_row2_mid1 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (2, s) ∈ μ)
    (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 2 s = μ.rowLen 2 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid1 h6 hs_ge hs_lt] at key; omega

/-- h(2,s) = rowLen 2 - s + 1 for rowLen 4 ≤ s < rowLen 3. -/
private lemma sixRow_hookLen_row2_mid2 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (2, s) ∈ μ)
    (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 2 s = μ.rowLen 2 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid2 h6 hs_ge hs_lt] at key; omega

/-- h(2,s) = rowLen 2 - s for rowLen 3 ≤ s. -/
private lemma sixRow_hookLen_row2_ge {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 3 ≤ s) :
    hookLength μ 2 s = μ.rowLen 2 - s := by
  have hs_lt : s < μ.rowLen 2 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid3 h6 hs_ge hs_lt] at key; omega

/-- h(1,s) = rowLen 1 - s + 4 for s < rowLen 5. -/
private lemma sixRow_hookLen_row1_lt {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (1, s) ∈ μ) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 1 s = μ.rowLen 1 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_lt h6 hs_lt] at key; omega

/-- h(1,s) = rowLen 1 - s + 3 for rowLen 5 ≤ s < rowLen 4. -/
private lemma sixRow_hookLen_row1_mid1 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (1, s) ∈ μ)
    (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 1 s = μ.rowLen 1 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid1 h6 hs_ge hs_lt] at key; omega

/-- h(1,s) = rowLen 1 - s + 2 for rowLen 4 ≤ s < rowLen 3. -/
private lemma sixRow_hookLen_row1_mid2 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (1, s) ∈ μ)
    (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 1 s = μ.rowLen 1 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid2 h6 hs_ge hs_lt] at key; omega

/-- h(1,s) = rowLen 1 - s + 1 for rowLen 3 ≤ s < rowLen 2. -/
private lemma sixRow_hookLen_row1_mid3 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (1, s) ∈ μ)
    (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    hookLength μ 1 s = μ.rowLen 1 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid3 h6 hs_ge hs_lt] at key; omega

/-- h(1,s) = rowLen 1 - s for rowLen 2 ≤ s. -/
private lemma sixRow_hookLen_row1_ge {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 2 ≤ s) :
    hookLength μ 1 s = μ.rowLen 1 - s := by
  have hs_lt : s < μ.rowLen 1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid4 h6 hs_ge hs_lt] at key; omega

/-- h(0,s) = rowLen 0 - s + 5 for s < rowLen 5. -/
private lemma sixRow_hookLen_row0_lt {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (0, s) ∈ μ) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 0 s = μ.rowLen 0 - s + 5 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_lt h6 hs_lt] at key; omega

/-- h(0,s) = rowLen 0 - s + 4 for rowLen 5 ≤ s < rowLen 4. -/
private lemma sixRow_hookLen_row0_mid1 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (0, s) ∈ μ)
    (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 0 s = μ.rowLen 0 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid1 h6 hs_ge hs_lt] at key; omega

/-- h(0,s) = rowLen 0 - s + 3 for rowLen 4 ≤ s < rowLen 3. -/
private lemma sixRow_hookLen_row0_mid2 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (0, s) ∈ μ)
    (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 0 s = μ.rowLen 0 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid2 h6 hs_ge hs_lt] at key; omega

/-- h(0,s) = rowLen 0 - s + 2 for rowLen 3 ≤ s < rowLen 2. -/
private lemma sixRow_hookLen_row0_mid3 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (0, s) ∈ μ)
    (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    hookLength μ 0 s = μ.rowLen 0 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid3 h6 hs_ge hs_lt] at key; omega

/-- h(0,s) = rowLen 0 - s + 1 for rowLen 2 ≤ s < rowLen 1. -/
private lemma sixRow_hookLen_row0_mid4 {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (0, s) ∈ μ)
    (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    hookLength μ 0 s = μ.rowLen 0 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [sixRow_colLen_mid4 h6 hs_ge hs_lt] at key; omega

/-- h(0,s) = rowLen 0 - s for rowLen 1 ≤ s. -/
private lemma sixRow_hookLen_row0_ge {μ : YoungDiagram} {s : ℕ}
    (h6 : μ.rowLen 6 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 1 ≤ s) :
    hookLength μ 0 s = μ.rowLen 0 - s := by
  have hs_lt : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  have hcol1 : μ.colLen s = 1 := by
    apply Nat.le_antisymm
    · by_contra hlt; push_neg at hlt
      have h1s : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
      have := YoungDiagram.mem_iff_lt_rowLen.mp h1s; omega
    · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)
  rw [hcol1] at key; omega

/-- Card of a 6-row diagram. -/
private lemma sixRow_card {μ : YoungDiagram} (h6 : μ.rowLen 6 = 0) :
    μ.card = μ.rowLen 0 + μ.rowLen 1 + μ.rowLen 2 + μ.rowLen 3 + μ.rowLen 4 + μ.rowLen 5 := by
  have hcells : μ.cells =
      (Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
      (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
      (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
      (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
      (Finset.range (μ.rowLen 4)).image (Prod.mk 4) ∪
      (Finset.range (μ.rowLen 5)).image (Prod.mk 5) := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
               Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · intro h
      interval_cases i <;> simp_all <;> omega
    · rintro (((((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
                ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) <;>
      simp_all <;> omega
  simp only [YoungDiagram.card, hcells]
  have hd1 : Disjoint
      ((Finset.range (μ.rowLen 0)).image (Prod.mk 0))
      ((Finset.range (μ.rowLen 1)).image (Prod.mk 1)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ⟨_, _, rfl, rfl⟩ := hx; obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd2 : Disjoint
      ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
       (Finset.range (μ.rowLen 1)).image (Prod.mk 1))
      ((Finset.range (μ.rowLen 2)).image (Prod.mk 2)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd3 : Disjoint
      ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
       (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
       (Finset.range (μ.rowLen 2)).image (Prod.mk 2))
      ((Finset.range (μ.rowLen 3)).image (Prod.mk 3)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd4 : Disjoint
      ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
       (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
       (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
       (Finset.range (μ.rowLen 3)).image (Prod.mk 3))
      ((Finset.range (μ.rowLen 4)).image (Prod.mk 4)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
               ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd5 : Disjoint
      ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
       (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
       (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
       (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
       (Finset.range (μ.rowLen 4)).image (Prod.mk 4))
      ((Finset.range (μ.rowLen 5)).image (Prod.mk 5)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
               ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  rw [Finset.card_union_of_disjoint hd5, Finset.card_union_of_disjoint hd4,
      Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
      Finset.card_union_of_disjoint hd1,
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun p q h => (Prod.mk.inj h).2),
      Finset.card_range, Finset.card_range, Finset.card_range,
      Finset.card_range, Finset.card_range, Finset.card_range]

/-- Arm product for corner (5, f-1) telescopes to f. -/
private lemma sixRow_arm_row5 (μ : YoungDiagram) (h6 : μ.rowLen 6 = 0)
    (hf : isCorner μ (5, μ.rowLen 5 - 1)) :
    ∏ s ∈ Finset.range (μ.rowLen 5 - 1),
      ((hookLength μ 5 s : ℚ) / ((hookLength μ 5 s : ℚ) - 1)) =
    (μ.rowLen 5 : ℚ) := by
  set f := μ.rowLen 5
  have hf_pos : 0 < f := by
    have := YoungDiagram.mem_iff_lt_rowLen.mp hf.1; omega
  have hconv : ∀ s ∈ Finset.range (f - 1),
      (hookLength μ 5 s : ℚ) / ((hookLength μ 5 s : ℚ) - 1) =
      ((f : ℚ) - s) / ((f : ℚ) - s - 1) := by
    intro s hs
    have hsc : s < f - 1 := Finset.mem_range.mp hs
    have hmem : (5, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row5 h6 hmem]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv]
  rw [prod_div_telescope f (f - 1) (Nat.sub_lt hf_pos Nat.one_pos)]
  push_cast; simp [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hf_pos))]

/-- Arm product for corner (4, e-1) in a 6-row shape:
    ∏ = (e+1)(e-f)/(e-f+1). -/
private lemma sixRow_arm_row4 {μ : YoungDiagram} (h6 : μ.rowLen 6 = 0)
    (hef : μ.rowLen 5 < μ.rowLen 4) :
    ∏ s ∈ Finset.range (μ.rowLen 4 - 1),
      ((hookLength μ 4 s : ℚ) / ((hookLength μ 4 s : ℚ) - 1)) =
    ((μ.rowLen 4 : ℚ) + 1) * ((μ.rowLen 4 : ℚ) - μ.rowLen 5) /
    ((μ.rowLen 4 : ℚ) - μ.rowLen 5 + 1) := by
  set e := μ.rowLen 4; set f := μ.rowLen 5
  -- Split range(e-1) into [0,f) and [f, e-1)
  rw [show Finset.range (e - 1) = Finset.range f ∪ Finset.Ico f (e - 1) from by
    ext s; simp [Finset.mem_Ico]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- Product 1: [0,f), h(4,s) = e-s+1
  have hconv1 : ∀ s ∈ Finset.range f,
      (hookLength μ 4 s : ℚ) / ((hookLength μ 4 s : ℚ) - 1) =
      ((e : ℚ) + 1 - s) / ((e : ℚ) + 1 - s - 1) := by
    intro s hs
    have hse : s < f := Finset.mem_range.mp hs
    have hmem : (4, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row4_lt h6 hmem hse]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (e + 1) f (by omega)]
  -- Product 2: [f, e-1), reindex t = s-f, h(4,t+f) = e-f-t
  rw [show Finset.Ico f (e - 1) = (Finset.range (e - 1 - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (e - 1 - f),
      (hookLength μ 4 (t + f) : ℚ) / ((hookLength μ 4 (t + f) : ℚ) - 1) =
      ((e : ℚ) - f - t) / ((e : ℚ) - f - t - 1) := by
    intro t ht
    have htm : t < e - 1 - f := Finset.mem_range.mp ht
    have hmem : (4, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row4_ge h6 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (e - f) (e - 1 - f) (by omega)]
  push_cast [Nat.cast_sub hef.le, Nat.cast_sub (show 1 ≤ e - f by omega)]
  have hne : (e : ℚ) - f + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - f + 1 by omega)
  field_simp [hne]; ring

/-- Arm product for corner (3, d-1) in a 6-row shape:
    ∏ = (d+2)(d-f+1)(d-e)/((d+2-f)(d-e+1)). -/
private lemma sixRow_arm_row3 {μ : YoungDiagram} (h6 : μ.rowLen 6 = 0)
    (hed : μ.rowLen 4 < μ.rowLen 3) :
    ∏ s ∈ Finset.range (μ.rowLen 3 - 1),
      ((hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1)) =
    ((μ.rowLen 3 : ℚ) + 2) * ((μ.rowLen 3 : ℚ) - μ.rowLen 5 + 1) *
    ((μ.rowLen 3 : ℚ) - μ.rowLen 4) /
    (((μ.rowLen 3 : ℚ) - μ.rowLen 5 + 2) * ((μ.rowLen 3 : ℚ) - μ.rowLen 4 + 1)) := by
  set d := μ.rowLen 3; set e := μ.rowLen 4; set f := μ.rowLen 5
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  -- Split range(d-1) into [0,f), [f,e), [e, d-1)
  rw [show Finset.range (d - 1) = Finset.range f ∪ Finset.Ico f e ∪ Finset.Ico e (d - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- Product 1: [0,f), h(3,s) = d-s+2
  have hconv1 : ∀ s ∈ Finset.range f,
      (hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1) =
      ((d : ℚ) + 2 - s) / ((d : ℚ) + 2 - s - 1) := by
    intro s hs
    have hse : s < f := Finset.mem_range.mp hs
    have hmem : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row3_lt h6 hmem hse]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (d + 2) f (by omega)]
  -- Product 2: [f, e), h(3,t+f) = d-f+1-t
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 3 (t + f) : ℚ) / ((hookLength μ 3 (t + f) : ℚ) - 1) =
      ((d : ℚ) - f + 1 - t) / ((d : ℚ) - f + 1 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (3, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row3_mid1 h6 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (d - f + 1) (e - f) (by omega)]
  -- Product 3: [e, d-1), h(3,t+e) = d-e-t
  rw [show Finset.Ico e (d - 1) = (Finset.range (d - 1 - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (d - 1 - e),
      (hookLength μ 3 (t + e) : ℚ) / ((hookLength μ 3 (t + e) : ℚ) - 1) =
      ((d : ℚ) - e - t) / ((d : ℚ) - e - t - 1) := by
    intro t ht
    have htm : t < d - 1 - e := Finset.mem_range.mp ht
    have hmem : (3, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row3_ge h6 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (d - e) (d - 1 - e) (by omega)]
  push_cast [Nat.cast_sub hfe, Nat.cast_sub hed.le, Nat.cast_sub (show 1 ≤ d - e by omega)]
  have hne1 : (d : ℚ) - f + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - f + 2 by omega)
  have hne2 : (d : ℚ) - e + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - e + 1 by omega)
  field_simp [hne1, hne2]; ring

/-- Arm product for corner (2, c-1) in a 6-row shape:
    ∏ = (c+3)(c-f+2)(c-e+1)(c-d)/((c+3-f)(c-e+2)(c-d+1)). -/
private lemma sixRow_arm_row2 {μ : YoungDiagram} (h6 : μ.rowLen 6 = 0)
    (hdc : μ.rowLen 3 < μ.rowLen 2) :
    ∏ s ∈ Finset.range (μ.rowLen 2 - 1),
      ((hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1)) =
    ((μ.rowLen 2 : ℚ) + 3) * ((μ.rowLen 2 : ℚ) - μ.rowLen 5 + 2) *
    ((μ.rowLen 2 : ℚ) - μ.rowLen 4 + 1) * ((μ.rowLen 2 : ℚ) - μ.rowLen 3) /
    (((μ.rowLen 2 : ℚ) - μ.rowLen 5 + 3) * ((μ.rowLen 2 : ℚ) - μ.rowLen 4 + 2) *
     ((μ.rowLen 2 : ℚ) - μ.rowLen 3 + 1)) := by
  set c := μ.rowLen 2; set d := μ.rowLen 3; set e := μ.rowLen 4; set f := μ.rowLen 5
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  rw [show Finset.range (c - 1) =
      Finset.range f ∪ Finset.Ico f e ∪ Finset.Ico e d ∪ Finset.Ico d (c - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- Product 1: [0,f), h(2,s) = c-s+3
  have hconv1 : ∀ s ∈ Finset.range f,
      (hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1) =
      ((c : ℚ) + 3 - s) / ((c : ℚ) + 3 - s - 1) := by
    intro s hs
    have hse : s < f := Finset.mem_range.mp hs
    have hmem : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row2_lt h6 hmem hse]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (c + 3) f (by omega)]
  -- Product 2: [f, e), h(2,t+f) = c-f+2-t
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 2 (t + f) : ℚ) / ((hookLength μ 2 (t + f) : ℚ) - 1) =
      ((c : ℚ) - f + 2 - t) / ((c : ℚ) - f + 2 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (2, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row2_mid1 h6 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (c - f + 2) (e - f) (by omega)]
  -- Product 3: [e, d), h(2,t+e) = c-e+1-t
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 2 (t + e) : ℚ) / ((hookLength μ 2 (t + e) : ℚ) - 1) =
      ((c : ℚ) - e + 1 - t) / ((c : ℚ) - e + 1 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (2, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row2_mid2 h6 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (c - e + 1) (d - e) (by omega)]
  -- Product 4: [d, c-1), h(2,t+d) = c-d-t
  rw [show Finset.Ico d (c - 1) = (Finset.range (c - 1 - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (c - 1 - d),
      (hookLength μ 2 (t + d) : ℚ) / ((hookLength μ 2 (t + d) : ℚ) - 1) =
      ((c : ℚ) - d - t) / ((c : ℚ) - d - t - 1) := by
    intro t ht
    have htm : t < c - 1 - d := Finset.mem_range.mp ht
    have hmem : (2, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row2_ge h6 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (c - d) (c - 1 - d) (by omega)]
  push_cast [Nat.cast_sub hfe, Nat.cast_sub hed, Nat.cast_sub hdc.le,
             Nat.cast_sub (show 1 ≤ c - d by omega)]
  have hne1 : (c : ℚ) - f + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - f + 3 by omega)
  have hne2 : (c : ℚ) - e + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - e + 2 by omega)
  have hne3 : (c : ℚ) - d + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  field_simp [hne1, hne2, hne3]; ring

/-- Arm product for corner (1, b-1) in a 6-row shape. -/
private lemma sixRow_arm_row1 {μ : YoungDiagram} (h6 : μ.rowLen 6 = 0)
    (hcb : μ.rowLen 2 < μ.rowLen 1) :
    ∏ s ∈ Finset.range (μ.rowLen 1 - 1),
      ((hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1)) =
    ((μ.rowLen 1 : ℚ) + 4) * ((μ.rowLen 1 : ℚ) - μ.rowLen 5 + 3) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 4 + 2) * ((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 1) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 2) /
    (((μ.rowLen 1 : ℚ) - μ.rowLen 5 + 4) * ((μ.rowLen 1 : ℚ) - μ.rowLen 4 + 3) *
     ((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 2) * ((μ.rowLen 1 : ℚ) - μ.rowLen 2 + 1)) := by
  set b := μ.rowLen 1; set c := μ.rowLen 2; set d := μ.rowLen 3
  set e := μ.rowLen 4; set f := μ.rowLen 5
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  rw [show Finset.range (b - 1) =
      Finset.range f ∪ Finset.Ico f e ∪ Finset.Ico e d ∪ Finset.Ico d c ∪
      Finset.Ico c (b - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- Product 1: [0,f), h(1,s) = b-s+4
  have hconv1 : ∀ s ∈ Finset.range f,
      (hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1) =
      ((b : ℚ) + 4 - s) / ((b : ℚ) + 4 - s - 1) := by
    intro s hs
    have hse : s < f := Finset.mem_range.mp hs
    have hmem : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row1_lt h6 hmem hse]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (b + 4) f (by omega)]
  -- Product 2: [f, e), h(1,t+f) = b-f+3-t
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 1 (t + f) : ℚ) / ((hookLength μ 1 (t + f) : ℚ) - 1) =
      ((b : ℚ) - f + 3 - t) / ((b : ℚ) - f + 3 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (1, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row1_mid1 h6 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (b - f + 3) (e - f) (by omega)]
  -- Product 3: [e, d), h(1,t+e) = b-e+2-t
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 1 (t + e) : ℚ) / ((hookLength μ 1 (t + e) : ℚ) - 1) =
      ((b : ℚ) - e + 2 - t) / ((b : ℚ) - e + 2 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (1, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row1_mid2 h6 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (b - e + 2) (d - e) (by omega)]
  -- Product 4: [d, c), h(1,t+d) = b-d+1-t
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 1 (t + d) : ℚ) / ((hookLength μ 1 (t + d) : ℚ) - 1) =
      ((b : ℚ) - d + 1 - t) / ((b : ℚ) - d + 1 - t - 1) := by
    intro t ht
    have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (1, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row1_mid3 h6 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (b - d + 1) (c - d) (by omega)]
  -- Product 5: [c, b-1), h(1,t+c) = b-c-t
  rw [show Finset.Ico c (b - 1) = (Finset.range (b - 1 - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (b - 1 - c),
      (hookLength μ 1 (t + c) : ℚ) / ((hookLength μ 1 (t + c) : ℚ) - 1) =
      ((b : ℚ) - c - t) / ((b : ℚ) - c - t - 1) := by
    intro t ht
    have htm : t < b - 1 - c := Finset.mem_range.mp ht
    have hmem : (1, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row1_ge h6 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (b - c) (b - 1 - c) (by omega)]
  push_cast [Nat.cast_sub hfe, Nat.cast_sub hed, Nat.cast_sub hdc, Nat.cast_sub hcb.le,
             Nat.cast_sub (show 1 ≤ b - c by omega)]
  have hne1 : (b : ℚ) - f + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - f + 4 by omega)
  have hne2 : (b : ℚ) - e + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - e + 3 by omega)
  have hne3 : (b : ℚ) - d + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne4 : (b : ℚ) - c + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4]; ring

/-- Arm product for corner (0, a-1) in a 6-row shape. -/
private lemma sixRow_arm_row0 {μ : YoungDiagram} (h6 : μ.rowLen 6 = 0)
    (h5 : 0 < μ.rowLen 5) (hab : μ.rowLen 1 < μ.rowLen 0) :
    ∏ s ∈ Finset.range (μ.rowLen 0 - 1),
      ((hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1)) =
    ((μ.rowLen 0 : ℚ) + 5) * ((μ.rowLen 0 : ℚ) - μ.rowLen 5 + 4) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 4 + 3) * ((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 2) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 1) * ((μ.rowLen 0 : ℚ) - μ.rowLen 1) /
    (((μ.rowLen 0 : ℚ) - μ.rowLen 5 + 5) * ((μ.rowLen 0 : ℚ) - μ.rowLen 4 + 4) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 3) * ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 2) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 1 + 1)) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set c := μ.rowLen 2
  set d := μ.rowLen 3; set e := μ.rowLen 4; set f := μ.rowLen 5
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  rw [show Finset.range (a - 1) =
      Finset.range f ∪ Finset.Ico f e ∪ Finset.Ico e d ∪ Finset.Ico d c ∪
      Finset.Ico c b ∪ Finset.Ico b (a - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  -- Product 1: [0,f), h(0,s) = a-s+5
  have hconv1 : ∀ s ∈ Finset.range f,
      (hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1) =
      ((a : ℚ) + 5 - s) / ((a : ℚ) + 5 - s - 1) := by
    intro s hs
    have hse : s < f := Finset.mem_range.mp hs
    have hmem : (0, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row0_lt h6 hmem hse]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (a + 5) f (by omega)]
  -- Product 2: [f, e), h(0,t+f) = a-f+4-t
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 0 (t + f) : ℚ) / ((hookLength μ 0 (t + f) : ℚ) - 1) =
      ((a : ℚ) - f + 4 - t) / ((a : ℚ) - f + 4 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (0, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row0_mid1 h6 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (a - f + 4) (e - f) (by omega)]
  -- Product 3: [e, d), h(0,t+e) = a-e+3-t
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 0 (t + e) : ℚ) / ((hookLength μ 0 (t + e) : ℚ) - 1) =
      ((a : ℚ) - e + 3 - t) / ((a : ℚ) - e + 3 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (0, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row0_mid2 h6 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (a - e + 3) (d - e) (by omega)]
  -- Product 4: [d, c), h(0,t+d) = a-d+2-t
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 0 (t + d) : ℚ) / ((hookLength μ 0 (t + d) : ℚ) - 1) =
      ((a : ℚ) - d + 2 - t) / ((a : ℚ) - d + 2 - t - 1) := by
    intro t ht
    have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (0, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row0_mid3 h6 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (a - d + 2) (c - d) (by omega)]
  -- Product 5: [c, b), h(0,t+c) = a-c+1-t
  rw [show Finset.Ico c b = (Finset.range (b - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (b - c),
      (hookLength μ 0 (t + c) : ℚ) / ((hookLength μ 0 (t + c) : ℚ) - 1) =
      ((a : ℚ) - c + 1 - t) / ((a : ℚ) - c + 1 - t - 1) := by
    intro t ht
    have htm : t < b - c := Finset.mem_range.mp ht
    have hmem : (0, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row0_mid4 h6 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (a - c + 1) (b - c) (by omega)]
  -- Product 6: [b, a-1), h(0,t+b) = a-b-t
  rw [show Finset.Ico b (a - 1) = (Finset.range (a - 1 - b)).image (· + b) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv6 : ∀ t ∈ Finset.range (a - 1 - b),
      (hookLength μ 0 (t + b) : ℚ) / ((hookLength μ 0 (t + b) : ℚ) - 1) =
      ((a : ℚ) - b - t) / ((a : ℚ) - b - t - 1) := by
    intro t ht
    have htm : t < a - 1 - b := Finset.mem_range.mp ht
    have hmem : (0, t + b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sixRow_hookLen_row0_ge h6 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv6, prod_div_telescope (a - b) (a - 1 - b) (by omega)]
  push_cast [Nat.cast_sub hfe, Nat.cast_sub hed, Nat.cast_sub hdc, Nat.cast_sub hcb,
             Nat.cast_sub hab.le, Nat.cast_sub (show 1 ≤ a - b by omega)]
  have hne1 : (a : ℚ) - f + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - f + 5 by omega)
  have hne2 : (a : ℚ) - e + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - e + 4 by omega)
  have hne3 : (a : ℚ) - d + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne4 : (a : ℚ) - c + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne5 : (a : ℚ) - b + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4, hne5]; ring

/-- The hook walk identity for 6-row Young diagrams [a,b,c,d,e,f].
    NON-CIRCULAR: proved directly via hookProd_ratio_formula. -/
lemma hook_walk_identity_sixRow (μ : YoungDiagram)
    (h6 : μ.rowLen 6 = 0) (h5 : 0 < μ.rowLen 5) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / (hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) : ℚ))
    = (μ.card : ℚ) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set c := μ.rowLen 2
  set d := μ.rowLen 3; set e := μ.rowLen 4; set f := μ.rowLen 5
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  have hba : b ≤ a := μ.rowLen_anti 0 1 (by omega)
  have hbot : isCorner μ (5, f - 1) := by
    refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
    · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
    · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
  have hcard : (μ.card : ℚ) = (a : ℚ) + b + c + d + e + f := by
    exact_mod_cast sixRow_card h6
  rw [hcard]
  let ratio : ℕ × ℕ → ℚ := fun x =>
    if hx : isCorner μ x then (hookProd μ : ℚ) / hookProd (removeCorner μ x hx) else 0
  have hconvert : ∑ cc ∈ (corners μ).attach,
        ((hookProd μ : ℚ) / hookProd (removeCorner μ cc.val (mem_corners.mp cc.prop))) =
      ∑ x ∈ corners μ, ratio x := by
    rw [← Finset.sum_attach (f := ratio)]
    apply Finset.sum_congr rfl
    intro cx _; exact dif_pos (mem_corners.mp cx.2)
  -- Corners of a 6-row shape are a subset of {(5,f-1),(4,e-1),(3,d-1),(2,c-1),(1,b-1),(0,a-1)}
  have hsub : corners μ ⊆
      ({(5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
       Finset (ℕ × ℕ)) := by
    intro x hx
    have hxc := mem_corners.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨i, j⟩ := x
    obtain ⟨hmem, hright, hbelow⟩ := hxc
    have hi_lt : i < 6 := by
      by_contra h6i; push_neg at h6i
      have : (6, j) ∈ μ := by
        calc (6, j) ≤ (i, j) := by constructor <;> omega
          _ ∈ μ := hmem
        |>.mp hmem
      exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp this) (by omega)
    interval_cases i
    · right; right; right; right; right
      have hja : j = a - 1 := by
        have : ¬(j + 1 < a) := fun hlt => hright (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
        omega
      exact ⟨rfl, hja⟩
    · right; right; right; right; left
      have hjb : j = b - 1 := by
        have : ¬(j + 1 < b) := fun hlt => hright (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
        omega
      exact ⟨rfl, hjb⟩
    · right; right; right; left
      have hjc : j = c - 1 := by
        have : ¬(j + 1 < c) := fun hlt => hright (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
        omega
      exact ⟨rfl, hjc⟩
    · right; right; left
      have hjd : j = d - 1 := by
        have : ¬(j + 1 < d) := fun hlt => hright (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
        omega
      exact ⟨rfl, hjd⟩
    · right; left
      have hje : j = e - 1 := by
        have : ¬(j + 1 < e) := fun hlt => hright (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
        omega
      exact ⟨rfl, hje⟩
    · left
      have hjf : j = f - 1 := by
        have : ¬(j + 1 < f) := fun hlt => hright (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
        omega
      exact ⟨rfl, hjf⟩
  have hext : ∑ x ∈ corners μ, ratio x =
      ∑ x ∈ ({(5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
             Finset (ℕ × ℕ)), ratio x := by
    apply Finset.sum_subset hsub
    intro x _ hxnc; exact dif_neg (mt mem_corners.mpr hxnc)
  -- Ratio for corner (5, f-1)
  have hR5 : ratio (5, f - 1) =
      (f : ℚ) * ((a : ℚ) - f + 6) / ((a : ℚ) - f + 5) *
      ((b : ℚ) - f + 5) / ((b : ℚ) - f + 4) *
      ((c : ℚ) - f + 4) / ((c : ℚ) - f + 3) *
      ((d : ℚ) - f + 3) / ((d : ℚ) - f + 2) *
      ((e : ℚ) - f + 2) / ((e : ℚ) - f + 1) := by
    simp only [ratio, dif_pos hbot]
    rw [hookProd_ratio_formula hbot]
    simp only [Prod.fst, Prod.snd]
    rw [sixRow_arm_row5 μ h6 hbot]
    have hf1 : f - 1 < f := Nat.sub_lt h5 Nat.one_pos
    have hmem0 : (0, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem1 : (1, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem2 : (2, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem3 : (3, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem4 : (4, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [show Finset.range 5 = {0, 1, 2, 3, 4} from by ext k; simp; omega]
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
        Finset.prod_insert (by simp), Finset.prod_insert (by simp),
        Finset.prod_singleton]
    rw [sixRow_hookLen_row0_lt h6 hmem0 hf1,
        sixRow_hookLen_row1_lt h6 hmem1 hf1,
        sixRow_hookLen_row2_lt h6 hmem2 hf1,
        sixRow_hookLen_row3_lt h6 hmem3 hf1,
        sixRow_hookLen_row4_lt h6 hmem4 hf1]
    push_cast [Nat.cast_sub (show 1 ≤ f from h5),
               Nat.cast_sub (show f - 1 ≤ a by omega),
               Nat.cast_sub (show f - 1 ≤ b by omega),
               Nat.cast_sub (show f - 1 ≤ c by omega),
               Nat.cast_sub (show f - 1 ≤ d by omega),
               Nat.cast_sub (show f - 1 ≤ e by omega)]
    ring
  -- Ratio for corner (4, e-1) [when e > f]
  have hR4 : ratio (4, e - 1) =
      ((e : ℚ) + 1) * ((e : ℚ) - f) / ((e : ℚ) - f + 1) *
      ((a : ℚ) - e + 5) / ((a : ℚ) - e + 4) *
      ((b : ℚ) - e + 4) / ((b : ℚ) - e + 3) *
      ((c : ℚ) - e + 3) / ((c : ℚ) - e + 2) *
      ((d : ℚ) - e + 2) / ((d : ℚ) - e + 1) := by
    by_cases hef : f < e
    · have hmid : isCorner μ (4, e - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [sixRow_arm_row4 h6 hef]
      have he1 : e - 1 < e := Nat.sub_lt (by omega) Nat.one_pos
      have hef1 : f ≤ e - 1 := by omega
      have hmem0 : (0, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem3 : (3, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 4 = {0, 1, 2, 3} from by ext k; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [sixRow_hookLen_row0_mid1 h6 hmem0 hef1 he1,
          sixRow_hookLen_row1_mid1 h6 hmem1 hef1 he1,
          sixRow_hookLen_row2_mid1 h6 hmem2 hef1 he1,
          sixRow_hookLen_row3_mid1 h6 hmem3 hef1 he1]
      push_cast [Nat.cast_sub (show 1 ≤ e from by omega),
                 Nat.cast_sub hef.le,
                 Nat.cast_sub (show e - 1 ≤ a by omega),
                 Nat.cast_sub (show e - 1 ≤ b by omega),
                 Nat.cast_sub (show e - 1 ≤ c by omega),
                 Nat.cast_sub (show e - 1 ≤ d by omega)]
      ring
    · have hef_eq : e = f := Nat.le_antisymm (not_lt.mp hef) hfe
      have hnotcorner : ¬ isCorner μ (4, e - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (e : ℚ) - f = 0 := by rw [hef_eq]; ring
      rw [this]; ring
  -- Ratio for corner (3, d-1) [when d > e]
  have hR3 : ratio (3, d - 1) =
      ((d : ℚ) + 2) * ((d : ℚ) - f + 1) * ((d : ℚ) - e) /
      (((d : ℚ) - f + 2) * ((d : ℚ) - e + 1)) *
      ((a : ℚ) - d + 4) / ((a : ℚ) - d + 3) *
      ((b : ℚ) - d + 3) / ((b : ℚ) - d + 2) *
      ((c : ℚ) - d + 2) / ((c : ℚ) - d + 1) := by
    by_cases hde : e < d
    · have hmid : isCorner μ (3, d - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [sixRow_arm_row3 h6 hde]
      have hd1 : d - 1 < d := Nat.sub_lt (by omega) Nat.one_pos
      have hed1 : e ≤ d - 1 := by omega
      have hmem0 : (0, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 3 = {0, 1, 2} from by ext k; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_singleton]
      rw [sixRow_hookLen_row0_mid2 h6 hmem0 hed1 hd1,
          sixRow_hookLen_row1_mid2 h6 hmem1 hed1 hd1,
          sixRow_hookLen_row2_mid2 h6 hmem2 hed1 hd1]
      push_cast [Nat.cast_sub (show 1 ≤ d from by omega),
                 Nat.cast_sub hde.le,
                 Nat.cast_sub hfe,
                 Nat.cast_sub (show d - 1 ≤ a by omega),
                 Nat.cast_sub (show d - 1 ≤ b by omega),
                 Nat.cast_sub (show d - 1 ≤ c by omega)]
      ring
    · have hde_eq : d = e := Nat.le_antisymm (not_lt.mp hde) hed
      have hnotcorner : ¬ isCorner μ (3, d - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (d : ℚ) - e = 0 := by rw [hde_eq]; ring
      rw [this]; ring
  -- Ratio for corner (2, c-1) [when c > d]
  have hR2 : ratio (2, c - 1) =
      ((c : ℚ) + 3) * ((c : ℚ) - f + 2) * ((c : ℚ) - e + 1) * ((c : ℚ) - d) /
      (((c : ℚ) - f + 3) * ((c : ℚ) - e + 2) * ((c : ℚ) - d + 1)) *
      ((a : ℚ) - c + 3) / ((a : ℚ) - c + 2) *
      ((b : ℚ) - c + 2) / ((b : ℚ) - c + 1) := by
    by_cases hcd : d < c
    · have hmid : isCorner μ (2, c - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [sixRow_arm_row2 h6 hcd]
      have hc1 : c - 1 < c := Nat.sub_lt (by omega) Nat.one_pos
      have hdc1 : d ≤ c - 1 := by omega
      have hmem0 : (0, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 2 = {0, 1} from by ext k; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [sixRow_hookLen_row0_mid3 h6 hmem0 hdc1 hc1,
          sixRow_hookLen_row1_mid3 h6 hmem1 hdc1 hc1]
      push_cast [Nat.cast_sub (show 1 ≤ c from by omega),
                 Nat.cast_sub hcd.le,
                 Nat.cast_sub hed,
                 Nat.cast_sub hfe,
                 Nat.cast_sub (show c - 1 ≤ a by omega),
                 Nat.cast_sub (show c - 1 ≤ b by omega)]
      ring
    · have hcd_eq : c = d := Nat.le_antisymm (not_lt.mp hcd) hdc
      have hnotcorner : ¬ isCorner μ (2, c - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (c : ℚ) - d = 0 := by rw [hcd_eq]; ring
      rw [this]; ring
  -- Ratio for corner (1, b-1) [when b > c]
  have hR1 : ratio (1, b - 1) =
      ((b : ℚ) + 4) * ((b : ℚ) - f + 3) * ((b : ℚ) - e + 2) * ((b : ℚ) - d + 1) *
      ((b : ℚ) - c) /
      (((b : ℚ) - f + 4) * ((b : ℚ) - e + 3) * ((b : ℚ) - d + 2) *
       ((b : ℚ) - c + 1)) *
      ((a : ℚ) - b + 2) / ((a : ℚ) - b + 1) := by
    by_cases hbc : c < b
    · have hmid : isCorner μ (1, b - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [sixRow_arm_row1 h6 hbc]
      have hb1 : b - 1 < b := Nat.sub_lt (by omega) Nat.one_pos
      have hcb1 : c ≤ b - 1 := by omega
      have hmem0 : (0, b - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 1 = {0} from by ext k; simp; omega]
      rw [Finset.prod_singleton]
      rw [sixRow_hookLen_row0_mid4 h6 hmem0 hcb1 hb1]
      push_cast [Nat.cast_sub (show 1 ≤ b from by omega),
                 Nat.cast_sub hbc.le,
                 Nat.cast_sub hdc,
                 Nat.cast_sub hed,
                 Nat.cast_sub hfe,
                 Nat.cast_sub (show b - 1 ≤ a by omega)]
      ring
    · have hbc_eq : b = c := Nat.le_antisymm (not_lt.mp hbc) hcb
      have hnotcorner : ¬ isCorner μ (1, b - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (b : ℚ) - c = 0 := by rw [hbc_eq]; ring
      rw [this]; ring
  -- Ratio for corner (0, a-1) [when a > b]
  have hR0 : ratio (0, a - 1) =
      ((a : ℚ) + 5) * ((a : ℚ) - f + 4) * ((a : ℚ) - e + 3) * ((a : ℚ) - d + 2) *
      ((a : ℚ) - c + 1) * ((a : ℚ) - b) /
      (((a : ℚ) - f + 5) * ((a : ℚ) - e + 4) * ((a : ℚ) - d + 3) *
       ((a : ℚ) - c + 2) * ((a : ℚ) - b + 1)) := by
    by_cases hab : b < a
    · have htop : isCorner μ (0, a - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos htop]
      rw [hookProd_ratio_formula htop]
      simp only [Prod.fst, Prod.snd, Finset.prod_range_zero, mul_one]
      rw [sixRow_arm_row0 h6 h5 hab]
      ring
    · have hab_eq : a = b := Nat.le_antisymm (not_lt.mp hab) hba
      have hnotcorner : ¬ isCorner μ (0, a - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (a : ℚ) - b = 0 := by rw [hab_eq]; ring
      rw [this]; ring
  rw [hconvert, hext]
  have hd1 : (5, f - 1) ∉ ({(4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
    Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hd2 : (4, e - 1) ∉ ({(3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
    Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hd3 : (3, d - 1) ∉ ({(2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hd4 : (2, c - 1) ∉ ({(1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hd5 : (1, b - 1) ∉ ({(0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  rw [show ({(5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
           Finset (ℕ × ℕ)) =
      insert (5, f - 1) (insert (4, e - 1) (insert (3, d - 1) (insert (2, c - 1)
        (insert (1, b - 1) {(0, a - 1)})))) from rfl,
      Finset.sum_insert hd1, Finset.sum_insert hd2, Finset.sum_insert hd3,
      Finset.sum_insert hd4, Finset.sum_insert hd5, Finset.sum_singleton,
      hR5, hR4, hR3, hR2, hR1, hR0]
  have hne_ef1 : (e : ℚ) - f + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < e - f + 1 by omega)
  have hne_de1 : (d : ℚ) - e + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < d - e + 1 by omega)
  have hne_df2 : (d : ℚ) - f + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < d - f + 2 by omega)
  have hne_cd1 : (c : ℚ) - d + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  have hne_ce2 : (c : ℚ) - e + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - e + 2 by omega)
  have hne_cf3 : (c : ℚ) - f + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - f + 3 by omega)
  have hne_bc1 : (b : ℚ) - c + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  have hne_bd2 : (b : ℚ) - d + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne_be3 : (b : ℚ) - e + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - e + 3 by omega)
  have hne_bf4 : (b : ℚ) - f + 4 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - f + 4 by omega)
  have hne_ab1 : (a : ℚ) - b + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  have hne_ac2 : (a : ℚ) - c + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne_ad3 : (a : ℚ) - d + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne_ae4 : (a : ℚ) - e + 4 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - e + 4 by omega)
  have hne_af5 : (a : ℚ) - f + 5 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - f + 5 by omega)
  push_cast [Nat.cast_sub hfe, Nat.cast_sub hed, Nat.cast_sub hdc, Nat.cast_sub hcb,
             Nat.cast_sub hba,
             Nat.cast_sub (show f ≤ d by omega), Nat.cast_sub (show f ≤ c by omega),
             Nat.cast_sub (show f ≤ b by omega), Nat.cast_sub (show f ≤ a by omega),
             Nat.cast_sub (show e ≤ c by omega), Nat.cast_sub (show e ≤ b by omega),
             Nat.cast_sub (show e ≤ a by omega), Nat.cast_sub (show d ≤ b by omega),
             Nat.cast_sub (show d ≤ a by omega), Nat.cast_sub (show c ≤ a by omega)]
  field_simp [hne_ef1, hne_de1, hne_df2, hne_cd1, hne_ce2, hne_cf3,
              hne_bc1, hne_bd2, hne_be3, hne_bf4,
              hne_ab1, hne_ac2, hne_ad3, hne_ae4, hne_af5]
  ring



/-! ## PART XXI: hook_walk_identity for exactly-7-row Young diagrams

  For μ with rowLen 7 = 0 and rowLen 6 > 0: direct computation via hookProd_ratio_formula.
  Uses 6 colLen zones, 28 hookLen lemmas, 7 arm lemmas, then field_simp/ring.
-/

/-- colLen(s) = 7 for s < rowLen 6 in a 7-row shape (rowLen 7 = 0). -/
private lemma sevenRow_colLen_lt {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hs : s < μ.rowLen 6) : μ.colLen s = 7 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h7s : (7, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h7s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs)

/-- colLen(s) = 6 for rowLen 6 ≤ s < rowLen 5 in a 7-row shape. -/
private lemma sevenRow_colLen_mid1 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    μ.colLen s = 6 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h6s : (6, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h6s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 5 for rowLen 5 ≤ s < rowLen 4 in a 7-row shape. -/
private lemma sevenRow_colLen_mid2 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    μ.colLen s = 5 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h5s : (5, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h5s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 4 for rowLen 4 ≤ s < rowLen 3 in a 7-row shape. -/
private lemma sevenRow_colLen_mid3 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    μ.colLen s = 4 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h4s : (4, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h4s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 3 for rowLen 3 ≤ s < rowLen 2 in a 7-row shape. -/
private lemma sevenRow_colLen_mid4 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    μ.colLen s = 3 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h3s : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h3s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 2 for rowLen 2 ≤ s < rowLen 1 in a 7-row shape. -/
private lemma sevenRow_colLen_mid5 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    μ.colLen s = 2 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h2s : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h2s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

-- hookLen lemmas: row 6 (1 zone)
private lemma sevenRow_hookLen_row6 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (6, s) ∈ μ) :
    hookLength μ 6 s = μ.rowLen 6 - s := by
  have hs : s < μ.rowLen 6 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_lt h7 hs] at key; omega

-- hookLen lemmas: row 5 (2 zones)
private lemma sevenRow_hookLen_row5_lt {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (5, s) ∈ μ) (hs : s < μ.rowLen 6) :
    hookLength μ 5 s = μ.rowLen 5 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_lt h7 hs] at key; omega

private lemma sevenRow_hookLen_row5_ge {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (5, s) ∈ μ) (hs : μ.rowLen 6 ≤ s) :
    hookLength μ 5 s = μ.rowLen 5 - s := by
  have hs_lt : s < μ.rowLen 5 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid1 h7 hs hs_lt] at key; omega

-- hookLen lemmas: row 4 (3 zones)
private lemma sevenRow_hookLen_row4_lt {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (4, s) ∈ μ) (hs : s < μ.rowLen 6) :
    hookLength μ 4 s = μ.rowLen 4 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_lt h7 hs] at key; omega

private lemma sevenRow_hookLen_row4_mid1 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (4, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 4 s = μ.rowLen 4 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid1 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row4_ge {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (4, s) ∈ μ) (hs : μ.rowLen 5 ≤ s) :
    hookLength μ 4 s = μ.rowLen 4 - s := by
  have hs_lt : s < μ.rowLen 4 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid2 h7 hs hs_lt] at key; omega

-- hookLen lemmas: row 3 (4 zones)
private lemma sevenRow_hookLen_row3_lt {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (3, s) ∈ μ) (hs : s < μ.rowLen 6) :
    hookLength μ 3 s = μ.rowLen 3 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_lt h7 hs] at key; omega

private lemma sevenRow_hookLen_row3_mid1 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (3, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 3 s = μ.rowLen 3 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid1 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row3_mid2 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (3, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 3 s = μ.rowLen 3 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid2 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row3_ge {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (3, s) ∈ μ) (hs : μ.rowLen 4 ≤ s) :
    hookLength μ 3 s = μ.rowLen 3 - s := by
  have hs_lt : s < μ.rowLen 3 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid3 h7 hs hs_lt] at key; omega

-- hookLen lemmas: row 2 (5 zones)
private lemma sevenRow_hookLen_row2_lt {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (2, s) ∈ μ) (hs : s < μ.rowLen 6) :
    hookLength μ 2 s = μ.rowLen 2 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_lt h7 hs] at key; omega

private lemma sevenRow_hookLen_row2_mid1 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 2 s = μ.rowLen 2 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid1 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row2_mid2 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 2 s = μ.rowLen 2 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid2 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row2_mid3 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 2 s = μ.rowLen 2 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid3 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row2_ge {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (2, s) ∈ μ) (hs : μ.rowLen 3 ≤ s) :
    hookLength μ 2 s = μ.rowLen 2 - s := by
  have hs_lt : s < μ.rowLen 2 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid4 h7 hs hs_lt] at key; omega

-- hookLen lemmas: row 1 (6 zones)
private lemma sevenRow_hookLen_row1_lt {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (1, s) ∈ μ) (hs : s < μ.rowLen 6) :
    hookLength μ 1 s = μ.rowLen 1 - s + 5 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_lt h7 hs] at key; omega

private lemma sevenRow_hookLen_row1_mid1 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 1 s = μ.rowLen 1 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid1 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row1_mid2 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 1 s = μ.rowLen 1 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid2 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row1_mid3 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 1 s = μ.rowLen 1 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid3 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row1_mid4 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    hookLength μ 1 s = μ.rowLen 1 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid4 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row1_ge {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (1, s) ∈ μ) (hs : μ.rowLen 2 ≤ s) :
    hookLength μ 1 s = μ.rowLen 1 - s := by
  have hs_lt : s < μ.rowLen 1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid5 h7 hs hs_lt] at key; omega

-- hookLen lemmas: row 0 (7 zones)
private lemma sevenRow_hookLen_row0_lt {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (0, s) ∈ μ) (hs : s < μ.rowLen 6) :
    hookLength μ 0 s = μ.rowLen 0 - s + 6 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_lt h7 hs] at key; omega

private lemma sevenRow_hookLen_row0_mid1 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 0 s = μ.rowLen 0 - s + 5 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid1 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row0_mid2 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 0 s = μ.rowLen 0 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid2 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row0_mid3 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 0 s = μ.rowLen 0 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid3 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row0_mid4 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    hookLength μ 0 s = μ.rowLen 0 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid4 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row0_mid5 {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    hookLength μ 0 s = μ.rowLen 0 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [sevenRow_colLen_mid5 h7 hs_ge hs_lt] at key; omega

private lemma sevenRow_hookLen_row0_ge {μ : YoungDiagram} {s : ℕ}
    (h7 : μ.rowLen 7 = 0) (hmem : (0, s) ∈ μ) (hs : μ.rowLen 1 ≤ s) :
    hookLength μ 0 s = μ.rowLen 0 - s := by
  have hs_lt : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  have hcol : μ.colLen s = 1 := by
    apply Nat.le_antisymm
    · by_contra hlt; push_neg at hlt
      have h1s : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
      have := YoungDiagram.mem_iff_lt_rowLen.mp h1s; omega
    · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)
  rw [hcol] at key; omega


/-- Bottom corner (6, rowLen 6 - 1) always exists in a 7-row shape. -/
private lemma sevenRow_corner_bot {μ : YoungDiagram} (h7 : μ.rowLen 7 = 0) (h6 : 0 < μ.rowLen 6) :
    isCorner μ (6, μ.rowLen 6 - 1) := by
  refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
  · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
  · intro h
    have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega

/-- Corner classification for 7-row shapes: corners are among the 7 possible positions. -/
private lemma sevenRow_corner_cases {μ : YoungDiagram} (h7 : μ.rowLen 7 = 0) (h6 : 0 < μ.rowLen 6)
    {cell : ℕ × ℕ} (hc : isCorner μ cell) :
    (cell = (6, μ.rowLen 6 - 1)) ∨
    (cell = (5, μ.rowLen 5 - 1) ∧ μ.rowLen 6 < μ.rowLen 5) ∨
    (cell = (4, μ.rowLen 4 - 1) ∧ μ.rowLen 5 < μ.rowLen 4) ∨
    (cell = (3, μ.rowLen 3 - 1) ∧ μ.rowLen 4 < μ.rowLen 3) ∨
    (cell = (2, μ.rowLen 2 - 1) ∧ μ.rowLen 3 < μ.rowLen 2) ∨
    (cell = (1, μ.rowLen 1 - 1) ∧ μ.rowLen 2 < μ.rowLen 1) ∨
    (cell = (0, μ.rowLen 0 - 1) ∧ μ.rowLen 1 < μ.rowLen 0) := by
  obtain ⟨hmem, hnext, hprev⟩ := hc
  have hrow := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  -- cell = (i, j) for some i, j
  obtain ⟨i, j⟩ := cell
  simp only [Prod.mk.injEq]
  -- i ≤ 6 since rowLen 7 = 0 means no row 7
  have hi6 : i ≤ 6 := by
    by_contra h; push_neg at h
    have : μ.rowLen 7 > 0 := by
      calc μ.rowLen 7 ≥ μ.rowLen i := μ.rowLen_anti (by omega) (by omega)
        _ > 0 := by omega
    omega
  -- j = rowLen i - 1 (since (i, j+1) ∉ μ)
  have hj : j = μ.rowLen i - 1 := by
    apply Nat.le_antisymm
    · by_contra h; push_neg at h
      have : (i, j + 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hnext this
    · have : ¬ (i, j + 1) ∈ μ := hnext
      by_contra h; push_neg at h
      have : μ.rowLen i > j + 1 := by omega
      exact absurd (YoungDiagram.mem_iff_lt_rowLen.mpr this) hnext
  subst hj
  interval_cases i
  · right; right; right; right; right; right
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 1 = μ.rowLen 0 := Nat.le_antisymm (μ.rowLen_anti 0 1 (by omega)) h
      have : (1, μ.rowLen 0 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 2 = μ.rowLen 1 := Nat.le_antisymm (μ.rowLen_anti 1 2 (by omega)) h
      have : (2, μ.rowLen 1 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 3 = μ.rowLen 2 := Nat.le_antisymm (μ.rowLen_anti 2 3 (by omega)) h
      have : (3, μ.rowLen 2 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 4 = μ.rowLen 3 := Nat.le_antisymm (μ.rowLen_anti 3 4 (by omega)) h
      have : (4, μ.rowLen 3 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 5 = μ.rowLen 4 := Nat.le_antisymm (μ.rowLen_anti 4 5 (by omega)) h
      have : (5, μ.rowLen 4 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 6 = μ.rowLen 5 := Nat.le_antisymm (μ.rowLen_anti 5 6 (by omega)) h
      have : (6, μ.rowLen 5 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · left; rfl

/-- Card of a 7-row shape equals sum of row lengths. -/
private lemma sevenRow_card {μ : YoungDiagram} (h7 : μ.rowLen 7 = 0) :
    μ.card = μ.rowLen 0 + μ.rowLen 1 + μ.rowLen 2 + μ.rowLen 3 +
             μ.rowLen 4 + μ.rowLen 5 + μ.rowLen 6 := by
  have hcells : μ.cells =
      (Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
      (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
      (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
      (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
      (Finset.range (μ.rowLen 4)).image (Prod.mk 4) ∪
      (Finset.range (μ.rowLen 5)).image (Prod.mk 5) ∪
      (Finset.range (μ.rowLen 6)).image (Prod.mk 6) := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, Finset.mem_union, Finset.mem_image,
               Finset.mem_range, Prod.mk.injEq]
    constructor
    · intro h
      have hil : i ≤ 6 := by
        by_contra hlt; push_neg at hlt
        have : μ.rowLen 7 > 0 := calc
          μ.rowLen 7 ≥ μ.rowLen i := μ.rowLen_anti (by omega) (by omega)
          _ > 0 := by
            have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega
        omega
      have hj := YoungDiagram.mem_iff_lt_rowLen.mp h
      interval_cases i <;> simp_all [Prod.mk.injEq]
    · rintro (((((( ⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) |
                  ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) |
                ⟨k, hk, rfl, rfl⟩)
      all_goals exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have mk_inj : ∀ (n : ℕ), Function.Injective (Prod.mk n) := fun _ _ _ h => (Prod.mk.inj h).2
  have hd01 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0))
                       ((Finset.range (μ.rowLen 1)).image (Prod.mk 1)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ⟨_, _, rfl, rfl⟩ := hx; obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd012 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                         (Finset.range (μ.rowLen 1)).image (Prod.mk 1))
                        ((Finset.range (μ.rowLen 2)).image (Prod.mk 2)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd0123 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                          (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                          (Finset.range (μ.rowLen 2)).image (Prod.mk 2))
                         ((Finset.range (μ.rowLen 3)).image (Prod.mk 3)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd01234 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                           (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                           (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                           (Finset.range (μ.rowLen 3)).image (Prod.mk 3))
                          ((Finset.range (μ.rowLen 4)).image (Prod.mk 4)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
               ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd012345 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                            (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                            (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                            (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
                            (Finset.range (μ.rowLen 4)).image (Prod.mk 4))
                           ((Finset.range (μ.rowLen 5)).image (Prod.mk 5)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
                ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd0123456 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                             (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                             (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                             (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
                             (Finset.range (μ.rowLen 4)).image (Prod.mk 4) ∪
                             (Finset.range (μ.rowLen 5)).image (Prod.mk 5))
                            ((Finset.range (μ.rowLen 6)).image (Prod.mk 6)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (((((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
                 ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  rw [hcells,
      Finset.card_union_of_disjoint hd0123456,
      Finset.card_union_of_disjoint hd012345,
      Finset.card_union_of_disjoint hd01234,
      Finset.card_union_of_disjoint hd0123,
      Finset.card_union_of_disjoint hd012,
      Finset.card_union_of_disjoint hd01,
      Finset.card_image_of_injective _ (mk_inj 0),
      Finset.card_image_of_injective _ (mk_inj 1),
      Finset.card_image_of_injective _ (mk_inj 2),
      Finset.card_image_of_injective _ (mk_inj 3),
      Finset.card_image_of_injective _ (mk_inj 4),
      Finset.card_image_of_injective _ (mk_inj 5),
      Finset.card_image_of_injective _ (mk_inj 6),
      Finset.card_range, Finset.card_range, Finset.card_range, Finset.card_range,
      Finset.card_range, Finset.card_range, Finset.card_range]


/-- Arm product for corner (6, g-1) in a 7-row shape telescopes to g. -/
private lemma sevenRow_arm_row6 (μ : YoungDiagram) (h7 : μ.rowLen 7 = 0)
    (hg : isCorner μ (6, μ.rowLen 6 - 1)) :
    ∏ s ∈ Finset.range (μ.rowLen 6 - 1),
      ((hookLength μ 6 s : ℚ) / ((hookLength μ 6 s : ℚ) - 1)) =
    (μ.rowLen 6 : ℚ) := by
  set g := μ.rowLen 6
  have hg_pos : 0 < g := by have := YoungDiagram.mem_iff_lt_rowLen.mp hg.1; omega
  have hconv : ∀ s ∈ Finset.range (g - 1),
      (hookLength μ 6 s : ℚ) / ((hookLength μ 6 s : ℚ) - 1) =
      ((g : ℚ) - s) / ((g : ℚ) - s - 1) := by
    intro s hs
    have hsc : s < g - 1 := Finset.mem_range.mp hs
    have hmem : (6, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row6 h7 hmem]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv]
  rw [prod_div_telescope g (g - 1) (Nat.sub_lt hg_pos Nat.one_pos)]
  push_cast; simp [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hg_pos))]

/-- Arm product for corner (5, f-1) in a 7-row shape:
    ∏ = (f+1)(f-g)/((f-g+1)). -/
private lemma sevenRow_arm_row5 {μ : YoungDiagram} (h7 : μ.rowLen 7 = 0)
    (hgf : μ.rowLen 6 < μ.rowLen 5) :
    ∏ s ∈ Finset.range (μ.rowLen 5 - 1),
      ((hookLength μ 5 s : ℚ) / ((hookLength μ 5 s : ℚ) - 1)) =
    ((μ.rowLen 5 : ℚ) + 1) * ((μ.rowLen 5 : ℚ) - μ.rowLen 6) /
    ((μ.rowLen 5 : ℚ) - μ.rowLen 6 + 1) := by
  set f := μ.rowLen 5; set g := μ.rowLen 6
  rw [show Finset.range (f - 1) = Finset.range g ∪ Finset.Ico g (f - 1) from by
    ext s; simp [Finset.mem_Ico]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range g,
      (hookLength μ 5 s : ℚ) / ((hookLength μ 5 s : ℚ) - 1) =
      ((f : ℚ) + 1 - s) / ((f : ℚ) + 1 - s - 1) := by
    intro s hs
    have hsg : s < g := Finset.mem_range.mp hs
    have hmem : (5, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row5_lt h7 hmem hsg]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (f + 1) g (by omega)]
  rw [show Finset.Ico g (f - 1) = (Finset.range (f - 1 - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (f - 1 - g),
      (hookLength μ 5 (t + g) : ℚ) / ((hookLength μ 5 (t + g) : ℚ) - 1) =
      ((f : ℚ) - g - t) / ((f : ℚ) - g - t - 1) := by
    intro t ht
    have htm : t < f - 1 - g := Finset.mem_range.mp ht
    have hmem : (5, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row5_ge h7 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (f - g) (f - 1 - g) (by omega)]
  push_cast [Nat.cast_sub hgf.le, Nat.cast_sub (show 1 ≤ f - g by omega)]
  have hne : (f : ℚ) - g + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < f - g + 1 by omega)
  field_simp [hne]; ring

/-- Arm product for corner (4, e-1) in a 7-row shape:
    ∏ = (e+2)(e-g+1)(e-f)/((e-g+2)(e-f+1)). -/
private lemma sevenRow_arm_row4 {μ : YoungDiagram} (h7 : μ.rowLen 7 = 0)
    (hfe : μ.rowLen 5 < μ.rowLen 4) :
    ∏ s ∈ Finset.range (μ.rowLen 4 - 1),
      ((hookLength μ 4 s : ℚ) / ((hookLength μ 4 s : ℚ) - 1)) =
    ((μ.rowLen 4 : ℚ) + 2) * ((μ.rowLen 4 : ℚ) - μ.rowLen 6 + 1) *
    ((μ.rowLen 4 : ℚ) - μ.rowLen 5) /
    (((μ.rowLen 4 : ℚ) - μ.rowLen 6 + 2) * ((μ.rowLen 4 : ℚ) - μ.rowLen 5 + 1)) := by
  set e := μ.rowLen 4; set f := μ.rowLen 5; set g := μ.rowLen 6
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  rw [show Finset.range (e - 1) = Finset.range g ∪ Finset.Ico g f ∪ Finset.Ico f (e - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range g,
      (hookLength μ 4 s : ℚ) / ((hookLength μ 4 s : ℚ) - 1) =
      ((e : ℚ) + 2 - s) / ((e : ℚ) + 2 - s - 1) := by
    intro s hs
    have hsg : s < g := Finset.mem_range.mp hs
    have hmem : (4, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row4_lt h7 hmem hsg]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (e + 2) g (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 4 (t + g) : ℚ) / ((hookLength μ 4 (t + g) : ℚ) - 1) =
      ((e : ℚ) - g + 1 - t) / ((e : ℚ) - g + 1 - t - 1) := by
    intro t ht
    have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (4, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row4_mid1 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (e - g + 1) (f - g) (by omega)]
  rw [show Finset.Ico f (e - 1) = (Finset.range (e - 1 - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (e - 1 - f),
      (hookLength μ 4 (t + f) : ℚ) / ((hookLength μ 4 (t + f) : ℚ) - 1) =
      ((e : ℚ) - f - t) / ((e : ℚ) - f - t - 1) := by
    intro t ht
    have htm : t < e - 1 - f := Finset.mem_range.mp ht
    have hmem : (4, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row4_ge h7 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (e - f) (e - 1 - f) (by omega)]
  push_cast [Nat.cast_sub hgf, Nat.cast_sub hfe.le, Nat.cast_sub (show 1 ≤ e - f by omega)]
  have hne1 : (e : ℚ) - g + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - g + 2 by omega)
  have hne2 : (e : ℚ) - f + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - f + 1 by omega)
  field_simp [hne1, hne2]; ring

/-- Arm product for corner (3, d-1) in a 7-row shape:
    ∏ = (d+3)(d-g+2)(d-f+1)(d-e)/((d-g+3)(d-f+2)(d-e+1)). -/
private lemma sevenRow_arm_row3 {μ : YoungDiagram} (h7 : μ.rowLen 7 = 0)
    (hed : μ.rowLen 4 < μ.rowLen 3) :
    ∏ s ∈ Finset.range (μ.rowLen 3 - 1),
      ((hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1)) =
    ((μ.rowLen 3 : ℚ) + 3) * ((μ.rowLen 3 : ℚ) - μ.rowLen 6 + 2) *
    ((μ.rowLen 3 : ℚ) - μ.rowLen 5 + 1) * ((μ.rowLen 3 : ℚ) - μ.rowLen 4) /
    (((μ.rowLen 3 : ℚ) - μ.rowLen 6 + 3) * ((μ.rowLen 3 : ℚ) - μ.rowLen 5 + 2) *
     ((μ.rowLen 3 : ℚ) - μ.rowLen 4 + 1)) := by
  set d := μ.rowLen 3; set e := μ.rowLen 4; set f := μ.rowLen 5; set g := μ.rowLen 6
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  rw [show Finset.range (d - 1) = Finset.range g ∪ Finset.Ico g f ∪
      Finset.Ico f e ∪ Finset.Ico e (d - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range g,
      (hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1) =
      ((d : ℚ) + 3 - s) / ((d : ℚ) + 3 - s - 1) := by
    intro s hs
    have hsg : s < g := Finset.mem_range.mp hs
    have hmem : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row3_lt h7 hmem hsg]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (d + 3) g (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 3 (t + g) : ℚ) / ((hookLength μ 3 (t + g) : ℚ) - 1) =
      ((d : ℚ) - g + 2 - t) / ((d : ℚ) - g + 2 - t - 1) := by
    intro t ht
    have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (3, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row3_mid1 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (d - g + 2) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 3 (t + f) : ℚ) / ((hookLength μ 3 (t + f) : ℚ) - 1) =
      ((d : ℚ) - f + 1 - t) / ((d : ℚ) - f + 1 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (3, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row3_mid2 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (d - f + 1) (e - f) (by omega)]
  rw [show Finset.Ico e (d - 1) = (Finset.range (d - 1 - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (d - 1 - e),
      (hookLength μ 3 (t + e) : ℚ) / ((hookLength μ 3 (t + e) : ℚ) - 1) =
      ((d : ℚ) - e - t) / ((d : ℚ) - e - t - 1) := by
    intro t ht
    have htm : t < d - 1 - e := Finset.mem_range.mp ht
    have hmem : (3, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row3_ge h7 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (d - e) (d - 1 - e) (by omega)]
  push_cast [Nat.cast_sub hgf, Nat.cast_sub hfe, Nat.cast_sub hed.le,
             Nat.cast_sub (show 1 ≤ d - e by omega)]
  have hne1 : (d : ℚ) - g + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - g + 3 by omega)
  have hne2 : (d : ℚ) - f + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - f + 2 by omega)
  have hne3 : (d : ℚ) - e + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - e + 1 by omega)
  field_simp [hne1, hne2, hne3]; ring


/-- Arm product for corner (2, c-1) in a 7-row shape:
    ∏ = (c+4)(c-g+3)(c-f+2)(c-e+1)(c-d)/((c-g+4)(c-f+3)(c-e+2)(c-d+1)). -/
private lemma sevenRow_arm_row2 {μ : YoungDiagram} (h7 : μ.rowLen 7 = 0)
    (hdc : μ.rowLen 3 < μ.rowLen 2) :
    ∏ s ∈ Finset.range (μ.rowLen 2 - 1),
      ((hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1)) =
    ((μ.rowLen 2 : ℚ) + 4) * ((μ.rowLen 2 : ℚ) - μ.rowLen 6 + 3) *
    ((μ.rowLen 2 : ℚ) - μ.rowLen 5 + 2) * ((μ.rowLen 2 : ℚ) - μ.rowLen 4 + 1) *
    ((μ.rowLen 2 : ℚ) - μ.rowLen 3) /
    (((μ.rowLen 2 : ℚ) - μ.rowLen 6 + 4) * ((μ.rowLen 2 : ℚ) - μ.rowLen 5 + 3) *
     ((μ.rowLen 2 : ℚ) - μ.rowLen 4 + 2) * ((μ.rowLen 2 : ℚ) - μ.rowLen 3 + 1)) := by
  set c := μ.rowLen 2; set d := μ.rowLen 3; set e := μ.rowLen 4
  set f := μ.rowLen 5; set g := μ.rowLen 6
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  rw [show Finset.range (c - 1) = Finset.range g ∪ Finset.Ico g f ∪
      Finset.Ico f e ∪ Finset.Ico e d ∪ Finset.Ico d (c - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range g,
      (hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1) =
      ((c : ℚ) + 4 - s) / ((c : ℚ) + 4 - s - 1) := by
    intro s hs
    have hsg : s < g := Finset.mem_range.mp hs
    have hmem : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row2_lt h7 hmem hsg]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (c + 4) g (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 2 (t + g) : ℚ) / ((hookLength μ 2 (t + g) : ℚ) - 1) =
      ((c : ℚ) - g + 3 - t) / ((c : ℚ) - g + 3 - t - 1) := by
    intro t ht
    have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (2, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row2_mid1 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (c - g + 3) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 2 (t + f) : ℚ) / ((hookLength μ 2 (t + f) : ℚ) - 1) =
      ((c : ℚ) - f + 2 - t) / ((c : ℚ) - f + 2 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (2, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row2_mid2 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (c - f + 2) (e - f) (by omega)]
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 2 (t + e) : ℚ) / ((hookLength μ 2 (t + e) : ℚ) - 1) =
      ((c : ℚ) - e + 1 - t) / ((c : ℚ) - e + 1 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (2, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row2_mid3 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (c - e + 1) (d - e) (by omega)]
  rw [show Finset.Ico d (c - 1) = (Finset.range (c - 1 - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (c - 1 - d),
      (hookLength μ 2 (t + d) : ℚ) / ((hookLength μ 2 (t + d) : ℚ) - 1) =
      ((c : ℚ) - d - t) / ((c : ℚ) - d - t - 1) := by
    intro t ht
    have htm : t < c - 1 - d := Finset.mem_range.mp ht
    have hmem : (2, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row2_ge h7 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (c - d) (c - 1 - d) (by omega)]
  push_cast [Nat.cast_sub hgf, Nat.cast_sub hfe, Nat.cast_sub hed, Nat.cast_sub hdc.le,
             Nat.cast_sub (show 1 ≤ c - d by omega)]
  have hne1 : (c : ℚ) - g + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - g + 4 by omega)
  have hne2 : (c : ℚ) - f + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - f + 3 by omega)
  have hne3 : (c : ℚ) - e + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - e + 2 by omega)
  have hne4 : (c : ℚ) - d + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4]; ring

/-- Arm product for corner (1, b-1) in a 7-row shape:
    ∏ = (b+5)(b-g+4)(b-f+3)(b-e+2)(b-d+1)(b-c)/((b-g+5)(b-f+4)(b-e+3)(b-d+2)(b-c+1)). -/
private lemma sevenRow_arm_row1 {μ : YoungDiagram} (h7 : μ.rowLen 7 = 0)
    (hcb : μ.rowLen 2 < μ.rowLen 1) :
    ∏ s ∈ Finset.range (μ.rowLen 1 - 1),
      ((hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1)) =
    ((μ.rowLen 1 : ℚ) + 5) * ((μ.rowLen 1 : ℚ) - μ.rowLen 6 + 4) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 5 + 3) * ((μ.rowLen 1 : ℚ) - μ.rowLen 4 + 2) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 1) * ((μ.rowLen 1 : ℚ) - μ.rowLen 2) /
    (((μ.rowLen 1 : ℚ) - μ.rowLen 6 + 5) * ((μ.rowLen 1 : ℚ) - μ.rowLen 5 + 4) *
     ((μ.rowLen 1 : ℚ) - μ.rowLen 4 + 3) * ((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 2) *
     ((μ.rowLen 1 : ℚ) - μ.rowLen 2 + 1)) := by
  set b := μ.rowLen 1; set c := μ.rowLen 2; set d := μ.rowLen 3
  set e := μ.rowLen 4; set f := μ.rowLen 5; set g := μ.rowLen 6
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  rw [show Finset.range (b - 1) = Finset.range g ∪ Finset.Ico g f ∪
      Finset.Ico f e ∪ Finset.Ico e d ∪ Finset.Ico d c ∪ Finset.Ico c (b - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range g,
      (hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1) =
      ((b : ℚ) + 5 - s) / ((b : ℚ) + 5 - s - 1) := by
    intro s hs
    have hsg : s < g := Finset.mem_range.mp hs
    have hmem : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row1_lt h7 hmem hsg]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (b + 5) g (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 1 (t + g) : ℚ) / ((hookLength μ 1 (t + g) : ℚ) - 1) =
      ((b : ℚ) - g + 4 - t) / ((b : ℚ) - g + 4 - t - 1) := by
    intro t ht
    have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (1, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row1_mid1 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (b - g + 4) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 1 (t + f) : ℚ) / ((hookLength μ 1 (t + f) : ℚ) - 1) =
      ((b : ℚ) - f + 3 - t) / ((b : ℚ) - f + 3 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (1, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row1_mid2 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (b - f + 3) (e - f) (by omega)]
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 1 (t + e) : ℚ) / ((hookLength μ 1 (t + e) : ℚ) - 1) =
      ((b : ℚ) - e + 2 - t) / ((b : ℚ) - e + 2 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (1, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row1_mid3 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (b - e + 2) (d - e) (by omega)]
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 1 (t + d) : ℚ) / ((hookLength μ 1 (t + d) : ℚ) - 1) =
      ((b : ℚ) - d + 1 - t) / ((b : ℚ) - d + 1 - t - 1) := by
    intro t ht
    have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (1, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row1_mid4 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (b - d + 1) (c - d) (by omega)]
  rw [show Finset.Ico c (b - 1) = (Finset.range (b - 1 - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv6 : ∀ t ∈ Finset.range (b - 1 - c),
      (hookLength μ 1 (t + c) : ℚ) / ((hookLength μ 1 (t + c) : ℚ) - 1) =
      ((b : ℚ) - c - t) / ((b : ℚ) - c - t - 1) := by
    intro t ht
    have htm : t < b - 1 - c := Finset.mem_range.mp ht
    have hmem : (1, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row1_ge h7 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv6, prod_div_telescope (b - c) (b - 1 - c) (by omega)]
  push_cast [Nat.cast_sub hgf, Nat.cast_sub hfe, Nat.cast_sub hed, Nat.cast_sub hdc,
             Nat.cast_sub hcb.le, Nat.cast_sub (show 1 ≤ b - c by omega)]
  have hne1 : (b : ℚ) - g + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - g + 5 by omega)
  have hne2 : (b : ℚ) - f + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - f + 4 by omega)
  have hne3 : (b : ℚ) - e + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - e + 3 by omega)
  have hne4 : (b : ℚ) - d + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne5 : (b : ℚ) - c + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4, hne5]; ring

/-- Arm product for corner (0, a-1) in a 7-row shape:
    ∏ = (a+6)(a-g+5)(a-f+4)(a-e+3)(a-d+2)(a-c+1)(a-b)/
        ((a-g+6)(a-f+5)(a-e+4)(a-d+3)(a-c+2)(a-b+1)). -/
private lemma sevenRow_arm_row0 {μ : YoungDiagram} (h7 : μ.rowLen 7 = 0)
    (h6 : 0 < μ.rowLen 6) (hab : μ.rowLen 1 < μ.rowLen 0) :
    ∏ s ∈ Finset.range (μ.rowLen 0 - 1),
      ((hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1)) =
    ((μ.rowLen 0 : ℚ) + 6) * ((μ.rowLen 0 : ℚ) - μ.rowLen 6 + 5) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 5 + 4) * ((μ.rowLen 0 : ℚ) - μ.rowLen 4 + 3) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 2) * ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 1) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 1) /
    (((μ.rowLen 0 : ℚ) - μ.rowLen 6 + 6) * ((μ.rowLen 0 : ℚ) - μ.rowLen 5 + 5) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 4 + 4) * ((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 3) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 2) * ((μ.rowLen 0 : ℚ) - μ.rowLen 1 + 1)) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set c := μ.rowLen 2
  set d := μ.rowLen 3; set e := μ.rowLen 4; set f := μ.rowLen 5; set g := μ.rowLen 6
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  rw [show Finset.range (a - 1) = Finset.range g ∪ Finset.Ico g f ∪
      Finset.Ico f e ∪ Finset.Ico e d ∪ Finset.Ico d c ∪ Finset.Ico c b ∪
      Finset.Ico b (a - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range g,
      (hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1) =
      ((a : ℚ) + 6 - s) / ((a : ℚ) + 6 - s - 1) := by
    intro s hs
    have hsg : s < g := Finset.mem_range.mp hs
    have hmem : (0, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row0_lt h7 hmem hsg]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (a + 6) g (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 0 (t + g) : ℚ) / ((hookLength μ 0 (t + g) : ℚ) - 1) =
      ((a : ℚ) - g + 5 - t) / ((a : ℚ) - g + 5 - t - 1) := by
    intro t ht
    have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (0, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row0_mid1 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (a - g + 5) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 0 (t + f) : ℚ) / ((hookLength μ 0 (t + f) : ℚ) - 1) =
      ((a : ℚ) - f + 4 - t) / ((a : ℚ) - f + 4 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (0, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row0_mid2 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (a - f + 4) (e - f) (by omega)]
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 0 (t + e) : ℚ) / ((hookLength μ 0 (t + e) : ℚ) - 1) =
      ((a : ℚ) - e + 3 - t) / ((a : ℚ) - e + 3 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (0, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row0_mid3 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (a - e + 3) (d - e) (by omega)]
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 0 (t + d) : ℚ) / ((hookLength μ 0 (t + d) : ℚ) - 1) =
      ((a : ℚ) - d + 2 - t) / ((a : ℚ) - d + 2 - t - 1) := by
    intro t ht
    have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (0, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row0_mid4 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (a - d + 2) (c - d) (by omega)]
  rw [show Finset.Ico c b = (Finset.range (b - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv6 : ∀ t ∈ Finset.range (b - c),
      (hookLength μ 0 (t + c) : ℚ) / ((hookLength μ 0 (t + c) : ℚ) - 1) =
      ((a : ℚ) - c + 1 - t) / ((a : ℚ) - c + 1 - t - 1) := by
    intro t ht
    have htm : t < b - c := Finset.mem_range.mp ht
    have hmem : (0, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row0_mid5 h7 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv6, prod_div_telescope (a - c + 1) (b - c) (by omega)]
  rw [show Finset.Ico b (a - 1) = (Finset.range (a - 1 - b)).image (· + b) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv7 : ∀ t ∈ Finset.range (a - 1 - b),
      (hookLength μ 0 (t + b) : ℚ) / ((hookLength μ 0 (t + b) : ℚ) - 1) =
      ((a : ℚ) - b - t) / ((a : ℚ) - b - t - 1) := by
    intro t ht
    have htm : t < a - 1 - b := Finset.mem_range.mp ht
    have hmem : (0, t + b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [sevenRow_hookLen_row0_ge h7 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv7, prod_div_telescope (a - b) (a - 1 - b) (by omega)]
  push_cast [Nat.cast_sub hgf, Nat.cast_sub hfe, Nat.cast_sub hed, Nat.cast_sub hdc,
             Nat.cast_sub hcb, Nat.cast_sub hab.le, Nat.cast_sub (show 1 ≤ a - b by omega)]
  have hne1 : (a : ℚ) - g + 6 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - g + 6 by omega)
  have hne2 : (a : ℚ) - f + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - f + 5 by omega)
  have hne3 : (a : ℚ) - e + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - e + 4 by omega)
  have hne4 : (a : ℚ) - d + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne5 : (a : ℚ) - c + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne6 : (a : ℚ) - b + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4, hne5, hne6]; ring


/-- The hook walk identity for exactly-7-row Young diagrams.
    Direct computation via hookProd_ratio_formula and telescoping — no HLF used.
    NON-CIRCULAR: does not call hook_length_formula_Q or hook_walk_identity. -/
lemma hook_walk_identity_sevenRow (μ : YoungDiagram)
    (h7 : μ.rowLen 7 = 0) (h6 : 0 < μ.rowLen 6) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / (hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) : ℚ))
    = (μ.card : ℚ) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set c := μ.rowLen 2
  set d := μ.rowLen 3; set e := μ.rowLen 4; set f := μ.rowLen 5; set g := μ.rowLen 6
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  have hba : b ≤ a := μ.rowLen_anti 0 1 (by omega)
  have hbot : isCorner μ (6, g - 1) := sevenRow_corner_bot h7 h6
  have hcard : (μ.card : ℚ) = (a : ℚ) + b + c + d + e + f + g := by
    exact_mod_cast sevenRow_card h7
  rw [hcard]
  let ratio : ℕ × ℕ → ℚ := fun x =>
    if hx : isCorner μ x then (hookProd μ : ℚ) / hookProd (removeCorner μ x hx) else 0
  have hconvert : ∑ cc ∈ (corners μ).attach,
        ((hookProd μ : ℚ) / hookProd (removeCorner μ cc.val (mem_corners.mp cc.prop))) =
      ∑ x ∈ corners μ, ratio x := by
    rw [← Finset.sum_attach (f := ratio)]
    apply Finset.sum_congr rfl
    intro cx _; exact dif_pos (mem_corners.mp cx.2)
  have hsub : corners μ ⊆
      ({(6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
       Finset (ℕ × ℕ)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases sevenRow_corner_cases h7 h6 (mem_corners.mp hx) with
      heq | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
    · left; exact heq
    · right; left; exact heq
    · right; right; left; exact heq
    · right; right; right; left; exact heq
    · right; right; right; right; left; exact heq
    · right; right; right; right; right; left; exact heq
    · right; right; right; right; right; right; exact heq
  have hext : ∑ x ∈ corners μ, ratio x =
      ∑ x ∈ ({(6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
              Finset (ℕ × ℕ)), ratio x := by
    apply Finset.sum_subset hsub
    intro x _ hxnc; exact dif_neg (mt mem_corners.mpr hxnc)
  -- Compute ratio for corner (6, g-1)
  have hR6 : ratio (6, g - 1) =
      (g : ℚ) * ((f : ℚ) - g + 2) / ((f : ℚ) - g + 1) *
      ((e : ℚ) - g + 3) / ((e : ℚ) - g + 2) *
      ((d : ℚ) - g + 4) / ((d : ℚ) - g + 3) *
      ((c : ℚ) - g + 5) / ((c : ℚ) - g + 4) *
      ((b : ℚ) - g + 6) / ((b : ℚ) - g + 5) *
      ((a : ℚ) - g + 7) / ((a : ℚ) - g + 6) := by
    simp only [ratio, dif_pos hbot]
    rw [hookProd_ratio_formula hbot]
    simp only [Prod.fst, Prod.snd]
    rw [sevenRow_arm_row6 μ h7 hbot]
    have hg1 : g - 1 < g := Nat.sub_lt h6 Nat.one_pos
    have hmem0 : (0, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem1 : (1, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem2 : (2, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem3 : (3, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem4 : (4, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem5 : (5, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [show Finset.range 6 = {0, 1, 2, 3, 4, 5} from by ext k; simp; omega]
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
        Finset.prod_insert (by simp), Finset.prod_insert (by simp),
        Finset.prod_insert (by simp), Finset.prod_singleton]
    rw [sevenRow_hookLen_row0_lt h7 hmem0 hg1,
        sevenRow_hookLen_row1_lt h7 hmem1 hg1,
        sevenRow_hookLen_row2_lt h7 hmem2 hg1,
        sevenRow_hookLen_row3_lt h7 hmem3 hg1,
        sevenRow_hookLen_row4_lt h7 hmem4 hg1,
        sevenRow_hookLen_row5_lt h7 hmem5 hg1]
    push_cast [Nat.cast_sub (show 1 ≤ g from h6),
               Nat.cast_sub (show g - 1 ≤ a by omega),
               Nat.cast_sub (show g - 1 ≤ b by omega),
               Nat.cast_sub (show g - 1 ≤ c by omega),
               Nat.cast_sub (show g - 1 ≤ d by omega),
               Nat.cast_sub (show g - 1 ≤ e by omega),
               Nat.cast_sub (show g - 1 ≤ f by omega)]
    ring
  -- Compute ratio for corner (5, f-1) [when f > g]
  have hR5 : ratio (5, f - 1) =
      ((f : ℚ) + 1) * ((f : ℚ) - g) / ((f : ℚ) - g + 1) *
      ((e : ℚ) - f + 2) / ((e : ℚ) - f + 1) *
      ((d : ℚ) - f + 3) / ((d : ℚ) - f + 2) *
      ((c : ℚ) - f + 4) / ((c : ℚ) - f + 3) *
      ((b : ℚ) - f + 5) / ((b : ℚ) - f + 4) *
      ((a : ℚ) - f + 6) / ((a : ℚ) - f + 5) := by
    by_cases hgf' : g < f
    · have hmid : isCorner μ (5, f - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [sevenRow_arm_row5 h7 hgf']
      have hf1 : f - 1 < f := Nat.sub_lt (by omega) Nat.one_pos
      have hgf1 : g ≤ f - 1 := by omega
      have hmem0 : (0, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem3 : (3, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem4 : (4, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 5 = {0, 1, 2, 3, 4} from by ext k; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [sevenRow_hookLen_row0_mid1 h7 hmem0 hgf1 (by omega),
          sevenRow_hookLen_row1_mid1 h7 hmem1 hgf1 (by omega),
          sevenRow_hookLen_row2_mid1 h7 hmem2 hgf1 (by omega),
          sevenRow_hookLen_row3_mid1 h7 hmem3 hgf1 (by omega),
          sevenRow_hookLen_row4_mid1 h7 hmem4 hgf1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ f by omega),
                 Nat.cast_sub (show f - 1 ≤ a by omega),
                 Nat.cast_sub (show f - 1 ≤ b by omega),
                 Nat.cast_sub (show f - 1 ≤ c by omega),
                 Nat.cast_sub (show f - 1 ≤ d by omega),
                 Nat.cast_sub (show f - 1 ≤ e by omega),
                 Nat.cast_sub hgf'.le]
      ring
    · have hgf_eq : f = g := Nat.le_antisymm (not_lt.mp hgf') hgf
      have hnotcorner : ¬ isCorner μ (5, f - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (f : ℚ) - g = 0 := by rw [hgf_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (4, e-1) [when e > f]
  have hR4 : ratio (4, e - 1) =
      ((e : ℚ) + 2) * ((e : ℚ) - g + 1) * ((e : ℚ) - f) /
      (((e : ℚ) - g + 2) * ((e : ℚ) - f + 1)) *
      ((d : ℚ) - e + 2) / ((d : ℚ) - e + 1) *
      ((c : ℚ) - e + 3) / ((c : ℚ) - e + 2) *
      ((b : ℚ) - e + 4) / ((b : ℚ) - e + 3) *
      ((a : ℚ) - e + 5) / ((a : ℚ) - e + 4) := by
    by_cases hfe' : f < e
    · have hmid : isCorner μ (4, e - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [sevenRow_arm_row4 h7 hfe']
      have he1 : e - 1 < e := Nat.sub_lt (by omega) Nat.one_pos
      have hfe1 : f ≤ e - 1 := by omega
      have hmem0 : (0, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem3 : (3, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 4 = {0, 1, 2, 3} from by ext k; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [sevenRow_hookLen_row0_mid2 h7 hmem0 hfe1 (by omega),
          sevenRow_hookLen_row1_mid2 h7 hmem1 hfe1 (by omega),
          sevenRow_hookLen_row2_mid2 h7 hmem2 hfe1 (by omega),
          sevenRow_hookLen_row3_mid2 h7 hmem3 hfe1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ e by omega),
                 Nat.cast_sub (show e - 1 ≤ a by omega),
                 Nat.cast_sub (show e - 1 ≤ b by omega),
                 Nat.cast_sub (show e - 1 ≤ c by omega),
                 Nat.cast_sub (show e - 1 ≤ d by omega),
                 Nat.cast_sub hfe'.le, Nat.cast_sub hgf]
      ring
    · have hfe_eq : e = f := Nat.le_antisymm (not_lt.mp hfe') hfe
      have hnotcorner : ¬ isCorner μ (4, e - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (e : ℚ) - f = 0 := by rw [hfe_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (3, d-1) [when d > e]
  have hR3 : ratio (3, d - 1) =
      ((d : ℚ) + 3) * ((d : ℚ) - g + 2) * ((d : ℚ) - f + 1) * ((d : ℚ) - e) /
      (((d : ℚ) - g + 3) * ((d : ℚ) - f + 2) * ((d : ℚ) - e + 1)) *
      ((c : ℚ) - d + 2) / ((c : ℚ) - d + 1) *
      ((b : ℚ) - d + 3) / ((b : ℚ) - d + 2) *
      ((a : ℚ) - d + 4) / ((a : ℚ) - d + 3) := by
    by_cases hed' : e < d
    · have hmid : isCorner μ (3, d - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [sevenRow_arm_row3 h7 hed']
      have hd1 : d - 1 < d := Nat.sub_lt (by omega) Nat.one_pos
      have hed1 : e ≤ d - 1 := by omega
      have hmem0 : (0, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 3 = {0, 1, 2} from by ext k; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [sevenRow_hookLen_row0_mid3 h7 hmem0 hed1 (by omega),
          sevenRow_hookLen_row1_mid3 h7 hmem1 hed1 (by omega),
          sevenRow_hookLen_row2_mid3 h7 hmem2 hed1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ d by omega),
                 Nat.cast_sub (show d - 1 ≤ a by omega),
                 Nat.cast_sub (show d - 1 ≤ b by omega),
                 Nat.cast_sub (show d - 1 ≤ c by omega),
                 Nat.cast_sub hed'.le, Nat.cast_sub hfe, Nat.cast_sub hgf]
      ring
    · have hed_eq : d = e := Nat.le_antisymm (not_lt.mp hed') hed
      have hnotcorner : ¬ isCorner μ (3, d - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (d : ℚ) - e = 0 := by rw [hed_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (2, c-1) [when c > d]
  have hR2 : ratio (2, c - 1) =
      ((c : ℚ) + 4) * ((c : ℚ) - g + 3) * ((c : ℚ) - f + 2) *
      ((c : ℚ) - e + 1) * ((c : ℚ) - d) /
      (((c : ℚ) - g + 4) * ((c : ℚ) - f + 3) * ((c : ℚ) - e + 2) *
       ((c : ℚ) - d + 1)) *
      ((b : ℚ) - c + 2) / ((b : ℚ) - c + 1) *
      ((a : ℚ) - c + 3) / ((a : ℚ) - c + 2) := by
    by_cases hdc' : d < c
    · have hmid : isCorner μ (2, c - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [sevenRow_arm_row2 h7 hdc']
      have hc1 : c - 1 < c := Nat.sub_lt (by omega) Nat.one_pos
      have hdc1 : d ≤ c - 1 := by omega
      have hmem0 : (0, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 2 = {0, 1} from by ext k; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [sevenRow_hookLen_row0_mid4 h7 hmem0 hdc1 (by omega),
          sevenRow_hookLen_row1_mid4 h7 hmem1 hdc1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ c by omega),
                 Nat.cast_sub (show c - 1 ≤ a by omega),
                 Nat.cast_sub (show c - 1 ≤ b by omega),
                 Nat.cast_sub hdc'.le, Nat.cast_sub hed, Nat.cast_sub hfe, Nat.cast_sub hgf]
      ring
    · have hdc_eq : c = d := Nat.le_antisymm (not_lt.mp hdc') hdc
      have hnotcorner : ¬ isCorner μ (2, c - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (c : ℚ) - d = 0 := by rw [hdc_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (1, b-1) [when b > c]
  have hR1 : ratio (1, b - 1) =
      ((b : ℚ) + 5) * ((b : ℚ) - g + 4) * ((b : ℚ) - f + 3) *
      ((b : ℚ) - e + 2) * ((b : ℚ) - d + 1) * ((b : ℚ) - c) /
      (((b : ℚ) - g + 5) * ((b : ℚ) - f + 4) * ((b : ℚ) - e + 3) *
       ((b : ℚ) - d + 2) * ((b : ℚ) - c + 1)) *
      ((a : ℚ) - b + 2) / ((a : ℚ) - b + 1) := by
    by_cases hcb' : c < b
    · have hmid : isCorner μ (1, b - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [sevenRow_arm_row1 h7 hcb']
      have hmem0 : (0, b - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      rw [sevenRow_hookLen_row0_mid5 h7 hmem0 (by omega) (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ b by omega),
                 Nat.cast_sub (show b - 1 ≤ a by omega),
                 Nat.cast_sub hcb'.le, Nat.cast_sub hdc, Nat.cast_sub hed,
                 Nat.cast_sub hfe, Nat.cast_sub hgf]
      ring
    · have hcb_eq : b = c := Nat.le_antisymm (not_lt.mp hcb') hcb
      have hnotcorner : ¬ isCorner μ (1, b - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (b : ℚ) - c = 0 := by rw [hcb_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (0, a-1) [when a > b]
  have hR0 : ratio (0, a - 1) =
      ((a : ℚ) + 6) * ((a : ℚ) - g + 5) * ((a : ℚ) - f + 4) *
      ((a : ℚ) - e + 3) * ((a : ℚ) - d + 2) * ((a : ℚ) - c + 1) * ((a : ℚ) - b) /
      (((a : ℚ) - g + 6) * ((a : ℚ) - f + 5) * ((a : ℚ) - e + 4) *
       ((a : ℚ) - d + 3) * ((a : ℚ) - c + 2) * ((a : ℚ) - b + 1)) := by
    by_cases hab' : b < a
    · have htop : isCorner μ (0, a - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos htop]
      rw [hookProd_ratio_formula htop]
      simp only [Prod.fst, Prod.snd, Finset.prod_range_zero, mul_one]
      rw [sevenRow_arm_row0 h7 h6 hab']
      push_cast [Nat.cast_sub hab'.le, Nat.cast_sub hcb, Nat.cast_sub hdc,
                 Nat.cast_sub hed, Nat.cast_sub hfe, Nat.cast_sub hgf]
      ring
    · have hab_eq : a = b := Nat.le_antisymm (not_lt.mp hab') hba
      have hnotcorner : ¬ isCorner μ (0, a - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (a : ℚ) - b = 0 := by rw [hab_eq]; ring
      rw [this]; ring
  rw [hconvert, hext]
  have hne65 : (6, g - 1) ∉ ({(5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
      Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne54 : (5, f - 1) ∉ ({(4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
      Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne43 : (4, e - 1) ∉ ({(3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
      Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne32 : (3, d - 1) ∉ ({(2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hne21 : (2, c - 1) ∉ ({(1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hne10 : (1, b - 1) ∉ ({(0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  rw [show ({(6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
      Finset (ℕ × ℕ)) = insert (6, g - 1) (insert (5, f - 1) (insert (4, e - 1)
        (insert (3, d - 1) (insert (2, c - 1) (insert (1, b - 1) {(0, a - 1)}))))) from rfl,
      Finset.sum_insert hne65, Finset.sum_insert hne54, Finset.sum_insert hne43,
      Finset.sum_insert hne32, Finset.sum_insert hne21, Finset.sum_insert hne10,
      Finset.sum_singleton,
      hR6, hR5, hR4, hR3, hR2, hR1, hR0]
  have hne_fg1 : (f : ℚ) - g + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < f - g + 1 by omega)
  have hne_eg2 : (e : ℚ) - g + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < e - g + 2 by omega)
  have hne_dg3 : (d : ℚ) - g + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < d - g + 3 by omega)
  have hne_cg4 : (c : ℚ) - g + 4 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - g + 4 by omega)
  have hne_bg5 : (b : ℚ) - g + 5 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - g + 5 by omega)
  have hne_ag6 : (a : ℚ) - g + 6 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - g + 6 by omega)
  have hne_ef1 : (e : ℚ) - f + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < e - f + 1 by omega)
  have hne_df2 : (d : ℚ) - f + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < d - f + 2 by omega)
  have hne_cf3 : (c : ℚ) - f + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - f + 3 by omega)
  have hne_bf4 : (b : ℚ) - f + 4 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - f + 4 by omega)
  have hne_af5 : (a : ℚ) - f + 5 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - f + 5 by omega)
  have hne_de1 : (d : ℚ) - e + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < d - e + 1 by omega)
  have hne_ce2 : (c : ℚ) - e + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - e + 2 by omega)
  have hne_be3 : (b : ℚ) - e + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - e + 3 by omega)
  have hne_ae4 : (a : ℚ) - e + 4 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - e + 4 by omega)
  have hne_cd1 : (c : ℚ) - d + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  have hne_bd2 : (b : ℚ) - d + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne_ad3 : (a : ℚ) - d + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne_bc1 : (b : ℚ) - c + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  have hne_ac2 : (a : ℚ) - c + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne_ab1 : (a : ℚ) - b + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  push_cast [Nat.cast_sub hgf, Nat.cast_sub hfe, Nat.cast_sub hed, Nat.cast_sub hdc,
             Nat.cast_sub hcb, Nat.cast_sub hba,
             Nat.cast_sub (show g ≤ e by omega), Nat.cast_sub (show g ≤ d by omega),
             Nat.cast_sub (show g ≤ c by omega), Nat.cast_sub (show g ≤ b by omega),
             Nat.cast_sub (show g ≤ a by omega), Nat.cast_sub (show f ≤ d by omega),
             Nat.cast_sub (show f ≤ c by omega), Nat.cast_sub (show f ≤ b by omega),
             Nat.cast_sub (show f ≤ a by omega), Nat.cast_sub (show e ≤ c by omega),
             Nat.cast_sub (show e ≤ b by omega), Nat.cast_sub (show e ≤ a by omega),
             Nat.cast_sub (show d ≤ b by omega), Nat.cast_sub (show d ≤ a by omega),
             Nat.cast_sub (show c ≤ a by omega)]
  field_simp [hne_fg1, hne_eg2, hne_dg3, hne_cg4, hne_bg5, hne_ag6,
              hne_ef1, hne_df2, hne_cf3, hne_bf4, hne_af5,
              hne_de1, hne_ce2, hne_be3, hne_ae4,
              hne_cd1, hne_bd2, hne_ad3, hne_bc1, hne_ac2, hne_ab1]
  ring

/-! ## PART XXII: hook_walk_identity for exactly-8-row Young diagrams

  For μ with rowLen 8 = 0 and rowLen 7 > 0: direct computation via hookProd_ratio_formula.
  Uses 7 colLen zones, 36 hookLen lemmas, 8 arm lemmas, then field_simp/ring. -/

/-- colLen(s) = 8 for s < rowLen 7 in an 8-row shape (rowLen 8 = 0). -/
private lemma eightRow_colLen_lt {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hs : s < μ.rowLen 7) : μ.colLen s = 8 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h8s : (8, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h8s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs)

/-- colLen(s) = 7 for rowLen 7 ≤ s < rowLen 6 in an 8-row shape. -/
private lemma eightRow_colLen_mid1 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    μ.colLen s = 7 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h7s : (7, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h7s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 6 for rowLen 6 ≤ s < rowLen 5 in an 8-row shape. -/
private lemma eightRow_colLen_mid2 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    μ.colLen s = 6 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h6s : (6, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h6s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 5 for rowLen 5 ≤ s < rowLen 4 in an 8-row shape. -/
private lemma eightRow_colLen_mid3 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    μ.colLen s = 5 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h5s : (5, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h5s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 4 for rowLen 4 ≤ s < rowLen 3 in an 8-row shape. -/
private lemma eightRow_colLen_mid4 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    μ.colLen s = 4 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h4s : (4, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h4s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 3 for rowLen 3 ≤ s < rowLen 2 in an 8-row shape. -/
private lemma eightRow_colLen_mid5 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    μ.colLen s = 3 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h3s : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h3s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 2 for rowLen 2 ≤ s < rowLen 1 in an 8-row shape. -/
private lemma eightRow_colLen_mid6 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    μ.colLen s = 2 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h2s : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h2s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

-- hookLen lemmas: row 7 (1 zone)
private lemma eightRow_hookLen_row7 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (7, s) ∈ μ) :
    hookLength μ 7 s = μ.rowLen 7 - s := by
  have hs : s < μ.rowLen 7 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_lt h8 hs] at key; omega

-- hookLen lemmas: row 6 (2 zones)
private lemma eightRow_hookLen_row6_lt {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (6, s) ∈ μ) (hs : s < μ.rowLen 7) :
    hookLength μ 6 s = μ.rowLen 6 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_lt h8 hs] at key; omega

private lemma eightRow_hookLen_row6_ge {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (6, s) ∈ μ) (hs : μ.rowLen 7 ≤ s) :
    hookLength μ 6 s = μ.rowLen 6 - s := by
  have hs_lt : s < μ.rowLen 6 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid1 h8 hs hs_lt] at key; omega

-- hookLen lemmas: row 5 (3 zones)
private lemma eightRow_hookLen_row5_lt {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (5, s) ∈ μ) (hs : s < μ.rowLen 7) :
    hookLength μ 5 s = μ.rowLen 5 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_lt h8 hs] at key; omega

private lemma eightRow_hookLen_row5_mid1 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (5, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 5 s = μ.rowLen 5 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid1 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row5_ge {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (5, s) ∈ μ) (hs : μ.rowLen 6 ≤ s) :
    hookLength μ 5 s = μ.rowLen 5 - s := by
  have hs_lt : s < μ.rowLen 5 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid2 h8 hs hs_lt] at key; omega

-- hookLen lemmas: row 4 (4 zones)
private lemma eightRow_hookLen_row4_lt {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (4, s) ∈ μ) (hs : s < μ.rowLen 7) :
    hookLength μ 4 s = μ.rowLen 4 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_lt h8 hs] at key; omega

private lemma eightRow_hookLen_row4_mid1 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (4, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 4 s = μ.rowLen 4 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid1 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row4_mid2 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (4, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 4 s = μ.rowLen 4 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid2 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row4_ge {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (4, s) ∈ μ) (hs : μ.rowLen 5 ≤ s) :
    hookLength μ 4 s = μ.rowLen 4 - s := by
  have hs_lt : s < μ.rowLen 4 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid3 h8 hs hs_lt] at key; omega

-- hookLen lemmas: row 3 (5 zones)
private lemma eightRow_hookLen_row3_lt {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (3, s) ∈ μ) (hs : s < μ.rowLen 7) :
    hookLength μ 3 s = μ.rowLen 3 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_lt h8 hs] at key; omega

private lemma eightRow_hookLen_row3_mid1 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (3, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 3 s = μ.rowLen 3 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid1 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row3_mid2 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (3, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 3 s = μ.rowLen 3 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid2 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row3_mid3 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (3, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 3 s = μ.rowLen 3 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid3 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row3_ge {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (3, s) ∈ μ) (hs : μ.rowLen 4 ≤ s) :
    hookLength μ 3 s = μ.rowLen 3 - s := by
  have hs_lt : s < μ.rowLen 3 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid4 h8 hs hs_lt] at key; omega

-- hookLen lemmas: row 2 (6 zones)
private lemma eightRow_hookLen_row2_lt {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (2, s) ∈ μ) (hs : s < μ.rowLen 7) :
    hookLength μ 2 s = μ.rowLen 2 - s + 5 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_lt h8 hs] at key; omega

private lemma eightRow_hookLen_row2_mid1 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 2 s = μ.rowLen 2 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid1 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row2_mid2 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 2 s = μ.rowLen 2 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid2 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row2_mid3 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 2 s = μ.rowLen 2 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid3 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row2_mid4 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 2 s = μ.rowLen 2 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid4 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row2_ge {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (2, s) ∈ μ) (hs : μ.rowLen 3 ≤ s) :
    hookLength μ 2 s = μ.rowLen 2 - s := by
  have hs_lt : s < μ.rowLen 2 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid5 h8 hs hs_lt] at key; omega

-- hookLen lemmas: row 1 (7 zones)
private lemma eightRow_hookLen_row1_lt {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (1, s) ∈ μ) (hs : s < μ.rowLen 7) :
    hookLength μ 1 s = μ.rowLen 1 - s + 6 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_lt h8 hs] at key; omega

private lemma eightRow_hookLen_row1_mid1 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 1 s = μ.rowLen 1 - s + 5 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid1 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row1_mid2 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 1 s = μ.rowLen 1 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid2 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row1_mid3 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 1 s = μ.rowLen 1 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid3 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row1_mid4 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 1 s = μ.rowLen 1 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid4 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row1_mid5 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    hookLength μ 1 s = μ.rowLen 1 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid5 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row1_ge {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (1, s) ∈ μ) (hs : μ.rowLen 2 ≤ s) :
    hookLength μ 1 s = μ.rowLen 1 - s := by
  have hs_lt : s < μ.rowLen 1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid6 h8 hs hs_lt] at key; omega

-- hookLen lemmas: row 0 (8 zones)
private lemma eightRow_hookLen_row0_lt {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (0, s) ∈ μ) (hs : s < μ.rowLen 7) :
    hookLength μ 0 s = μ.rowLen 0 - s + 7 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_lt h8 hs] at key; omega

private lemma eightRow_hookLen_row0_mid1 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 0 s = μ.rowLen 0 - s + 6 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid1 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row0_mid2 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 0 s = μ.rowLen 0 - s + 5 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid2 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row0_mid3 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 0 s = μ.rowLen 0 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid3 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row0_mid4 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 0 s = μ.rowLen 0 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid4 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row0_mid5 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    hookLength μ 0 s = μ.rowLen 0 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid5 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row0_mid6 {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    hookLength μ 0 s = μ.rowLen 0 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [eightRow_colLen_mid6 h8 hs_ge hs_lt] at key; omega

private lemma eightRow_hookLen_row0_ge {μ : YoungDiagram} {s : ℕ}
    (h8 : μ.rowLen 8 = 0) (hmem : (0, s) ∈ μ) (hs : μ.rowLen 1 ≤ s) :
    hookLength μ 0 s = μ.rowLen 0 - s := by
  have hs_lt : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  have hcol : μ.colLen s = 1 := by
    apply Nat.le_antisymm
    · by_contra hlt; push_neg at hlt
      have h1s : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
      have := YoungDiagram.mem_iff_lt_rowLen.mp h1s; omega
    · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)
  rw [hcol] at key; omega

/-- Bottom corner (7, rowLen 7 - 1) always exists in an 8-row shape. -/
private lemma eightRow_corner_bot {μ : YoungDiagram} (h8 : μ.rowLen 8 = 0) (h7 : 0 < μ.rowLen 7) :
    isCorner μ (7, μ.rowLen 7 - 1) := by
  refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
  · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
  · intro h
    have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega

/-- Corner classification for 8-row shapes: corners are among the 8 possible positions. -/
private lemma eightRow_corner_cases {μ : YoungDiagram} (h8 : μ.rowLen 8 = 0) (h7 : 0 < μ.rowLen 7)
    {cell : ℕ × ℕ} (hc : isCorner μ cell) :
    (cell = (7, μ.rowLen 7 - 1)) ∨
    (cell = (6, μ.rowLen 6 - 1) ∧ μ.rowLen 7 < μ.rowLen 6) ∨
    (cell = (5, μ.rowLen 5 - 1) ∧ μ.rowLen 6 < μ.rowLen 5) ∨
    (cell = (4, μ.rowLen 4 - 1) ∧ μ.rowLen 5 < μ.rowLen 4) ∨
    (cell = (3, μ.rowLen 3 - 1) ∧ μ.rowLen 4 < μ.rowLen 3) ∨
    (cell = (2, μ.rowLen 2 - 1) ∧ μ.rowLen 3 < μ.rowLen 2) ∨
    (cell = (1, μ.rowLen 1 - 1) ∧ μ.rowLen 2 < μ.rowLen 1) ∨
    (cell = (0, μ.rowLen 0 - 1) ∧ μ.rowLen 1 < μ.rowLen 0) := by
  obtain ⟨hmem, hnext, hprev⟩ := hc
  have hrow := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  obtain ⟨i, j⟩ := cell
  simp only [Prod.mk.injEq]
  have hi7 : i ≤ 7 := by
    by_contra h; push_neg at h
    have : μ.rowLen 8 > 0 := by
      calc μ.rowLen 8 ≥ μ.rowLen i := μ.rowLen_anti (by omega) (by omega)
        _ > 0 := by omega
    omega
  have hj : j = μ.rowLen i - 1 := by
    apply Nat.le_antisymm
    · by_contra h; push_neg at h
      have : (i, j + 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hnext this
    · have : ¬ (i, j + 1) ∈ μ := hnext
      by_contra h; push_neg at h
      have : μ.rowLen i > j + 1 := by omega
      exact absurd (YoungDiagram.mem_iff_lt_rowLen.mpr this) hnext
  subst hj
  interval_cases i
  · right; right; right; right; right; right; right
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 1 = μ.rowLen 0 := Nat.le_antisymm (μ.rowLen_anti 0 1 (by omega)) h
      have : (1, μ.rowLen 0 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 2 = μ.rowLen 1 := Nat.le_antisymm (μ.rowLen_anti 1 2 (by omega)) h
      have : (2, μ.rowLen 1 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 3 = μ.rowLen 2 := Nat.le_antisymm (μ.rowLen_anti 2 3 (by omega)) h
      have : (3, μ.rowLen 2 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 4 = μ.rowLen 3 := Nat.le_antisymm (μ.rowLen_anti 3 4 (by omega)) h
      have : (4, μ.rowLen 3 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 5 = μ.rowLen 4 := Nat.le_antisymm (μ.rowLen_anti 4 5 (by omega)) h
      have : (5, μ.rowLen 4 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 6 = μ.rowLen 5 := Nat.le_antisymm (μ.rowLen_anti 5 6 (by omega)) h
      have : (6, μ.rowLen 5 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 7 = μ.rowLen 6 := Nat.le_antisymm (μ.rowLen_anti 6 7 (by omega)) h
      have : (7, μ.rowLen 6 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · left; rfl

/-- Card of an 8-row shape equals sum of row lengths. -/
private lemma eightRow_card {μ : YoungDiagram} (h8 : μ.rowLen 8 = 0) :
    μ.card = μ.rowLen 0 + μ.rowLen 1 + μ.rowLen 2 + μ.rowLen 3 +
             μ.rowLen 4 + μ.rowLen 5 + μ.rowLen 6 + μ.rowLen 7 := by
  have hcells : μ.cells =
      (Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
      (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
      (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
      (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
      (Finset.range (μ.rowLen 4)).image (Prod.mk 4) ∪
      (Finset.range (μ.rowLen 5)).image (Prod.mk 5) ∪
      (Finset.range (μ.rowLen 6)).image (Prod.mk 6) ∪
      (Finset.range (μ.rowLen 7)).image (Prod.mk 7) := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, Finset.mem_union, Finset.mem_image,
               Finset.mem_range, Prod.mk.injEq]
    constructor
    · intro h
      have hil : i ≤ 7 := by
        by_contra hlt; push_neg at hlt
        have : μ.rowLen 8 > 0 := calc
          μ.rowLen 8 ≥ μ.rowLen i := μ.rowLen_anti (by omega) (by omega)
          _ > 0 := by
            have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega
        omega
      have hj := YoungDiagram.mem_iff_lt_rowLen.mp h
      interval_cases i <;> simp_all [Prod.mk.injEq]
    · rintro (((((((⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) |
                   ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) |
                 ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩)
      all_goals exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have mk_inj : ∀ (n : ℕ), Function.Injective (Prod.mk n) := fun _ _ _ h => (Prod.mk.inj h).2
  have hd01 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0))
                       ((Finset.range (μ.rowLen 1)).image (Prod.mk 1)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ⟨_, _, rfl, rfl⟩ := hx; obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd012 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                         (Finset.range (μ.rowLen 1)).image (Prod.mk 1))
                        ((Finset.range (μ.rowLen 2)).image (Prod.mk 2)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd0123 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                          (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                          (Finset.range (μ.rowLen 2)).image (Prod.mk 2))
                         ((Finset.range (μ.rowLen 3)).image (Prod.mk 3)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd01234 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                           (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                           (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                           (Finset.range (μ.rowLen 3)).image (Prod.mk 3))
                          ((Finset.range (μ.rowLen 4)).image (Prod.mk 4)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
               ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd012345 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                            (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                            (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                            (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
                            (Finset.range (μ.rowLen 4)).image (Prod.mk 4))
                           ((Finset.range (μ.rowLen 5)).image (Prod.mk 5)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
                ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd0123456 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                             (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                             (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                             (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
                             (Finset.range (μ.rowLen 4)).image (Prod.mk 4) ∪
                             (Finset.range (μ.rowLen 5)).image (Prod.mk 5))
                            ((Finset.range (μ.rowLen 6)).image (Prod.mk 6)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (((((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
                 ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd01234567 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                              (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                              (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                              (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
                              (Finset.range (μ.rowLen 4)).image (Prod.mk 4) ∪
                              (Finset.range (μ.rowLen 5)).image (Prod.mk 5) ∪
                              (Finset.range (μ.rowLen 6)).image (Prod.mk 6))
                             ((Finset.range (μ.rowLen 7)).image (Prod.mk 7)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((((((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
                  ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
               ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  rw [hcells,
      Finset.card_union_of_disjoint hd01234567,
      Finset.card_union_of_disjoint hd0123456,
      Finset.card_union_of_disjoint hd012345,
      Finset.card_union_of_disjoint hd01234,
      Finset.card_union_of_disjoint hd0123,
      Finset.card_union_of_disjoint hd012,
      Finset.card_union_of_disjoint hd01,
      Finset.card_image_of_injective _ (mk_inj 0),
      Finset.card_image_of_injective _ (mk_inj 1),
      Finset.card_image_of_injective _ (mk_inj 2),
      Finset.card_image_of_injective _ (mk_inj 3),
      Finset.card_image_of_injective _ (mk_inj 4),
      Finset.card_image_of_injective _ (mk_inj 5),
      Finset.card_image_of_injective _ (mk_inj 6),
      Finset.card_image_of_injective _ (mk_inj 7),
      Finset.card_range, Finset.card_range, Finset.card_range, Finset.card_range,
      Finset.card_range, Finset.card_range, Finset.card_range, Finset.card_range]

/-- Arm product for corner (7, k-1) in an 8-row shape telescopes to k. -/
private lemma eightRow_arm_row7 (μ : YoungDiagram) (h8 : μ.rowLen 8 = 0)
    (hk : isCorner μ (7, μ.rowLen 7 - 1)) :
    ∏ s ∈ Finset.range (μ.rowLen 7 - 1),
      ((hookLength μ 7 s : ℚ) / ((hookLength μ 7 s : ℚ) - 1)) =
    (μ.rowLen 7 : ℚ) := by
  set k := μ.rowLen 7
  have hk_pos : 0 < k := by have := YoungDiagram.mem_iff_lt_rowLen.mp hk.1; omega
  have hconv : ∀ s ∈ Finset.range (k - 1),
      (hookLength μ 7 s : ℚ) / ((hookLength μ 7 s : ℚ) - 1) =
      ((k : ℚ) - s) / ((k : ℚ) - s - 1) := by
    intro s hs
    have hsc : s < k - 1 := Finset.mem_range.mp hs
    have hmem : (7, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row7 h8 hmem]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv]
  rw [prod_div_telescope k (k - 1) (Nat.sub_lt hk_pos Nat.one_pos)]
  push_cast; simp [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk_pos))]

/-- Arm product for corner (6, g-1) in an 8-row shape:
    ∏ = (g+1)(g-k)/((g-k+1)). -/
private lemma eightRow_arm_row6 {μ : YoungDiagram} (h8 : μ.rowLen 8 = 0)
    (hkg : μ.rowLen 7 < μ.rowLen 6) :
    ∏ s ∈ Finset.range (μ.rowLen 6 - 1),
      ((hookLength μ 6 s : ℚ) / ((hookLength μ 6 s : ℚ) - 1)) =
    ((μ.rowLen 6 : ℚ) + 1) * ((μ.rowLen 6 : ℚ) - μ.rowLen 7) /
    ((μ.rowLen 6 : ℚ) - μ.rowLen 7 + 1) := by
  set g := μ.rowLen 6; set k := μ.rowLen 7
  rw [show Finset.range (g - 1) = Finset.range k ∪ Finset.Ico k (g - 1) from by
    ext s; simp [Finset.mem_Ico]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range k,
      (hookLength μ 6 s : ℚ) / ((hookLength μ 6 s : ℚ) - 1) =
      ((g : ℚ) + 1 - s) / ((g : ℚ) + 1 - s - 1) := by
    intro s hs
    have hsk : s < k := Finset.mem_range.mp hs
    have hmem : (6, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row6_lt h8 hmem hsk]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (g + 1) k (by omega)]
  rw [show Finset.Ico k (g - 1) = (Finset.range (g - 1 - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (g - 1 - k),
      (hookLength μ 6 (t + k) : ℚ) / ((hookLength μ 6 (t + k) : ℚ) - 1) =
      ((g : ℚ) - k - t) / ((g : ℚ) - k - t - 1) := by
    intro t ht
    have htm : t < g - 1 - k := Finset.mem_range.mp ht
    have hmem : (6, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row6_ge h8 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (g - k) (g - 1 - k) (by omega)]
  push_cast [Nat.cast_sub hkg.le, Nat.cast_sub (show 1 ≤ g - k by omega)]
  have hne : (g : ℚ) - k + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < g - k + 1 by omega)
  field_simp [hne]; ring

/-- Arm product for corner (5, f-1) in an 8-row shape:
    ∏ = (f+2)(f-k+1)(f-g)/((f-k+2)(f-g+1)). -/
private lemma eightRow_arm_row5 {μ : YoungDiagram} (h8 : μ.rowLen 8 = 0)
    (hgf : μ.rowLen 6 < μ.rowLen 5) :
    ∏ s ∈ Finset.range (μ.rowLen 5 - 1),
      ((hookLength μ 5 s : ℚ) / ((hookLength μ 5 s : ℚ) - 1)) =
    ((μ.rowLen 5 : ℚ) + 2) * ((μ.rowLen 5 : ℚ) - μ.rowLen 7 + 1) *
    ((μ.rowLen 5 : ℚ) - μ.rowLen 6) /
    (((μ.rowLen 5 : ℚ) - μ.rowLen 7 + 2) * ((μ.rowLen 5 : ℚ) - μ.rowLen 6 + 1)) := by
  set f := μ.rowLen 5; set g := μ.rowLen 6; set k := μ.rowLen 7
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  rw [show Finset.range (f - 1) = Finset.range k ∪ Finset.Ico k g ∪ Finset.Ico g (f - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range k,
      (hookLength μ 5 s : ℚ) / ((hookLength μ 5 s : ℚ) - 1) =
      ((f : ℚ) + 2 - s) / ((f : ℚ) + 2 - s - 1) := by
    intro s hs
    have hsk : s < k := Finset.mem_range.mp hs
    have hmem : (5, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row5_lt h8 hmem hsk]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (f + 2) k (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 5 (t + k) : ℚ) / ((hookLength μ 5 (t + k) : ℚ) - 1) =
      ((f : ℚ) - k + 1 - t) / ((f : ℚ) - k + 1 - t - 1) := by
    intro t ht
    have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (5, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row5_mid1 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (f - k + 1) (g - k) (by omega)]
  rw [show Finset.Ico g (f - 1) = (Finset.range (f - 1 - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (f - 1 - g),
      (hookLength μ 5 (t + g) : ℚ) / ((hookLength μ 5 (t + g) : ℚ) - 1) =
      ((f : ℚ) - g - t) / ((f : ℚ) - g - t - 1) := by
    intro t ht
    have htm : t < f - 1 - g := Finset.mem_range.mp ht
    have hmem : (5, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row5_ge h8 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (f - g) (f - 1 - g) (by omega)]
  push_cast [Nat.cast_sub hkg, Nat.cast_sub hgf.le, Nat.cast_sub (show 1 ≤ f - g by omega)]
  have hne1 : (f : ℚ) - k + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < f - k + 2 by omega)
  have hne2 : (f : ℚ) - g + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < f - g + 1 by omega)
  field_simp [hne1, hne2]; ring

/-- Arm product for corner (4, e-1) in an 8-row shape:
    ∏ = (e+3)(e-k+2)(e-g+1)(e-f)/((e-k+3)(e-g+2)(e-f+1)). -/
private lemma eightRow_arm_row4 {μ : YoungDiagram} (h8 : μ.rowLen 8 = 0)
    (hfe : μ.rowLen 5 < μ.rowLen 4) :
    ∏ s ∈ Finset.range (μ.rowLen 4 - 1),
      ((hookLength μ 4 s : ℚ) / ((hookLength μ 4 s : ℚ) - 1)) =
    ((μ.rowLen 4 : ℚ) + 3) * ((μ.rowLen 4 : ℚ) - μ.rowLen 7 + 2) *
    ((μ.rowLen 4 : ℚ) - μ.rowLen 6 + 1) * ((μ.rowLen 4 : ℚ) - μ.rowLen 5) /
    (((μ.rowLen 4 : ℚ) - μ.rowLen 7 + 3) * ((μ.rowLen 4 : ℚ) - μ.rowLen 6 + 2) *
     ((μ.rowLen 4 : ℚ) - μ.rowLen 5 + 1)) := by
  set e := μ.rowLen 4; set f := μ.rowLen 5; set g := μ.rowLen 6; set k := μ.rowLen 7
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  rw [show Finset.range (e - 1) = Finset.range k ∪ Finset.Ico k g ∪
      Finset.Ico g f ∪ Finset.Ico f (e - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range k,
      (hookLength μ 4 s : ℚ) / ((hookLength μ 4 s : ℚ) - 1) =
      ((e : ℚ) + 3 - s) / ((e : ℚ) + 3 - s - 1) := by
    intro s hs
    have hsk : s < k := Finset.mem_range.mp hs
    have hmem : (4, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row4_lt h8 hmem hsk]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (e + 3) k (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 4 (t + k) : ℚ) / ((hookLength μ 4 (t + k) : ℚ) - 1) =
      ((e : ℚ) - k + 2 - t) / ((e : ℚ) - k + 2 - t - 1) := by
    intro t ht
    have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (4, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row4_mid1 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (e - k + 2) (g - k) (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 4 (t + g) : ℚ) / ((hookLength μ 4 (t + g) : ℚ) - 1) =
      ((e : ℚ) - g + 1 - t) / ((e : ℚ) - g + 1 - t - 1) := by
    intro t ht
    have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (4, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row4_mid2 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (e - g + 1) (f - g) (by omega)]
  rw [show Finset.Ico f (e - 1) = (Finset.range (e - 1 - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (e - 1 - f),
      (hookLength μ 4 (t + f) : ℚ) / ((hookLength μ 4 (t + f) : ℚ) - 1) =
      ((e : ℚ) - f - t) / ((e : ℚ) - f - t - 1) := by
    intro t ht
    have htm : t < e - 1 - f := Finset.mem_range.mp ht
    have hmem : (4, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row4_ge h8 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (e - f) (e - 1 - f) (by omega)]
  push_cast [Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe.le,
             Nat.cast_sub (show 1 ≤ e - f by omega)]
  have hne1 : (e : ℚ) - k + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - k + 3 by omega)
  have hne2 : (e : ℚ) - g + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - g + 2 by omega)
  have hne3 : (e : ℚ) - f + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - f + 1 by omega)
  field_simp [hne1, hne2, hne3]; ring

/-- Arm product for corner (3, d-1) in an 8-row shape:
    ∏ = (d+4)(d-k+3)(d-g+2)(d-f+1)(d-e)/((d-k+4)(d-g+3)(d-f+2)(d-e+1)). -/
private lemma eightRow_arm_row3 {μ : YoungDiagram} (h8 : μ.rowLen 8 = 0)
    (hed : μ.rowLen 4 < μ.rowLen 3) :
    ∏ s ∈ Finset.range (μ.rowLen 3 - 1),
      ((hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1)) =
    ((μ.rowLen 3 : ℚ) + 4) * ((μ.rowLen 3 : ℚ) - μ.rowLen 7 + 3) *
    ((μ.rowLen 3 : ℚ) - μ.rowLen 6 + 2) * ((μ.rowLen 3 : ℚ) - μ.rowLen 5 + 1) *
    ((μ.rowLen 3 : ℚ) - μ.rowLen 4) /
    (((μ.rowLen 3 : ℚ) - μ.rowLen 7 + 4) * ((μ.rowLen 3 : ℚ) - μ.rowLen 6 + 3) *
     ((μ.rowLen 3 : ℚ) - μ.rowLen 5 + 2) * ((μ.rowLen 3 : ℚ) - μ.rowLen 4 + 1)) := by
  set d := μ.rowLen 3; set e := μ.rowLen 4; set f := μ.rowLen 5
  set g := μ.rowLen 6; set k := μ.rowLen 7
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  rw [show Finset.range (d - 1) = Finset.range k ∪ Finset.Ico k g ∪
      Finset.Ico g f ∪ Finset.Ico f e ∪ Finset.Ico e (d - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range k,
      (hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1) =
      ((d : ℚ) + 4 - s) / ((d : ℚ) + 4 - s - 1) := by
    intro s hs
    have hsk : s < k := Finset.mem_range.mp hs
    have hmem : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row3_lt h8 hmem hsk]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (d + 4) k (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 3 (t + k) : ℚ) / ((hookLength μ 3 (t + k) : ℚ) - 1) =
      ((d : ℚ) - k + 3 - t) / ((d : ℚ) - k + 3 - t - 1) := by
    intro t ht
    have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (3, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row3_mid1 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (d - k + 3) (g - k) (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 3 (t + g) : ℚ) / ((hookLength μ 3 (t + g) : ℚ) - 1) =
      ((d : ℚ) - g + 2 - t) / ((d : ℚ) - g + 2 - t - 1) := by
    intro t ht
    have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (3, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row3_mid2 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (d - g + 2) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 3 (t + f) : ℚ) / ((hookLength μ 3 (t + f) : ℚ) - 1) =
      ((d : ℚ) - f + 1 - t) / ((d : ℚ) - f + 1 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (3, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row3_mid3 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (d - f + 1) (e - f) (by omega)]
  rw [show Finset.Ico e (d - 1) = (Finset.range (d - 1 - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (d - 1 - e),
      (hookLength μ 3 (t + e) : ℚ) / ((hookLength μ 3 (t + e) : ℚ) - 1) =
      ((d : ℚ) - e - t) / ((d : ℚ) - e - t - 1) := by
    intro t ht
    have htm : t < d - 1 - e := Finset.mem_range.mp ht
    have hmem : (3, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row3_ge h8 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (d - e) (d - 1 - e) (by omega)]
  push_cast [Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe, Nat.cast_sub hed.le,
             Nat.cast_sub (show 1 ≤ d - e by omega)]
  have hne1 : (d : ℚ) - k + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - k + 4 by omega)
  have hne2 : (d : ℚ) - g + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - g + 3 by omega)
  have hne3 : (d : ℚ) - f + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - f + 2 by omega)
  have hne4 : (d : ℚ) - e + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - e + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4]; ring

/-- Arm product for corner (2, c-1) in an 8-row shape:
    ∏ = (c+5)(c-k+4)(c-g+3)(c-f+2)(c-e+1)(c-d)/((c-k+5)(c-g+4)(c-f+3)(c-e+2)(c-d+1)). -/
private lemma eightRow_arm_row2 {μ : YoungDiagram} (h8 : μ.rowLen 8 = 0)
    (hdc : μ.rowLen 3 < μ.rowLen 2) :
    ∏ s ∈ Finset.range (μ.rowLen 2 - 1),
      ((hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1)) =
    ((μ.rowLen 2 : ℚ) + 5) * ((μ.rowLen 2 : ℚ) - μ.rowLen 7 + 4) *
    ((μ.rowLen 2 : ℚ) - μ.rowLen 6 + 3) * ((μ.rowLen 2 : ℚ) - μ.rowLen 5 + 2) *
    ((μ.rowLen 2 : ℚ) - μ.rowLen 4 + 1) * ((μ.rowLen 2 : ℚ) - μ.rowLen 3) /
    (((μ.rowLen 2 : ℚ) - μ.rowLen 7 + 5) * ((μ.rowLen 2 : ℚ) - μ.rowLen 6 + 4) *
     ((μ.rowLen 2 : ℚ) - μ.rowLen 5 + 3) * ((μ.rowLen 2 : ℚ) - μ.rowLen 4 + 2) *
     ((μ.rowLen 2 : ℚ) - μ.rowLen 3 + 1)) := by
  set c := μ.rowLen 2; set d := μ.rowLen 3; set e := μ.rowLen 4
  set f := μ.rowLen 5; set g := μ.rowLen 6; set k := μ.rowLen 7
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  rw [show Finset.range (c - 1) = Finset.range k ∪ Finset.Ico k g ∪
      Finset.Ico g f ∪ Finset.Ico f e ∪ Finset.Ico e d ∪ Finset.Ico d (c - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range k,
      (hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1) =
      ((c : ℚ) + 5 - s) / ((c : ℚ) + 5 - s - 1) := by
    intro s hs
    have hsk : s < k := Finset.mem_range.mp hs
    have hmem : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row2_lt h8 hmem hsk]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (c + 5) k (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 2 (t + k) : ℚ) / ((hookLength μ 2 (t + k) : ℚ) - 1) =
      ((c : ℚ) - k + 4 - t) / ((c : ℚ) - k + 4 - t - 1) := by
    intro t ht
    have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (2, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row2_mid1 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (c - k + 4) (g - k) (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 2 (t + g) : ℚ) / ((hookLength μ 2 (t + g) : ℚ) - 1) =
      ((c : ℚ) - g + 3 - t) / ((c : ℚ) - g + 3 - t - 1) := by
    intro t ht
    have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (2, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row2_mid2 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (c - g + 3) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 2 (t + f) : ℚ) / ((hookLength μ 2 (t + f) : ℚ) - 1) =
      ((c : ℚ) - f + 2 - t) / ((c : ℚ) - f + 2 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (2, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row2_mid3 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (c - f + 2) (e - f) (by omega)]
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 2 (t + e) : ℚ) / ((hookLength μ 2 (t + e) : ℚ) - 1) =
      ((c : ℚ) - e + 1 - t) / ((c : ℚ) - e + 1 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (2, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row2_mid4 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (c - e + 1) (d - e) (by omega)]
  rw [show Finset.Ico d (c - 1) = (Finset.range (c - 1 - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv6 : ∀ t ∈ Finset.range (c - 1 - d),
      (hookLength μ 2 (t + d) : ℚ) / ((hookLength μ 2 (t + d) : ℚ) - 1) =
      ((c : ℚ) - d - t) / ((c : ℚ) - d - t - 1) := by
    intro t ht
    have htm : t < c - 1 - d := Finset.mem_range.mp ht
    have hmem : (2, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row2_ge h8 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv6, prod_div_telescope (c - d) (c - 1 - d) (by omega)]
  push_cast [Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe, Nat.cast_sub hed,
             Nat.cast_sub hdc.le, Nat.cast_sub (show 1 ≤ c - d by omega)]
  have hne1 : (c : ℚ) - k + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - k + 5 by omega)
  have hne2 : (c : ℚ) - g + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - g + 4 by omega)
  have hne3 : (c : ℚ) - f + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - f + 3 by omega)
  have hne4 : (c : ℚ) - e + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - e + 2 by omega)
  have hne5 : (c : ℚ) - d + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4, hne5]; ring

/-- Arm product for corner (1, b-1) in an 8-row shape:
    ∏ = (b+6)(b-k+5)(b-g+4)(b-f+3)(b-e+2)(b-d+1)(b-c)/
        ((b-k+6)(b-g+5)(b-f+4)(b-e+3)(b-d+2)(b-c+1)). -/
private lemma eightRow_arm_row1 {μ : YoungDiagram} (h8 : μ.rowLen 8 = 0)
    (hcb : μ.rowLen 2 < μ.rowLen 1) :
    ∏ s ∈ Finset.range (μ.rowLen 1 - 1),
      ((hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1)) =
    ((μ.rowLen 1 : ℚ) + 6) * ((μ.rowLen 1 : ℚ) - μ.rowLen 7 + 5) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 6 + 4) * ((μ.rowLen 1 : ℚ) - μ.rowLen 5 + 3) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 4 + 2) * ((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 1) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 2) /
    (((μ.rowLen 1 : ℚ) - μ.rowLen 7 + 6) * ((μ.rowLen 1 : ℚ) - μ.rowLen 6 + 5) *
     ((μ.rowLen 1 : ℚ) - μ.rowLen 5 + 4) * ((μ.rowLen 1 : ℚ) - μ.rowLen 4 + 3) *
     ((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 2) * ((μ.rowLen 1 : ℚ) - μ.rowLen 2 + 1)) := by
  set b := μ.rowLen 1; set c := μ.rowLen 2; set d := μ.rowLen 3
  set e := μ.rowLen 4; set f := μ.rowLen 5; set g := μ.rowLen 6; set k := μ.rowLen 7
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  rw [show Finset.range (b - 1) = Finset.range k ∪ Finset.Ico k g ∪
      Finset.Ico g f ∪ Finset.Ico f e ∪ Finset.Ico e d ∪ Finset.Ico d c ∪
      Finset.Ico c (b - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range k,
      (hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1) =
      ((b : ℚ) + 6 - s) / ((b : ℚ) + 6 - s - 1) := by
    intro s hs
    have hsk : s < k := Finset.mem_range.mp hs
    have hmem : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row1_lt h8 hmem hsk]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (b + 6) k (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 1 (t + k) : ℚ) / ((hookLength μ 1 (t + k) : ℚ) - 1) =
      ((b : ℚ) - k + 5 - t) / ((b : ℚ) - k + 5 - t - 1) := by
    intro t ht
    have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (1, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row1_mid1 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (b - k + 5) (g - k) (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 1 (t + g) : ℚ) / ((hookLength μ 1 (t + g) : ℚ) - 1) =
      ((b : ℚ) - g + 4 - t) / ((b : ℚ) - g + 4 - t - 1) := by
    intro t ht
    have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (1, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row1_mid2 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (b - g + 4) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 1 (t + f) : ℚ) / ((hookLength μ 1 (t + f) : ℚ) - 1) =
      ((b : ℚ) - f + 3 - t) / ((b : ℚ) - f + 3 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (1, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row1_mid3 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (b - f + 3) (e - f) (by omega)]
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 1 (t + e) : ℚ) / ((hookLength μ 1 (t + e) : ℚ) - 1) =
      ((b : ℚ) - e + 2 - t) / ((b : ℚ) - e + 2 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (1, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row1_mid4 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (b - e + 2) (d - e) (by omega)]
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv6 : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 1 (t + d) : ℚ) / ((hookLength μ 1 (t + d) : ℚ) - 1) =
      ((b : ℚ) - d + 1 - t) / ((b : ℚ) - d + 1 - t - 1) := by
    intro t ht
    have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (1, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row1_mid5 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv6, prod_div_telescope (b - d + 1) (c - d) (by omega)]
  rw [show Finset.Ico c (b - 1) = (Finset.range (b - 1 - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv7 : ∀ t ∈ Finset.range (b - 1 - c),
      (hookLength μ 1 (t + c) : ℚ) / ((hookLength μ 1 (t + c) : ℚ) - 1) =
      ((b : ℚ) - c - t) / ((b : ℚ) - c - t - 1) := by
    intro t ht
    have htm : t < b - 1 - c := Finset.mem_range.mp ht
    have hmem : (1, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row1_ge h8 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv7, prod_div_telescope (b - c) (b - 1 - c) (by omega)]
  push_cast [Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe, Nat.cast_sub hed,
             Nat.cast_sub hdc, Nat.cast_sub hcb.le, Nat.cast_sub (show 1 ≤ b - c by omega)]
  have hne1 : (b : ℚ) - k + 6 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - k + 6 by omega)
  have hne2 : (b : ℚ) - g + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - g + 5 by omega)
  have hne3 : (b : ℚ) - f + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - f + 4 by omega)
  have hne4 : (b : ℚ) - e + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - e + 3 by omega)
  have hne5 : (b : ℚ) - d + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne6 : (b : ℚ) - c + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4, hne5, hne6]; ring

/-- Arm product for corner (0, a-1) in an 8-row shape:
    ∏ = (a+7)(a-k+6)(a-g+5)(a-f+4)(a-e+3)(a-d+2)(a-c+1)(a-b)/
        ((a-k+7)(a-g+6)(a-f+5)(a-e+4)(a-d+3)(a-c+2)(a-b+1)). -/
private lemma eightRow_arm_row0 {μ : YoungDiagram} (h8 : μ.rowLen 8 = 0)
    (h7 : 0 < μ.rowLen 7) (hab : μ.rowLen 1 < μ.rowLen 0) :
    ∏ s ∈ Finset.range (μ.rowLen 0 - 1),
      ((hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1)) =
    ((μ.rowLen 0 : ℚ) + 7) * ((μ.rowLen 0 : ℚ) - μ.rowLen 7 + 6) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 6 + 5) * ((μ.rowLen 0 : ℚ) - μ.rowLen 5 + 4) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 4 + 3) * ((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 2) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 1) * ((μ.rowLen 0 : ℚ) - μ.rowLen 1) /
    (((μ.rowLen 0 : ℚ) - μ.rowLen 7 + 7) * ((μ.rowLen 0 : ℚ) - μ.rowLen 6 + 6) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 5 + 5) * ((μ.rowLen 0 : ℚ) - μ.rowLen 4 + 4) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 3) * ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 2) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 1 + 1)) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set c := μ.rowLen 2
  set d := μ.rowLen 3; set e := μ.rowLen 4; set f := μ.rowLen 5
  set g := μ.rowLen 6; set k := μ.rowLen 7
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  rw [show Finset.range (a - 1) = Finset.range k ∪ Finset.Ico k g ∪
      Finset.Ico g f ∪ Finset.Ico f e ∪ Finset.Ico e d ∪ Finset.Ico d c ∪
      Finset.Ico c b ∪ Finset.Ico b (a - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range k,
      (hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1) =
      ((a : ℚ) + 7 - s) / ((a : ℚ) + 7 - s - 1) := by
    intro s hs
    have hsk : s < k := Finset.mem_range.mp hs
    have hmem : (0, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row0_lt h8 hmem hsk]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (a + 7) k (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 0 (t + k) : ℚ) / ((hookLength μ 0 (t + k) : ℚ) - 1) =
      ((a : ℚ) - k + 6 - t) / ((a : ℚ) - k + 6 - t - 1) := by
    intro t ht
    have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (0, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row0_mid1 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (a - k + 6) (g - k) (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 0 (t + g) : ℚ) / ((hookLength μ 0 (t + g) : ℚ) - 1) =
      ((a : ℚ) - g + 5 - t) / ((a : ℚ) - g + 5 - t - 1) := by
    intro t ht
    have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (0, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row0_mid2 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (a - g + 5) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 0 (t + f) : ℚ) / ((hookLength μ 0 (t + f) : ℚ) - 1) =
      ((a : ℚ) - f + 4 - t) / ((a : ℚ) - f + 4 - t - 1) := by
    intro t ht
    have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (0, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row0_mid3 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (a - f + 4) (e - f) (by omega)]
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 0 (t + e) : ℚ) / ((hookLength μ 0 (t + e) : ℚ) - 1) =
      ((a : ℚ) - e + 3 - t) / ((a : ℚ) - e + 3 - t - 1) := by
    intro t ht
    have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (0, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row0_mid4 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (a - e + 3) (d - e) (by omega)]
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv6 : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 0 (t + d) : ℚ) / ((hookLength μ 0 (t + d) : ℚ) - 1) =
      ((a : ℚ) - d + 2 - t) / ((a : ℚ) - d + 2 - t - 1) := by
    intro t ht
    have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (0, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row0_mid5 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv6, prod_div_telescope (a - d + 2) (c - d) (by omega)]
  rw [show Finset.Ico c b = (Finset.range (b - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv7 : ∀ t ∈ Finset.range (b - c),
      (hookLength μ 0 (t + c) : ℚ) / ((hookLength μ 0 (t + c) : ℚ) - 1) =
      ((a : ℚ) - c + 1 - t) / ((a : ℚ) - c + 1 - t - 1) := by
    intro t ht
    have htm : t < b - c := Finset.mem_range.mp ht
    have hmem : (0, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row0_mid6 h8 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv7, prod_div_telescope (a - c + 1) (b - c) (by omega)]
  rw [show Finset.Ico b (a - 1) = (Finset.range (a - 1 - b)).image (· + b) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv8 : ∀ t ∈ Finset.range (a - 1 - b),
      (hookLength μ 0 (t + b) : ℚ) / ((hookLength μ 0 (t + b) : ℚ) - 1) =
      ((a : ℚ) - b - t) / ((a : ℚ) - b - t - 1) := by
    intro t ht
    have htm : t < a - 1 - b := Finset.mem_range.mp ht
    have hmem : (0, t + b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [eightRow_hookLen_row0_ge h8 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv8, prod_div_telescope (a - b) (a - 1 - b) (by omega)]
  push_cast [Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe, Nat.cast_sub hed,
             Nat.cast_sub hdc, Nat.cast_sub hcb, Nat.cast_sub hab.le,
             Nat.cast_sub (show 1 ≤ a - b by omega)]
  have hne1 : (a : ℚ) - k + 7 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - k + 7 by omega)
  have hne2 : (a : ℚ) - g + 6 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - g + 6 by omega)
  have hne3 : (a : ℚ) - f + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - f + 5 by omega)
  have hne4 : (a : ℚ) - e + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - e + 4 by omega)
  have hne5 : (a : ℚ) - d + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne6 : (a : ℚ) - c + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne7 : (a : ℚ) - b + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4, hne5, hne6, hne7]; ring


/-- The hook walk identity for exactly-8-row Young diagrams.
    Direct computation via hookProd_ratio_formula and telescoping — no HLF used.
    NON-CIRCULAR: does not call hook_length_formula_Q or hook_walk_identity. -/
lemma hook_walk_identity_eightRow (μ : YoungDiagram)
    (h8 : μ.rowLen 8 = 0) (h7 : 0 < μ.rowLen 7) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / (hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) : ℚ))
    = (μ.card : ℚ) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set c := μ.rowLen 2
  set d := μ.rowLen 3; set e := μ.rowLen 4; set f := μ.rowLen 5
  set g := μ.rowLen 6; set k := μ.rowLen 7
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  have hba : b ≤ a := μ.rowLen_anti 0 1 (by omega)
  have hbot : isCorner μ (7, k - 1) := eightRow_corner_bot h8 h7
  have hcard : (μ.card : ℚ) = (a : ℚ) + b + c + d + e + f + g + k := by
    exact_mod_cast eightRow_card h8
  rw [hcard]
  let ratio : ℕ × ℕ → ℚ := fun x =>
    if hx : isCorner μ x then (hookProd μ : ℚ) / hookProd (removeCorner μ x hx) else 0
  have hconvert : ∑ cc ∈ (corners μ).attach,
        ((hookProd μ : ℚ) / hookProd (removeCorner μ cc.val (mem_corners.mp cc.prop))) =
      ∑ x ∈ corners μ, ratio x := by
    rw [← Finset.sum_attach (f := ratio)]
    apply Finset.sum_congr rfl
    intro cx _; exact dif_pos (mem_corners.mp cx.2)
  have hsub : corners μ ⊆
      ({(7, k - 1), (6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1),
        (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases eightRow_corner_cases h8 h7 (mem_corners.mp hx) with
      heq | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
    · left; exact heq
    · right; left; exact heq
    · right; right; left; exact heq
    · right; right; right; left; exact heq
    · right; right; right; right; left; exact heq
    · right; right; right; right; right; left; exact heq
    · right; right; right; right; right; right; left; exact heq
    · right; right; right; right; right; right; right; exact heq
  have hext : ∑ x ∈ corners μ, ratio x =
      ∑ x ∈ ({(7, k - 1), (6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1),
               (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)), ratio x := by
    apply Finset.sum_subset hsub
    intro x _ hxnc; exact dif_neg (mt mem_corners.mpr hxnc)
  -- Compute ratio for corner (7, k-1)
  have hR7 : ratio (7, k - 1) =
      (k : ℚ) * ((g : ℚ) - k + 2) / ((g : ℚ) - k + 1) *
      ((f : ℚ) - k + 3) / ((f : ℚ) - k + 2) *
      ((e : ℚ) - k + 4) / ((e : ℚ) - k + 3) *
      ((d : ℚ) - k + 5) / ((d : ℚ) - k + 4) *
      ((c : ℚ) - k + 6) / ((c : ℚ) - k + 5) *
      ((b : ℚ) - k + 7) / ((b : ℚ) - k + 6) *
      ((a : ℚ) - k + 8) / ((a : ℚ) - k + 7) := by
    simp only [ratio, dif_pos hbot]
    rw [hookProd_ratio_formula hbot]
    simp only [Prod.fst, Prod.snd]
    rw [eightRow_arm_row7 μ h8 hbot]
    have hk1 : k - 1 < k := Nat.sub_lt h7 Nat.one_pos
    have hmem0 : (0, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem1 : (1, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem2 : (2, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem3 : (3, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem4 : (4, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem5 : (5, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem6 : (6, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [show Finset.range 7 = {0, 1, 2, 3, 4, 5, 6} from by ext m; simp; omega]
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
        Finset.prod_insert (by simp), Finset.prod_insert (by simp),
        Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
    rw [eightRow_hookLen_row0_lt h8 hmem0 hk1,
        eightRow_hookLen_row1_lt h8 hmem1 hk1,
        eightRow_hookLen_row2_lt h8 hmem2 hk1,
        eightRow_hookLen_row3_lt h8 hmem3 hk1,
        eightRow_hookLen_row4_lt h8 hmem4 hk1,
        eightRow_hookLen_row5_lt h8 hmem5 hk1,
        eightRow_hookLen_row6_lt h8 hmem6 hk1]
    push_cast [Nat.cast_sub (show 1 ≤ k from h7),
               Nat.cast_sub (show k - 1 ≤ a by omega),
               Nat.cast_sub (show k - 1 ≤ b by omega),
               Nat.cast_sub (show k - 1 ≤ c by omega),
               Nat.cast_sub (show k - 1 ≤ d by omega),
               Nat.cast_sub (show k - 1 ≤ e by omega),
               Nat.cast_sub (show k - 1 ≤ f by omega),
               Nat.cast_sub (show k - 1 ≤ g by omega)]
    ring
  -- Compute ratio for corner (6, g-1) [when g > k]
  have hR6 : ratio (6, g - 1) =
      ((g : ℚ) + 1) * ((g : ℚ) - k) / ((g : ℚ) - k + 1) *
      ((f : ℚ) - g + 2) / ((f : ℚ) - g + 1) *
      ((e : ℚ) - g + 3) / ((e : ℚ) - g + 2) *
      ((d : ℚ) - g + 4) / ((d : ℚ) - g + 3) *
      ((c : ℚ) - g + 5) / ((c : ℚ) - g + 4) *
      ((b : ℚ) - g + 6) / ((b : ℚ) - g + 5) *
      ((a : ℚ) - g + 7) / ((a : ℚ) - g + 6) := by
    by_cases hkg' : k < g
    · have hmid : isCorner μ (6, g - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [eightRow_arm_row6 h8 hkg']
      have hg1 : g - 1 < g := Nat.sub_lt (by omega) Nat.one_pos
      have hkg1 : k ≤ g - 1 := by omega
      have hmem0 : (0, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem3 : (3, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem4 : (4, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem5 : (5, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 6 = {0, 1, 2, 3, 4, 5} from by ext m; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [eightRow_hookLen_row0_mid1 h8 hmem0 hkg1 (by omega),
          eightRow_hookLen_row1_mid1 h8 hmem1 hkg1 (by omega),
          eightRow_hookLen_row2_mid1 h8 hmem2 hkg1 (by omega),
          eightRow_hookLen_row3_mid1 h8 hmem3 hkg1 (by omega),
          eightRow_hookLen_row4_mid1 h8 hmem4 hkg1 (by omega),
          eightRow_hookLen_row5_mid1 h8 hmem5 hkg1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ g by omega),
                 Nat.cast_sub (show g - 1 ≤ a by omega),
                 Nat.cast_sub (show g - 1 ≤ b by omega),
                 Nat.cast_sub (show g - 1 ≤ c by omega),
                 Nat.cast_sub (show g - 1 ≤ d by omega),
                 Nat.cast_sub (show g - 1 ≤ e by omega),
                 Nat.cast_sub (show g - 1 ≤ f by omega),
                 Nat.cast_sub hkg'.le]
      ring
    · have hkg_eq : g = k := Nat.le_antisymm (not_lt.mp hkg') hkg
      have hnotcorner : ¬ isCorner μ (6, g - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (g : ℚ) - k = 0 := by rw [hkg_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (5, f-1) [when f > g]
  have hR5 : ratio (5, f - 1) =
      ((f : ℚ) + 2) * ((f : ℚ) - k + 1) * ((f : ℚ) - g) /
      (((f : ℚ) - k + 2) * ((f : ℚ) - g + 1)) *
      ((e : ℚ) - f + 2) / ((e : ℚ) - f + 1) *
      ((d : ℚ) - f + 3) / ((d : ℚ) - f + 2) *
      ((c : ℚ) - f + 4) / ((c : ℚ) - f + 3) *
      ((b : ℚ) - f + 5) / ((b : ℚ) - f + 4) *
      ((a : ℚ) - f + 6) / ((a : ℚ) - f + 5) := by
    by_cases hgf' : g < f
    · have hmid : isCorner μ (5, f - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [eightRow_arm_row5 h8 hgf']
      have hf1 : f - 1 < f := Nat.sub_lt (by omega) Nat.one_pos
      have hgf1 : g ≤ f - 1 := by omega
      have hmem0 : (0, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem3 : (3, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem4 : (4, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 5 = {0, 1, 2, 3, 4} from by ext m; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [eightRow_hookLen_row0_mid2 h8 hmem0 hgf1 (by omega),
          eightRow_hookLen_row1_mid2 h8 hmem1 hgf1 (by omega),
          eightRow_hookLen_row2_mid2 h8 hmem2 hgf1 (by omega),
          eightRow_hookLen_row3_mid2 h8 hmem3 hgf1 (by omega),
          eightRow_hookLen_row4_mid2 h8 hmem4 hgf1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ f by omega),
                 Nat.cast_sub (show f - 1 ≤ a by omega),
                 Nat.cast_sub (show f - 1 ≤ b by omega),
                 Nat.cast_sub (show f - 1 ≤ c by omega),
                 Nat.cast_sub (show f - 1 ≤ d by omega),
                 Nat.cast_sub (show f - 1 ≤ e by omega),
                 Nat.cast_sub hgf'.le, Nat.cast_sub hkg]
      ring
    · have hgf_eq : f = g := Nat.le_antisymm (not_lt.mp hgf') hgf
      have hnotcorner : ¬ isCorner μ (5, f - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (f : ℚ) - g = 0 := by rw [hgf_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (4, e-1) [when e > f]
  have hR4 : ratio (4, e - 1) =
      ((e : ℚ) + 3) * ((e : ℚ) - k + 2) * ((e : ℚ) - g + 1) * ((e : ℚ) - f) /
      (((e : ℚ) - k + 3) * ((e : ℚ) - g + 2) * ((e : ℚ) - f + 1)) *
      ((d : ℚ) - e + 2) / ((d : ℚ) - e + 1) *
      ((c : ℚ) - e + 3) / ((c : ℚ) - e + 2) *
      ((b : ℚ) - e + 4) / ((b : ℚ) - e + 3) *
      ((a : ℚ) - e + 5) / ((a : ℚ) - e + 4) := by
    by_cases hfe' : f < e
    · have hmid : isCorner μ (4, e - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [eightRow_arm_row4 h8 hfe']
      have he1 : e - 1 < e := Nat.sub_lt (by omega) Nat.one_pos
      have hfe1 : f ≤ e - 1 := by omega
      have hmem0 : (0, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem3 : (3, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 4 = {0, 1, 2, 3} from by ext m; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [eightRow_hookLen_row0_mid3 h8 hmem0 hfe1 (by omega),
          eightRow_hookLen_row1_mid3 h8 hmem1 hfe1 (by omega),
          eightRow_hookLen_row2_mid3 h8 hmem2 hfe1 (by omega),
          eightRow_hookLen_row3_mid3 h8 hmem3 hfe1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ e by omega),
                 Nat.cast_sub (show e - 1 ≤ a by omega),
                 Nat.cast_sub (show e - 1 ≤ b by omega),
                 Nat.cast_sub (show e - 1 ≤ c by omega),
                 Nat.cast_sub (show e - 1 ≤ d by omega),
                 Nat.cast_sub hfe'.le, Nat.cast_sub hgf, Nat.cast_sub hkg]
      ring
    · have hfe_eq : e = f := Nat.le_antisymm (not_lt.mp hfe') hfe
      have hnotcorner : ¬ isCorner μ (4, e - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (e : ℚ) - f = 0 := by rw [hfe_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (3, d-1) [when d > e]
  have hR3 : ratio (3, d - 1) =
      ((d : ℚ) + 4) * ((d : ℚ) - k + 3) * ((d : ℚ) - g + 2) *
      ((d : ℚ) - f + 1) * ((d : ℚ) - e) /
      (((d : ℚ) - k + 4) * ((d : ℚ) - g + 3) * ((d : ℚ) - f + 2) *
       ((d : ℚ) - e + 1)) *
      ((c : ℚ) - d + 2) / ((c : ℚ) - d + 1) *
      ((b : ℚ) - d + 3) / ((b : ℚ) - d + 2) *
      ((a : ℚ) - d + 4) / ((a : ℚ) - d + 3) := by
    by_cases hed' : e < d
    · have hmid : isCorner μ (3, d - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [eightRow_arm_row3 h8 hed']
      have hd1 : d - 1 < d := Nat.sub_lt (by omega) Nat.one_pos
      have hed1 : e ≤ d - 1 := by omega
      have hmem0 : (0, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 3 = {0, 1, 2} from by ext m; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [eightRow_hookLen_row0_mid4 h8 hmem0 hed1 (by omega),
          eightRow_hookLen_row1_mid4 h8 hmem1 hed1 (by omega),
          eightRow_hookLen_row2_mid4 h8 hmem2 hed1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ d by omega),
                 Nat.cast_sub (show d - 1 ≤ a by omega),
                 Nat.cast_sub (show d - 1 ≤ b by omega),
                 Nat.cast_sub (show d - 1 ≤ c by omega),
                 Nat.cast_sub hed'.le, Nat.cast_sub hfe, Nat.cast_sub hgf, Nat.cast_sub hkg]
      ring
    · have hed_eq : d = e := Nat.le_antisymm (not_lt.mp hed') hed
      have hnotcorner : ¬ isCorner μ (3, d - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (d : ℚ) - e = 0 := by rw [hed_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (2, c-1) [when c > d]
  have hR2 : ratio (2, c - 1) =
      ((c : ℚ) + 5) * ((c : ℚ) - k + 4) * ((c : ℚ) - g + 3) *
      ((c : ℚ) - f + 2) * ((c : ℚ) - e + 1) * ((c : ℚ) - d) /
      (((c : ℚ) - k + 5) * ((c : ℚ) - g + 4) * ((c : ℚ) - f + 3) *
       ((c : ℚ) - e + 2) * ((c : ℚ) - d + 1)) *
      ((b : ℚ) - c + 2) / ((b : ℚ) - c + 1) *
      ((a : ℚ) - c + 3) / ((a : ℚ) - c + 2) := by
    by_cases hdc' : d < c
    · have hmid : isCorner μ (2, c - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [eightRow_arm_row2 h8 hdc']
      have hc1 : c - 1 < c := Nat.sub_lt (by omega) Nat.one_pos
      have hdc1 : d ≤ c - 1 := by omega
      have hmem0 : (0, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 2 = {0, 1} from by ext m; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [eightRow_hookLen_row0_mid5 h8 hmem0 hdc1 (by omega),
          eightRow_hookLen_row1_mid5 h8 hmem1 hdc1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ c by omega),
                 Nat.cast_sub (show c - 1 ≤ a by omega),
                 Nat.cast_sub (show c - 1 ≤ b by omega),
                 Nat.cast_sub hdc'.le, Nat.cast_sub hed, Nat.cast_sub hfe,
                 Nat.cast_sub hgf, Nat.cast_sub hkg]
      ring
    · have hdc_eq : c = d := Nat.le_antisymm (not_lt.mp hdc') hdc
      have hnotcorner : ¬ isCorner μ (2, c - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (c : ℚ) - d = 0 := by rw [hdc_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (1, b-1) [when b > c]
  have hR1 : ratio (1, b - 1) =
      ((b : ℚ) + 6) * ((b : ℚ) - k + 5) * ((b : ℚ) - g + 4) *
      ((b : ℚ) - f + 3) * ((b : ℚ) - e + 2) * ((b : ℚ) - d + 1) * ((b : ℚ) - c) /
      (((b : ℚ) - k + 6) * ((b : ℚ) - g + 5) * ((b : ℚ) - f + 4) *
       ((b : ℚ) - e + 3) * ((b : ℚ) - d + 2) * ((b : ℚ) - c + 1)) *
      ((a : ℚ) - b + 2) / ((a : ℚ) - b + 1) := by
    by_cases hcb' : c < b
    · have hmid : isCorner μ (1, b - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [eightRow_arm_row1 h8 hcb']
      have hmem0 : (0, b - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      rw [eightRow_hookLen_row0_mid6 h8 hmem0 (by omega) (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ b by omega),
                 Nat.cast_sub (show b - 1 ≤ a by omega),
                 Nat.cast_sub hcb'.le, Nat.cast_sub hdc, Nat.cast_sub hed,
                 Nat.cast_sub hfe, Nat.cast_sub hgf, Nat.cast_sub hkg]
      ring
    · have hcb_eq : b = c := Nat.le_antisymm (not_lt.mp hcb') hcb
      have hnotcorner : ¬ isCorner μ (1, b - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (b : ℚ) - c = 0 := by rw [hcb_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (0, a-1) [when a > b]
  have hR0 : ratio (0, a - 1) =
      ((a : ℚ) + 7) * ((a : ℚ) - k + 6) * ((a : ℚ) - g + 5) *
      ((a : ℚ) - f + 4) * ((a : ℚ) - e + 3) * ((a : ℚ) - d + 2) *
      ((a : ℚ) - c + 1) * ((a : ℚ) - b) /
      (((a : ℚ) - k + 7) * ((a : ℚ) - g + 6) * ((a : ℚ) - f + 5) *
       ((a : ℚ) - e + 4) * ((a : ℚ) - d + 3) * ((a : ℚ) - c + 2) *
       ((a : ℚ) - b + 1)) := by
    by_cases hab' : b < a
    · have htop : isCorner μ (0, a - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos htop]
      rw [hookProd_ratio_formula htop]
      simp only [Prod.fst, Prod.snd, Finset.prod_range_zero, mul_one]
      rw [eightRow_arm_row0 h8 h7 hab']
      push_cast [Nat.cast_sub hab'.le, Nat.cast_sub hcb, Nat.cast_sub hdc,
                 Nat.cast_sub hed, Nat.cast_sub hfe, Nat.cast_sub hgf, Nat.cast_sub hkg]
      ring
    · have hab_eq : a = b := Nat.le_antisymm (not_lt.mp hab') hba
      have hnotcorner : ¬ isCorner μ (0, a - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (a : ℚ) - b = 0 := by rw [hab_eq]; ring
      rw [this]; ring
  rw [hconvert, hext]
  have hne76 : (7, k - 1) ∉ ({(6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1),
      (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne65 : (6, g - 1) ∉ ({(5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1),
      (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne54 : (5, f - 1) ∉ ({(4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1),
      (0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne43 : (4, e - 1) ∉ ({(3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
      Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne32 : (3, d - 1) ∉ ({(2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hne21 : (2, c - 1) ∉ ({(1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hne10 : (1, b - 1) ∉ ({(0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  rw [show ({(7, k - 1), (6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1),
              (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) =
      insert (7, k - 1) (insert (6, g - 1) (insert (5, f - 1) (insert (4, e - 1)
        (insert (3, d - 1) (insert (2, c - 1) (insert (1, b - 1) {(0, a - 1)})))))) from rfl,
      Finset.sum_insert hne76, Finset.sum_insert hne65, Finset.sum_insert hne54,
      Finset.sum_insert hne43, Finset.sum_insert hne32, Finset.sum_insert hne21,
      Finset.sum_insert hne10, Finset.sum_singleton,
      hR7, hR6, hR5, hR4, hR3, hR2, hR1, hR0]
  have hne_gk1 : (g : ℚ) - k + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < g - k + 1 by omega)
  have hne_fk2 : (f : ℚ) - k + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < f - k + 2 by omega)
  have hne_ek3 : (e : ℚ) - k + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < e - k + 3 by omega)
  have hne_dk4 : (d : ℚ) - k + 4 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < d - k + 4 by omega)
  have hne_ck5 : (c : ℚ) - k + 5 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - k + 5 by omega)
  have hne_bk6 : (b : ℚ) - k + 6 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - k + 6 by omega)
  have hne_ak7 : (a : ℚ) - k + 7 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - k + 7 by omega)
  have hne_fg1 : (f : ℚ) - g + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < f - g + 1 by omega)
  have hne_eg2 : (e : ℚ) - g + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < e - g + 2 by omega)
  have hne_dg3 : (d : ℚ) - g + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < d - g + 3 by omega)
  have hne_cg4 : (c : ℚ) - g + 4 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - g + 4 by omega)
  have hne_bg5 : (b : ℚ) - g + 5 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - g + 5 by omega)
  have hne_ag6 : (a : ℚ) - g + 6 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - g + 6 by omega)
  have hne_ef1 : (e : ℚ) - f + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < e - f + 1 by omega)
  have hne_df2 : (d : ℚ) - f + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < d - f + 2 by omega)
  have hne_cf3 : (c : ℚ) - f + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - f + 3 by omega)
  have hne_bf4 : (b : ℚ) - f + 4 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - f + 4 by omega)
  have hne_af5 : (a : ℚ) - f + 5 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - f + 5 by omega)
  have hne_de1 : (d : ℚ) - e + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < d - e + 1 by omega)
  have hne_ce2 : (c : ℚ) - e + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - e + 2 by omega)
  have hne_be3 : (b : ℚ) - e + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - e + 3 by omega)
  have hne_ae4 : (a : ℚ) - e + 4 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - e + 4 by omega)
  have hne_cd1 : (c : ℚ) - d + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  have hne_bd2 : (b : ℚ) - d + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne_ad3 : (a : ℚ) - d + 3 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne_bc1 : (b : ℚ) - c + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  have hne_ac2 : (a : ℚ) - c + 2 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne_ab1 : (a : ℚ) - b + 1 ≠ 0 := by
    exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  push_cast [Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe, Nat.cast_sub hed,
             Nat.cast_sub hdc, Nat.cast_sub hcb, Nat.cast_sub hba,
             Nat.cast_sub (show k ≤ f by omega), Nat.cast_sub (show k ≤ e by omega),
             Nat.cast_sub (show k ≤ d by omega), Nat.cast_sub (show k ≤ c by omega),
             Nat.cast_sub (show k ≤ b by omega), Nat.cast_sub (show k ≤ a by omega),
             Nat.cast_sub (show g ≤ e by omega), Nat.cast_sub (show g ≤ d by omega),
             Nat.cast_sub (show g ≤ c by omega), Nat.cast_sub (show g ≤ b by omega),
             Nat.cast_sub (show g ≤ a by omega), Nat.cast_sub (show f ≤ d by omega),
             Nat.cast_sub (show f ≤ c by omega), Nat.cast_sub (show f ≤ b by omega),
             Nat.cast_sub (show f ≤ a by omega), Nat.cast_sub (show e ≤ c by omega),
             Nat.cast_sub (show e ≤ b by omega), Nat.cast_sub (show e ≤ a by omega),
             Nat.cast_sub (show d ≤ b by omega), Nat.cast_sub (show d ≤ a by omega),
             Nat.cast_sub (show c ≤ a by omega)]
  field_simp [hne_gk1, hne_fk2, hne_ek3, hne_dk4, hne_ck5, hne_bk6, hne_ak7,
              hne_fg1, hne_eg2, hne_dg3, hne_cg4, hne_bg5, hne_ag6,
              hne_ef1, hne_df2, hne_cf3, hne_bf4, hne_af5,
              hne_de1, hne_ce2, hne_be3, hne_ae4,
              hne_cd1, hne_bd2, hne_ad3, hne_bc1, hne_ac2, hne_ab1]
  ring


-- ============================================================================
-- PART XXIII: hook_walk_identity for 9-row shapes
-- ============================================================================

-- ============================================================================
-- PART XXIII: hook_walk_identity for 9-row shapes
-- Variables: j=rowLen 8, k=rowLen 7, g=rowLen 6, f=rowLen 5, e=rowLen 4,
--            d=rowLen 3, c=rowLen 2, b=rowLen 1, a=rowLen 0
-- ============================================================================

/-- colLen(s) = 9 for s < rowLen 8 in a 9-row shape (rowLen 9 = 0). -/
private lemma nineRow_colLen_lt {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hs : s < μ.rowLen 8) : μ.colLen s = 9 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h9s : (9, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h9s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs)

/-- colLen(s) = 8 for rowLen 8 ≤ s < rowLen 7 in a 9-row shape. -/
private lemma nineRow_colLen_mid1 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hs_ge : μ.rowLen 8 ≤ s) (hs_lt : s < μ.rowLen 7) :
    μ.colLen s = 8 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h8s : (8, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h8s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 7 for rowLen 7 ≤ s < rowLen 6 in a 9-row shape. -/
private lemma nineRow_colLen_mid2 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    μ.colLen s = 7 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h7s : (7, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h7s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 6 for rowLen 6 ≤ s < rowLen 5 in a 9-row shape. -/
private lemma nineRow_colLen_mid3 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    μ.colLen s = 6 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h6s : (6, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h6s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 5 for rowLen 5 ≤ s < rowLen 4 in a 9-row shape. -/
private lemma nineRow_colLen_mid4 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    μ.colLen s = 5 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h5s : (5, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h5s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 4 for rowLen 4 ≤ s < rowLen 3 in a 9-row shape. -/
private lemma nineRow_colLen_mid5 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    μ.colLen s = 4 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h4s : (4, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h4s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 3 for rowLen 3 ≤ s < rowLen 2 in a 9-row shape. -/
private lemma nineRow_colLen_mid6 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    μ.colLen s = 3 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h3s : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h3s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

/-- colLen(s) = 2 for rowLen 2 ≤ s < rowLen 1 in a 9-row shape. -/
private lemma nineRow_colLen_mid7 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    μ.colLen s = 2 := by
  apply Nat.le_antisymm
  · by_contra hlt; push_neg at hlt
    have h2s : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mp h2s; omega
  · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)

-- hookLen lemmas: row 8 (1 zone)
private lemma nineRow_hookLen_row8 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (8, s) ∈ μ) :
    hookLength μ 8 s = μ.rowLen 8 - s := by
  have hs : s < μ.rowLen 8 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_lt h9 hs] at key; omega

-- hookLen lemmas: row 7 (2 zones)
private lemma nineRow_hookLen_row7_lt {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (7, s) ∈ μ) (hs : s < μ.rowLen 8) :
    hookLength μ 7 s = μ.rowLen 7 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_lt h9 hs] at key; omega

private lemma nineRow_hookLen_row7_ge {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (7, s) ∈ μ) (hs : μ.rowLen 8 ≤ s) :
    hookLength μ 7 s = μ.rowLen 7 - s := by
  have hs_lt : s < μ.rowLen 7 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid1 h9 hs hs_lt] at key; omega

-- hookLen lemmas: row 6 (3 zones)
private lemma nineRow_hookLen_row6_lt {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (6, s) ∈ μ) (hs : s < μ.rowLen 8) :
    hookLength μ 6 s = μ.rowLen 6 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_lt h9 hs] at key; omega

private lemma nineRow_hookLen_row6_mid1 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (6, s) ∈ μ) (hs_ge : μ.rowLen 8 ≤ s) (hs_lt : s < μ.rowLen 7) :
    hookLength μ 6 s = μ.rowLen 6 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid1 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row6_ge {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (6, s) ∈ μ) (hs : μ.rowLen 7 ≤ s) :
    hookLength μ 6 s = μ.rowLen 6 - s := by
  have hs_lt : s < μ.rowLen 6 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid2 h9 hs hs_lt] at key; omega

-- hookLen lemmas: row 5 (4 zones)
private lemma nineRow_hookLen_row5_lt {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (5, s) ∈ μ) (hs : s < μ.rowLen 8) :
    hookLength μ 5 s = μ.rowLen 5 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_lt h9 hs] at key; omega

private lemma nineRow_hookLen_row5_mid1 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (5, s) ∈ μ) (hs_ge : μ.rowLen 8 ≤ s) (hs_lt : s < μ.rowLen 7) :
    hookLength μ 5 s = μ.rowLen 5 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid1 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row5_mid2 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (5, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 5 s = μ.rowLen 5 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid2 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row5_ge {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (5, s) ∈ μ) (hs : μ.rowLen 6 ≤ s) :
    hookLength μ 5 s = μ.rowLen 5 - s := by
  have hs_lt : s < μ.rowLen 5 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid3 h9 hs hs_lt] at key; omega

-- hookLen lemmas: row 4 (5 zones)
private lemma nineRow_hookLen_row4_lt {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (4, s) ∈ μ) (hs : s < μ.rowLen 8) :
    hookLength μ 4 s = μ.rowLen 4 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_lt h9 hs] at key; omega

private lemma nineRow_hookLen_row4_mid1 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (4, s) ∈ μ) (hs_ge : μ.rowLen 8 ≤ s) (hs_lt : s < μ.rowLen 7) :
    hookLength μ 4 s = μ.rowLen 4 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid1 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row4_mid2 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (4, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 4 s = μ.rowLen 4 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid2 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row4_mid3 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (4, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 4 s = μ.rowLen 4 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid3 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row4_ge {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (4, s) ∈ μ) (hs : μ.rowLen 5 ≤ s) :
    hookLength μ 4 s = μ.rowLen 4 - s := by
  have hs_lt : s < μ.rowLen 4 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid4 h9 hs hs_lt] at key; omega

-- hookLen lemmas: row 3 (6 zones)
private lemma nineRow_hookLen_row3_lt {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (3, s) ∈ μ) (hs : s < μ.rowLen 8) :
    hookLength μ 3 s = μ.rowLen 3 - s + 5 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_lt h9 hs] at key; omega

private lemma nineRow_hookLen_row3_mid1 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (3, s) ∈ μ) (hs_ge : μ.rowLen 8 ≤ s) (hs_lt : s < μ.rowLen 7) :
    hookLength μ 3 s = μ.rowLen 3 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid1 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row3_mid2 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (3, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 3 s = μ.rowLen 3 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid2 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row3_mid3 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (3, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 3 s = μ.rowLen 3 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid3 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row3_mid4 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (3, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 3 s = μ.rowLen 3 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid4 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row3_ge {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (3, s) ∈ μ) (hs : μ.rowLen 4 ≤ s) :
    hookLength μ 3 s = μ.rowLen 3 - s := by
  have hs_lt : s < μ.rowLen 3 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid5 h9 hs hs_lt] at key; omega

-- hookLen lemmas: row 2 (7 zones)
private lemma nineRow_hookLen_row2_lt {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (2, s) ∈ μ) (hs : s < μ.rowLen 8) :
    hookLength μ 2 s = μ.rowLen 2 - s + 6 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_lt h9 hs] at key; omega

private lemma nineRow_hookLen_row2_mid1 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 8 ≤ s) (hs_lt : s < μ.rowLen 7) :
    hookLength μ 2 s = μ.rowLen 2 - s + 5 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid1 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row2_mid2 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 2 s = μ.rowLen 2 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid2 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row2_mid3 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 2 s = μ.rowLen 2 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid3 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row2_mid4 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 2 s = μ.rowLen 2 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid4 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row2_mid5 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (2, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 2 s = μ.rowLen 2 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid5 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row2_ge {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (2, s) ∈ μ) (hs : μ.rowLen 3 ≤ s) :
    hookLength μ 2 s = μ.rowLen 2 - s := by
  have hs_lt : s < μ.rowLen 2 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid6 h9 hs hs_lt] at key; omega

-- hookLen lemmas: row 1 (8 zones)
private lemma nineRow_hookLen_row1_lt {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (1, s) ∈ μ) (hs : s < μ.rowLen 8) :
    hookLength μ 1 s = μ.rowLen 1 - s + 7 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_lt h9 hs] at key; omega

private lemma nineRow_hookLen_row1_mid1 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 8 ≤ s) (hs_lt : s < μ.rowLen 7) :
    hookLength μ 1 s = μ.rowLen 1 - s + 6 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid1 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row1_mid2 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 1 s = μ.rowLen 1 - s + 5 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid2 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row1_mid3 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 1 s = μ.rowLen 1 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid3 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row1_mid4 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 1 s = μ.rowLen 1 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid4 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row1_mid5 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 1 s = μ.rowLen 1 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid5 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row1_mid6 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (1, s) ∈ μ) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    hookLength μ 1 s = μ.rowLen 1 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid6 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row1_ge {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (1, s) ∈ μ) (hs : μ.rowLen 2 ≤ s) :
    hookLength μ 1 s = μ.rowLen 1 - s := by
  have hs_lt : s < μ.rowLen 1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid7 h9 hs hs_lt] at key; omega

-- hookLen lemmas: row 0 (9 zones)
private lemma nineRow_hookLen_row0_lt {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (0, s) ∈ μ) (hs : s < μ.rowLen 8) :
    hookLength μ 0 s = μ.rowLen 0 - s + 8 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_lt h9 hs] at key; omega

private lemma nineRow_hookLen_row0_mid1 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 8 ≤ s) (hs_lt : s < μ.rowLen 7) :
    hookLength μ 0 s = μ.rowLen 0 - s + 7 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid1 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row0_mid2 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 7 ≤ s) (hs_lt : s < μ.rowLen 6) :
    hookLength μ 0 s = μ.rowLen 0 - s + 6 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid2 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row0_mid3 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 6 ≤ s) (hs_lt : s < μ.rowLen 5) :
    hookLength μ 0 s = μ.rowLen 0 - s + 5 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid3 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row0_mid4 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 5 ≤ s) (hs_lt : s < μ.rowLen 4) :
    hookLength μ 0 s = μ.rowLen 0 - s + 4 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid4 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row0_mid5 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 4 ≤ s) (hs_lt : s < μ.rowLen 3) :
    hookLength μ 0 s = μ.rowLen 0 - s + 3 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid5 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row0_mid6 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 3 ≤ s) (hs_lt : s < μ.rowLen 2) :
    hookLength μ 0 s = μ.rowLen 0 - s + 2 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid6 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row0_mid7 {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (0, s) ∈ μ) (hs_ge : μ.rowLen 2 ≤ s) (hs_lt : s < μ.rowLen 1) :
    hookLength μ 0 s = μ.rowLen 0 - s + 1 := by
  have key := hookLength_add_eq μ hmem
  rw [nineRow_colLen_mid7 h9 hs_ge hs_lt] at key; omega

private lemma nineRow_hookLen_row0_ge {μ : YoungDiagram} {s : ℕ}
    (h9 : μ.rowLen 9 = 0) (hmem : (0, s) ∈ μ) (hs : μ.rowLen 1 ≤ s) :
    hookLength μ 0 s = μ.rowLen 0 - s := by
  have hs_lt : s < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have key := hookLength_add_eq μ hmem
  have hcol : μ.colLen s = 1 := by
    apply Nat.le_antisymm
    · by_contra hlt; push_neg at hlt
      have h1s : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
      have := YoungDiagram.mem_iff_lt_rowLen.mp h1s; omega
    · exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hs_lt)
  rw [hcol] at key; omega

/-- Bottom corner (8, rowLen 8 - 1) always exists in a 9-row shape. -/
private lemma nineRow_corner_bot {μ : YoungDiagram} (h9 : μ.rowLen 9 = 0) (h8 : 0 < μ.rowLen 8) :
    isCorner μ (8, μ.rowLen 8 - 1) := by
  refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
  · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
  · intro h
    have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega

/-- Corner classification for 9-row shapes: corners are among the 9 possible positions. -/
private lemma nineRow_corner_cases {μ : YoungDiagram} (h9 : μ.rowLen 9 = 0) (h8 : 0 < μ.rowLen 8)
    {cell : ℕ × ℕ} (hc : isCorner μ cell) :
    (cell = (8, μ.rowLen 8 - 1)) ∨
    (cell = (7, μ.rowLen 7 - 1) ∧ μ.rowLen 8 < μ.rowLen 7) ∨
    (cell = (6, μ.rowLen 6 - 1) ∧ μ.rowLen 7 < μ.rowLen 6) ∨
    (cell = (5, μ.rowLen 5 - 1) ∧ μ.rowLen 6 < μ.rowLen 5) ∨
    (cell = (4, μ.rowLen 4 - 1) ∧ μ.rowLen 5 < μ.rowLen 4) ∨
    (cell = (3, μ.rowLen 3 - 1) ∧ μ.rowLen 4 < μ.rowLen 3) ∨
    (cell = (2, μ.rowLen 2 - 1) ∧ μ.rowLen 3 < μ.rowLen 2) ∨
    (cell = (1, μ.rowLen 1 - 1) ∧ μ.rowLen 2 < μ.rowLen 1) ∨
    (cell = (0, μ.rowLen 0 - 1) ∧ μ.rowLen 1 < μ.rowLen 0) := by
  obtain ⟨hmem, hnext, hprev⟩ := hc
  have hrow := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  obtain ⟨i, j⟩ := cell
  simp only [Prod.mk.injEq]
  have hi8 : i ≤ 8 := by
    by_contra h; push_neg at h
    have : μ.rowLen 9 > 0 := by
      calc μ.rowLen 9 ≥ μ.rowLen i := μ.rowLen_anti (by omega) (by omega)
        _ > 0 := by omega
    omega
  have hj : j = μ.rowLen i - 1 := by
    apply Nat.le_antisymm
    · by_contra h; push_neg at h
      have : (i, j + 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hnext this
    · have : ¬ (i, j + 1) ∈ μ := hnext
      by_contra h; push_neg at h
      have : μ.rowLen i > j + 1 := by omega
      exact absurd (YoungDiagram.mem_iff_lt_rowLen.mpr this) hnext
  subst hj
  interval_cases i
  · right; right; right; right; right; right; right; right
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 1 = μ.rowLen 0 := Nat.le_antisymm (μ.rowLen_anti 0 1 (by omega)) h
      have : (1, μ.rowLen 0 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; right; right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 2 = μ.rowLen 1 := Nat.le_antisymm (μ.rowLen_anti 1 2 (by omega)) h
      have : (2, μ.rowLen 1 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 3 = μ.rowLen 2 := Nat.le_antisymm (μ.rowLen_anti 2 3 (by omega)) h
      have : (3, μ.rowLen 2 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 4 = μ.rowLen 3 := Nat.le_antisymm (μ.rowLen_anti 3 4 (by omega)) h
      have : (4, μ.rowLen 3 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 5 = μ.rowLen 4 := Nat.le_antisymm (μ.rowLen_anti 4 5 (by omega)) h
      have : (5, μ.rowLen 4 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 6 = μ.rowLen 5 := Nat.le_antisymm (μ.rowLen_anti 5 6 (by omega)) h
      have : (6, μ.rowLen 5 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 7 = μ.rowLen 6 := Nat.le_antisymm (μ.rowLen_anti 6 7 (by omega)) h
      have : (7, μ.rowLen 6 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · right; left
    constructor
    · rfl
    · by_contra h; push_neg at h
      have heq : μ.rowLen 8 = μ.rowLen 7 := Nat.le_antisymm (μ.rowLen_anti 7 8 (by omega)) h
      have : (8, μ.rowLen 7 - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      exact hprev this
  · left; rfl

/-- Card of a 9-row shape equals sum of row lengths. -/
private lemma nineRow_card {μ : YoungDiagram} (h9 : μ.rowLen 9 = 0) :
    μ.card = μ.rowLen 0 + μ.rowLen 1 + μ.rowLen 2 + μ.rowLen 3 +
             μ.rowLen 4 + μ.rowLen 5 + μ.rowLen 6 + μ.rowLen 7 + μ.rowLen 8 := by
  have hcells : μ.cells =
      (Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
      (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
      (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
      (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
      (Finset.range (μ.rowLen 4)).image (Prod.mk 4) ∪
      (Finset.range (μ.rowLen 5)).image (Prod.mk 5) ∪
      (Finset.range (μ.rowLen 6)).image (Prod.mk 6) ∪
      (Finset.range (μ.rowLen 7)).image (Prod.mk 7) ∪
      (Finset.range (μ.rowLen 8)).image (Prod.mk 8) := by
    ext ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, Finset.mem_union, Finset.mem_image,
               Finset.mem_range, Prod.mk.injEq]
    constructor
    · intro h
      have hil : i ≤ 8 := by
        by_contra hlt; push_neg at hlt
        have : μ.rowLen 9 > 0 := calc
          μ.rowLen 9 ≥ μ.rowLen i := μ.rowLen_anti (by omega) (by omega)
          _ > 0 := by
            have := YoungDiagram.mem_iff_lt_rowLen.mp h; omega
        omega
      have hj := YoungDiagram.mem_iff_lt_rowLen.mp h
      interval_cases i <;> simp_all [Prod.mk.injEq]
    · rintro ((((((((⟨k, hk, rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) |
                    ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) |
                  ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩) | ⟨k, hk, rfl, rfl⟩)
      all_goals exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have mk_inj : ∀ (n : ℕ), Function.Injective (Prod.mk n) := fun _ _ _ h => (Prod.mk.inj h).2
  have hd01 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0))
                       ((Finset.range (μ.rowLen 1)).image (Prod.mk 1)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ⟨_, _, rfl, rfl⟩ := hx; obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd012 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                         (Finset.range (μ.rowLen 1)).image (Prod.mk 1))
                        ((Finset.range (μ.rowLen 2)).image (Prod.mk 2)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd0123 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                          (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                          (Finset.range (μ.rowLen 2)).image (Prod.mk 2))
                         ((Finset.range (μ.rowLen 3)).image (Prod.mk 3)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd01234 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                           (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                           (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                           (Finset.range (μ.rowLen 3)).image (Prod.mk 3))
                          ((Finset.range (μ.rowLen 4)).image (Prod.mk 4)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
               ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd012345 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                            (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                            (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                            (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
                            (Finset.range (μ.rowLen 4)).image (Prod.mk 4))
                           ((Finset.range (μ.rowLen 5)).image (Prod.mk 5)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
                ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd0123456 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                             (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                             (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                             (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
                             (Finset.range (μ.rowLen 4)).image (Prod.mk 4) ∪
                             (Finset.range (μ.rowLen 5)).image (Prod.mk 5))
                            ((Finset.range (μ.rowLen 6)).image (Prod.mk 6)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (((((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
                 ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd01234567 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                              (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                              (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                              (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
                              (Finset.range (μ.rowLen 4)).image (Prod.mk 4) ∪
                              (Finset.range (μ.rowLen 5)).image (Prod.mk 5) ∪
                              (Finset.range (μ.rowLen 6)).image (Prod.mk 6))
                             ((Finset.range (μ.rowLen 7)).image (Prod.mk 7)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain ((((((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
                  ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
               ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  have hd012345678 : Disjoint ((Finset.range (μ.rowLen 0)).image (Prod.mk 0) ∪
                               (Finset.range (μ.rowLen 1)).image (Prod.mk 1) ∪
                               (Finset.range (μ.rowLen 2)).image (Prod.mk 2) ∪
                               (Finset.range (μ.rowLen 3)).image (Prod.mk 3) ∪
                               (Finset.range (μ.rowLen 4)).image (Prod.mk 4) ∪
                               (Finset.range (μ.rowLen 5)).image (Prod.mk 5) ∪
                               (Finset.range (μ.rowLen 6)).image (Prod.mk 6) ∪
                               (Finset.range (μ.rowLen 7)).image (Prod.mk 7))
                              ((Finset.range (μ.rowLen 8)).image (Prod.mk 8)) :=
    Finset.disjoint_left.mpr fun x hx hy => by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Prod.mk.injEq] at hx hy
      obtain (((((((⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
                   ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) |
                ⟨_, _, rfl, rfl⟩) | ⟨_, _, rfl, rfl⟩) := hx
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
      · obtain ⟨_, _, h, _⟩ := hy; exact absurd h (by norm_num)
  rw [hcells,
      Finset.card_union_of_disjoint hd012345678,
      Finset.card_union_of_disjoint hd01234567,
      Finset.card_union_of_disjoint hd0123456,
      Finset.card_union_of_disjoint hd012345,
      Finset.card_union_of_disjoint hd01234,
      Finset.card_union_of_disjoint hd0123,
      Finset.card_union_of_disjoint hd012,
      Finset.card_union_of_disjoint hd01,
      Finset.card_image_of_injective _ (mk_inj 0),
      Finset.card_image_of_injective _ (mk_inj 1),
      Finset.card_image_of_injective _ (mk_inj 2),
      Finset.card_image_of_injective _ (mk_inj 3),
      Finset.card_image_of_injective _ (mk_inj 4),
      Finset.card_image_of_injective _ (mk_inj 5),
      Finset.card_image_of_injective _ (mk_inj 6),
      Finset.card_image_of_injective _ (mk_inj 7),
      Finset.card_image_of_injective _ (mk_inj 8),
      Finset.card_range, Finset.card_range, Finset.card_range, Finset.card_range,
      Finset.card_range, Finset.card_range, Finset.card_range, Finset.card_range,
      Finset.card_range]

/-- Arm product for corner (8, j-1) in a 9-row shape telescopes to j. -/
private lemma nineRow_arm_row8 (μ : YoungDiagram) (h9 : μ.rowLen 9 = 0)
    (hj : isCorner μ (8, μ.rowLen 8 - 1)) :
    ∏ s ∈ Finset.range (μ.rowLen 8 - 1),
      ((hookLength μ 8 s : ℚ) / ((hookLength μ 8 s : ℚ) - 1)) =
    (μ.rowLen 8 : ℚ) := by
  set j := μ.rowLen 8
  have hj_pos : 0 < j := by have := YoungDiagram.mem_iff_lt_rowLen.mp hj.1; omega
  have hconv : ∀ s ∈ Finset.range (j - 1),
      (hookLength μ 8 s : ℚ) / ((hookLength μ 8 s : ℚ) - 1) =
      ((j : ℚ) - s) / ((j : ℚ) - s - 1) := by
    intro s hs
    have hsc : s < j - 1 := Finset.mem_range.mp hs
    have hmem : (8, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row8 h9 hmem]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv]
  rw [prod_div_telescope j (j - 1) (Nat.sub_lt hj_pos Nat.one_pos)]
  push_cast; simp [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hj_pos))]

/-- Arm product for corner (7, k-1) in a 9-row shape:
    ∏ = (k+1)(k-j) / (k-j+1). -/
private lemma nineRow_arm_row7 {μ : YoungDiagram} (h9 : μ.rowLen 9 = 0)
    (hjk : μ.rowLen 8 < μ.rowLen 7) :
    ∏ s ∈ Finset.range (μ.rowLen 7 - 1),
      ((hookLength μ 7 s : ℚ) / ((hookLength μ 7 s : ℚ) - 1)) =
    ((μ.rowLen 7 : ℚ) + 1) * ((μ.rowLen 7 : ℚ) - μ.rowLen 8) /
    ((μ.rowLen 7 : ℚ) - μ.rowLen 8 + 1) := by
  set k := μ.rowLen 7; set j := μ.rowLen 8
  rw [show Finset.range (k - 1) = Finset.range j ∪ Finset.Ico j (k - 1) from by
    ext s; simp [Finset.mem_Ico]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range j,
      (hookLength μ 7 s : ℚ) / ((hookLength μ 7 s : ℚ) - 1) =
      ((k : ℚ) + 1 - s) / ((k : ℚ) + 1 - s - 1) := by
    intro s hs
    have hsj : s < j := Finset.mem_range.mp hs
    have hmem : (7, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row7_lt h9 hmem hsj]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (k + 1) j (by omega)]
  rw [show Finset.Ico j (k - 1) = (Finset.range (k - 1 - j)).image (· + j) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (k - 1 - j),
      (hookLength μ 7 (t + j) : ℚ) / ((hookLength μ 7 (t + j) : ℚ) - 1) =
      ((k : ℚ) - j - t) / ((k : ℚ) - j - t - 1) := by
    intro t ht
    have htm : t < k - 1 - j := Finset.mem_range.mp ht
    have hmem : (7, t + j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row7_ge h9 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (k - j) (k - 1 - j) (by omega)]
  push_cast [Nat.cast_sub hjk.le, Nat.cast_sub (show 1 ≤ k - j by omega)]
  have hne : (k : ℚ) - j + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < k - j + 1 by omega)
  field_simp [hne]; ring

/-- Arm product for corner (6, g-1) in a 9-row shape:
    ∏ = (g+2)(g-j+1)(g-k) / ((g-j+2)(g-k+1)). -/
private lemma nineRow_arm_row6 {μ : YoungDiagram} (h9 : μ.rowLen 9 = 0)
    (hkg : μ.rowLen 7 < μ.rowLen 6) :
    ∏ s ∈ Finset.range (μ.rowLen 6 - 1),
      ((hookLength μ 6 s : ℚ) / ((hookLength μ 6 s : ℚ) - 1)) =
    ((μ.rowLen 6 : ℚ) + 2) * ((μ.rowLen 6 : ℚ) - μ.rowLen 8 + 1) *
    ((μ.rowLen 6 : ℚ) - μ.rowLen 7) /
    (((μ.rowLen 6 : ℚ) - μ.rowLen 8 + 2) * ((μ.rowLen 6 : ℚ) - μ.rowLen 7 + 1)) := by
  set g := μ.rowLen 6; set k := μ.rowLen 7; set j := μ.rowLen 8
  have hjk : j ≤ k := μ.rowLen_anti 7 8 (by omega)
  rw [show Finset.range (g - 1) = Finset.range j ∪ Finset.Ico j k ∪ Finset.Ico k (g - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range j,
      (hookLength μ 6 s : ℚ) / ((hookLength μ 6 s : ℚ) - 1) =
      ((g : ℚ) + 2 - s) / ((g : ℚ) + 2 - s - 1) := by
    intro s hs
    have hsj : s < j := Finset.mem_range.mp hs
    have hmem : (6, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row6_lt h9 hmem hsj]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (g + 2) j (by omega)]
  rw [show Finset.Ico j k = (Finset.range (k - j)).image (· + j) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (k - j),
      (hookLength μ 6 (t + j) : ℚ) / ((hookLength μ 6 (t + j) : ℚ) - 1) =
      ((g : ℚ) - j + 1 - t) / ((g : ℚ) - j + 1 - t - 1) := by
    intro t ht
    have htm : t < k - j := Finset.mem_range.mp ht
    have hmem : (6, t + j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row6_mid1 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (g - j + 1) (k - j) (by omega)]
  rw [show Finset.Ico k (g - 1) = (Finset.range (g - 1 - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (g - 1 - k),
      (hookLength μ 6 (t + k) : ℚ) / ((hookLength μ 6 (t + k) : ℚ) - 1) =
      ((g : ℚ) - k - t) / ((g : ℚ) - k - t - 1) := by
    intro t ht
    have htm : t < g - 1 - k := Finset.mem_range.mp ht
    have hmem : (6, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row6_ge h9 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (g - k) (g - 1 - k) (by omega)]
  push_cast [Nat.cast_sub hjk, Nat.cast_sub hkg.le, Nat.cast_sub (show 1 ≤ g - k by omega)]
  have hne1 : (g : ℚ) - j + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < g - j + 2 by omega)
  have hne2 : (g : ℚ) - k + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < g - k + 1 by omega)
  field_simp [hne1, hne2]; ring

/-- Arm product for corner (5, f-1) in a 9-row shape:
    ∏ = (f+3)(f-j+2)(f-k+1)(f-g) / ((f-j+3)(f-k+2)(f-g+1)). -/
private lemma nineRow_arm_row5 {μ : YoungDiagram} (h9 : μ.rowLen 9 = 0)
    (hgf : μ.rowLen 6 < μ.rowLen 5) :
    ∏ s ∈ Finset.range (μ.rowLen 5 - 1),
      ((hookLength μ 5 s : ℚ) / ((hookLength μ 5 s : ℚ) - 1)) =
    ((μ.rowLen 5 : ℚ) + 3) * ((μ.rowLen 5 : ℚ) - μ.rowLen 8 + 2) *
    ((μ.rowLen 5 : ℚ) - μ.rowLen 7 + 1) * ((μ.rowLen 5 : ℚ) - μ.rowLen 6) /
    (((μ.rowLen 5 : ℚ) - μ.rowLen 8 + 3) * ((μ.rowLen 5 : ℚ) - μ.rowLen 7 + 2) *
     ((μ.rowLen 5 : ℚ) - μ.rowLen 6 + 1)) := by
  set f := μ.rowLen 5; set g := μ.rowLen 6; set k := μ.rowLen 7; set j := μ.rowLen 8
  have hjk : j ≤ k := μ.rowLen_anti 7 8 (by omega)
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  rw [show Finset.range (f - 1) = Finset.range j ∪ Finset.Ico j k ∪
      Finset.Ico k g ∪ Finset.Ico g (f - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range j,
      (hookLength μ 5 s : ℚ) / ((hookLength μ 5 s : ℚ) - 1) =
      ((f : ℚ) + 3 - s) / ((f : ℚ) + 3 - s - 1) := by
    intro s hs
    have hsj : s < j := Finset.mem_range.mp hs
    have hmem : (5, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row5_lt h9 hmem hsj]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (f + 3) j (by omega)]
  rw [show Finset.Ico j k = (Finset.range (k - j)).image (· + j) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (k - j),
      (hookLength μ 5 (t + j) : ℚ) / ((hookLength μ 5 (t + j) : ℚ) - 1) =
      ((f : ℚ) - j + 2 - t) / ((f : ℚ) - j + 2 - t - 1) := by
    intro t ht
    have htm : t < k - j := Finset.mem_range.mp ht
    have hmem : (5, t + j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row5_mid1 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (f - j + 2) (k - j) (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 5 (t + k) : ℚ) / ((hookLength μ 5 (t + k) : ℚ) - 1) =
      ((f : ℚ) - k + 1 - t) / ((f : ℚ) - k + 1 - t - 1) := by
    intro t ht
    have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (5, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row5_mid2 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (f - k + 1) (g - k) (by omega)]
  rw [show Finset.Ico g (f - 1) = (Finset.range (f - 1 - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (f - 1 - g),
      (hookLength μ 5 (t + g) : ℚ) / ((hookLength μ 5 (t + g) : ℚ) - 1) =
      ((f : ℚ) - g - t) / ((f : ℚ) - g - t - 1) := by
    intro t ht
    have htm : t < f - 1 - g := Finset.mem_range.mp ht
    have hmem : (5, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row5_ge h9 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (f - g) (f - 1 - g) (by omega)]
  push_cast [Nat.cast_sub hjk, Nat.cast_sub hkg, Nat.cast_sub hgf.le,
             Nat.cast_sub (show 1 ≤ f - g by omega)]
  have hne1 : (f : ℚ) - j + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < f - j + 3 by omega)
  have hne2 : (f : ℚ) - k + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < f - k + 2 by omega)
  have hne3 : (f : ℚ) - g + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < f - g + 1 by omega)
  field_simp [hne1, hne2, hne3]; ring

/-- Arm product for corner (4, e-1) in a 9-row shape:
    ∏ = (e+4)(e-j+3)(e-k+2)(e-g+1)(e-f) / ((e-j+4)(e-k+3)(e-g+2)(e-f+1)). -/
private lemma nineRow_arm_row4 {μ : YoungDiagram} (h9 : μ.rowLen 9 = 0)
    (hfe : μ.rowLen 5 < μ.rowLen 4) :
    ∏ s ∈ Finset.range (μ.rowLen 4 - 1),
      ((hookLength μ 4 s : ℚ) / ((hookLength μ 4 s : ℚ) - 1)) =
    ((μ.rowLen 4 : ℚ) + 4) * ((μ.rowLen 4 : ℚ) - μ.rowLen 8 + 3) *
    ((μ.rowLen 4 : ℚ) - μ.rowLen 7 + 2) * ((μ.rowLen 4 : ℚ) - μ.rowLen 6 + 1) *
    ((μ.rowLen 4 : ℚ) - μ.rowLen 5) /
    (((μ.rowLen 4 : ℚ) - μ.rowLen 8 + 4) * ((μ.rowLen 4 : ℚ) - μ.rowLen 7 + 3) *
     ((μ.rowLen 4 : ℚ) - μ.rowLen 6 + 2) * ((μ.rowLen 4 : ℚ) - μ.rowLen 5 + 1)) := by
  set e := μ.rowLen 4; set f := μ.rowLen 5; set g := μ.rowLen 6
  set k := μ.rowLen 7; set j := μ.rowLen 8
  have hjk : j ≤ k := μ.rowLen_anti 7 8 (by omega)
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  rw [show Finset.range (e - 1) = Finset.range j ∪ Finset.Ico j k ∪
      Finset.Ico k g ∪ Finset.Ico g f ∪ Finset.Ico f (e - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range j,
      (hookLength μ 4 s : ℚ) / ((hookLength μ 4 s : ℚ) - 1) =
      ((e : ℚ) + 4 - s) / ((e : ℚ) + 4 - s - 1) := by
    intro s hs
    have hsj : s < j := Finset.mem_range.mp hs
    have hmem : (4, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row4_lt h9 hmem hsj]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (e + 4) j (by omega)]
  rw [show Finset.Ico j k = (Finset.range (k - j)).image (· + j) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (k - j),
      (hookLength μ 4 (t + j) : ℚ) / ((hookLength μ 4 (t + j) : ℚ) - 1) =
      ((e : ℚ) - j + 3 - t) / ((e : ℚ) - j + 3 - t - 1) := by
    intro t ht
    have htm : t < k - j := Finset.mem_range.mp ht
    have hmem : (4, t + j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row4_mid1 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (e - j + 3) (k - j) (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 4 (t + k) : ℚ) / ((hookLength μ 4 (t + k) : ℚ) - 1) =
      ((e : ℚ) - k + 2 - t) / ((e : ℚ) - k + 2 - t - 1) := by
    intro t ht
    have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (4, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row4_mid2 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (e - k + 2) (g - k) (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 4 (t + g) : ℚ) / ((hookLength μ 4 (t + g) : ℚ) - 1) =
      ((e : ℚ) - g + 1 - t) / ((e : ℚ) - g + 1 - t - 1) := by
    intro t ht
    have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (4, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row4_mid3 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (e - g + 1) (f - g) (by omega)]
  rw [show Finset.Ico f (e - 1) = (Finset.range (e - 1 - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (e - 1 - f),
      (hookLength μ 4 (t + f) : ℚ) / ((hookLength μ 4 (t + f) : ℚ) - 1) =
      ((e : ℚ) - f - t) / ((e : ℚ) - f - t - 1) := by
    intro t ht
    have htm : t < e - 1 - f := Finset.mem_range.mp ht
    have hmem : (4, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row4_ge h9 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (e - f) (e - 1 - f) (by omega)]
  push_cast [Nat.cast_sub hjk, Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe.le,
             Nat.cast_sub (show 1 ≤ e - f by omega)]
  have hne1 : (e : ℚ) - j + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - j + 4 by omega)
  have hne2 : (e : ℚ) - k + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - k + 3 by omega)
  have hne3 : (e : ℚ) - g + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - g + 2 by omega)
  have hne4 : (e : ℚ) - f + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - f + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4]; ring

/-- Arm product for corner (3, d-1) in a 9-row shape:
    ∏ = (d+5)(d-j+4)(d-k+3)(d-g+2)(d-f+1)(d-e) / ((d-j+5)(d-k+4)(d-g+3)(d-f+2)(d-e+1)). -/
private lemma nineRow_arm_row3 {μ : YoungDiagram} (h9 : μ.rowLen 9 = 0)
    (hed : μ.rowLen 4 < μ.rowLen 3) :
    ∏ s ∈ Finset.range (μ.rowLen 3 - 1),
      ((hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1)) =
    ((μ.rowLen 3 : ℚ) + 5) * ((μ.rowLen 3 : ℚ) - μ.rowLen 8 + 4) *
    ((μ.rowLen 3 : ℚ) - μ.rowLen 7 + 3) * ((μ.rowLen 3 : ℚ) - μ.rowLen 6 + 2) *
    ((μ.rowLen 3 : ℚ) - μ.rowLen 5 + 1) * ((μ.rowLen 3 : ℚ) - μ.rowLen 4) /
    (((μ.rowLen 3 : ℚ) - μ.rowLen 8 + 5) * ((μ.rowLen 3 : ℚ) - μ.rowLen 7 + 4) *
     ((μ.rowLen 3 : ℚ) - μ.rowLen 6 + 3) * ((μ.rowLen 3 : ℚ) - μ.rowLen 5 + 2) *
     ((μ.rowLen 3 : ℚ) - μ.rowLen 4 + 1)) := by
  set d := μ.rowLen 3; set e := μ.rowLen 4; set f := μ.rowLen 5
  set g := μ.rowLen 6; set k := μ.rowLen 7; set j := μ.rowLen 8
  have hjk : j ≤ k := μ.rowLen_anti 7 8 (by omega)
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  rw [show Finset.range (d - 1) = Finset.range j ∪ Finset.Ico j k ∪
      Finset.Ico k g ∪ Finset.Ico g f ∪ Finset.Ico f e ∪ Finset.Ico e (d - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range j,
      (hookLength μ 3 s : ℚ) / ((hookLength μ 3 s : ℚ) - 1) =
      ((d : ℚ) + 5 - s) / ((d : ℚ) + 5 - s - 1) := by
    intro s hs; have hsj : s < j := Finset.mem_range.mp hs
    have hmem : (3, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row3_lt h9 hmem hsj]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (d + 5) j (by omega)]
  rw [show Finset.Ico j k = (Finset.range (k - j)).image (· + j) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (k - j),
      (hookLength μ 3 (t + j) : ℚ) / ((hookLength μ 3 (t + j) : ℚ) - 1) =
      ((d : ℚ) - j + 4 - t) / ((d : ℚ) - j + 4 - t - 1) := by
    intro t ht; have htm : t < k - j := Finset.mem_range.mp ht
    have hmem : (3, t + j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row3_mid1 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (d - j + 4) (k - j) (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 3 (t + k) : ℚ) / ((hookLength μ 3 (t + k) : ℚ) - 1) =
      ((d : ℚ) - k + 3 - t) / ((d : ℚ) - k + 3 - t - 1) := by
    intro t ht; have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (3, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row3_mid2 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (d - k + 3) (g - k) (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 3 (t + g) : ℚ) / ((hookLength μ 3 (t + g) : ℚ) - 1) =
      ((d : ℚ) - g + 2 - t) / ((d : ℚ) - g + 2 - t - 1) := by
    intro t ht; have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (3, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row3_mid3 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (d - g + 2) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 3 (t + f) : ℚ) / ((hookLength μ 3 (t + f) : ℚ) - 1) =
      ((d : ℚ) - f + 1 - t) / ((d : ℚ) - f + 1 - t - 1) := by
    intro t ht; have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (3, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row3_mid4 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (d - f + 1) (e - f) (by omega)]
  rw [show Finset.Ico e (d - 1) = (Finset.range (d - 1 - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv6 : ∀ t ∈ Finset.range (d - 1 - e),
      (hookLength μ 3 (t + e) : ℚ) / ((hookLength μ 3 (t + e) : ℚ) - 1) =
      ((d : ℚ) - e - t) / ((d : ℚ) - e - t - 1) := by
    intro t ht; have htm : t < d - 1 - e := Finset.mem_range.mp ht
    have hmem : (3, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row3_ge h9 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv6, prod_div_telescope (d - e) (d - 1 - e) (by omega)]
  push_cast [Nat.cast_sub hjk, Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe,
             Nat.cast_sub hed.le, Nat.cast_sub (show 1 ≤ d - e by omega)]
  have hne1 : (d : ℚ) - j + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - j + 5 by omega)
  have hne2 : (d : ℚ) - k + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - k + 4 by omega)
  have hne3 : (d : ℚ) - g + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - g + 3 by omega)
  have hne4 : (d : ℚ) - f + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - f + 2 by omega)
  have hne5 : (d : ℚ) - e + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - e + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4, hne5]; ring

/-- Arm product for corner (2, c-1) in a 9-row shape:
    ∏ = (c+6)(c-j+5)(c-k+4)(c-g+3)(c-f+2)(c-e+1)(c-d) /
        ((c-j+6)(c-k+5)(c-g+4)(c-f+3)(c-e+2)(c-d+1)). -/
private lemma nineRow_arm_row2 {μ : YoungDiagram} (h9 : μ.rowLen 9 = 0)
    (hdc : μ.rowLen 3 < μ.rowLen 2) :
    ∏ s ∈ Finset.range (μ.rowLen 2 - 1),
      ((hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1)) =
    ((μ.rowLen 2 : ℚ) + 6) * ((μ.rowLen 2 : ℚ) - μ.rowLen 8 + 5) *
    ((μ.rowLen 2 : ℚ) - μ.rowLen 7 + 4) * ((μ.rowLen 2 : ℚ) - μ.rowLen 6 + 3) *
    ((μ.rowLen 2 : ℚ) - μ.rowLen 5 + 2) * ((μ.rowLen 2 : ℚ) - μ.rowLen 4 + 1) *
    ((μ.rowLen 2 : ℚ) - μ.rowLen 3) /
    (((μ.rowLen 2 : ℚ) - μ.rowLen 8 + 6) * ((μ.rowLen 2 : ℚ) - μ.rowLen 7 + 5) *
     ((μ.rowLen 2 : ℚ) - μ.rowLen 6 + 4) * ((μ.rowLen 2 : ℚ) - μ.rowLen 5 + 3) *
     ((μ.rowLen 2 : ℚ) - μ.rowLen 4 + 2) * ((μ.rowLen 2 : ℚ) - μ.rowLen 3 + 1)) := by
  set c := μ.rowLen 2; set d := μ.rowLen 3; set e := μ.rowLen 4
  set f := μ.rowLen 5; set g := μ.rowLen 6; set k := μ.rowLen 7; set j := μ.rowLen 8
  have hjk : j ≤ k := μ.rowLen_anti 7 8 (by omega)
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  rw [show Finset.range (c - 1) = Finset.range j ∪ Finset.Ico j k ∪
      Finset.Ico k g ∪ Finset.Ico g f ∪ Finset.Ico f e ∪ Finset.Ico e d ∪
      Finset.Ico d (c - 1) from by ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range j,
      (hookLength μ 2 s : ℚ) / ((hookLength μ 2 s : ℚ) - 1) =
      ((c : ℚ) + 6 - s) / ((c : ℚ) + 6 - s - 1) := by
    intro s hs; have hsj : s < j := Finset.mem_range.mp hs
    have hmem : (2, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row2_lt h9 hmem hsj]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (c + 6) j (by omega)]
  rw [show Finset.Ico j k = (Finset.range (k - j)).image (· + j) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (k - j),
      (hookLength μ 2 (t + j) : ℚ) / ((hookLength μ 2 (t + j) : ℚ) - 1) =
      ((c : ℚ) - j + 5 - t) / ((c : ℚ) - j + 5 - t - 1) := by
    intro t ht; have htm : t < k - j := Finset.mem_range.mp ht
    have hmem : (2, t + j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row2_mid1 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (c - j + 5) (k - j) (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 2 (t + k) : ℚ) / ((hookLength μ 2 (t + k) : ℚ) - 1) =
      ((c : ℚ) - k + 4 - t) / ((c : ℚ) - k + 4 - t - 1) := by
    intro t ht; have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (2, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row2_mid2 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (c - k + 4) (g - k) (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 2 (t + g) : ℚ) / ((hookLength μ 2 (t + g) : ℚ) - 1) =
      ((c : ℚ) - g + 3 - t) / ((c : ℚ) - g + 3 - t - 1) := by
    intro t ht; have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (2, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row2_mid3 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (c - g + 3) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 2 (t + f) : ℚ) / ((hookLength μ 2 (t + f) : ℚ) - 1) =
      ((c : ℚ) - f + 2 - t) / ((c : ℚ) - f + 2 - t - 1) := by
    intro t ht; have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (2, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row2_mid4 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (c - f + 2) (e - f) (by omega)]
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv6 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 2 (t + e) : ℚ) / ((hookLength μ 2 (t + e) : ℚ) - 1) =
      ((c : ℚ) - e + 1 - t) / ((c : ℚ) - e + 1 - t - 1) := by
    intro t ht; have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (2, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row2_mid5 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv6, prod_div_telescope (c - e + 1) (d - e) (by omega)]
  rw [show Finset.Ico d (c - 1) = (Finset.range (c - 1 - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv7 : ∀ t ∈ Finset.range (c - 1 - d),
      (hookLength μ 2 (t + d) : ℚ) / ((hookLength μ 2 (t + d) : ℚ) - 1) =
      ((c : ℚ) - d - t) / ((c : ℚ) - d - t - 1) := by
    intro t ht; have htm : t < c - 1 - d := Finset.mem_range.mp ht
    have hmem : (2, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row2_ge h9 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv7, prod_div_telescope (c - d) (c - 1 - d) (by omega)]
  push_cast [Nat.cast_sub hjk, Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe,
             Nat.cast_sub hed, Nat.cast_sub hdc.le, Nat.cast_sub (show 1 ≤ c - d by omega)]
  have hne1 : (c : ℚ) - j + 6 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - j + 6 by omega)
  have hne2 : (c : ℚ) - k + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - k + 5 by omega)
  have hne3 : (c : ℚ) - g + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - g + 4 by omega)
  have hne4 : (c : ℚ) - f + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - f + 3 by omega)
  have hne5 : (c : ℚ) - e + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - e + 2 by omega)
  have hne6 : (c : ℚ) - d + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4, hne5, hne6]; ring

/-- Arm product for corner (1, b-1) in a 9-row shape:
    ∏ = (b+7)(b-j+6)(b-k+5)(b-g+4)(b-f+3)(b-e+2)(b-d+1)(b-c) /
        ((b-j+7)(b-k+6)(b-g+5)(b-f+4)(b-e+3)(b-d+2)(b-c+1)). -/
private lemma nineRow_arm_row1 {μ : YoungDiagram} (h9 : μ.rowLen 9 = 0)
    (hcb : μ.rowLen 2 < μ.rowLen 1) :
    ∏ s ∈ Finset.range (μ.rowLen 1 - 1),
      ((hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1)) =
    ((μ.rowLen 1 : ℚ) + 7) * ((μ.rowLen 1 : ℚ) - μ.rowLen 8 + 6) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 7 + 5) * ((μ.rowLen 1 : ℚ) - μ.rowLen 6 + 4) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 5 + 3) * ((μ.rowLen 1 : ℚ) - μ.rowLen 4 + 2) *
    ((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 1) * ((μ.rowLen 1 : ℚ) - μ.rowLen 2) /
    (((μ.rowLen 1 : ℚ) - μ.rowLen 8 + 7) * ((μ.rowLen 1 : ℚ) - μ.rowLen 7 + 6) *
     ((μ.rowLen 1 : ℚ) - μ.rowLen 6 + 5) * ((μ.rowLen 1 : ℚ) - μ.rowLen 5 + 4) *
     ((μ.rowLen 1 : ℚ) - μ.rowLen 4 + 3) * ((μ.rowLen 1 : ℚ) - μ.rowLen 3 + 2) *
     ((μ.rowLen 1 : ℚ) - μ.rowLen 2 + 1)) := by
  set b := μ.rowLen 1; set c := μ.rowLen 2; set d := μ.rowLen 3; set e := μ.rowLen 4
  set f := μ.rowLen 5; set g := μ.rowLen 6; set k := μ.rowLen 7; set j := μ.rowLen 8
  have hjk : j ≤ k := μ.rowLen_anti 7 8 (by omega)
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  rw [show Finset.range (b - 1) = Finset.range j ∪ Finset.Ico j k ∪
      Finset.Ico k g ∪ Finset.Ico g f ∪ Finset.Ico f e ∪ Finset.Ico e d ∪
      Finset.Ico d c ∪ Finset.Ico c (b - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range j,
      (hookLength μ 1 s : ℚ) / ((hookLength μ 1 s : ℚ) - 1) =
      ((b : ℚ) + 7 - s) / ((b : ℚ) + 7 - s - 1) := by
    intro s hs; have hsj : s < j := Finset.mem_range.mp hs
    have hmem : (1, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row1_lt h9 hmem hsj]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (b + 7) j (by omega)]
  rw [show Finset.Ico j k = (Finset.range (k - j)).image (· + j) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (k - j),
      (hookLength μ 1 (t + j) : ℚ) / ((hookLength μ 1 (t + j) : ℚ) - 1) =
      ((b : ℚ) - j + 6 - t) / ((b : ℚ) - j + 6 - t - 1) := by
    intro t ht; have htm : t < k - j := Finset.mem_range.mp ht
    have hmem : (1, t + j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row1_mid1 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (b - j + 6) (k - j) (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 1 (t + k) : ℚ) / ((hookLength μ 1 (t + k) : ℚ) - 1) =
      ((b : ℚ) - k + 5 - t) / ((b : ℚ) - k + 5 - t - 1) := by
    intro t ht; have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (1, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row1_mid2 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (b - k + 5) (g - k) (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 1 (t + g) : ℚ) / ((hookLength μ 1 (t + g) : ℚ) - 1) =
      ((b : ℚ) - g + 4 - t) / ((b : ℚ) - g + 4 - t - 1) := by
    intro t ht; have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (1, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row1_mid3 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (b - g + 4) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 1 (t + f) : ℚ) / ((hookLength μ 1 (t + f) : ℚ) - 1) =
      ((b : ℚ) - f + 3 - t) / ((b : ℚ) - f + 3 - t - 1) := by
    intro t ht; have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (1, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row1_mid4 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (b - f + 3) (e - f) (by omega)]
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv6 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 1 (t + e) : ℚ) / ((hookLength μ 1 (t + e) : ℚ) - 1) =
      ((b : ℚ) - e + 2 - t) / ((b : ℚ) - e + 2 - t - 1) := by
    intro t ht; have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (1, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row1_mid5 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv6, prod_div_telescope (b - e + 2) (d - e) (by omega)]
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv7 : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 1 (t + d) : ℚ) / ((hookLength μ 1 (t + d) : ℚ) - 1) =
      ((b : ℚ) - d + 1 - t) / ((b : ℚ) - d + 1 - t - 1) := by
    intro t ht; have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (1, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row1_mid6 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv7, prod_div_telescope (b - d + 1) (c - d) (by omega)]
  rw [show Finset.Ico c (b - 1) = (Finset.range (b - 1 - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv8 : ∀ t ∈ Finset.range (b - 1 - c),
      (hookLength μ 1 (t + c) : ℚ) / ((hookLength μ 1 (t + c) : ℚ) - 1) =
      ((b : ℚ) - c - t) / ((b : ℚ) - c - t - 1) := by
    intro t ht; have htm : t < b - 1 - c := Finset.mem_range.mp ht
    have hmem : (1, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row1_ge h9 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv8, prod_div_telescope (b - c) (b - 1 - c) (by omega)]
  push_cast [Nat.cast_sub hjk, Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe,
             Nat.cast_sub hed, Nat.cast_sub hdc, Nat.cast_sub hcb.le,
             Nat.cast_sub (show 1 ≤ b - c by omega)]
  have hne1 : (b : ℚ) - j + 7 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - j + 7 by omega)
  have hne2 : (b : ℚ) - k + 6 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - k + 6 by omega)
  have hne3 : (b : ℚ) - g + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - g + 5 by omega)
  have hne4 : (b : ℚ) - f + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - f + 4 by omega)
  have hne5 : (b : ℚ) - e + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - e + 3 by omega)
  have hne6 : (b : ℚ) - d + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne7 : (b : ℚ) - c + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4, hne5, hne6, hne7]; ring

/-- Arm product for corner (0, a-1) in a 9-row shape:
    ∏ = (a+8)(a-j+7)(a-k+6)(a-g+5)(a-f+4)(a-e+3)(a-d+2)(a-c+1)(a-b) /
        ((a-j+8)(a-k+7)(a-g+6)(a-f+5)(a-e+4)(a-d+3)(a-c+2)(a-b+1)). -/
private lemma nineRow_arm_row0 {μ : YoungDiagram} (h9 : μ.rowLen 9 = 0)
    (h8 : 0 < μ.rowLen 8) (hab : μ.rowLen 1 < μ.rowLen 0) :
    ∏ s ∈ Finset.range (μ.rowLen 0 - 1),
      ((hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1)) =
    ((μ.rowLen 0 : ℚ) + 8) * ((μ.rowLen 0 : ℚ) - μ.rowLen 8 + 7) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 7 + 6) * ((μ.rowLen 0 : ℚ) - μ.rowLen 6 + 5) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 5 + 4) * ((μ.rowLen 0 : ℚ) - μ.rowLen 4 + 3) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 2) * ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 1) *
    ((μ.rowLen 0 : ℚ) - μ.rowLen 1) /
    (((μ.rowLen 0 : ℚ) - μ.rowLen 8 + 8) * ((μ.rowLen 0 : ℚ) - μ.rowLen 7 + 7) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 6 + 6) * ((μ.rowLen 0 : ℚ) - μ.rowLen 5 + 5) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 4 + 4) * ((μ.rowLen 0 : ℚ) - μ.rowLen 3 + 3) *
     ((μ.rowLen 0 : ℚ) - μ.rowLen 2 + 2) * ((μ.rowLen 0 : ℚ) - μ.rowLen 1 + 1)) := by
  set a := μ.rowLen 0; set b := μ.rowLen 1; set c := μ.rowLen 2; set d := μ.rowLen 3
  set e := μ.rowLen 4; set f := μ.rowLen 5; set g := μ.rowLen 6
  set k := μ.rowLen 7; set j := μ.rowLen 8
  have hjk : j ≤ k := μ.rowLen_anti 7 8 (by omega)
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  rw [show Finset.range (a - 1) = Finset.range j ∪ Finset.Ico j k ∪
      Finset.Ico k g ∪ Finset.Ico g f ∪ Finset.Ico f e ∪ Finset.Ico e d ∪
      Finset.Ico d c ∪ Finset.Ico c b ∪ Finset.Ico b (a - 1) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega),
      Finset.prod_union (by simp [Finset.disjoint_left, Finset.mem_Ico]; omega)]
  have hconv1 : ∀ s ∈ Finset.range j,
      (hookLength μ 0 s : ℚ) / ((hookLength μ 0 s : ℚ) - 1) =
      ((a : ℚ) + 8 - s) / ((a : ℚ) + 8 - s - 1) := by
    intro s hs; have hsj : s < j := Finset.mem_range.mp hs
    have hmem : (0, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row0_lt h9 hmem hsj]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv1, prod_div_telescope (a + 8) j (by omega)]
  rw [show Finset.Ico j k = (Finset.range (k - j)).image (· + j) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv2 : ∀ t ∈ Finset.range (k - j),
      (hookLength μ 0 (t + j) : ℚ) / ((hookLength μ 0 (t + j) : ℚ) - 1) =
      ((a : ℚ) - j + 7 - t) / ((a : ℚ) - j + 7 - t - 1) := by
    intro t ht; have htm : t < k - j := Finset.mem_range.mp ht
    have hmem : (0, t + j) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row0_mid1 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv2, prod_div_telescope (a - j + 7) (k - j) (by omega)]
  rw [show Finset.Ico k g = (Finset.range (g - k)).image (· + k) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv3 : ∀ t ∈ Finset.range (g - k),
      (hookLength μ 0 (t + k) : ℚ) / ((hookLength μ 0 (t + k) : ℚ) - 1) =
      ((a : ℚ) - k + 6 - t) / ((a : ℚ) - k + 6 - t - 1) := by
    intro t ht; have htm : t < g - k := Finset.mem_range.mp ht
    have hmem : (0, t + k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row0_mid2 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv3, prod_div_telescope (a - k + 6) (g - k) (by omega)]
  rw [show Finset.Ico g f = (Finset.range (f - g)).image (· + g) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv4 : ∀ t ∈ Finset.range (f - g),
      (hookLength μ 0 (t + g) : ℚ) / ((hookLength μ 0 (t + g) : ℚ) - 1) =
      ((a : ℚ) - g + 5 - t) / ((a : ℚ) - g + 5 - t - 1) := by
    intro t ht; have htm : t < f - g := Finset.mem_range.mp ht
    have hmem : (0, t + g) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row0_mid3 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv4, prod_div_telescope (a - g + 5) (f - g) (by omega)]
  rw [show Finset.Ico f e = (Finset.range (e - f)).image (· + f) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv5 : ∀ t ∈ Finset.range (e - f),
      (hookLength μ 0 (t + f) : ℚ) / ((hookLength μ 0 (t + f) : ℚ) - 1) =
      ((a : ℚ) - f + 4 - t) / ((a : ℚ) - f + 4 - t - 1) := by
    intro t ht; have htm : t < e - f := Finset.mem_range.mp ht
    have hmem : (0, t + f) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row0_mid4 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv5, prod_div_telescope (a - f + 4) (e - f) (by omega)]
  rw [show Finset.Ico e d = (Finset.range (d - e)).image (· + e) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv6 : ∀ t ∈ Finset.range (d - e),
      (hookLength μ 0 (t + e) : ℚ) / ((hookLength μ 0 (t + e) : ℚ) - 1) =
      ((a : ℚ) - e + 3 - t) / ((a : ℚ) - e + 3 - t - 1) := by
    intro t ht; have htm : t < d - e := Finset.mem_range.mp ht
    have hmem : (0, t + e) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row0_mid5 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv6, prod_div_telescope (a - e + 3) (d - e) (by omega)]
  rw [show Finset.Ico d c = (Finset.range (c - d)).image (· + d) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv7 : ∀ t ∈ Finset.range (c - d),
      (hookLength μ 0 (t + d) : ℚ) / ((hookLength μ 0 (t + d) : ℚ) - 1) =
      ((a : ℚ) - d + 2 - t) / ((a : ℚ) - d + 2 - t - 1) := by
    intro t ht; have htm : t < c - d := Finset.mem_range.mp ht
    have hmem : (0, t + d) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row0_mid6 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv7, prod_div_telescope (a - d + 2) (c - d) (by omega)]
  rw [show Finset.Ico c b = (Finset.range (b - c)).image (· + c) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv8 : ∀ t ∈ Finset.range (b - c),
      (hookLength μ 0 (t + c) : ℚ) / ((hookLength μ 0 (t + c) : ℚ) - 1) =
      ((a : ℚ) - c + 1 - t) / ((a : ℚ) - c + 1 - t - 1) := by
    intro t ht; have htm : t < b - c := Finset.mem_range.mp ht
    have hmem : (0, t + c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row0_mid7 h9 hmem (by omega) (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv8, prod_div_telescope (a - c + 1) (b - c) (by omega)]
  rw [show Finset.Ico b (a - 1) = (Finset.range (a - 1 - b)).image (· + b) from by
    ext s; simp [Finset.mem_Ico, Finset.mem_range]; omega]
  rw [Finset.prod_image (by intro x _ y _ h; omega)]
  have hconv9 : ∀ t ∈ Finset.range (a - 1 - b),
      (hookLength μ 0 (t + b) : ℚ) / ((hookLength μ 0 (t + b) : ℚ) - 1) =
      ((a : ℚ) - b - t) / ((a : ℚ) - b - t - 1) := by
    intro t ht; have htm : t < a - 1 - b := Finset.mem_range.mp ht
    have hmem : (0, t + b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [nineRow_hookLen_row0_ge h9 hmem (by omega)]; push_cast; congr 1 <;> push_cast <;> omega
  rw [Finset.prod_congr rfl hconv9, prod_div_telescope (a - b) (a - 1 - b) (by omega)]
  push_cast [Nat.cast_sub hjk, Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe,
             Nat.cast_sub hed, Nat.cast_sub hdc, Nat.cast_sub hcb, Nat.cast_sub hab.le,
             Nat.cast_sub (show 1 ≤ a - b by omega)]
  have hne1 : (a : ℚ) - j + 8 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - j + 8 by omega)
  have hne2 : (a : ℚ) - k + 7 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - k + 7 by omega)
  have hne3 : (a : ℚ) - g + 6 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - g + 6 by omega)
  have hne4 : (a : ℚ) - f + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - f + 5 by omega)
  have hne5 : (a : ℚ) - e + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - e + 4 by omega)
  have hne6 : (a : ℚ) - d + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne7 : (a : ℚ) - c + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne8 : (a : ℚ) - b + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  field_simp [hne1, hne2, hne3, hne4, hne5, hne6, hne7, hne8]; ring

/-- Hook walk identity for 9-row shapes: Σ_corners hookProd(μ)/hookProd(μ\c) = card(μ). -/
lemma hook_walk_identity_nineRow (μ : YoungDiagram)
    (h9 : μ.rowLen 9 = 0) (h8 : 0 < μ.rowLen 8) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / (hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) : ℚ))
    = (μ.card : ℚ) := by
  set j := μ.rowLen 8; set k := μ.rowLen 7; set g := μ.rowLen 6
  set f := μ.rowLen 5; set e := μ.rowLen 4; set d := μ.rowLen 3
  set c := μ.rowLen 2; set b := μ.rowLen 1; set a := μ.rowLen 0
  have hjk : j ≤ k := μ.rowLen_anti 7 8 (by omega)
  have hkg : k ≤ g := μ.rowLen_anti 6 7 (by omega)
  have hgf : g ≤ f := μ.rowLen_anti 5 6 (by omega)
  have hfe : f ≤ e := μ.rowLen_anti 4 5 (by omega)
  have hed : e ≤ d := μ.rowLen_anti 3 4 (by omega)
  have hdc : d ≤ c := μ.rowLen_anti 2 3 (by omega)
  have hcb : c ≤ b := μ.rowLen_anti 1 2 (by omega)
  have hba : b ≤ a := μ.rowLen_anti 0 1 (by omega)
  have hbot : isCorner μ (8, j - 1) := nineRow_corner_bot h9 h8
  have hcard : (μ.card : ℚ) = (a : ℚ) + b + c + d + e + f + g + k + j := by
    exact_mod_cast nineRow_card h9
  rw [hcard]
  let ratio : ℕ × ℕ → ℚ := fun x =>
    if hx : isCorner μ x then (hookProd μ : ℚ) / hookProd (removeCorner μ x hx) else 0
  have hconvert : ∑ cc ∈ (corners μ).attach,
        ((hookProd μ : ℚ) / hookProd (removeCorner μ cc.val (mem_corners.mp cc.prop))) =
      ∑ x ∈ corners μ, ratio x := by
    rw [← Finset.sum_attach (f := ratio)]
    apply Finset.sum_congr rfl
    intro cx _; exact dif_pos (mem_corners.mp cx.2)
  have hsub : corners μ ⊆
      ({(8, j - 1), (7, k - 1), (6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1),
        (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases nineRow_corner_cases h9 h8 (mem_corners.mp hx) with
      heq | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩ | ⟨heq, _⟩
    · left; exact heq
    · right; left; exact heq
    · right; right; left; exact heq
    · right; right; right; left; exact heq
    · right; right; right; right; left; exact heq
    · right; right; right; right; right; left; exact heq
    · right; right; right; right; right; right; left; exact heq
    · right; right; right; right; right; right; right; left; exact heq
    · right; right; right; right; right; right; right; right; exact heq
  have hext : ∑ x ∈ corners μ, ratio x =
      ∑ x ∈ ({(8, j - 1), (7, k - 1), (6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1),
               (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)), ratio x := by
    apply Finset.sum_subset hsub
    intro x _ hxnc; exact dif_neg (mt mem_corners.mpr hxnc)
  -- Compute ratio for corner (8, j-1) [always present]
  have hR8 : ratio (8, j - 1) =
      (j : ℚ) *
      ((k : ℚ) - j + 2) / ((k : ℚ) - j + 1) *
      ((g : ℚ) - j + 3) / ((g : ℚ) - j + 2) *
      ((f : ℚ) - j + 4) / ((f : ℚ) - j + 3) *
      ((e : ℚ) - j + 5) / ((e : ℚ) - j + 4) *
      ((d : ℚ) - j + 6) / ((d : ℚ) - j + 5) *
      ((c : ℚ) - j + 7) / ((c : ℚ) - j + 6) *
      ((b : ℚ) - j + 8) / ((b : ℚ) - j + 7) *
      ((a : ℚ) - j + 9) / ((a : ℚ) - j + 8) := by
    simp only [ratio, dif_pos hbot]
    rw [hookProd_ratio_formula hbot]
    simp only [Prod.fst, Prod.snd]
    rw [nineRow_arm_row8 μ h9 hbot]
    have hj1 : j - 1 < j := Nat.sub_lt h8 Nat.one_pos
    have hmem0 : (0, j - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem1 : (1, j - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem2 : (2, j - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem3 : (3, j - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem4 : (4, j - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem5 : (5, j - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem6 : (6, j - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hmem7 : (7, j - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    rw [show Finset.range 8 = {0, 1, 2, 3, 4, 5, 6, 7} from by ext m; simp; omega]
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
        Finset.prod_insert (by simp), Finset.prod_insert (by simp),
        Finset.prod_insert (by simp), Finset.prod_insert (by simp),
        Finset.prod_insert (by simp), Finset.prod_singleton]
    rw [nineRow_hookLen_row0_lt h9 hmem0 hj1,
        nineRow_hookLen_row1_lt h9 hmem1 hj1,
        nineRow_hookLen_row2_lt h9 hmem2 hj1,
        nineRow_hookLen_row3_lt h9 hmem3 hj1,
        nineRow_hookLen_row4_lt h9 hmem4 hj1,
        nineRow_hookLen_row5_lt h9 hmem5 hj1,
        nineRow_hookLen_row6_lt h9 hmem6 hj1,
        nineRow_hookLen_row7_lt h9 hmem7 hj1]
    push_cast [Nat.cast_sub (show 1 ≤ j from h8),
               Nat.cast_sub (show j - 1 ≤ a by omega),
               Nat.cast_sub (show j - 1 ≤ b by omega),
               Nat.cast_sub (show j - 1 ≤ c by omega),
               Nat.cast_sub (show j - 1 ≤ d by omega),
               Nat.cast_sub (show j - 1 ≤ e by omega),
               Nat.cast_sub (show j - 1 ≤ f by omega),
               Nat.cast_sub (show j - 1 ≤ g by omega),
               Nat.cast_sub (show j - 1 ≤ k by omega)]
    ring
  -- Compute ratio for corner (7, k-1) [when k > j]
  have hR7 : ratio (7, k - 1) =
      ((k : ℚ) + 1) * ((k : ℚ) - j) / ((k : ℚ) - j + 1) *
      ((g : ℚ) - k + 2) / ((g : ℚ) - k + 1) *
      ((f : ℚ) - k + 3) / ((f : ℚ) - k + 2) *
      ((e : ℚ) - k + 4) / ((e : ℚ) - k + 3) *
      ((d : ℚ) - k + 5) / ((d : ℚ) - k + 4) *
      ((c : ℚ) - k + 6) / ((c : ℚ) - k + 5) *
      ((b : ℚ) - k + 7) / ((b : ℚ) - k + 6) *
      ((a : ℚ) - k + 8) / ((a : ℚ) - k + 7) := by
    by_cases hjk' : j < k
    · have hmid : isCorner μ (7, k - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [nineRow_arm_row7 h9 hjk']
      have hk1 : k - 1 < k := Nat.sub_lt (by omega) Nat.one_pos
      have hjk1 : j ≤ k - 1 := by omega
      have hmem0 : (0, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem3 : (3, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem4 : (4, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem5 : (5, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem6 : (6, k - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 7 = {0, 1, 2, 3, 4, 5, 6} from by ext m; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [nineRow_hookLen_row0_mid1 h9 hmem0 hjk1 (by omega),
          nineRow_hookLen_row1_mid1 h9 hmem1 hjk1 (by omega),
          nineRow_hookLen_row2_mid1 h9 hmem2 hjk1 (by omega),
          nineRow_hookLen_row3_mid1 h9 hmem3 hjk1 (by omega),
          nineRow_hookLen_row4_mid1 h9 hmem4 hjk1 (by omega),
          nineRow_hookLen_row5_mid1 h9 hmem5 hjk1 (by omega),
          nineRow_hookLen_row6_mid1 h9 hmem6 hjk1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ k by omega),
                 Nat.cast_sub (show k - 1 ≤ a by omega),
                 Nat.cast_sub (show k - 1 ≤ b by omega),
                 Nat.cast_sub (show k - 1 ≤ c by omega),
                 Nat.cast_sub (show k - 1 ≤ d by omega),
                 Nat.cast_sub (show k - 1 ≤ e by omega),
                 Nat.cast_sub (show k - 1 ≤ f by omega),
                 Nat.cast_sub (show k - 1 ≤ g by omega),
                 Nat.cast_sub hjk'.le]
      ring
    · have hjk_eq : k = j := Nat.le_antisymm (not_lt.mp hjk') hjk
      have hnotcorner : ¬ isCorner μ (7, k - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (k : ℚ) - j = 0 := by rw [hjk_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (6, g-1) [when g > k]
  have hR6 : ratio (6, g - 1) =
      ((g : ℚ) + 2) * ((g : ℚ) - j + 1) * ((g : ℚ) - k) /
      (((g : ℚ) - j + 2) * ((g : ℚ) - k + 1)) *
      ((f : ℚ) - g + 2) / ((f : ℚ) - g + 1) *
      ((e : ℚ) - g + 3) / ((e : ℚ) - g + 2) *
      ((d : ℚ) - g + 4) / ((d : ℚ) - g + 3) *
      ((c : ℚ) - g + 5) / ((c : ℚ) - g + 4) *
      ((b : ℚ) - g + 6) / ((b : ℚ) - g + 5) *
      ((a : ℚ) - g + 7) / ((a : ℚ) - g + 6) := by
    by_cases hkg' : k < g
    · have hmid : isCorner μ (6, g - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [nineRow_arm_row6 h9 hkg']
      have hg1 : g - 1 < g := Nat.sub_lt (by omega) Nat.one_pos
      have hkg1 : k ≤ g - 1 := by omega
      have hmem0 : (0, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem3 : (3, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem4 : (4, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem5 : (5, g - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 6 = {0, 1, 2, 3, 4, 5} from by ext m; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [nineRow_hookLen_row0_mid2 h9 hmem0 hkg1 (by omega),
          nineRow_hookLen_row1_mid2 h9 hmem1 hkg1 (by omega),
          nineRow_hookLen_row2_mid2 h9 hmem2 hkg1 (by omega),
          nineRow_hookLen_row3_mid2 h9 hmem3 hkg1 (by omega),
          nineRow_hookLen_row4_mid2 h9 hmem4 hkg1 (by omega),
          nineRow_hookLen_row5_mid2 h9 hmem5 hkg1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ g by omega),
                 Nat.cast_sub (show g - 1 ≤ a by omega),
                 Nat.cast_sub (show g - 1 ≤ b by omega),
                 Nat.cast_sub (show g - 1 ≤ c by omega),
                 Nat.cast_sub (show g - 1 ≤ d by omega),
                 Nat.cast_sub (show g - 1 ≤ e by omega),
                 Nat.cast_sub (show g - 1 ≤ f by omega),
                 Nat.cast_sub hkg'.le, Nat.cast_sub hjk]
      ring
    · have hkg_eq : g = k := Nat.le_antisymm (not_lt.mp hkg') hkg
      have hnotcorner : ¬ isCorner μ (6, g - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (g : ℚ) - k = 0 := by rw [hkg_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (5, f-1) [when f > g]
  have hR5 : ratio (5, f - 1) =
      ((f : ℚ) + 3) * ((f : ℚ) - j + 2) * ((f : ℚ) - k + 1) * ((f : ℚ) - g) /
      (((f : ℚ) - j + 3) * ((f : ℚ) - k + 2) * ((f : ℚ) - g + 1)) *
      ((e : ℚ) - f + 2) / ((e : ℚ) - f + 1) *
      ((d : ℚ) - f + 3) / ((d : ℚ) - f + 2) *
      ((c : ℚ) - f + 4) / ((c : ℚ) - f + 3) *
      ((b : ℚ) - f + 5) / ((b : ℚ) - f + 4) *
      ((a : ℚ) - f + 6) / ((a : ℚ) - f + 5) := by
    by_cases hgf' : g < f
    · have hmid : isCorner μ (5, f - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [nineRow_arm_row5 h9 hgf']
      have hf1 : f - 1 < f := Nat.sub_lt (by omega) Nat.one_pos
      have hgf1 : g ≤ f - 1 := by omega
      have hmem0 : (0, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem3 : (3, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem4 : (4, f - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 5 = {0, 1, 2, 3, 4} from by ext m; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [nineRow_hookLen_row0_mid3 h9 hmem0 hgf1 (by omega),
          nineRow_hookLen_row1_mid3 h9 hmem1 hgf1 (by omega),
          nineRow_hookLen_row2_mid3 h9 hmem2 hgf1 (by omega),
          nineRow_hookLen_row3_mid3 h9 hmem3 hgf1 (by omega),
          nineRow_hookLen_row4_mid3 h9 hmem4 hgf1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ f by omega),
                 Nat.cast_sub (show f - 1 ≤ a by omega),
                 Nat.cast_sub (show f - 1 ≤ b by omega),
                 Nat.cast_sub (show f - 1 ≤ c by omega),
                 Nat.cast_sub (show f - 1 ≤ d by omega),
                 Nat.cast_sub (show f - 1 ≤ e by omega),
                 Nat.cast_sub hgf'.le, Nat.cast_sub hkg, Nat.cast_sub hjk]
      ring
    · have hgf_eq : f = g := Nat.le_antisymm (not_lt.mp hgf') hgf
      have hnotcorner : ¬ isCorner μ (5, f - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (f : ℚ) - g = 0 := by rw [hgf_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (4, e-1) [when e > f]
  have hR4 : ratio (4, e - 1) =
      ((e : ℚ) + 4) * ((e : ℚ) - j + 3) * ((e : ℚ) - k + 2) * ((e : ℚ) - g + 1) *
      ((e : ℚ) - f) /
      (((e : ℚ) - j + 4) * ((e : ℚ) - k + 3) * ((e : ℚ) - g + 2) * ((e : ℚ) - f + 1)) *
      ((d : ℚ) - e + 2) / ((d : ℚ) - e + 1) *
      ((c : ℚ) - e + 3) / ((c : ℚ) - e + 2) *
      ((b : ℚ) - e + 4) / ((b : ℚ) - e + 3) *
      ((a : ℚ) - e + 5) / ((a : ℚ) - e + 4) := by
    by_cases hfe' : f < e
    · have hmid : isCorner μ (4, e - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [nineRow_arm_row4 h9 hfe']
      have he1 : e - 1 < e := Nat.sub_lt (by omega) Nat.one_pos
      have hfe1 : f ≤ e - 1 := by omega
      have hmem0 : (0, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem3 : (3, e - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 4 = {0, 1, 2, 3} from by ext m; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
          Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [nineRow_hookLen_row0_mid4 h9 hmem0 hfe1 (by omega),
          nineRow_hookLen_row1_mid4 h9 hmem1 hfe1 (by omega),
          nineRow_hookLen_row2_mid4 h9 hmem2 hfe1 (by omega),
          nineRow_hookLen_row3_mid4 h9 hmem3 hfe1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ e by omega),
                 Nat.cast_sub (show e - 1 ≤ a by omega),
                 Nat.cast_sub (show e - 1 ≤ b by omega),
                 Nat.cast_sub (show e - 1 ≤ c by omega),
                 Nat.cast_sub (show e - 1 ≤ d by omega),
                 Nat.cast_sub hfe'.le, Nat.cast_sub hgf, Nat.cast_sub hkg, Nat.cast_sub hjk]
      ring
    · have hfe_eq : e = f := Nat.le_antisymm (not_lt.mp hfe') hfe
      have hnotcorner : ¬ isCorner μ (4, e - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (e : ℚ) - f = 0 := by rw [hfe_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (3, d-1) [when d > e]
  have hR3 : ratio (3, d - 1) =
      ((d : ℚ) + 5) * ((d : ℚ) - j + 4) * ((d : ℚ) - k + 3) * ((d : ℚ) - g + 2) *
      ((d : ℚ) - f + 1) * ((d : ℚ) - e) /
      (((d : ℚ) - j + 5) * ((d : ℚ) - k + 4) * ((d : ℚ) - g + 3) * ((d : ℚ) - f + 2) *
       ((d : ℚ) - e + 1)) *
      ((c : ℚ) - d + 2) / ((c : ℚ) - d + 1) *
      ((b : ℚ) - d + 3) / ((b : ℚ) - d + 2) *
      ((a : ℚ) - d + 4) / ((a : ℚ) - d + 3) := by
    by_cases hed' : e < d
    · have hmid : isCorner μ (3, d - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [nineRow_arm_row3 h9 hed']
      have hd1 : d - 1 < d := Nat.sub_lt (by omega) Nat.one_pos
      have hed1 : e ≤ d - 1 := by omega
      have hmem0 : (0, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem2 : (2, d - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 3 = {0, 1, 2} from by ext m; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [nineRow_hookLen_row0_mid5 h9 hmem0 hed1 (by omega),
          nineRow_hookLen_row1_mid5 h9 hmem1 hed1 (by omega),
          nineRow_hookLen_row2_mid5 h9 hmem2 hed1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ d by omega),
                 Nat.cast_sub (show d - 1 ≤ a by omega),
                 Nat.cast_sub (show d - 1 ≤ b by omega),
                 Nat.cast_sub (show d - 1 ≤ c by omega),
                 Nat.cast_sub hed'.le, Nat.cast_sub hfe, Nat.cast_sub hgf,
                 Nat.cast_sub hkg, Nat.cast_sub hjk]
      ring
    · have hed_eq : d = e := Nat.le_antisymm (not_lt.mp hed') hed
      have hnotcorner : ¬ isCorner μ (3, d - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (d : ℚ) - e = 0 := by rw [hed_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (2, c-1) [when c > d]
  have hR2 : ratio (2, c - 1) =
      ((c : ℚ) + 6) * ((c : ℚ) - j + 5) * ((c : ℚ) - k + 4) * ((c : ℚ) - g + 3) *
      ((c : ℚ) - f + 2) * ((c : ℚ) - e + 1) * ((c : ℚ) - d) /
      (((c : ℚ) - j + 6) * ((c : ℚ) - k + 5) * ((c : ℚ) - g + 4) * ((c : ℚ) - f + 3) *
       ((c : ℚ) - e + 2) * ((c : ℚ) - d + 1)) *
      ((b : ℚ) - c + 2) / ((b : ℚ) - c + 1) *
      ((a : ℚ) - c + 3) / ((a : ℚ) - c + 2) := by
    by_cases hdc' : d < c
    · have hmid : isCorner μ (2, c - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [nineRow_arm_row2 h9 hdc']
      have hc1 : c - 1 < c := Nat.sub_lt (by omega) Nat.one_pos
      have hdc1 : d ≤ c - 1 := by omega
      have hmem0 : (0, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hmem1 : (1, c - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [show Finset.range 2 = {0, 1} from by ext m; simp; omega]
      rw [Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [nineRow_hookLen_row0_mid6 h9 hmem0 hdc1 (by omega),
          nineRow_hookLen_row1_mid6 h9 hmem1 hdc1 (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ c by omega),
                 Nat.cast_sub (show c - 1 ≤ a by omega),
                 Nat.cast_sub (show c - 1 ≤ b by omega),
                 Nat.cast_sub hdc'.le, Nat.cast_sub hed, Nat.cast_sub hfe,
                 Nat.cast_sub hgf, Nat.cast_sub hkg, Nat.cast_sub hjk]
      ring
    · have hdc_eq : c = d := Nat.le_antisymm (not_lt.mp hdc') hdc
      have hnotcorner : ¬ isCorner μ (2, c - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (c : ℚ) - d = 0 := by rw [hdc_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (1, b-1) [when b > c]
  have hR1 : ratio (1, b - 1) =
      ((b : ℚ) + 7) * ((b : ℚ) - j + 6) * ((b : ℚ) - k + 5) * ((b : ℚ) - g + 4) *
      ((b : ℚ) - f + 3) * ((b : ℚ) - e + 2) * ((b : ℚ) - d + 1) * ((b : ℚ) - c) /
      (((b : ℚ) - j + 7) * ((b : ℚ) - k + 6) * ((b : ℚ) - g + 5) * ((b : ℚ) - f + 4) *
       ((b : ℚ) - e + 3) * ((b : ℚ) - d + 2) * ((b : ℚ) - c + 1)) *
      ((a : ℚ) - b + 2) / ((a : ℚ) - b + 1) := by
    by_cases hcb' : c < b
    · have hmid : isCorner μ (1, b - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos hmid]
      rw [hookProd_ratio_formula hmid]
      simp only [Prod.fst, Prod.snd]
      rw [nineRow_arm_row1 h9 hcb']
      have hmem0 : (0, b - 1) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      rw [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
      rw [nineRow_hookLen_row0_mid7 h9 hmem0 (by omega) (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ b by omega),
                 Nat.cast_sub (show b - 1 ≤ a by omega),
                 Nat.cast_sub hcb'.le, Nat.cast_sub hdc, Nat.cast_sub hed,
                 Nat.cast_sub hfe, Nat.cast_sub hgf, Nat.cast_sub hkg, Nat.cast_sub hjk]
      ring
    · have hcb_eq : b = c := Nat.le_antisymm (not_lt.mp hcb') hcb
      have hnotcorner : ¬ isCorner μ (1, b - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (b : ℚ) - c = 0 := by rw [hcb_eq]; ring
      rw [this]; ring
  -- Compute ratio for corner (0, a-1) [when a > b]
  have hR0 : ratio (0, a - 1) =
      ((a : ℚ) + 8) * ((a : ℚ) - j + 7) * ((a : ℚ) - k + 6) * ((a : ℚ) - g + 5) *
      ((a : ℚ) - f + 4) * ((a : ℚ) - e + 3) * ((a : ℚ) - d + 2) *
      ((a : ℚ) - c + 1) * ((a : ℚ) - b) /
      (((a : ℚ) - j + 8) * ((a : ℚ) - k + 7) * ((a : ℚ) - g + 6) * ((a : ℚ) - f + 5) *
       ((a : ℚ) - e + 4) * ((a : ℚ) - d + 3) * ((a : ℚ) - c + 2) *
       ((a : ℚ) - b + 1)) := by
    by_cases hab' : b < a
    · have htop : isCorner μ (0, a - 1) := by
        refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega), ?_, ?_⟩
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
        · intro h; exact absurd (YoungDiagram.mem_iff_lt_rowLen.mp h) (by omega)
      simp only [ratio, dif_pos htop]
      rw [hookProd_ratio_formula htop]
      simp only [Prod.fst, Prod.snd, Finset.prod_range_zero, mul_one]
      rw [nineRow_arm_row0 h9 h8 hab']
      push_cast [Nat.cast_sub hab'.le, Nat.cast_sub hcb, Nat.cast_sub hdc,
                 Nat.cast_sub hed, Nat.cast_sub hfe, Nat.cast_sub hgf,
                 Nat.cast_sub hkg, Nat.cast_sub hjk]
      ring
    · have hab_eq : a = b := Nat.le_antisymm (not_lt.mp hab') hba
      have hnotcorner : ¬ isCorner μ (0, a - 1) := by
        intro ⟨_, _, hbelow⟩
        exact hbelow (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      simp only [ratio, dif_neg hnotcorner]
      have : (a : ℚ) - b = 0 := by rw [hab_eq]; ring
      rw [this]; ring
  rw [hconvert, hext]
  have hne87 : (8, j - 1) ∉ ({(7, k - 1), (6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1),
      (2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne76 : (7, k - 1) ∉ ({(6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1),
      (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne65 : (6, g - 1) ∉ ({(5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1),
      (0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne54 : (5, f - 1) ∉ ({(4, e - 1), (3, d - 1), (2, c - 1), (1, b - 1),
      (0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne43 : (4, e - 1) ∉ ({(3, d - 1), (2, c - 1), (1, b - 1), (0, a - 1)} :
      Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  have hne32 : (3, d - 1) ∉ ({(2, c - 1), (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hne21 : (2, c - 1) ∉ ({(1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) := by
    simp [Prod.mk.injEq]
  have hne10 : (1, b - 1) ∉ ({(0, a - 1)} : Finset (ℕ × ℕ)) := by simp [Prod.mk.injEq]
  rw [show ({(8, j - 1), (7, k - 1), (6, g - 1), (5, f - 1), (4, e - 1), (3, d - 1), (2, c - 1),
              (1, b - 1), (0, a - 1)} : Finset (ℕ × ℕ)) =
      insert (8, j - 1) (insert (7, k - 1) (insert (6, g - 1) (insert (5, f - 1)
        (insert (4, e - 1) (insert (3, d - 1) (insert (2, c - 1)
          (insert (1, b - 1) {(0, a - 1)}))))))) from rfl,
      Finset.sum_insert hne87, Finset.sum_insert hne76, Finset.sum_insert hne65,
      Finset.sum_insert hne54, Finset.sum_insert hne43, Finset.sum_insert hne32,
      Finset.sum_insert hne21, Finset.sum_insert hne10, Finset.sum_singleton,
      hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, hR0]
  -- Non-zero denominators
  have hne_kj1 : (k : ℚ) - j + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < k - j + 1 by omega)
  have hne_gj2 : (g : ℚ) - j + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < g - j + 2 by omega)
  have hne_fj3 : (f : ℚ) - j + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < f - j + 3 by omega)
  have hne_ej4 : (e : ℚ) - j + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - j + 4 by omega)
  have hne_dj5 : (d : ℚ) - j + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - j + 5 by omega)
  have hne_cj6 : (c : ℚ) - j + 6 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - j + 6 by omega)
  have hne_bj7 : (b : ℚ) - j + 7 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - j + 7 by omega)
  have hne_aj8 : (a : ℚ) - j + 8 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - j + 8 by omega)
  have hne_gk1 : (g : ℚ) - k + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < g - k + 1 by omega)
  have hne_fk2 : (f : ℚ) - k + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < f - k + 2 by omega)
  have hne_ek3 : (e : ℚ) - k + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - k + 3 by omega)
  have hne_dk4 : (d : ℚ) - k + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - k + 4 by omega)
  have hne_ck5 : (c : ℚ) - k + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - k + 5 by omega)
  have hne_bk6 : (b : ℚ) - k + 6 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - k + 6 by omega)
  have hne_ak7 : (a : ℚ) - k + 7 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - k + 7 by omega)
  have hne_fg1 : (f : ℚ) - g + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < f - g + 1 by omega)
  have hne_eg2 : (e : ℚ) - g + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - g + 2 by omega)
  have hne_dg3 : (d : ℚ) - g + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - g + 3 by omega)
  have hne_cg4 : (c : ℚ) - g + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - g + 4 by omega)
  have hne_bg5 : (b : ℚ) - g + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - g + 5 by omega)
  have hne_ag6 : (a : ℚ) - g + 6 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - g + 6 by omega)
  have hne_ef1 : (e : ℚ) - f + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < e - f + 1 by omega)
  have hne_df2 : (d : ℚ) - f + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - f + 2 by omega)
  have hne_cf3 : (c : ℚ) - f + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - f + 3 by omega)
  have hne_bf4 : (b : ℚ) - f + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - f + 4 by omega)
  have hne_af5 : (a : ℚ) - f + 5 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - f + 5 by omega)
  have hne_de1 : (d : ℚ) - e + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < d - e + 1 by omega)
  have hne_ce2 : (c : ℚ) - e + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - e + 2 by omega)
  have hne_be3 : (b : ℚ) - e + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - e + 3 by omega)
  have hne_ae4 : (a : ℚ) - e + 4 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - e + 4 by omega)
  have hne_cd1 : (c : ℚ) - d + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < c - d + 1 by omega)
  have hne_bd2 : (b : ℚ) - d + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - d + 2 by omega)
  have hne_ad3 : (a : ℚ) - d + 3 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - d + 3 by omega)
  have hne_bc1 : (b : ℚ) - c + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < b - c + 1 by omega)
  have hne_ac2 : (a : ℚ) - c + 2 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - c + 2 by omega)
  have hne_ab1 : (a : ℚ) - b + 1 ≠ 0 := by exact_mod_cast (show (0 : ℤ) < a - b + 1 by omega)
  push_cast [Nat.cast_sub hjk, Nat.cast_sub hkg, Nat.cast_sub hgf, Nat.cast_sub hfe,
             Nat.cast_sub hed, Nat.cast_sub hdc, Nat.cast_sub hcb, Nat.cast_sub hba,
             Nat.cast_sub (show j ≤ g by omega), Nat.cast_sub (show j ≤ f by omega),
             Nat.cast_sub (show j ≤ e by omega), Nat.cast_sub (show j ≤ d by omega),
             Nat.cast_sub (show j ≤ c by omega), Nat.cast_sub (show j ≤ b by omega),
             Nat.cast_sub (show j ≤ a by omega),
             Nat.cast_sub (show k ≤ f by omega), Nat.cast_sub (show k ≤ e by omega),
             Nat.cast_sub (show k ≤ d by omega), Nat.cast_sub (show k ≤ c by omega),
             Nat.cast_sub (show k ≤ b by omega), Nat.cast_sub (show k ≤ a by omega),
             Nat.cast_sub (show g ≤ e by omega), Nat.cast_sub (show g ≤ d by omega),
             Nat.cast_sub (show g ≤ c by omega), Nat.cast_sub (show g ≤ b by omega),
             Nat.cast_sub (show g ≤ a by omega), Nat.cast_sub (show f ≤ d by omega),
             Nat.cast_sub (show f ≤ c by omega), Nat.cast_sub (show f ≤ b by omega),
             Nat.cast_sub (show f ≤ a by omega), Nat.cast_sub (show e ≤ c by omega),
             Nat.cast_sub (show e ≤ b by omega), Nat.cast_sub (show e ≤ a by omega),
             Nat.cast_sub (show d ≤ b by omega), Nat.cast_sub (show d ≤ a by omega),
             Nat.cast_sub (show c ≤ a by omega)]
  field_simp [hne_kj1, hne_gj2, hne_fj3, hne_ej4, hne_dj5, hne_cj6, hne_bj7, hne_aj8,
              hne_gk1, hne_fk2, hne_ek3, hne_dk4, hne_ck5, hne_bk6, hne_ak7,
              hne_fg1, hne_eg2, hne_dg3, hne_cg4, hne_bg5, hne_ag6,
              hne_ef1, hne_df2, hne_cf3, hne_bf4, hne_af5,
              hne_de1, hne_ce2, hne_be3, hne_ae4,
              hne_cd1, hne_bd2, hne_ad3, hne_bc1, hne_ac2, hne_ab1]
  ring

/-! ## PART XXIV: Transpose Duality — hook_walk_identity for ≤9-column Young diagrams

For any Young diagram μ with ≤9 columns (colLen 9 = 0), its transpose μᵀ has ≤9 rows (rowLen 9 = 0).
Since hook_walk_identity is proved for all ≤9-row shapes (PARTS XIV–XXIII), we derive it for μ
from μᵀ via the bijection c ↦ c.swap on corners.

This reduces the remaining sorry from {≥10 rows, ≥3 cols} to {≥10 rows, ≥10 cols}. -/

-- A. Extract the cells-transpose identity as a reusable lemma
private lemma cells_transpose_eq_image_swap (μ : YoungDiagram) :
    μ.transpose.cells = μ.cells.image Prod.swap := by
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Finset.mem_image, Prod.exists]
  exact ⟨fun h => ⟨j, i, h, rfl⟩, fun ⟨a, b, hab, heq⟩ => by
    simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; exact hab⟩

-- B. isCorner is transpose-symmetric: isCorner μᵀ c ↔ isCorner μ c.swap
private lemma isCorner_transpose_iff (μ : YoungDiagram) (c : ℕ × ℕ) :
    isCorner μ.transpose c ↔ isCorner μ c.swap := by
  simp only [isCorner, YoungDiagram.mem_transpose, Prod.swap_fst, Prod.swap_snd]
  constructor
  · rintro ⟨hmem, h1, h2⟩
    exact ⟨hmem,
           fun h => h1 (YoungDiagram.mem_transpose.mpr h),
           fun h => h2 (YoungDiagram.mem_transpose.mpr h)⟩
  · rintro ⟨hmem, h1, h2⟩
    exact ⟨hmem,
           fun h => h1 (YoungDiagram.mem_transpose.mp h),
           fun h => h2 (YoungDiagram.mem_transpose.mp h)⟩

-- C. corners μᵀ = (corners μ).image Prod.swap
private lemma corners_image_swap (μ : YoungDiagram) :
    corners μ.transpose = (corners μ).image Prod.swap := by
  ext c
  simp only [mem_corners, Finset.mem_image]
  constructor
  · intro hc
    exact ⟨c.swap, (isCorner_transpose_iff μ c.swap).mp (Prod.swap_swap c ▸ hc),
           Prod.swap_swap c⟩
  · rintro ⟨d, hd, rfl⟩
    exact (isCorner_transpose_iff μ d).mpr hd

-- D. removeCorner μᵀ c.swap = (removeCorner μ c).transpose (as YoungDiagrams)
private lemma removeCorner_transpose_eq (μ : YoungDiagram) (c : ℕ × ℕ) (hc : isCorner μ c) :
    removeCorner μ.transpose c.swap ((isCorner_transpose_iff μ c.swap).mpr (by rwa [Prod.swap_swap])) =
    (removeCorner μ c hc).transpose := by
  ext x
  constructor
  · intro hx
    rw [mem_removeCorner] at hx
    rw [YoungDiagram.mem_transpose, mem_removeCorner]
    exact ⟨YoungDiagram.mem_transpose.mp hx.1,
           fun h => hx.2 ((Prod.swap_swap x).symm.trans (congrArg Prod.swap h))⟩
  · intro hx
    rw [YoungDiagram.mem_transpose, mem_removeCorner] at hx
    rw [mem_removeCorner]
    exact ⟨YoungDiagram.mem_transpose.mpr hx.1,
           fun h => hx.2 ((congrArg Prod.swap h).trans (Prod.swap_swap c))⟩

-- E. hookProd is the same for removeCorner μᵀ c.swap and removeCorner μ c
private lemma hookProd_removeCorner_transpose (μ : YoungDiagram) (c : ℕ × ℕ) (hc : isCorner μ c) :
    hookProd (removeCorner μ.transpose c.swap
      ((isCorner_transpose_iff μ c.swap).mpr (by rwa [Prod.swap_swap]))) =
    hookProd (removeCorner μ c hc) := by
  rw [removeCorner_transpose_eq μ c hc]
  exact (hookProd_transpose _).symm

-- F. hook_walk_identity for μ follows from hook_walk_identity for μᵀ
--    Key: sum over corners μ reindexed via c ↦ c.swap to sum over corners μᵀ
private lemma hook_walk_identity_via_transpose (μ : YoungDiagram)
    (h_T : ∑ c ∈ (corners μ.transpose).attach,
        ((hookProd μ.transpose : ℚ) / hookProd (removeCorner μ.transpose c.val (mem_corners.mp c.prop)))
      = (μ.card : ℚ)) :
    ∑ c ∈ (corners μ).attach,
        ((hookProd μ : ℚ) / hookProd (removeCorner μ c.val (mem_corners.mp c.prop)))
      = (μ.card : ℚ) := by
  rw [hookProd_transpose] at h_T
  -- h_T: ∑ c ∈ (corners μᵀ).attach, hookProd μ / hookProd(removeCorner μᵀ c) = μ.card
  -- Goal: ∑ c ∈ (corners μ).attach, hookProd μ / hookProd(removeCorner μ c) = μ.card
  calc ∑ c ∈ (corners μ).attach,
          ((hookProd μ : ℚ) / hookProd (removeCorner μ c.val (mem_corners.mp c.prop)))
      -- Reindex: c ↦ c.swap bijection on corners
      = ∑ d ∈ (corners μ.transpose).attach,
          ((hookProd μ : ℚ) / hookProd (removeCorner μ.transpose d.val (mem_corners.mp d.prop))) := by
        -- Use bijection i: corners μ → corners μᵀ, c ↦ c.swap
        apply Finset.sum_nbij'
            (fun ⟨c, hc⟩ => ⟨c.swap,
                mem_corners.mpr ((isCorner_transpose_iff μ c.swap).mpr
                  (Prod.swap_swap c ▸ mem_corners.mp hc))⟩)
            (fun ⟨d, hd⟩ => ⟨d.swap,
                mem_corners.mpr ((isCorner_transpose_iff μ d).mp (mem_corners.mp hd))⟩)
        · intro _ _; exact Finset.mem_attach _ _
        · intro _ _; exact Finset.mem_attach _ _
        · intro _ _; exact Subtype.ext (Prod.swap_swap _)
        · intro _ _; exact Subtype.ext (Prod.swap_swap _)
        · intro ⟨c, hc⟩ _
          -- f(c) = hookProd μ / hookProd(removeCorner μ c)
          -- g(c.swap) = hookProd μ / hookProd(removeCorner μᵀ c.swap)
          -- These are equal by hookProd_removeCorner_transpose
          congr 1
          exact (hookProd_removeCorner_transpose μ c (mem_corners.mp hc)).symm
    _ = (μ.card : ℚ) := h_T

-- G. Dispatcher for ≤9-row shapes (consolidating PARTS XIV-XXIII for μ.transpose use)
private lemma hook_walk_identity_le9rows (μ : YoungDiagram) (h9 : μ.rowLen 9 = 0)
    (hpos : 0 < μ.card) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / hookProd (removeCorner μ c.val (mem_corners.mp c.prop)))
    = (μ.card : ℚ) := by
  by_cases h2 : μ.rowLen 2 = 0
  · exact hook_walk_identity_atMostTwoRows μ h2 hpos
  · by_cases hghook : ∃ (a b : ℕ) (ha : 0 < a) (hb : 0 < b), μ = gHookYD a b ha
    · obtain ⟨a, b, ha, hb, rfl⟩ := hghook
      exact hook_walk_identity_gHookYD a b ha hb
    · by_cases h2c : μ.colLen 2 = 0
      · exact hook_walk_identity_atMostTwoCols μ h2c hpos
      · by_cases h3 : μ.rowLen 3 = 0
        · exact hook_walk_identity_threeRow μ h3 (Nat.pos_of_ne_zero h2)
        · by_cases h4 : μ.rowLen 4 = 0
          · exact hook_walk_identity_fourRow μ h4 (Nat.pos_of_ne_zero h3)
          · by_cases h5 : μ.rowLen 5 = 0
            · exact hook_walk_identity_fiveRow μ h5 (Nat.pos_of_ne_zero h4)
            · by_cases h6 : μ.rowLen 6 = 0
              · exact hook_walk_identity_sixRow μ h6 (Nat.pos_of_ne_zero h5)
              · by_cases h7 : μ.rowLen 7 = 0
                · exact hook_walk_identity_sevenRow μ h7 (Nat.pos_of_ne_zero h6)
                · by_cases h8 : μ.rowLen 8 = 0
                  · exact hook_walk_identity_eightRow μ h8 (Nat.pos_of_ne_zero h7)
                  · exact hook_walk_identity_nineRow μ h9 (Nat.pos_of_ne_zero h8)

-- H. hook_walk_identity for ≤9-column shapes (via transpose to ≤9-row)
lemma hook_walk_identity_atMostNineCols (μ : YoungDiagram) (h9c : μ.colLen 9 = 0)
    (hpos : 0 < μ.card) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / hookProd (removeCorner μ c.val (mem_corners.mp c.prop)))
    = (μ.card : ℚ) := by
  apply hook_walk_identity_via_transpose
  -- μᵀ has ≤9 rows
  have h9t : μ.transpose.rowLen 9 = 0 := by rw [YoungDiagram.rowLen_transpose]; exact h9c
  have hpost : 0 < μ.transpose.card := by rwa [card_transpose]
  exact hook_walk_identity_le9rows μ.transpose h9t hpost

-- ============================================================
-- PART XXVI: GNW Hook Walk Infrastructure (Greene-Nijenhuis-Wilf 1979)
-- ============================================================
/-
  The Greene-Nijenhuis-Wilf 1979 random-walk proof of the hook-walk identity for
  non-rectangular Young diagrams with ≥10 rows and ≥10 cols.

  GNW walk from x ∈ μ:
  - If x is a corner: stop.
  - Otherwise: pick uniformly from strictHookCells(x) (arm + leg cells strictly
    beyond x) and recurse.

  Key identity: Σ_{c ∈ corners μ} gnwProb(μ,c,hookLen(x),x) = 1 for all x ∈ μ.
  GNW KEY: Σ_{x ∈ μ} gnwProb(μ,c,hookLen(x),x) = hookProd(μ) / hookProd(μ\c).

  Hook-walk identity: swap the double sum to obtain μ.card.
-/

/-- Strict hook cells beyond (i,j): arm cells (i,s) with s > j, and leg cells
    (r,j) with r > i. These are the cells the GNW walk can jump to from (i,j).
    Card = hookLength μ i j - 1. -/
private def strictHookCells (μ : YoungDiagram) (i j : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico (j + 1) (μ.rowLen i)).image (Prod.mk i) ∪
  (Finset.Ico (i + 1) (μ.colLen j)).image (fun r => (r, j))

/-- Every cell in strictHookCells μ i j is a member of μ. -/
private lemma strictHookCells_mem {μ : YoungDiagram} {i j : ℕ} {y : ℕ × ℕ}
    (hy : y ∈ strictHookCells μ i j) : y ∈ μ := by
  simp only [strictHookCells, mem_union, mem_image, mem_Ico] at hy
  rcases hy with ⟨s, ⟨_, hsr⟩, rfl⟩ | ⟨r, ⟨_, hrc⟩, rfl⟩
  · exact YoungDiagram.mem_iff_lt_rowLen.mpr hsr
  · exact YoungDiagram.mem_iff_lt_colLen.mpr hrc

/-- Cardinality of strictHookCells is hookLength - 1.
    The arm and leg image sets are disjoint (arm has first coord i; leg has first coord > i). -/
private lemma strictHookCells_card {μ : YoungDiagram} {i j : ℕ} (h : (i, j) ∈ μ) :
    (strictHookCells μ i j).card = hookLength μ i j - 1 := by
  have hrow : j < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp h
  have hcol : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp h
  have heq := hookLength_add_eq μ h
  -- Arm and leg image sets are disjoint: arm cells have first coord = i,
  -- leg cells have first coord ≥ i+1.
  have hdisj : Disjoint ((Finset.Ico (j + 1) (μ.rowLen i)).image (Prod.mk i))
                        ((Finset.Ico (i + 1) (μ.colLen j)).image (fun r => (r, j))) := by
    apply Finset.disjoint_left.mpr
    rintro x hmem_arm hmem_leg
    simp only [Finset.mem_image, Finset.mem_Ico] at hmem_arm hmem_leg
    obtain ⟨s, ⟨hjs, _⟩, rfl⟩ := hmem_arm
    obtain ⟨r, ⟨hir, _⟩, heq'⟩ := hmem_leg
    simp only [Prod.mk.injEq] at heq'
    omega
  rw [strictHookCells, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).2),
      Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).1),
      Finset.card_Ico, Finset.card_Ico]
  omega

/-- For a non-corner cell (i,j), strictHookCells is nonempty. -/
private lemma strictHookCells_nonempty {μ : YoungDiagram} {i j : ℕ}
    (hmem : (i, j) ∈ μ) (hnc : ¬isCorner μ (i, j)) :
    (strictHookCells μ i j).Nonempty := by
  -- ¬isCorner means (i,j+1) ∈ μ or (i+1,j) ∈ μ
  have hor : (i, j + 1) ∈ μ ∨ (i + 1, j) ∈ μ := by
    by_contra h
    push_neg at h
    exact hnc ⟨hmem, h.1, h.2⟩
  rcases hor with h_arm | h_leg
  · exact ⟨(i, j + 1), Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨j + 1, Finset.mem_Ico.mpr ⟨le_refl _, YoungDiagram.mem_iff_lt_rowLen.mp h_arm⟩, rfl⟩)⟩
  · exact ⟨(i + 1, j), Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨i + 1, Finset.mem_Ico.mpr ⟨le_refl _, YoungDiagram.mem_iff_lt_colLen.mp h_leg⟩, rfl⟩)⟩

/-- Each strict hook cell has strictly smaller hookLength than the base cell. -/
private lemma strictHookCells_hookLen_lt {μ : YoungDiagram} {i j : ℕ}
    (hmem : (i, j) ∈ μ) {y : ℕ × ℕ} (hy : y ∈ strictHookCells μ i j) :
    hookLength μ y.1 y.2 < hookLength μ i j := by
  have heq := hookLength_add_eq μ hmem
  simp only [strictHookCells, Finset.mem_union, Finset.mem_image, Finset.mem_Ico] at hy
  rcases hy with ⟨s, ⟨hjs, hsr⟩, rfl⟩ | ⟨r, ⟨hir, hrc⟩, rfl⟩
  · -- arm cell (i, s): s ∈ Ico (j+1) (rowLen i), so s < rowLen i → (i,s) ∈ μ
    have hs_mem : (i, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hsr
    have heq_y := hookLength_add_eq μ hs_mem
    -- colLen non-increasing: colLen s ≤ colLen j since j ≤ s
    have hcol_anti : μ.colLen s ≤ μ.colLen j := by
      have := μ.transpose.rowLen_anti j s (by omega : j ≤ s)
      rwa [YoungDiagram.rowLen_transpose, YoungDiagram.rowLen_transpose] at this
    change hookLength μ i s < hookLength μ i j; omega
  · -- leg cell (r, j): r ∈ Ico (i+1) (colLen j), so r < colLen j → (r,j) ∈ μ
    have hr_mem : (r, j) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hrc
    have heq_y := hookLength_add_eq μ hr_mem
    -- rowLen non-increasing: rowLen r ≤ rowLen i since i ≤ r
    have hrow_anti : μ.rowLen r ≤ μ.rowLen i := μ.rowLen_anti i r (by omega : i ≤ r)
    change hookLength μ r j < hookLength μ i j; omega

/-- Membership characterization for `strictHookCells`: a cell `(p, q)` is in the strict
    hook of `(i, j)` iff it is on the same row to the right (arm) or same column below
    (leg), within μ. -/
private lemma mem_strictHookCells_iff {μ : YoungDiagram} {i j p q : ℕ} :
    (p, q) ∈ strictHookCells μ i j ↔
      (p = i ∧ j < q ∧ q < μ.rowLen i) ∨ (i < p ∧ q = j ∧ p < μ.colLen j) := by
  simp only [strictHookCells, Finset.mem_union, Finset.mem_image, Finset.mem_Ico,
             Prod.mk.injEq]
  constructor
  · rintro (⟨s, ⟨hjs, hsr⟩, hps, hqs⟩ | ⟨r, ⟨hir, hrc⟩, hpr, hqr⟩)
    · exact Or.inl ⟨hps.symm, by omega, by omega⟩
    · exact Or.inr ⟨by omega, hqr.symm, by omega⟩
  · rintro (⟨hpi, hjq, hqr⟩ | ⟨hip, hqj, hpc⟩)
    · exact Or.inl ⟨q, ⟨by omega, hqr⟩, hpi.symm, rfl⟩
    · exact Or.inr ⟨p, ⟨by omega, hpc⟩, rfl, hqj.symm⟩

/-- For a corner `c'` of μ, membership in `strictHookCells μ i j` simplifies to a clean
    arm/leg disjunction (the upper bounds `c'.2 < μ.rowLen c'.1` and `c'.1 < μ.colLen c'.2`
    follow automatically from cornerhood). -/
private lemma mem_strictHookCells_of_isCorner {μ : YoungDiagram} {c' : ℕ × ℕ}
    (hc' : isCorner μ c') (i j : ℕ) :
    c' ∈ strictHookCells μ i j ↔
      (i = c'.1 ∧ j < c'.2) ∨ (i < c'.1 ∧ j = c'.2) := by
  obtain ⟨p, q⟩ := c'
  rw [mem_strictHookCells_iff]
  have hrl : μ.rowLen p = q + 1 := rowLen_of_isCorner hc'
  have hcl : μ.colLen q = p + 1 := colLen_of_isCorner hc'
  constructor
  · rintro (⟨hpi, hjq, _⟩ | ⟨hip, hqj, _⟩)
    · exact Or.inl ⟨hpi.symm, hjq⟩
    · exact Or.inr ⟨hip, hqj.symm⟩
  · rintro (⟨hip, hjq⟩ | ⟨hip, hjq⟩)
    · refine Or.inl ⟨hip.symm, hjq, ?_⟩; rw [← hip, hrl]; omega
    · refine Or.inr ⟨hip, hjq.symm, ?_⟩; rw [hjq, hcl]; omega

/-- GNW walk probability: gnwProb μ c K x = probability that a GNW walk started at
    x ends at corner c, with K as a termination bound (correct when hookLen(x) ≤ K). -/
noncomputable private def gnwProb (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ → ℕ × ℕ → ℚ
  | 0, _ => 0
  | K + 1, x =>
    if isCorner μ x then (if x = c then 1 else 0)
    else (1 / (strictHookCells μ x.1 x.2).card : ℚ) *
         ∑ y ∈ strictHookCells μ x.1 x.2, gnwProb μ c K y

/-- For any cell x ∈ μ with hookLength(x) ≤ K, the sum of gnwProb over all corners = 1.
    Proof: induction on K.
    - K = 0: vacuous (hookLen ≥ 1 contradicts hookLen ≤ 0).
    - K+1, x a corner: sum = indicator{x = c over corners} = 1 (x is the unique corner c=x).
    - K+1, x not a corner: pull (1/|H*(x)|) out, swap Σ_c Σ_{y∈H*(x)},
      apply IH to each y (hookLen y < hookLen x ≤ K+1 ⟹ hookLen y ≤ K). -/
private lemma gnwProb_sum_corners (μ : YoungDiagram) :
    ∀ K : ℕ, ∀ x : ℕ × ℕ, x ∈ μ → hookLength μ x.1 x.2 ≤ K →
      ∑ c ∈ (corners μ).attach, gnwProb μ c.val K x = 1 := by
  intro K
  induction K with
  | zero =>
    intro x _ hK
    -- hookLength ≥ 1 contradicts ≤ 0
    exact absurd hK (by have := hookLength_pos μ x.1 x.2; omega)
  | succ K ih =>
    intro x hx hK
    by_cases hcorn : isCorner μ x
    · -- Corner case: gnwProb (K+1) x = if x = c then 1 else 0
      have hxcorn : x ∈ corners μ := mem_corners.mpr hcorn
      have hfun : ∀ c ∈ (corners μ).attach, gnwProb μ c.val (K + 1) x =
                  if x = c.val then (1 : ℚ) else 0 := by
        intro c _
        have : gnwProb μ c.val (K + 1) x =
               if isCorner μ x then (if x = c.val then (1:ℚ) else 0)
               else (1 / ↑(strictHookCells μ x.1 x.2).card : ℚ) *
                    ∑ y ∈ strictHookCells μ x.1 x.2, gnwProb μ c.val K y := rfl
        rw [this, if_pos hcorn]
      rw [Finset.sum_congr rfl hfun]
      -- x appears exactly once in (corners μ).attach; all other terms are 0
      refine (Finset.sum_eq_single_of_mem ⟨x, hxcorn⟩ (Finset.mem_attach _ _) ?_).trans (by simp)
      intro c _ hne
      exact if_neg (fun h : x = c.val => hne (Subtype.ext h.symm))
    · -- Non-corner case: gnwProb (K+1) x = (1/|H*|) * Σ_{y∈H*} gnwProb K y
      have hH_ne := strictHookCells_nonempty hx hcorn
      have hcard_pos : 0 < (strictHookCells μ x.1 x.2).card := hH_ne.card_pos
      have hcard_ne : (strictHookCells μ x.1 x.2).card ≠ 0 := hcard_pos.ne'
      have hN : (↑(strictHookCells μ x.1 x.2).card : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr hcard_ne
      have hfun : ∀ c ∈ (corners μ).attach, gnwProb μ c.val (K + 1) x =
                  (1 / ↑(strictHookCells μ x.1 x.2).card : ℚ) *
                  ∑ y ∈ strictHookCells μ x.1 x.2, gnwProb μ c.val K y := by
        intro c _
        have : gnwProb μ c.val (K + 1) x =
               if isCorner μ x then (if x = c.val then (1:ℚ) else 0)
               else (1 / ↑(strictHookCells μ x.1 x.2).card : ℚ) *
                    ∑ y ∈ strictHookCells μ x.1 x.2, gnwProb μ c.val K y := rfl
        rw [this, if_neg hcorn]
      -- Factor constant out, swap sums, apply IH to each y
      rw [Finset.sum_congr rfl hfun, ← Finset.mul_sum, Finset.sum_comm]
      have hih : ∀ y ∈ strictHookCells μ x.1 x.2,
          ∑ c ∈ (corners μ).attach, gnwProb μ c.val K y = 1 := fun y hy =>
        ih y (strictHookCells_mem hy) (by have := strictHookCells_hookLen_lt hx hy; omega)
      rw [Finset.sum_congr rfl hih, Finset.sum_const_one]
      -- (1/N) * ↑N = 1
      exact one_div_mul_cancel hN

/-- For any corner c = (i,j) of μ, its hook length equals 1.
    Proof: isCorner gives rowLen i = j+1 and colLen j = i+1; hookLength_add_eq then forces hookLength = 1. -/
private lemma hookLength_isCorner_one {μ : YoungDiagram} {i j : ℕ}
    (hc : isCorner μ (i, j)) : hookLength μ i j = 1 := by
  obtain ⟨hmem, hright, hbelow⟩ := hc
  have heq := hookLength_add_eq μ hmem
  have hrow_lt : j < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have hrow_ge : ¬(j + 1 < μ.rowLen i) := fun h =>
    hright (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
  have hcol_lt : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hmem
  have hcol_ge : ¬(i + 1 < μ.colLen j) := fun h =>
    hbelow (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))
  omega

/-- GNW stability step: gnwProb (n+1) x = gnwProb n x whenever hookLength x ≤ n.
    Proved by strong induction on n: for corners, both sides are (if x=c then 1 else 0);
    for non-corners, the sums over strictHookCells agree by IH (hookLength y < hookLength x ≤ n). -/
private lemma gnwProb_step (μ : YoungDiagram) (c : ℕ × ℕ) :
    ∀ n : ℕ, ∀ x : ℕ × ℕ, x ∈ μ → hookLength μ x.1 x.2 ≤ n →
    gnwProb μ c (n + 1) x = gnwProb μ c n x := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro x hx hK
    rcases n with _ | n'
    · exact absurd hK (by have := hookLength_pos μ x.1 x.2; omega)
    · by_cases hcorn : isCorner μ x
      · simp only [gnwProb, if_pos hcorn]
      · simp only [gnwProb, if_neg hcorn]
        congr 1
        apply Finset.sum_congr rfl
        intro y hy
        have hy_mem := strictHookCells_mem hy
        have hy_lt := strictHookCells_hookLen_lt hx hy
        exact ih n' (Nat.lt_succ_self n') y hy_mem (by omega)

/-- GNW stability: gnwProb K x = gnwProb (hookLength x) x for any K ≥ hookLength x.
    Proved by induction on d = K - hookLength x, using gnwProb_step at each step. -/
private lemma gnwProb_stable (μ : YoungDiagram) (c : ℕ × ℕ) (x : ℕ × ℕ) (hx : x ∈ μ)
    (K : ℕ) (hK : hookLength μ x.1 x.2 ≤ K) :
    gnwProb μ c K x = gnwProb μ c (hookLength μ x.1 x.2) x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
  induction d with
  | zero => rfl
  | succ d ihd =>
    rw [Nat.add_succ, gnwProb_step μ c (hookLength μ x.1 x.2 + d) x hx (Nat.le_add_right _ _)]
    exact ihd

/-- Removing corner c' from μ deletes c' from the strict hook cells of every other cell.
    For x ∈ μ\c': strictHookCells (μ\c') x = strictHookCells μ x \ {c'}.

    Proof by case analysis on whether x shares a row/column with c':
    - If x.1 = c'.1 (same row, x left of c'): rowLen drops by 1, so c' is removed from arm.
    - If x.2 = c'.2 (same column, x above c'): colLen drops by 1, so c' is removed from leg.
    - Otherwise: row/col lengths unchanged, and c' was never in arm/leg of x. -/
private lemma strictHookCells_removeCorner_eq {μ : YoungDiagram} {c' : ℕ × ℕ}
    (hc' : isCorner μ c') (i j : ℕ) :
    strictHookCells (removeCorner μ c' hc') i j =
      strictHookCells μ i j \ {c'} := by
  set ν := removeCorner μ c' hc'
  ext y
  simp only [strictHookCells, Finset.mem_union, Finset.mem_image, Finset.mem_Ico,
             Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · -- (⊆) cells in strict hook of (i,j) inside ν are in strict hook inside μ and ≠ c'.
    rintro (⟨s, ⟨hjs, hsr⟩, hy_eq⟩ | ⟨r, ⟨hir, hrc⟩, hy_eq⟩)
    · subst hy_eq
      have hsν : (i, s) ∈ ν := YoungDiagram.mem_iff_lt_rowLen.mpr hsr
      have hsμ : (i, s) ∈ μ := ((mem_removeCorner hc').mp hsν).1
      have hsr_μ : s < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp hsμ
      refine ⟨Or.inl ⟨s, ⟨hjs, hsr_μ⟩, rfl⟩, ?_⟩
      intro hy_eq
      have h1 : i = c'.1 := congr_arg Prod.fst hy_eq
      have h2 : s = c'.2 := congr_arg Prod.snd hy_eq
      have hrl : ν.rowLen c'.1 = c'.2 := rowLen_removeCorner_self hc'
      rw [← h1, ← h2] at hrl
      omega
    · subst hy_eq
      have hrν : (r, j) ∈ ν := YoungDiagram.mem_iff_lt_colLen.mpr hrc
      have hrμ : (r, j) ∈ μ := ((mem_removeCorner hc').mp hrν).1
      have hrc_μ : r < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hrμ
      refine ⟨Or.inr ⟨r, ⟨hir, hrc_μ⟩, rfl⟩, ?_⟩
      intro hy_eq
      have h1 : r = c'.1 := congr_arg Prod.fst hy_eq
      have h2 : j = c'.2 := congr_arg Prod.snd hy_eq
      have hcl : ν.colLen c'.2 = c'.1 := colLen_removeCorner_self hc'
      rw [← h1, ← h2] at hcl
      omega
  · -- (⊇) cells in strict hook of (i,j) inside μ that are ≠ c' lift to ν.
    rintro ⟨h_or, hyne⟩
    rcases h_or with ⟨s, ⟨hjs, hsr⟩, hy_eq⟩ | ⟨r, ⟨hir, hrc⟩, hy_eq⟩
    · subst hy_eq
      by_cases hii' : i = c'.1
      · -- Same row as c': must have s ≠ c'.2 (else (i,s) = c') and s < rowLen μ i = c'.2 + 1.
        have hsj' : s ≠ c'.2 := fun hsj => hyne (Prod.ext hii' hsj)
        have hr_μ : μ.rowLen i = c'.2 + 1 := by
          rw [hii']; exact rowLen_of_isCorner hc'
        have hr_ν : ν.rowLen i = c'.2 := by
          rw [hii']; exact rowLen_removeCorner_self hc'
        have hs_lt : s < c'.2 := by omega
        exact Or.inl ⟨s, ⟨hjs, by rw [hr_ν]; exact hs_lt⟩, rfl⟩
      · -- Different row: rowLen unchanged.
        have hr_eq : ν.rowLen i = μ.rowLen i := rowLen_removeCorner_other hc' hii'
        exact Or.inl ⟨s, ⟨hjs, by rw [hr_eq]; exact hsr⟩, rfl⟩
    · subst hy_eq
      by_cases hjj' : j = c'.2
      · have hri' : r ≠ c'.1 := fun hri => hyne (Prod.ext hri hjj')
        have hc_μ : μ.colLen j = c'.1 + 1 := by
          rw [hjj']; exact colLen_of_isCorner hc'
        have hc_ν : ν.colLen j = c'.1 := by
          rw [hjj']; exact colLen_removeCorner_self hc'
        have hr_lt : r < c'.1 := by omega
        exact Or.inr ⟨r, ⟨hir, by rw [hc_ν]; exact hr_lt⟩, rfl⟩
      · have hc_eq : ν.colLen j = μ.colLen j := colLen_removeCorner_other hc' hjj'
        exact Or.inr ⟨r, ⟨hir, by rw [hc_eq]; exact hrc⟩, rfl⟩

/-- For distinct corners `c` and `c'` of `μ`, `gnwProb μ c K c' = 0` for every termination
    bound `K`.  At `K = 0` the function is identically zero; at `K + 1` the corner branch
    fires and yields `if c' = c then 1 else 0 = 0`. -/
private lemma gnwProb_at_other_corner {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc' : isCorner μ c') (hne : c ≠ c') (K : ℕ) :
    gnwProb μ c K c' = 0 := by
  cases K with
  | zero => rfl
  | succ K =>
    have h_unfold : gnwProb μ c (K + 1) c' =
        if isCorner μ c' then (if c' = c then (1 : ℚ) else 0)
        else (1 / ↑(strictHookCells μ c'.1 c'.2).card : ℚ) *
             ∑ y ∈ strictHookCells μ c'.1 c'.2, gnwProb μ c K y := rfl
    rw [h_unfold, if_pos hc', if_neg (fun h : c' = c => hne h.symm)]

/-- When `c'` is not in the strict hook of `(i, j)`, removing `c'` leaves the strict hook
    unchanged.  Direct corollary of `strictHookCells_removeCorner_eq`. -/
private lemma strictHookCells_removeCorner_eq_of_not_mem
    {μ : YoungDiagram} {c' : ℕ × ℕ} (hc' : isCorner μ c') {i j : ℕ}
    (hnotmem : c' ∉ strictHookCells μ i j) :
    strictHookCells (removeCorner μ c' hc') i j = strictHookCells μ i j := by
  rw [strictHookCells_removeCorner_eq hc' i j, ← Finset.erase_eq,
      Finset.erase_eq_of_notMem hnotmem]

/-- Bridge lemma: for distinct corners `c ≠ c'` of `μ`, summing `gnwProb μ c K` over the
    strict hook of any cell `(i, j)` is the same as summing it over the strict hook of
    that cell in `μ \ c'`.  This is because the two strict-hook sets differ at most by
    `c'`, and `gnwProb μ c K c' = 0` (`gnwProb_at_other_corner`).

    Why this matters for `gnwProb_exchange`: the sum over `strictHookCells μ` appearing
    in the recursive step of `gnwProb μ c (K+1) x` can be rewritten as a sum over
    `strictHookCells (μ\c') x.1 x.2`.  Crucially, this lifts the recursive comparison
    between `gnwProb μ` and `gnwProb (μ\c')` from "different summation domains" to "same
    summation domain", isolating the remaining comparison to the integrand. -/
private lemma sum_gnwProb_strictHookCells_eq_removeCorner
    {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc' : isCorner μ c') (hne : c ≠ c') (i j K : ℕ) :
    ∑ y ∈ strictHookCells μ i j, gnwProb μ c K y =
    ∑ y ∈ strictHookCells (removeCorner μ c' hc') i j, gnwProb μ c K y := by
  have h0 : gnwProb μ c K c' = 0 := gnwProb_at_other_corner hc' hne K
  rw [strictHookCells_removeCorner_eq hc' i j, ← Finset.erase_eq]
  by_cases hc'mem : c' ∈ strictHookCells μ i j
  · -- c' is in the strict hook: split off via Finset.sum_erase_add and use h0.
    have hsum := Finset.sum_erase_add (strictHookCells μ i j)
      (fun y => gnwProb μ c K y) hc'mem
    -- hsum : ∑ y ∈ S.erase c', gnwProb μ c K y + gnwProb μ c K c' = ∑ y ∈ S, gnwProb μ c K y
    linarith [hsum, h0]
  · -- c' is not in the strict hook: S.erase c' = S.
    rw [Finset.erase_eq_of_notMem hc'mem]

/-- F-domain bridge for `gnwProb_exchange`: For distinct corners `c ≠ c'` of `μ`, the
    sum of `gnwProb μ c (hookLength μ x.1 x.2) x` over `μ.cells` equals the same sum
    restricted to `(removeCorner μ c' hc').cells`.

    Why this matters: in `gnwProb_exchange`, the LHS sum runs over `μ.cells` while the
    RHS sum runs over `(μ\c').cells = μ.cells.erase c'`.  This lemma rewrites the LHS
    domain to match the RHS, isolating the remaining comparison to integrands alone
    (`gnwProb μ` vs `gnwProb (μ\c')`, and `hookLength μ` vs `hookLength (μ\c')`).

    Proof: `(μ\c').cells = μ.cells.erase c'` definitionally; the only term dropped is
    the `c'` term itself, which contributes `0` by `gnwProb_at_other_corner`. -/
private lemma sum_gnwProb_eq_removeCorner_cells
    {μ : YoungDiagram} {c c' : ℕ × ℕ}
    (hc' : isCorner μ c') (hne : c ≠ c') :
    ∑ x ∈ μ.cells, gnwProb μ c (hookLength μ x.1 x.2) x =
    ∑ x ∈ (removeCorner μ c' hc').cells,
        gnwProb μ c (hookLength μ x.1 x.2) x := by
  have hc'_mem : c' ∈ μ.cells := YoungDiagram.mem_cells.mpr hc'.1
  -- Goal RHS: (removeCorner μ c' hc').cells is definitionally μ.cells.erase c'.
  show ∑ x ∈ μ.cells, gnwProb μ c (hookLength μ x.1 x.2) x =
       ∑ x ∈ μ.cells.erase c', gnwProb μ c (hookLength μ x.1 x.2) x
  -- Split off c' from the LHS via Finset.sum_erase_add and use h0.
  have hsum := Finset.sum_erase_add μ.cells
    (fun x => gnwProb μ c (hookLength μ x.1 x.2) x) hc'_mem
  have h0 : gnwProb μ c (hookLength μ c'.1 c'.2) c' = 0 :=
    gnwProb_at_other_corner hc' hne (hookLength μ c'.1 c'.2)
  linarith [hsum, h0]

/-- GNW 1979 exchange identity (core inductive step, product form — no division).
    For distinct corners c and c' of μ, removing c' preserves the normalized walk probability:
      F(μ,c) · H(μ\c) · H(μ\c') = F(μ\c',c) · H((μ\c')\c) · H(μ)
    where F(ν,d) = Σ_{x∈ν} gnwProb(ν,d,h(x),x) and H = hookProd.
    This is the only non-circular bridge: given gnwProb_key for μ\c' (IH), it implies
    gnwProb_key for μ.  Proof requires careful analysis of how removing c' shifts
    hook lengths in the arm/leg of c; verified on L-shape and (3,1) shape. -/
private lemma gnwProb_exchange (μ : YoungDiagram) {c c' : ℕ × ℕ}
    (hc : isCorner μ c) (hc' : isCorner μ c') (hne : c ≠ c') :
    (∑ x ∈ μ.cells, gnwProb μ c (hookLength μ x.1 x.2) x) *
      (hookProd (removeCorner μ c hc) : ℚ) *
      (hookProd (removeCorner μ c' hc') : ℚ) =
    (∑ x ∈ (removeCorner μ c' hc').cells,
        gnwProb (removeCorner μ c' hc') c
          (hookLength (removeCorner μ c' hc') x.1 x.2) x) *
      (hookProd (removeCorner (removeCorner μ c' hc') c
          (isCorner_removeCorner_of_ne hc' hc hne.symm)) : ℚ) *
      (hookProd μ : ℚ) := by
  sorry

/-- GNW KEY theorem (Greene-Nijenhuis-Wilf 1979):
    The sum of GNW walk probabilities over all cells in μ equals the hookProd ratio.
    This is the hard combinatorial core of the GNW 1979 proof.

    Proof: by strong induction on μ.card.
    Base (single-corner, μ is a rectangle): gnwProb = 1 everywhere; ratio = μ.card.
    Step (multi-corner): pick any c' ≠ c.  gnwProb_exchange gives:
      F(μ,c) · H(μ\c) · H(μ\c') = F(μ\c',c) · H((μ\c')\c) · H(μ).
    By IH on μ\c' (using isCorner_removeCorner_of_ne):
      F(μ\c',c) · H((μ\c')\c) = H(μ\c').
    Substituting: F(μ,c) · H(μ\c) · H(μ\c') = H(μ\c') · H(μ),
    so F(μ,c) = H(μ)/H(μ\c)  (dividing by H(μ\c') > 0). -/
private lemma gnwProb_key (μ : YoungDiagram) {c : ℕ × ℕ} (hc : isCorner μ c) :
    ∑ x ∈ μ.cells, gnwProb μ c (hookLength μ x.1 x.2) x =
    (hookProd μ : ℚ) / hookProd (removeCorner μ c hc) := by
  have hcmem : c ∈ corners μ := mem_corners.mpr hc
  by_cases h_single : (corners μ).card = 1
  · -- Single-corner case: μ is a rectangle. gnwProb = 1 everywhere by gnwProb_sum_corners.
    -- Step 1: corners(μ) = {c}
    have h_corners_one : corners μ = {c} := by
      obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.mp h_single
      have hcc₀ : c = c₀ := Finset.mem_singleton.mp (hc₀ ▸ hcmem)
      simp [hc₀, hcc₀]
    -- Step 2: gnwProb(μ, c, h(x), x) = 1 for all x ∈ μ
    have h_gnw_one : ∀ x ∈ μ.cells, gnwProb μ c (hookLength μ x.1 x.2) x = 1 := by
      intro x hx
      have hxmem : x ∈ μ := YoungDiagram.mem_cells.mp hx
      have hsum := gnwProb_sum_corners μ (hookLength μ x.1 x.2) x hxmem le_rfl
      have heq : ∑ c' ∈ (corners μ).attach, gnwProb μ c'.val (hookLength μ x.1 x.2) x =
                 gnwProb μ c (hookLength μ x.1 x.2) x :=
        Finset.sum_eq_single_of_mem ⟨c, hcmem⟩ (Finset.mem_attach _ _) (fun c' _ hne =>
          absurd (Subtype.ext (Finset.mem_singleton.mp (h_corners_one ▸ c'.prop))) hne)
      linarith [hsum, heq]
    -- Step 3: sum over μ.cells = μ.card (as ℚ)
    have h_sum_card : ∑ x ∈ μ.cells, gnwProb μ c (hookLength μ x.1 x.2) x = μ.card := by
      have : ∑ x ∈ μ.cells, gnwProb μ c (hookLength μ x.1 x.2) x = ∑ _x ∈ μ.cells, (1 : ℚ) :=
        Finset.sum_congr rfl (fun x hx => h_gnw_one x hx)
      rw [this, sum_const_one]; simp [YoungDiagram.card]
    -- Step 4: hook ratio = μ.card for single-corner (rectangle) case.
    -- By hookProd_ratio_formula: ratio = Π_{s<c.2} h(c.1,s)/(h-1) * Π_{r<c.1} h(r,c.2)/(h-1).
    -- Single-corner implies: rowLen(r) = c.2+1 for r ≤ c.1, colLen(s) = c.1+1 for s ≤ c.2.
    -- This gives h(c.1,s) = c.2-s+1 and h(r,c.2) = c.1-r+1; each product telescopes
    -- (via prod_div_telescope) to c.2+1 and c.1+1; product = (c.2+1)*(c.1+1) = μ.card.
    have h_ratio_card : (hookProd μ : ℚ) / hookProd (removeCorner μ c hc) = μ.card := by
      -- Step A: rowLen 0 = c.2 + 1 (the corner at the bottom of the last column must be c)
      have hμ_mem : (0, 0) ∈ μ :=
        μ.isLowerSet (Prod.mk_le_mk.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩) hc.1
      have hrl0_pos : 0 < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp hμ_mem
      have hC_mem : (0, μ.rowLen 0 - 1) ∈ μ :=
        YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hcl_C_pos : 0 < μ.colLen (μ.rowLen 0 - 1) :=
        YoungDiagram.mem_iff_lt_colLen.mp hC_mem
      set r₀ := μ.colLen (μ.rowLen 0 - 1) - 1 with hr₀_def
      have hr₀_mem : (r₀, μ.rowLen 0 - 1) ∈ μ :=
        YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
      have hrl_r₀ : μ.rowLen r₀ = μ.rowLen 0 :=
        le_antisymm (μ.rowLen_anti 0 r₀ (Nat.zero_le _))
          (by have h := YoungDiagram.mem_iff_lt_rowLen.mp hr₀_mem; omega)
      have hr₀_corner : isCorner μ (r₀, μ.rowLen 0 - 1) := ⟨hr₀_mem,
        by rw [YoungDiagram.mem_iff_lt_rowLen]; push_neg; rw [hrl_r₀]; omega,
        by rw [YoungDiagram.mem_iff_lt_colLen]; push_neg; omega⟩
      have hrC_eq : (r₀, μ.rowLen 0 - 1) = c :=
        Finset.mem_singleton.mp (h_corners_one ▸ mem_corners.mpr hr₀_corner)
      have hrl0 : μ.rowLen 0 = c.2 + 1 := by
        have := congr_arg Prod.snd hrC_eq; simp only [Prod.snd] at this; omega
      -- Step B: colLen 0 = c.1 + 1 (the corner at the end of the last row must be c)
      have hcl0_pos : 0 < μ.colLen 0 :=
        YoungDiagram.mem_iff_lt_colLen.mp hμ_mem
      set R := μ.colLen 0 - 1 with hR_def
      have hR_mem : (R, 0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
      have hrl_R_pos : 0 < μ.rowLen R := YoungDiagram.mem_iff_lt_rowLen.mp hR_mem
      set c_R := μ.rowLen R - 1 with hcR_def
      have hcR_mem : (R, c_R) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hcl_cR_le : μ.colLen c_R ≤ μ.colLen 0 := by
        apply Nat.le_of_not_lt; intro hlt
        have h1 : (μ.colLen 0, c_R) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
        have h2 : (μ.colLen 0, 0) ∈ μ :=
          μ.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl _, Nat.zero_le _⟩) h1
        exact absurd (YoungDiagram.mem_iff_lt_colLen.mp h2) (lt_irrefl _)
      have hcl_cR : μ.colLen c_R = R + 1 :=
        le_antisymm (hcl_cR_le.trans (by omega))
          (Nat.succ_le_of_lt (YoungDiagram.mem_iff_lt_colLen.mp hcR_mem))
      have hR_corner : isCorner μ (R, c_R) := ⟨hcR_mem,
        by rw [YoungDiagram.mem_iff_lt_rowLen]; push_neg; omega,
        by rw [YoungDiagram.mem_iff_lt_colLen]; push_neg; rw [hcl_cR]; omega⟩
      have hRcR_eq : (R, c_R) = c :=
        Finset.mem_singleton.mp (h_corners_one ▸ mem_corners.mpr hR_corner)
      have hcl0 : μ.colLen 0 = c.1 + 1 := by
        have := congr_arg Prod.fst hRcR_eq; simp only [Prod.fst] at this; omega
      -- Step C: uniform rowLen = c.2+1 for rows ≤ c.1, colLen = c.1+1 for cols ≤ c.2
      have h_rowLen : ∀ r ≤ c.1, μ.rowLen r = c.2 + 1 := fun r hr =>
        le_antisymm ((μ.rowLen_anti 0 r (Nat.zero_le _)).trans_eq hrl0)
          ((μ.rowLen_anti r c.1 hr).trans_eq (rowLen_of_isCorner hc))
      have h_colLen_anti : ∀ {s t : ℕ}, s ≤ t → μ.colLen t ≤ μ.colLen s := fun {s t} hst => by
        apply Nat.le_of_not_lt; intro hlt
        have h1 : (μ.colLen s, t) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
        have h2 : (μ.colLen s, s) ∈ μ :=
          μ.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl _, hst⟩) h1
        exact absurd (YoungDiagram.mem_iff_lt_colLen.mp h2) (lt_irrefl _)
      have h_colLen : ∀ s ≤ c.2, μ.colLen s = c.1 + 1 := fun s hs =>
        le_antisymm ((h_colLen_anti (Nat.zero_le s)).trans_eq hcl0)
          ((h_colLen_anti hs).trans_eq (colLen_of_isCorner hc))
      -- Step D: hookLength at arm cells (c.1, s) and leg cells (r, c.2)
      have h_arm_hook : ∀ s < c.2, hookLength μ c.1 s = c.2 - s + 1 := fun s hs => by
        unfold hookLength armLen legLen
        rw [rowLen_of_isCorner hc, h_colLen s (by omega)]; omega
      have h_leg_hook : ∀ r < c.1, hookLength μ r c.2 = c.1 - r + 1 := fun r hr => by
        unfold hookLength armLen legLen
        rw [h_rowLen r (by omega), colLen_of_isCorner hc]; omega
      -- Step E: arm product ∏_{s<c.2} h/(h-1) = c.2+1 via telescoping
      have h_arm_prod : ∏ s ∈ Finset.range c.2,
          ((hookLength μ c.1 s : ℚ) / ((hookLength μ c.1 s : ℚ) - 1)) = ↑c.2 + 1 := by
        rcases Nat.eq_zero_or_pos c.2 with rfl | _
        · simp
        have hconv : ∀ s ∈ Finset.range c.2,
            (hookLength μ c.1 s : ℚ) / ((hookLength μ c.1 s : ℚ) - 1) =
            (((c.2 + 1 : ℕ) : ℚ) - ↑s) / (((c.2 + 1 : ℕ) : ℚ) - ↑s - 1) := by
          intro s hs
          have hlt : s < c.2 := Finset.mem_range.mp hs
          rw [h_arm_hook s hlt]
          push_cast [show s ≤ c.2 from by omega]; ring
        rw [Finset.prod_congr rfl hconv, prod_div_telescope (c.2 + 1) c.2 (by omega)]
        push_cast; field_simp
      -- Step F: leg product ∏_{r<c.1} h/(h-1) = c.1+1 via telescoping
      have h_leg_prod : ∏ r ∈ Finset.range c.1,
          ((hookLength μ r c.2 : ℚ) / ((hookLength μ r c.2 : ℚ) - 1)) = ↑c.1 + 1 := by
        rcases Nat.eq_zero_or_pos c.1 with rfl | _
        · simp
        have hconv : ∀ r ∈ Finset.range c.1,
            (hookLength μ r c.2 : ℚ) / ((hookLength μ r c.2 : ℚ) - 1) =
            (((c.1 + 1 : ℕ) : ℚ) - ↑r) / (((c.1 + 1 : ℕ) : ℚ) - ↑r - 1) := by
          intro r hr
          have hlt : r < c.1 := Finset.mem_range.mp hr
          rw [h_leg_hook r hlt]
          push_cast [show r ≤ c.1 from by omega]; ring
        rw [Finset.prod_congr rfl hconv, prod_div_telescope (c.1 + 1) c.1 (by omega)]
        push_cast; field_simp
      -- Step G: μ.cells is the rectangle {0..c.1} × {0..c.2}
      have h_cells : μ.cells = (Finset.range (c.1 + 1)) ×ˢ (Finset.range (c.2 + 1)) := by
        ext ⟨r, s⟩
        simp only [YoungDiagram.mem_cells, Finset.mem_product, Finset.mem_range]
        constructor
        · intro hmem
          exact ⟨by have h : (r, 0) ∈ μ :=
                       μ.isLowerSet (Prod.mk_le_mk.mpr ⟨le_refl _, Nat.zero_le _⟩) hmem
                     have := YoungDiagram.mem_iff_lt_colLen.mp h
                     omega,
                 by have h : (0, s) ∈ μ :=
                       μ.isLowerSet (Prod.mk_le_mk.mpr ⟨Nat.zero_le _, le_refl _⟩) hmem
                     have := YoungDiagram.mem_iff_lt_rowLen.mp h
                     omega⟩
        · rintro ⟨hr, hs⟩
          exact μ.isLowerSet (Prod.mk_le_mk.mpr ⟨by omega, by omega⟩) hc.1
      have h_card : μ.card = (c.1 + 1) * (c.2 + 1) := by
        unfold YoungDiagram.card
        rw [h_cells, Finset.card_product, Finset.card_range, Finset.card_range]
      -- Assemble: ratio = arm_prod * leg_prod = (c.2+1) * (c.1+1) = μ.card
      rw [hookProd_ratio_formula hc]
      simp only [Prod.fst, Prod.snd]
      rw [h_arm_prod, h_leg_prod]
      push_cast [h_card]; ring
    rw [h_sum_card, h_ratio_card]
  · -- Multi-corner case (|corners μ| ≥ 2), using gnwProb_exchange + strong induction.
    -- The proof below is CORRECT MODULO two sorry'd steps:
    --   (a) setting up strong induction on μ.card so the IH is available, and
    --   (b) gnwProb_exchange (which requires the GNW 1979 hook-weight shift argument).
    -- Once both are proved, the remaining algebraic steps close immediately.
    --
    -- Pick a second corner c' ≠ c.
    have h_card_ge2 : 2 ≤ (corners μ).card := by
      have hpos : 0 < (corners μ).card := Finset.card_pos.mpr ⟨c, hcmem⟩
      omega
    obtain ⟨c', hc'mem, hne⟩ : ∃ c' ∈ corners μ, c' ≠ c := by
      obtain ⟨c₁, hc₁, c₂, hc₂, hne12⟩ := Finset.one_lt_card.mp (by omega)
      by_cases h : c₁ = c
      · exact ⟨c₂, hc₂, fun h2 => hne12 (h.trans h2.symm)⟩
      · exact ⟨c₁, hc₁, h⟩
    have hc' : isCorner μ c' := mem_corners.mp hc'mem
    -- c is a corner of removeCorner μ c' hc' (distinct corners survive removal).
    have hc_in_rc' : isCorner (removeCorner μ c' hc') c :=
      isCorner_removeCorner_of_ne hc' hc hne.symm
    -- (a) IH: gnwProb_key holds for removeCorner μ c' hc' and corner c
    -- (well-founded recursion on μ.card; removeCorner_card hc' gives card - 1 < card).
    have h_IH := gnwProb_key (removeCorner μ c' hc') hc_in_rc'
    -- Rearrange IH: F(μ\c',c) * H((μ\c')\c) = H(μ\c')
    have hHrc' : (0 : ℚ) < hookProd (removeCorner (removeCorner μ c' hc') c hc_in_rc') :=
      Nat.cast_pos.mpr (Finset.prod_pos (fun x _ => hookLength_pos _ _ _))
    have hHc' : (0 : ℚ) < hookProd (removeCorner μ c' hc') :=
      Nat.cast_pos.mpr (Finset.prod_pos (fun x _ => hookLength_pos _ _ _))
    have h_IH_prod : (∑ x ∈ (removeCorner μ c' hc').cells,
        gnwProb (removeCorner μ c' hc') c
          (hookLength (removeCorner μ c' hc') x.1 x.2) x) *
        (hookProd (removeCorner (removeCorner μ c' hc') c hc_in_rc') : ℚ) =
        hookProd (removeCorner μ c' hc') := by
      rw [h_IH, div_mul_cancel₀ _ (ne_of_gt hHrc')]
    -- (b) Exchange identity: F(μ,c)*H(μ\c)*H(μ\c') = F(μ\c',c)*H((μ\c')\c)*H(μ)
    have h_exch := gnwProb_exchange μ hc hc' hne
    -- Substitute IH into exchange RHS: F'*H_cc' → H_c'
    rw [h_IH_prod] at h_exch
    -- h_exch now: F(μ,c)*H(μ\c)*H(μ\c') = H(μ\c')*H(μ)
    -- Normalize commutativity so H(μ\c') is on the right
    rw [mul_comm (hookProd (removeCorner μ c' hc') : ℚ) (hookProd μ : ℚ)] at h_exch
    -- h_exch: F(μ,c)*H(μ\c)*H(μ\c') = H(μ)*H(μ\c')
    -- Cancel H(μ\c') to get F(μ,c)*H(μ\c) = H(μ)
    have hHrc : (0 : ℚ) < hookProd (removeCorner μ c hc) :=
      Nat.cast_pos.mpr (Finset.prod_pos (fun x _ => hookLength_pos _ _ _))
    have h_Hc' : (hookProd (removeCorner μ c' hc') : ℚ) ≠ 0 := ne_of_gt hHc'
    have h_main_prod : (∑ x ∈ μ.cells, gnwProb μ c (hookLength μ x.1 x.2) x) *
        (hookProd (removeCorner μ c hc) : ℚ) = hookProd μ :=
      mul_right_cancel₀ h_Hc' h_exch
    rw [eq_div_iff (ne_of_gt hHrc)]
    linarith [h_main_prod]
termination_by μ.card
decreasing_by
  have hμpos : 0 < μ.card := Finset.card_pos.mpr ⟨c', hc'.1⟩
  simp only [removeCorner_card hc']
  omega

/-- Hook-walk identity for arbitrary non-empty Young diagrams via GNW walk.
    Proof: rewrite each ratio using gnwProb_key, swap the double sum, and apply
    gnwProb_sum_corners to collapse each inner sum to 1. -/
lemma hook_walk_identity_gnw (μ : YoungDiagram) (hn : 0 < μ.card) :
    ∑ c ∈ (corners μ).attach,
      ((hookProd μ : ℚ) / hookProd (removeCorner μ c.val (mem_corners.mp c.prop)))
    = (μ.card : ℚ) := by
  -- Step 1: rewrite each ratio as Σ_{x∈μ} gnwProb via gnwProb_key
  have h1 : ∑ c ∈ (corners μ).attach,
      (hookProd μ : ℚ) / hookProd (removeCorner μ c.val (mem_corners.mp c.prop)) =
      ∑ c ∈ (corners μ).attach, ∑ x ∈ μ.cells,
        gnwProb μ c.val (hookLength μ x.1 x.2) x :=
    Finset.sum_congr rfl (fun c _ => gnwProb_key μ (mem_corners.mp c.prop))
  rw [h1]
  -- Step 2: swap Σ_c Σ_x → Σ_x Σ_c
  rw [Finset.sum_comm]
  -- Step 3: each inner Σ_c gnwProb = 1 by gnwProb_sum_corners
  trans (∑ _x ∈ μ.cells, (1 : ℚ))
  · exact Finset.sum_congr rfl (fun x hx =>
      gnwProb_sum_corners μ (hookLength μ x.1 x.2) x hx le_rfl)
  -- Step 4: Σ 1 = μ.card
  · rw [sum_const_one]
    simp [YoungDiagram.card]

end HookLengthFormula
