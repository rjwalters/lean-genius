import Mathlib

/-
# General r×r Lindström-Gessel-Viennot Determinant

## Research Problem: ballot-problem-oq-03-oq-02

Generalize the 2×2 LGV lemma (proved in BallotProblemOQ03.lean) to the
full r×r case using permutations and `Matrix.det`.

## Mathematical Content

**The LGV Lemma** (Lindström 1973, Gessel-Viennot 1985):
Given r source points A₁, ..., Aᵣ on the y-axis and r target points
B₁, ..., Bᵣ on the line x = m, the number of r-tuples of pairwise
non-intersecting lattice paths (Pᵢ: Aᵢ → Bᵢ) equals

  det [ e(Aᵢ, Bⱼ) ]_{i,j=1}^r

where e(A,B) = C(dx + dy, dx) is the number of lattice paths from A to B.

**Proof approach**: Expand det as alternating sum over permutations.
The identity permutation contributes ∏ e(Aᵢ,Bᵢ). Non-identity permutations
cancel via a sign-reversing involution (Gessel-Viennot involution).

## Status (0 axioms, 0 sorries — COMPLETE)
- [x] Path tuple and non-intersecting definitions (closed-interval formulation)
- [x] Path weight matrix using Matrix.det
- [x] Permutation path tuples and signed counts
- [x] Gessel-Viennot involution infrastructure (swapTailsAt, firstNonFixed)
- [x] Algebraic bridge: det = signed sum of perm path tuple counts (proved)
- [x] r×r LGV lemma (proved from GV cancellation + wellFormed hypothesis)
- [x] Corollaries: non-negativity, r=0, r=1 special cases
- [x] PathMN cardinality C(m+n,m) (proved via double induction + Pascal)
- [x] Tagged sigma type (TaggedPathTuple) for involution domain
- [x] Sum decomposition: signed perm sum = sum over tagged tuples (proved)
- [x] Non-identity permutations have inversions (proved)
- [x] Non-identity σ-tuples always cross (proved from crossing lemma)
- [x] Well-formedness condition (∀ i j, sources i ≤ targets j)
- [x] Crossing lemma: discrete IVT for lattice paths (PROVED)
- [x] NonIntersecting definition fixed: closed intervals + final column
- [x] colEntry monotonicity and bound lemmas (proved)
- [x] GV cancellation structure: split = NI part + cancellable part (proved)
- [x] NI counting bijection (card_nonCancellable_eq_niTupleCount) (PROVED)
- [x] take_at_column_entry: East count at column entry (PROVED)
- [x] take_east_count_within_column: East count within column (PROVED)
- [x] cancellable_has_crossing: existence of crossing pair (PROVED)
- [x] GV involution structure: Finset.sum_involution application (PROVED)
- [x] gvInvolution_sign_reversal: sign cancellation property (PROVED)
- [x] gvInvolution_no_fixed: no fixed points property (PROVED)
- [x] gvNewPerm fixed: right multiplication σ*swap(i,j) (was wrong: swap(i,j)*σ)
- [x] northThenEastPath: canonical path constructor (all North then all East)
- [x] northThenEast_not_NI: these paths cross at column 0 under wellFormed (PROVED)
- [x] gvInvolutionFn: uses northThenEast paths (well-typed, compiles)
- [x] gvInvolution_sign_reversal + no_fixed: proved for northThenEast variant
- [x] Canonical crossing selection (Nat.find + lex encoding) (PROVED)
- [x] Tail-swap PathMN construction (take+drop with length/East proofs) (PROVED)
- [x] Canonical GV involution (gvCanonInv) with actual tail-swap paths (DEFINED)
- [x] gvCanon_sign_reversal (PROVED — same as before, only depends on perm)
- [x] gvCanon_no_fixed (PROVED — same as before, only depends on perm)
- [x] cancellable_sum_eq_zero wired to Finset.sum_involution (PROVED modulo sorries below)
- [x] gvCanon_membership (PROVED — tail-swapped paths share (c, y) → ¬NI)
- [x] gvCanon_self_inverse (PROVED — canonical crossing preserved + double swap = id)

## References
- Lindström (1973): "On the Vector Representations of Induced Matroids"
- Gessel-Viennot (1985): "Binomial Determinants, Paths, and Hook Length Formulae"
- Aigner (2007): "A Course in Enumeration", Chapter 10
-/

set_option linter.unusedVariables false

namespace LGV

open Finset

-- ============================================================
-- PART 1: Lattice Path Foundations
-- ============================================================

/-- A lattice path: false = East (+x), true = North (+y). -/
abbrev LPath := List Bool

/-- Count East (false) steps in a path. -/
def eastSteps (l : LPath) : ℕ := l.countP (· = false)

/-- Count North (true) steps in a path. -/
def northSteps (l : LPath) : ℕ := l.countP (· = true)

/-- A lattice path with exactly m East steps and n North steps.
    Represents a path from (0, y₀) to (m, y₀ + n). -/
def PathMN (m n : ℕ) : Type :=
  { l : LPath // l.length = m + n ∧ l.countP (· = false) = m }

/-- PathMN is a Fintype (finite set of paths). -/
noncomputable instance PathMN.instFintype (m n : ℕ) : Fintype (PathMN m n) := by
  haveI : DecidablePred (fun v : List.Vector Bool (m + n) =>
    v.val.countP (· = false) = m) := fun v => decEq _ _
  exact Fintype.ofEquiv
    { v : List.Vector Bool (m + n) // v.val.countP (· = false) = m }
    { toFun  := fun ⟨⟨l, hlen⟩, heast⟩ => ⟨l, hlen, heast⟩
      invFun := fun ⟨l, hlen, heast⟩   => ⟨⟨l, hlen⟩, heast⟩
      left_inv  := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }

/-- The number of lattice paths from (0, a) to (m, b) with a ≤ b
    equals C(m + (b - a), m). -/
noncomputable def pathCount (m a b : ℕ) : ℕ :=
  Nat.choose (m + (b - a)) m

-- ============================================================
-- PART 2: Column Entry and Non-Intersection (Pairwise)
-- ============================================================

/-- northBeforeEast l k = number of North steps before the k-th East step. -/
def northBeforeEast : LPath → ℕ → ℕ
  | [], _ => 0
  | (false :: _), 0 => 0
  | (false :: xs), (k + 1) => northBeforeEast xs k
  | (true :: xs), k => 1 + northBeforeEast xs k

/-- Column entry offset: y-coordinate offset when entering column x. -/
def colEntry (l : LPath) : ℕ → ℕ
  | 0 => 0
  | k + 1 => northBeforeEast l k

-- ============================================================
-- Column Entry Monotonicity
-- ============================================================

/-- northBeforeEast is non-decreasing in k. -/
private lemma northBeforeEast_mono (l : LPath) (k : ℕ) :
    northBeforeEast l k ≤ northBeforeEast l (k + 1) := by
  induction l generalizing k with
  | nil => simp [northBeforeEast]
  | cons b xs ih =>
    cases b with
    | false =>
      cases k with
      | zero => simp [northBeforeEast]
      | succ k' =>
        simp only [northBeforeEast]
        exact ih k'
    | true =>
      simp only [northBeforeEast]
      exact Nat.add_le_add_left (ih k) 1

/-- colEntry is non-decreasing: colEntry l x ≤ colEntry l (x + 1). -/
lemma colEntry_mono (l : LPath) (x : ℕ) : colEntry l x ≤ colEntry l (x + 1) := by
  cases x with
  | zero => simp [colEntry]
  | succ k => exact northBeforeEast_mono l k

/-- countP complement sum: countP false + countP true = length. -/
private lemma bool_countP_sum' (l : List Bool) :
    l.countP (· = false) + l.countP (· = true) = l.length := by
  induction l with
  | nil => simp
  | cons b xs ih => cases b <;> simp_all [List.countP_cons, List.length_cons] <;> omega

/-- northBeforeEast l k ≤ total number of North (true) steps in l. -/
private lemma northBeforeEast_le_countP_true (l : LPath) (k : ℕ) :
    northBeforeEast l k ≤ l.countP (· = true) := by
  induction l generalizing k with
  | nil => simp [northBeforeEast]
  | cons b xs ih =>
    cases b with
    | false =>
      cases k with
      | zero => simp [northBeforeEast]
      | succ k' =>
        simp only [northBeforeEast]
        have h1 := ih k'
        have h2 : (false :: xs).countP (· = true) = xs.countP (· = true) := by
          simp [List.countP_cons]
        omega
    | true =>
      simp only [northBeforeEast]
      have h1 := ih k
      have h2 : (true :: xs).countP (· = true) = xs.countP (· = true) + 1 := by
        simp [List.countP_cons]
      omega

/-- For PathMN m n, the total number of North (true) steps equals n. -/
private lemma pathMN_countP_true {m n : ℕ} (P : PathMN m n) :
    P.val.countP (· = true) = n := by
  have hlen := P.property.1
  have heast := P.property.2
  have hsum := bool_countP_sum' P.val
  omega

/-- For PathMN m n, colEntry P.val k ≤ n for any column k. -/
lemma colEntry_le_north {m n : ℕ} (P : PathMN m n) (k : ℕ) :
    colEntry P.val k ≤ n := by
  cases k with
  | zero => simp [colEntry]
  | succ k =>
    simp only [colEntry]
    calc northBeforeEast P.val k
        ≤ P.val.countP (· = true) := northBeforeEast_le_countP_true P.val k
      _ = n := pathMN_countP_true P

/-- The set of y-values visited by path l (starting at y₀) in column x.
    (Retained for reference; not used in NonIntersecting.) -/
def colYRange (l : LPath) (y₀ x : ℕ) : Set ℕ :=
  { y | y₀ + colEntry l x ≤ y ∧ y < y₀ + colEntry l (x + 1) }

/-- Two paths are non-intersecting if they share no lattice point.

    At each column x < m, the visited y-values form the closed interval
    [y₁ + colEntry l x, y₁ + colEntry l (x+1)].  Two such intervals are
    disjoint iff one ends strictly before the other begins.

    At the final column m, the interval extends to include trailing North
    steps: [y₁ + colEntry l m, y₁ + n₁].  The parameters n₁, n₂ are the
    total North step counts of each path (needed for the final column). -/
def NonIntersecting (l₁ l₂ : LPath) (m y₁ y₂ n₁ n₂ : ℕ) : Prop :=
  (∀ x : ℕ, x < m →
    y₁ + colEntry l₁ (x + 1) < y₂ + colEntry l₂ x ∨
    y₂ + colEntry l₂ (x + 1) < y₁ + colEntry l₁ x) ∧
  (y₁ + n₁ < y₂ + colEntry l₂ m ∨ y₂ + n₂ < y₁ + colEntry l₁ m)

-- ============================================================
-- PART 3: r-Tuple Infrastructure
-- ============================================================

/-- Configuration for an r×r LGV problem. -/
structure LGVConfig (r : ℕ) where
  m : ℕ
  sources : Fin r → ℕ
  targets : Fin r → ℕ
  sources_strictMono : StrictMono sources
  targets_strictMono : StrictMono targets
  source_le_target : ∀ i, sources i ≤ targets i

/-- An r-tuple of lattice paths, one per source-target pair. -/
def PathTuple {r : ℕ} (cfg : LGVConfig r) : Type :=
  (i : Fin r) → PathMN cfg.m (cfg.targets i - cfg.sources i)

noncomputable instance PathTuple.instFintype {r : ℕ} (cfg : LGVConfig r) :
    Fintype (PathTuple cfg) := by
  unfold PathTuple; infer_instance

/-- A path tuple is non-intersecting if all pairs (i < j) are non-intersecting.
    Each path i has n = targets(i) - sources(i) North steps. -/
def IsNonIntersecting {r : ℕ} (cfg : LGVConfig r) (paths : PathTuple cfg) : Prop :=
  ∀ i j : Fin r, i < j →
    NonIntersecting (paths i).val (paths j).val cfg.m
      (cfg.sources i) (cfg.sources j)
      (cfg.targets i - cfg.sources i) (cfg.targets j - cfg.sources j)

-- ============================================================
-- PART 4: The Path Weight Matrix
-- ============================================================

/-- The path weight matrix: M_{i,j} = C(m + (targets j - sources i), m). -/
noncomputable def pathMatrix {r : ℕ} (cfg : LGVConfig r) :
    Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j =>
    (Nat.choose (cfg.m + (cfg.targets j - cfg.sources i)) cfg.m : ℤ)

-- ============================================================
-- PART 5: Permutation Path Tuples
-- ============================================================

/-- A σ-path tuple: path i goes from source i to target σ(i). -/
def PermPathTuple {r : ℕ} (cfg : LGVConfig r) (σ : Equiv.Perm (Fin r)) : Type :=
  (i : Fin r) → PathMN cfg.m (cfg.targets (σ i) - cfg.sources i)

noncomputable instance PermPathTuple.instFintype {r : ℕ} (cfg : LGVConfig r)
    (σ : Equiv.Perm (Fin r)) : Fintype (PermPathTuple cfg σ) := by
  unfold PermPathTuple; infer_instance

/-- The signed count of σ-path tuples. -/
noncomputable def signedPermCount {r : ℕ} (cfg : LGVConfig r)
    (σ : Equiv.Perm (Fin r)) : ℤ :=
  (Equiv.Perm.sign σ : ℤ) *
    ∏ i : Fin r,
      (Nat.choose (cfg.m + (cfg.targets (σ i) - cfg.sources i)) cfg.m : ℤ)

-- ============================================================
-- PART 6: Non-Intersecting Tuple Count
-- ============================================================

/-- The count of non-intersecting identity-path tuples. -/
noncomputable def niTupleCount {r : ℕ} (cfg : LGVConfig r) : ℕ :=
  @Fintype.card { paths : PathTuple cfg // IsNonIntersecting cfg paths }
    (@Subtype.fintype _ _ (fun _ => Classical.dec _) (PathTuple.instFintype cfg))

-- ============================================================
-- PART 7: Gessel-Viennot Involution
-- ============================================================

/-- The tail-swap operation: given two paths and a split index k,
    swap the suffixes after position k. -/
def swapTailsAt (l₁ l₂ : LPath) (k : ℕ) : LPath × LPath :=
  (l₁.take k ++ l₂.drop k, l₂.take k ++ l₁.drop k)

/-- swapTailsAt preserves total length when paths have equal length. -/
theorem swapTailsAt_fst_length (l₁ l₂ : LPath) (k : ℕ)
    (h : l₁.length = l₂.length) :
    (swapTailsAt l₁ l₂ k).1.length = l₁.length := by
  simp [swapTailsAt, List.length_append, List.length_take, List.length_drop]
  omega

theorem swapTailsAt_snd_length (l₁ l₂ : LPath) (k : ℕ)
    (h : l₁.length = l₂.length) :
    (swapTailsAt l₁ l₂ k).2.length = l₂.length := by
  simp [swapTailsAt, List.length_append, List.length_take, List.length_drop]
  omega

/-- The Gessel-Viennot involution on non-identity permutation path tuples.

    For σ ≠ id with a σ-path tuple (P₁,...,Pᵣ), the involution maps:
    1. Find smallest i in a non-trivial cycle of σ (i ≠ σ(i))
    2. Paths Pᵢ (Aᵢ→B_{σ(i)}) and P_{σ(i)} (A_{σ(i)}→B_{σ²(i)})
       must share a lattice point (crossing lemma: sources ordered, targets permuted)
    3. Find the first shared lattice point p
    4. Swap tails: replace Pᵢ, P_{σ(i)} with tail-swaps at p
    5. New tuple is a τ-tuple where τ = (i, σ(i)) ∘ σ, sign(τ) = -sign(σ)

    The involution is its own inverse and sign-reversing, so all non-identity
    permutation contributions cancel in the determinant expansion. The
    surviving terms are exactly the non-intersecting identity tuples.

    **Why σ ≠ id paths must intersect**: If σ(i) ≠ i, then path Pᵢ goes from
    source i (y = aᵢ) to target σ(i) (y = b_{σ(i)}). With sources strictly
    increasing and targets permuted, some pair of paths must cross. Specifically,
    take the smallest i with σ(i) ≠ i. Then i < σ(i) (since σ fixes all j < i).
    Path Pᵢ: (0, aᵢ) → (m, b_{σ(i)}) and path P_{σ(i)}: (0, a_{σ(i)}) → (m, b_{σ²(i)}).
    Since aᵢ < a_{σ(i)} but the targets may be reordered, the crossing lemma
    (from BallotProblemOQ03.lean) guarantees they share a lattice point. -/
theorem gessel_viennot_transposition_sign {r : ℕ}
    (σ : Equiv.Perm (Fin r)) (i : Fin r) (hi : σ i ≠ i) :
    Equiv.Perm.sign (Equiv.swap i (σ i) * σ) = -Equiv.Perm.sign σ := by
  rw [map_mul, Equiv.Perm.sign_swap (Ne.symm hi)]
  simp

-- ============================================================
-- PART 7a: First Non-Fixed Point of a Permutation
-- ============================================================

/-- The smallest index not fixed by a non-identity permutation.
    For σ ≠ 1, this is the minimum of {i | σ(i) ≠ i}. -/
noncomputable def firstNonFixed {r : ℕ} (σ : Equiv.Perm (Fin r)) (hσ : σ ≠ 1) : Fin r :=
  (Finset.univ.filter (fun i => σ i ≠ i)).min' (by
    rw [Finset.filter_nonempty_iff]
    by_contra h
    push_neg at h
    exact hσ (Equiv.ext (fun i => by simpa using h i)))

/-- The first non-fixed point is indeed not fixed by σ. -/
theorem firstNonFixed_spec {r : ℕ} (σ : Equiv.Perm (Fin r)) (hσ : σ ≠ 1) :
    σ (firstNonFixed σ hσ) ≠ firstNonFixed σ hσ := by
  have hmem : firstNonFixed σ hσ ∈
      (Finset.univ : Finset (Fin r)).filter (fun (i : Fin r) => σ i ≠ i) :=
    Finset.min'_mem _ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem

/-- All indices strictly below firstNonFixed are fixed by σ. -/
theorem firstNonFixed_minimal {r : ℕ} (σ : Equiv.Perm (Fin r)) (hσ : σ ≠ 1)
    (j : Fin r) (hj : j < firstNonFixed σ hσ) : σ j = j := by
  by_contra h
  have hmem : j ∈ (Finset.univ : Finset (Fin r)).filter (fun i => σ i ≠ i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
  unfold firstNonFixed at hj
  exact absurd (Finset.min'_le _ _ hmem) (not_le.mpr hj)

/-- For a non-identity permutation, firstNonFixed maps strictly upward:
    σ(firstNonFixed) > firstNonFixed. Since σ fixes all smaller indices,
    σ(firstNonFixed) cannot equal any of them, nor itself. -/
theorem firstNonFixed_lt_image {r : ℕ} (σ : Equiv.Perm (Fin r)) (hσ : σ ≠ 1) :
    firstNonFixed σ hσ < σ (firstNonFixed σ hσ) := by
  have hne : σ (firstNonFixed σ hσ) ≠ firstNonFixed σ hσ := firstNonFixed_spec σ hσ
  obtain hlt | hgt := lt_or_gt_of_ne hne
  · exact absurd (σ.injective (firstNonFixed_minimal σ hσ _ hlt)) hne
  · exact hgt

-- ============================================================
-- PART 7b: PathMN Cardinality
-- ============================================================

-- countP helper lemmas for Bool cons
private lemma countP_false_cons_false (xs : List Bool) :
    (false :: xs).countP (· = false) = xs.countP (· = false) + 1 := by
  simp [List.countP_cons]

private lemma countP_false_cons_true (xs : List Bool) :
    (true :: xs).countP (· = false) = xs.countP (· = false) := by
  simp [List.countP_cons]

private lemma bool_countP_sum (l : List Bool) :
    l.countP (· = false) + l.countP (· = true) = l.length := by
  induction l with
  | nil => simp
  | cons b xs ih =>
    cases b
    · -- false case
      rw [countP_false_cons_false, List.length_cons]
      have : (false :: xs).countP (· = true) = xs.countP (· = true) := by
        simp [List.countP_cons]
      rw [this]; omega
    · -- true case
      rw [countP_false_cons_true, List.length_cons]
      have : (true :: xs).countP (· = true) = xs.countP (· = true) + 1 := by
        simp [List.countP_cons]
      rw [this]; omega

/-- Splitting: PathMN (m+1) (n+1) ≃ PathMN m (n+1) ⊕ PathMN (m+1) n. -/
private noncomputable def pathMN_split (m n : ℕ) :
    PathMN (m + 1) (n + 1) ≃ PathMN m (n + 1) ⊕ PathMN (m + 1) n where
  toFun := fun ⟨l, hlen, heast⟩ => by
    match l with
    | [] => exact absurd hlen (by simp; omega)
    | false :: xs =>
      have heast' : xs.countP (· = false) = m := by
        rw [countP_false_cons_false] at heast; omega
      exact Sum.inl ⟨xs, by simp at hlen; omega, heast'⟩
    | true :: xs =>
      have heast' : xs.countP (· = false) = m + 1 := by
        rw [countP_false_cons_true] at heast; exact heast
      exact Sum.inr ⟨xs, by simp at hlen; omega, heast'⟩
  invFun := fun s => by
    match s with
    | Sum.inl ⟨xs, hlen, heast⟩ =>
      have heast' : (false :: xs).countP (· = false) = m + 1 := by
        rw [countP_false_cons_false]; omega
      exact ⟨false :: xs, by simp; omega, heast'⟩
    | Sum.inr ⟨xs, hlen, heast⟩ =>
      have heast' : (true :: xs).countP (· = false) = m + 1 := by
        rw [countP_false_cons_true]; exact heast
      exact ⟨true :: xs, by simp; omega, heast'⟩
  left_inv := fun ⟨l, hlen, _⟩ => by
    match l with
    | [] => exact absurd hlen (by simp; omega)
    | false :: _ => rfl
    | true :: _ => rfl
  right_inv := fun s => by
    match s with
    | Sum.inl ⟨xs, hlen, heast⟩ => simp [countP_false_cons_false]
    | Sum.inr ⟨xs, hlen, heast⟩ => simp [countP_false_cons_true]

/-- The number of lattice paths with m East steps and n North steps
    equals C(m + n, m). -/
theorem pathMN_card (m n : ℕ) :
    Fintype.card (PathMN m n) = Nat.choose (m + n) m := by
  induction m generalizing n with
  | zero =>
    simp only [Nat.zero_add, Nat.choose_zero_right]
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨List.replicate n true, by simp, by simp⟩, ?_⟩
    intro ⟨l, hlen, heast⟩
    apply Subtype.ext; simp only
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi_l _
      rw [List.getElem_replicate]
      rcases Bool.eq_false_or_eq_true (l[i]) with h | h
      · exact h
      · exfalso
        have hmem : false ∈ l := h ▸ List.getElem_mem hi_l
        have : 0 < l.countP (· = false) :=
          List.countP_pos_iff.mpr ⟨false, hmem, by simp⟩
        omega
  | succ m ih =>
    induction n with
    | zero =>
      simp only [Nat.add_zero, Nat.choose_self]
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨List.replicate (m + 1) false, by simp,
               by simp [List.countP_replicate]⟩, ?_⟩
      intro ⟨l, hlen, heast⟩
      apply Subtype.ext; simp only
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi_l _
        rw [List.getElem_replicate]
        rcases Bool.eq_false_or_eq_true (l[i]) with h | h
        · exfalso
          have hmem : true ∈ l := h ▸ List.getElem_mem hi_l
          have h_pos : 0 < l.countP (· = true) :=
            List.countP_pos_iff.mpr ⟨true, hmem, by simp⟩
          have h_sum := bool_countP_sum l
          omega
        · exact h
    | succ n ih_n =>
      rw [Fintype.card_congr (pathMN_split m n), Fintype.card_sum, ih (n + 1), ih_n,
          show m + 1 + n = m + (n + 1) from by omega,
          show m + 1 + (n + 1) = m + (n + 1) + 1 from by omega]
      exact (Nat.choose_succ_succ' (m + (n + 1)) m).symm

-- ============================================================
-- PART 7c: Algebraic Bridge
-- ============================================================

/-- The cardinality of σ-path tuples factors as a product of
    binomial coefficients (one per source-target pair). -/
theorem permPathTuple_card {r : ℕ} (cfg : LGVConfig r)
    (σ : Equiv.Perm (Fin r)) :
    (Fintype.card (PermPathTuple cfg σ) : ℤ) =
      ∏ i : Fin r,
        (Nat.choose (cfg.m + (cfg.targets (σ i) - cfg.sources i)) cfg.m : ℤ) := by
  have h : Fintype.card (PermPathTuple cfg σ) =
      ∏ i : Fin r, Nat.choose (cfg.m + (cfg.targets (σ i) - cfg.sources i)) cfg.m := by
    show Fintype.card ((i : Fin r) → PathMN cfg.m (cfg.targets (σ i) - cfg.sources i)) = _
    rw [Fintype.card_pi]; simp only [pathMN_card]
  rw [h]; push_cast; ring

/-- The path weight matrix determinant equals the signed sum of
    permutation path tuple cardinalities.

    This is the algebraic half of the LGV lemma: it connects the
    Leibniz determinant expansion to a combinatorial counting
    interpretation. The combinatorial half (GV involution
    cancellation) shows this sum collapses to niTupleCount.

    Uses the column form of the Leibniz formula:
      det(M) = Σ_σ sign(σ) · Π_i M(i, σ(i))
    obtained via det(M) = det(Mᵀ). -/
theorem det_pathMatrix_eq_signed_sum {r : ℕ} (cfg : LGVConfig r) :
    (pathMatrix cfg).det =
      ∑ σ : Equiv.Perm (Fin r),
        (↑(Equiv.Perm.sign σ) : ℤ) * ↑(Fintype.card (PermPathTuple cfg σ)) := by
  conv_lhs => rw [← Matrix.det_transpose (pathMatrix cfg)]
  simp only [Matrix.det_apply, Units.smul_def,
    Matrix.transpose_apply, pathMatrix, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact (permPathTuple_card cfg σ).symm

-- ============================================================
-- PART 7d: Identity Permutation Infrastructure
-- ============================================================

/-- PermPathTuple for the identity permutation equals PathTuple
    (since (1 : Perm) i = i, targets match). -/
noncomputable def permPathTuple_one_equiv {r : ℕ} (cfg : LGVConfig r) :
    PermPathTuple cfg 1 ≃ PathTuple cfg := by
  have heq : PermPathTuple cfg 1 = PathTuple cfg := by
    simp only [PermPathTuple, PathTuple, Equiv.Perm.one_apply]
  rw [heq]

/-- Cardinality: identity-perm path tuples = regular path tuples. -/
theorem permPathTuple_one_card {r : ℕ} (cfg : LGVConfig r) :
    Fintype.card (PermPathTuple cfg 1) = Fintype.card (PathTuple cfg) :=
  Fintype.card_congr (permPathTuple_one_equiv cfg)

/-- When every path tuple is non-intersecting, niTupleCount = card(PathTuple). -/
theorem niTupleCount_eq_card_of_all_ni {r : ℕ} (cfg : LGVConfig r)
    (h : ∀ p : PathTuple cfg, IsNonIntersecting cfg p) :
    niTupleCount cfg = Fintype.card (PathTuple cfg) := by
  simp only [niTupleCount]
  exact @Fintype.card_congr _ _
    (@Subtype.fintype _ _ (fun _ => Classical.dec _) (PathTuple.instFintype cfg))
    (PathTuple.instFintype cfg)
    (Equiv.subtypeUnivEquiv h)

-- ============================================================
-- PART 7e: GV Cancellation for Small r (Proved Theorems)
-- ============================================================

/-- For r = 0, every path tuple is vacuously non-intersecting. -/
theorem isNonIntersecting_of_r_zero (cfg : LGVConfig 0) (paths : PathTuple cfg) :
    IsNonIntersecting cfg paths :=
  fun i => Fin.elim0 i

/-- GV cancellation for r = 0: proved (single perm, vacuously NI). -/
theorem gv_cancellation_r_zero (cfg : LGVConfig 0) :
    ∑ σ : Equiv.Perm (Fin 0),
      (↑(Equiv.Perm.sign σ) : ℤ) * ↑(Fintype.card (PermPathTuple cfg σ)) =
    ↑(niTupleCount cfg) := by
  have huniq : ∀ σ : Equiv.Perm (Fin 0), σ = 1 :=
    fun σ => Equiv.ext fun i => Fin.elim0 i
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 0))) = {1} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun σ _ => huniq σ⟩
  rw [huniv, Finset.sum_singleton]
  simp only [Equiv.Perm.sign_one, Units.val_one, one_mul]
  congr 1
  rw [permPathTuple_one_card]
  exact (niTupleCount_eq_card_of_all_ni cfg (isNonIntersecting_of_r_zero cfg)).symm

/-- GV cancellation for r = 1: proved (single perm, vacuously NI). -/
theorem gv_cancellation_r_one (cfg : LGVConfig 1) :
    ∑ σ : Equiv.Perm (Fin 1),
      (↑(Equiv.Perm.sign σ) : ℤ) * ↑(Fintype.card (PermPathTuple cfg σ)) =
    ↑(niTupleCount cfg) := by
  have huniq : ∀ σ : Equiv.Perm (Fin 1), σ = 1 :=
    fun σ => Equiv.ext fun i => Subsingleton.elim _ _
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 1))) = {1} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun σ _ => huniq σ⟩
  rw [huniv, Finset.sum_singleton]
  simp only [Equiv.Perm.sign_one, Units.val_one, one_mul]
  congr 1
  rw [permPathTuple_one_card]
  exact (niTupleCount_eq_card_of_all_ni cfg
    (fun p i j hij => absurd hij (by omega : ¬(i < j)))).symm

-- ============================================================
-- PART 8: The r×r LGV Lemma
-- ============================================================

-- ============================================================
-- PART 7d: Tagged Path Tuples (Sigma Type)
-- ============================================================

/-- A tagged path tuple: a permutation σ together with a σ-path tuple.
    This is the disjoint union ⨆_σ PermPathTuple(cfg, σ) on which the
    GV involution operates. -/
def TaggedPathTuple {r : ℕ} (cfg : LGVConfig r) : Type :=
  Σ σ : Equiv.Perm (Fin r), PermPathTuple cfg σ

noncomputable instance TaggedPathTuple.instFintype {r : ℕ} (cfg : LGVConfig r) :
    Fintype (TaggedPathTuple cfg) :=
  Sigma.instFintype

/-- The signed weight of a tagged path tuple. -/
def taggedWeight {r : ℕ} {cfg : LGVConfig r} (t : TaggedPathTuple cfg) : ℤ :=
  (Equiv.Perm.sign t.1 : ℤ)

/-- The sum over tagged tuples equals the sum over permutations of
    signed cardinalities. This is the key reformulation that allows
    us to work at the element level. -/
theorem sum_tagged_eq_sum_perm {r : ℕ} (cfg : LGVConfig r) :
    ∑ t : TaggedPathTuple cfg, taggedWeight t =
      ∑ σ : Equiv.Perm (Fin r),
        (↑(Equiv.Perm.sign σ) : ℤ) * ↑(Fintype.card (PermPathTuple cfg σ)) := by
  change ∑ t : (Σ σ : Equiv.Perm (Fin r), PermPathTuple cfg σ),
      (↑(Equiv.Perm.sign t.1) : ℤ) = _
  rw [Fintype.sum_sigma]
  congr 1; ext σ
  have : ∀ (x : PermPathTuple cfg σ),
      (↑(Equiv.Perm.sign (⟨σ, x⟩ : Σ _, PermPathTuple cfg _).1) : ℤ) =
        (↑(Equiv.Perm.sign σ) : ℤ) := fun _ => rfl
  simp only [this, Finset.sum_const, nsmul_eq_mul, mul_comm, Fintype.card]

/-- Coerce a σ-path tuple to an identity-path tuple when σ = 1. -/
def PermPathTuple.toPathTuple {r : ℕ} {cfg : LGVConfig r}
    {σ : Equiv.Perm (Fin r)} (h : σ = 1) (p : PermPathTuple cfg σ) :
    PathTuple cfg :=
  fun i => cast (by rw [PermPathTuple] at *; congr 1; simp [h]) (p i)

/-- A tagged path tuple is a "fixed point" of the GV involution iff
    it is an identity-permutation tuple that is non-intersecting. -/
def IsGVFixedPoint {r : ℕ} {cfg : LGVConfig r} (t : TaggedPathTuple cfg) : Prop :=
  ∃ (h : t.1 = 1), IsNonIntersecting cfg (t.2.toPathTuple h)

-- ============================================================
-- PART 7e: Crossing Lemma
-- ============================================================

/-- **Lattice path y-coordinate at column boundary.**
    The y-coordinate of a path starting at y₀ when entering column x. -/
def yAtCol (l : LPath) (y₀ : ℕ) (x : ℕ) : ℕ := y₀ + colEntry l x

/-- At column 0, the y-coordinate is the starting position. -/
theorem yAtCol_zero (l : LPath) (y₀ : ℕ) : yAtCol l y₀ 0 = y₀ := by
  simp [yAtCol, colEntry]

/-- Discrete IVT: if p(0) < q(0) and q(m) ≤ p(m), there is a crossing column. -/
private lemma crossing_column_exists {m : ℕ} (p q : ℕ → ℕ)
    (hm : 0 < m) (h0 : p 0 < q 0) (hfin : q m ≤ p m) :
    ∃ k, k < m ∧ p k < q k ∧ q (k + 1) ≤ p (k + 1) := by
  -- Take the largest k < m with p(k) < q(k)
  let S := (Finset.range m).filter (fun k => p k < q k)
  have hS : S.Nonempty := ⟨0, by simp [S, Finset.mem_filter, Finset.mem_range]; exact ⟨hm, h0⟩⟩
  refine ⟨S.max' hS, ?_, ?_, ?_⟩
  · exact Finset.mem_range.mp ((Finset.filter_subset _ _) (Finset.max'_mem S hS))
  · exact (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  · -- k₀ + 1 ∉ S (since k₀ is max), so either k₀ + 1 ≥ m or q(k₀+1) ≤ p(k₀+1)
    by_contra h
    push_neg at h
    have hmem : S.max' hS + 1 ∈ S := by
      have h_range : S.max' hS + 1 < m := by
        by_contra hge
        push_neg at hge
        have hmax_lt := Finset.mem_range.mp
          ((Finset.filter_subset _ _) (Finset.max'_mem S hS))
        have heq : S.max' hS + 1 = m := by omega
        rw [heq] at h
        exact absurd hfin (not_le.mpr h)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h_range, h⟩
    exact absurd (Finset.le_max' S _ hmem) (by omega)

/-- **Crossing lemma for lattice paths (discrete IVT).**
    If path P starts strictly below path Q (y₁ < y₂) but P ends at
    or above Q at column m, then their visited y-ranges overlap at some
    column — i.e., the paths share a lattice point.

    This is the combinatorial engine of the GV involution: it ensures
    that non-identity permutation path tuples always have crossings,
    so the involution is total on non-fixed-point tuples.

    **Proof**: The final column condition cannot hold:
    - First disjunct contradicts hend (colEntry ≤ n).
    - Second disjunct gives p_entry(m) > q_end. Then by discrete IVT
      on column entries, find x₀ where p crosses above q. At x₀,
      neither closed-interval disjointness condition can hold
      (both need colEntry non-decreasing). -/
theorem lattice_paths_must_cross {m : ℕ} {n₁ n₂ : ℕ} {y₁ y₂ : ℕ}
    (P : PathMN m n₁) (Q : PathMN m n₂)
    (hstart : y₁ < y₂)
    (hend : y₂ + n₂ ≤ y₁ + n₁) :
    ¬NonIntersecting P.val Q.val m y₁ y₂ n₁ n₂ := by
  intro ⟨hcols, hfinal⟩
  rcases hfinal with h1 | h2
  · -- y₁ + n₁ < y₂ + colEntry Q m: contradicts hend since colEntry Q m ≤ n₂
    have := colEntry_le_north Q m
    omega
  · -- y₂ + n₂ < y₁ + colEntry P m: P enters column m above Q's endpoint
    -- Therefore q_entry(m) ≤ q_end < p_entry(m)
    have hQ_le : colEntry Q.val m ≤ n₂ := colEntry_le_north Q m
    -- At column 0: p < q. At column m: p > q. Find the crossing.
    have hm_pos : 0 < m := by
      by_contra hm0
      push_neg at hm0
      interval_cases m
      simp [colEntry] at h2
      omega
    have hfin : y₂ + colEntry Q.val m ≤ y₁ + colEntry P.val m := by omega
    obtain ⟨k, hk, hbelow, habove⟩ := crossing_column_exists
      (fun x => y₁ + colEntry P.val x) (fun x => y₂ + colEntry Q.val x)
      hm_pos (by simp [colEntry]; omega) hfin
    -- At column k: p(k) < q(k) and p(k+1) ≥ q(k+1)
    -- Check the column disjointness condition at k
    have hcol_k := hcols k hk
    rcases hcol_k with hleft | hright
    · -- p_entry(k+1) < q_entry(k): but p(k+1) ≥ q(k+1) ≥ q(k)
      have := colEntry_mono Q.val k
      omega
    · -- q_entry(k+1) < p_entry(k): but q(k+1) ≥ q(k) > p(k)
      have := colEntry_mono Q.val k
      omega

-- ============================================================
-- PART 7f: GV Involution Construction
-- ============================================================

/-- **Well-formedness**: every source-target pair is reachable by lattice paths.
    This is stronger than `source_le_target` (which only covers identity pairing).
    Required because Nat subtraction makes `PathMN m 0` represent horizontal paths
    even when the target is below the source, giving wrong path counts.
    Equivalent to `sources (Fin.last) ≤ targets 0` when both are strictly mono. -/
def LGVConfig.wellFormed {r : ℕ} (cfg : LGVConfig r) : Prop :=
  ∀ i j : Fin r, cfg.sources i ≤ cfg.targets j

theorem LGVConfig.wellFormed_iff_max_le_min {r : ℕ} (cfg : LGVConfig r) (hr : 0 < r) :
    cfg.wellFormed ↔ cfg.sources ⟨r - 1, by omega⟩ ≤ cfg.targets ⟨0, hr⟩ := by
  constructor
  · intro h; exact h _ _
  · intro h i j
    calc cfg.sources i ≤ cfg.sources ⟨r - 1, by omega⟩ :=
          cfg.sources_strictMono.monotone (by omega : i.val ≤ r - 1)
      _ ≤ cfg.targets ⟨0, hr⟩ := h
      _ ≤ cfg.targets j := cfg.targets_strictMono.monotone (Nat.zero_le j.val)

/-- **Non-identity permutations have inversions when domain is strictly ordered.**
    If σ ≠ 1 and f is strictly monotone, then there exist i < j with
    f(σ(i)) > f(σ(j)). In other words, σ is not order-preserving. -/
theorem perm_ne_one_has_inversion {r : ℕ} (σ : Equiv.Perm (Fin r)) (hσ : σ ≠ 1)
    {f : Fin r → ℕ} (hf : StrictMono f) :
    ∃ i j : Fin r, i < j ∧ f (σ j) < f (σ i) := by
  -- Since σ ≠ 1, it has a non-fixed point. By firstNonFixed_lt_image,
  -- i < σ(i). Take j = σ(i), so σ(j) ≠ j (σ is not identity on j's orbit).
  -- The strict monotonicity of f turns the permutation disorder into
  -- a numeric inversion.
  have hi := firstNonFixed_spec σ hσ
  have hlt := firstNonFixed_lt_image σ hσ
  -- Let i₀ = firstNonFixed, then i₀ < σ(i₀)
  -- Since σ fixes all j < i₀, and σ(i₀) ≠ i₀, there's a cycle.
  -- In that cycle, some pair must be inverted w.r.t. the natural order.
  -- Specifically, take the first non-fixed point i₀. Then i₀ < σ(i₀).
  -- Consider σ⁻¹(i₀). If σ⁻¹(i₀) > i₀, then we have j = σ⁻¹(i₀) > i₀
  -- with σ(j) = i₀ < σ(i₀), giving an inversion at (i₀, j).
  -- If σ⁻¹(i₀) < i₀, that contradicts minimality (σ fixes all below i₀,
  -- so σ(σ⁻¹(i₀)) = i₀ means σ⁻¹(i₀) is not fixed, but it's below i₀).
  -- If σ⁻¹(i₀) = i₀, then σ(i₀) = i₀, contradiction.
  set i₀ := firstNonFixed σ hσ with hi₀_def
  have hinv_ne : σ⁻¹ i₀ ≠ i₀ := by
    intro h
    have : σ (σ⁻¹ i₀) = σ i₀ := by rw [h]
    simp at this
    exact hi this.symm
  have hinv_ge : σ⁻¹ i₀ ≥ i₀ := by
    by_contra hlt'
    push_neg at hlt'
    have hfixed := firstNonFixed_minimal σ hσ (σ⁻¹ i₀) hlt'
    have : σ (σ⁻¹ i₀) = σ⁻¹ i₀ := hfixed
    simp at this
    exact hinv_ne this.symm
  have hinv_gt : i₀ < σ⁻¹ i₀ := lt_of_le_of_ne hinv_ge (Ne.symm hinv_ne)
  refine ⟨i₀, σ⁻¹ i₀, hinv_gt, ?_⟩
  simp
  exact hf hlt

/-- **Non-identity σ-path tuples always have crossing paths.**
    For a non-identity permutation σ with strictly ordered sources and targets,
    any σ-path tuple must contain a pair of intersecting paths. This ensures
    the GV involution is defined on all non-fixed-point tuples. -/
theorem nonid_perm_paths_cross {r : ℕ} (cfg : LGVConfig r)
    (hwf : cfg.wellFormed)
    (σ : Equiv.Perm (Fin r)) (hσ : σ ≠ 1)
    (paths : PermPathTuple cfg σ) :
    ∃ i j : Fin r, i < j ∧
      ¬NonIntersecting (paths i).val (paths j).val cfg.m
        (cfg.sources i) (cfg.sources j)
        (cfg.targets (σ i) - cfg.sources i) (cfg.targets (σ j) - cfg.sources j) := by
  -- By perm_ne_one_has_inversion, ∃ i < j with targets(σ j) < targets(σ i).
  obtain ⟨i, j, hij, hinv⟩ := perm_ne_one_has_inversion σ hσ cfg.targets_strictMono
  refine ⟨i, j, hij, ?_⟩
  -- Path i starts at sources(i), ends at targets(σ i)
  -- Path j starts at sources(j), ends at targets(σ j)
  -- sources(i) < sources(j) and targets(σ j) < targets(σ i)
  -- So path i starts lower and ends higher → must cross
  have hsrc := cfg.sources_strictMono hij
  -- With well-formedness, Nat subtraction gives correct values:
  -- sources(k) + (targets(σ k) - sources(k)) = targets(σ k)
  have hwf_i := hwf i (σ i)
  have hwf_j := hwf j (σ j)
  apply lattice_paths_must_cross (paths i) (paths j) hsrc
  -- Need: sources(j) + (targets(σ j) - sources(j)) ≤ sources(i) + (targets(σ i) - sources(i))
  -- i.e., targets(σ j) ≤ targets(σ i)
  omega

-- ============================================================
-- PART 7g: GV Involution Infrastructure
-- ============================================================

/-  GV involution cancellation proof structure:
    1. `sum_tagged_eq_sum_perm`: reformulate as sum over tagged sigma type
    2. `nonid_perm_paths_cross`: non-identity tuples always have crossings
    3. Sign-reversing involution on tagged tuples (tail-swap at first crossing)
    Components 1-2 are proved. Component 3 is in `cancellable_sum_eq_zero`. -/

/-- **Key lemma**: At a column entry point, the prefix has the correct East step count.
    When entering column x (having seen x East steps and colEntry(l,x) North steps),
    the first (x + colEntry l x) elements contain exactly x East (false) steps.
    This is the foundation of the GV tail-swap construction. -/
private lemma take_at_column_entry (l : LPath) (x : ℕ)
    (hx : x ≤ l.countP (· = false)) :
    (l.take (x + colEntry l x)).countP (· = false) = x := by
  induction l generalizing x with
  | nil =>
    simp only [List.countP_nil, Nat.le_zero] at hx
    subst hx; simp [colEntry, northBeforeEast]
  | cons b l' ih =>
    cases b with
    | false =>
      -- l = false :: l'; the first element is an East step
      cases x with
      | zero => simp [colEntry, List.take]
      | succ x' =>
        -- Need: ((false :: l').take ((x'+1) + colEntry (false :: l') (x'+1))).countP (false) = x'+1
        have hx' : x' ≤ l'.countP (· = false) := by
          have hcp : (false :: l').countP (· = false) = l'.countP (· = false) + 1 :=
            List.countP_cons_of_pos (by decide)
          omega
        -- colEntry (false :: l') (x'+1) = colEntry l' x'
        have hce : colEntry (false :: l') (x' + 1) = colEntry l' x' := by
          simp only [colEntry, northBeforeEast]
          cases x' with
          | zero => rfl
          | succ _ => rfl
        rw [hce, show x' + 1 + colEntry l' x' = (x' + colEntry l' x') + 1 from by omega]
        rw [List.take_succ_cons, countP_false_cons_false]
        rw [ih x' hx']
    | true =>
      -- l = true :: l'; the first element is a North step
      cases x with
      | zero => simp [colEntry, List.take]
      | succ x' =>
        -- Need: ((true :: l').take ((x'+1) + colEntry (true :: l') (x'+1))).countP (false) = x'+1
        have hx' : x' + 1 ≤ l'.countP (· = false) := by
          have hcp : (true :: l').countP (· = false) = l'.countP (· = false) :=
            List.countP_cons_of_neg (by decide)
          omega
        -- colEntry (true :: l') (x'+1) = 1 + colEntry l' (x'+1)
        have hce : colEntry (true :: l') (x' + 1) = 1 + colEntry l' (x' + 1) := by
          simp [colEntry, northBeforeEast]
        rw [hce, show x' + 1 + (1 + colEntry l' (x' + 1)) =
            ((x' + 1) + colEntry l' (x' + 1)) + 1 from by omega]
        rw [List.take_succ_cons, countP_false_cons_true]
        exact ih (x' + 1) hx'

/-- Between the x-th and (x+1)-th East steps, all list elements are North (true).
    Consequence: at any position x + h with colEntry(l,x) ≤ h ≤ colEntry(l,x+1),
    the prefix has exactly x East steps. -/
private lemma take_east_count_within_column (l : LPath) (x h : ℕ)
    (hx : x ≤ l.countP (· = false))
    (hlow : colEntry l x ≤ h) (hhigh : h ≤ colEntry l (x + 1)) :
    (l.take (x + h)).countP (· = false) = x := by
  -- Between positions (x + colEntry l x) and (x + colEntry l (x+1)),
  -- all elements are North steps. So extending the prefix from
  -- colEntry(l,x) to h doesn't add any East steps.
  -- Strategy: show that take(l, x+h) has the same East count as take(l, x+colEntry l x).
  -- The elements between these positions are all true (North).
  induction l generalizing x h with
  | nil =>
    simp only [List.countP_nil, Nat.le_zero] at hx
    subst hx
    simp only [colEntry, northBeforeEast, Nat.le_zero] at hhigh
    subst hhigh; rfl
  | cons b l' ih =>
    cases b with
    | false =>
      cases x with
      | zero =>
        -- x=0: colEntry(false::l', 0) = 0 ≤ h ≤ colEntry(false::l', 1)
        -- colEntry(false::l', 1) = northBeforeEast(false::l', 0) = 0
        simp only [colEntry, northBeforeEast] at hlow hhigh
        -- So h = 0
        have : h = 0 := by omega
        subst this; simp [List.take]
      | succ x' =>
        -- colEntry (false :: l') (x'+1) = colEntry l' x'
        -- colEntry (false :: l') (x'+2) = colEntry l' (x'+1)
        have hce1 : colEntry (false :: l') (x' + 1) = colEntry l' x' := by
          simp only [colEntry, northBeforeEast]; cases x' <;> rfl
        have hce2 : colEntry (false :: l') (x' + 1 + 1) = colEntry l' (x' + 1) := by
          simp only [colEntry, northBeforeEast]
        rw [hce1] at hlow; rw [hce2] at hhigh
        have hx' : x' ≤ l'.countP (· = false) := by
          have hcp : (false :: l').countP (· = false) = l'.countP (· = false) + 1 :=
            List.countP_cons_of_pos (by decide)
          omega
        -- take(false :: l', (x'+1) + h) = false :: take(l', x' + h)
        rw [show x' + 1 + h = (x' + h) + 1 from by omega]
        rw [List.take_succ_cons, countP_false_cons_false]
        rw [ih x' h hx' hlow hhigh]
    | true =>
      cases x with
      | zero =>
        -- x=0: no East steps yet. colEntry(true::l', 0) = 0 ≤ h ≤ colEntry(true::l', 1)
        -- colEntry(true::l', 1) = northBeforeEast(true::l', 0) = 1 + northBeforeEast l' 0 = 1 + colEntry l' 1
        -- We need take(true :: l', h).countP(false) = 0
        -- Since h ≤ 1 + colEntry l' 1, and the first element is true...
        cases h with
        | zero => simp [List.take]
        | succ h' =>
          -- take(true :: l', h'+1) = true :: take(l', h')
          rw [Nat.zero_add, List.take_succ_cons, countP_false_cons_true]
          -- Need: take(l', h').countP(false) = 0
          -- colEntry(true::l', 0) = 0, colEntry(true::l', 1) = 1 + colEntry l' 1
          -- So 0 ≤ h'+1 ≤ 1 + colEntry l' 1, meaning h' ≤ colEntry l' 1
          -- Also colEntry l' 0 = 0 ≤ h'
          have hlow' : colEntry l' 0 ≤ h' := by simp [colEntry]
          have hhigh' : h' ≤ colEntry l' (0 + 1) := by
            simp only [colEntry, northBeforeEast] at hhigh ⊢
            omega
          have hx' : 0 ≤ l'.countP (· = false) := Nat.zero_le _
          simpa [Nat.zero_add] using ih 0 h' hx' hlow' hhigh'
      | succ x' =>
        -- colEntry(true::l', x'+1) = 1 + colEntry l' (x'+1)
        -- colEntry(true::l', x'+2) = 1 + colEntry l' (x'+2)
        have hce1 : colEntry (true :: l') (x' + 1) = 1 + colEntry l' (x' + 1) := by
          simp [colEntry, northBeforeEast]
        have hce2 : colEntry (true :: l') (x' + 1 + 1) = 1 + colEntry l' (x' + 1 + 1) := by
          simp [colEntry, northBeforeEast]
        rw [hce1] at hlow; rw [hce2] at hhigh
        have hx' : x' + 1 ≤ l'.countP (· = false) := by
          have hcp : (true :: l').countP (· = false) = l'.countP (· = false) :=
            List.countP_cons_of_neg (by decide)
          omega
        -- h ≥ 1 + colEntry l' (x'+1), so h ≥ 1
        have hh_pos : h ≥ 1 := by omega
        -- take(true :: l', (x'+1) + h) = true :: take(l', x' + h)
        rw [show x' + 1 + h = (x' + (h - 1)) + 1 + 1 from by omega]
        rw [List.take_succ_cons, countP_false_cons_true]
        rw [show x' + (h - 1) + 1 = x' + 1 + (h - 1) from by omega]
        exact ih (x' + 1) (h - 1) hx' (by omega) (by omega)

/-- **Helper**: A tagged tuple is "non-cancellable" iff it is an NI identity tuple.
    All other tagged tuples (σ ≠ 1, or σ = 1 with crossings) are paired and cancelled
    by the GV involution. -/
private def isNonCancellable {r : ℕ} {cfg : LGVConfig r}
    (t : TaggedPathTuple cfg) : Prop :=
  IsGVFixedPoint t

private noncomputable instance {r : ℕ} {cfg : LGVConfig r}
    (t : TaggedPathTuple cfg) : Decidable (isNonCancellable t) :=
  Classical.dec _

/-- A cancellable tagged tuple always has a crossing pair (i,j) with i < j. -/
private theorem cancellable_has_crossing {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    ∃ i j : Fin r, i < j ∧
      ¬NonIntersecting (t.2 i).val (t.2 j).val cfg.m
        (cfg.sources i) (cfg.sources j)
        (cfg.targets (t.1 i) - cfg.sources i) (cfg.targets (t.1 j) - cfg.sources j) := by
  simp only [isNonCancellable, IsGVFixedPoint] at ht
  push_neg at ht
  by_cases hσ : t.1 = 1
  · -- σ = 1, but paths are not NI
    have hni := ht hσ
    simp only [IsNonIntersecting] at hni
    push_neg at hni
    obtain ⟨i, j, hij, hcross⟩ := hni
    refine ⟨i, j, hij, ?_⟩
    -- Need to reconcile: paths from toPathTuple vs paths directly
    -- When σ = 1: targets(σ i) = targets(1 i) = targets i
    -- Need to reconcile: toPathTuple applies cast; t.fst needs to be rewritten as 1
    -- Destructure t as ⟨σ, paths⟩ and substitute σ = 1
    obtain ⟨σ, paths⟩ := t
    simp only at hσ; subst hσ
    simp only [Equiv.Perm.one_apply] at hcross ⊢
    unfold PermPathTuple.toPathTuple at hcross
    simpa using hcross
  · -- σ ≠ 1
    exact nonid_perm_paths_cross cfg hwf t.1 hσ t.2

-- ============================================================
-- PART 7g-2: GV Involution Cancellation (Structured Proof)
-- ============================================================

/-- **Helper**: The weight of a non-cancellable (NI identity) tagged tuple is 1,
    since sign(id) = 1. -/
private theorem nonCancellable_weight {r : ℕ} {cfg : LGVConfig r}
    (t : TaggedPathTuple cfg) (ht : isNonCancellable t) :
    taggedWeight t = 1 := by
  obtain ⟨h1, _⟩ := ht
  simp [taggedWeight, h1, Equiv.Perm.sign_one]

/-- **Helper**: The number of non-cancellable tagged tuples equals niTupleCount.

    Both count the same thing: non-intersecting identity path tuples.
    - LHS: tagged tuples ⟨σ, paths⟩ with σ = 1 and paths NI
    - RHS: path tuples with NI property
    The bijection is trivial since PermPathTuple cfg 1 = PathTuple cfg. -/
private theorem card_nonCancellable_eq_niTupleCount {r : ℕ} (cfg : LGVConfig r) :
    ((Finset.univ.filter (fun t : TaggedPathTuple cfg => isNonCancellable t)).card : ℤ) =
    ↑(niTupleCount cfg) := by
  -- Both count NI identity path tuples, just with different packaging.
  -- Since PermPathTuple cfg 1 ≡ PathTuple cfg (definitionally), the bijection is trivial.
  norm_cast
  rw [← @Fintype.card_coe _ (Finset.univ.filter (fun t : TaggedPathTuple cfg => isNonCancellable t))]
  simp only [niTupleCount]
  apply @Fintype.card_congr _ _ _
    (@Subtype.fintype _ _ (fun _ => Classical.dec _) (PathTuple.instFintype cfg))
  exact {
    toFun := fun ⟨t, ht⟩ =>
      let hnc := (Finset.mem_filter.mp ht).2
      ⟨t.2.toPathTuple hnc.choose, hnc.choose_spec⟩
    invFun := fun ⟨p, hp⟩ =>
      ⟨⟨1, p⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨rfl, hp⟩⟩⟩
    left_inv := by
      rintro ⟨⟨σ, paths⟩, hmem⟩
      have hnc := (Finset.mem_filter.mp hmem).2
      have hσ : σ = 1 := hnc.choose
      subst hσ
      exact Subtype.ext (Sigma.ext rfl (heq_of_eq rfl))
    right_inv := by
      rintro ⟨p, hp⟩
      exact Subtype.ext rfl
  }

/-- The first index of the crossing pair for a cancellable tuple. -/
private noncomputable def crossingI {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) : Fin r :=
  (cancellable_has_crossing cfg hwf t ht).choose

/-- The second index of the crossing pair for a cancellable tuple. -/
private noncomputable def crossingJ {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) : Fin r :=
  (cancellable_has_crossing cfg hwf t ht).choose_spec.choose

/-- The crossing pair has i < j. -/
private theorem crossingI_lt_J {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    crossingI cfg hwf t ht < crossingJ cfg hwf t ht :=
  (cancellable_has_crossing cfg hwf t ht).choose_spec.choose_spec.1

/-- The crossing pair has non-intersecting paths. -/
private theorem crossingPair_not_NI {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    ¬NonIntersecting (t.2 (crossingI cfg hwf t ht)).val
      (t.2 (crossingJ cfg hwf t ht)).val cfg.m
      (cfg.sources (crossingI cfg hwf t ht))
      (cfg.sources (crossingJ cfg hwf t ht))
      (cfg.targets (t.1 (crossingI cfg hwf t ht)) - cfg.sources (crossingI cfg hwf t ht))
      (cfg.targets (t.1 (crossingJ cfg hwf t ht)) - cfg.sources (crossingJ cfg hwf t ht)) :=
  (cancellable_has_crossing cfg hwf t ht).choose_spec.choose_spec.2

/-- PathMN m n is always nonempty: there exists at least one lattice path
    with m East and n North steps (namely, all East steps then all North steps). -/
private noncomputable instance pathMN_nonempty (m n : ℕ) : Nonempty (PathMN m n) :=
  Fintype.card_pos_iff.mp (by rw [pathMN_card]; exact Nat.choose_pos (Nat.le_add_right m n))

/-- The "all North then all East" path: n true values followed by m false values.
    This canonical path starts at (0, y₀) and goes North to (0, y₀+n) then East to (m, y₀+n).
    At column 0, it visits all y-values from y₀ to y₀+n. -/
private def northThenEastList (m n : ℕ) : LPath :=
  List.replicate n true ++ List.replicate m false

private lemma northThenEastList_length (m n : ℕ) :
    (northThenEastList m n).length = m + n := by
  simp [northThenEastList, List.length_replicate, Nat.add_comm]

private lemma northThenEastList_east (m n : ℕ) :
    (northThenEastList m n).countP (· = false) = m := by
  simp [northThenEastList, List.countP_append, List.countP_replicate]

/-- The canonical "all North then all East" PathMN. -/
private def northThenEastPath (m n : ℕ) : PathMN m n :=
  ⟨northThenEastList m n, northThenEastList_length m n, northThenEastList_east m n⟩

/-- Cast between PathMN types with equal n preserves the underlying list. -/
private lemma cast_pathMN_val {m n₁ n₂ : ℕ} (hn : n₁ = n₂)
    (p : PathMN m n₁) {heq : PathMN m n₁ = PathMN m n₂} :
    (cast heq p).val = p.val := by
  subst hn; rfl

/-- colEntry of northThenEastList at column 0: the path has n North steps before any East step. -/
private lemma northThenEast_colEntry_one (m n : ℕ) (hm : 0 < m) :
    colEntry (northThenEastList m n) 1 = n := by
  simp only [colEntry]
  -- northBeforeEast (replicate n true ++ replicate m false) 0 = n
  induction n with
  | zero =>
    simp only [northThenEastList, List.replicate_zero, List.nil_append]
    cases m with
    | zero => omega
    | succ m' => rfl
  | succ n' ih =>
    simp only [northThenEastList] at ih
    simp only [northThenEastList, List.replicate_succ, List.cons_append, northBeforeEast]
    omega

/-- Two northThenEast paths overlap at column 0 when well-formedness holds.
    Path P from y₁ visits [y₁, y₁+n₁] at column 0.
    Path Q from y₂ visits [y₂, y₂+n₂] at column 0.
    Overlap iff max(y₁, y₂) ≤ min(y₁+n₁, y₂+n₂),
    which follows from y₁ ≤ y₂+n₂ and y₂ ≤ y₁+n₁ (wellFormed). -/
private lemma northThenEast_not_NI {m n₁ n₂ y₁ y₂ : ℕ}
    (hm : 0 < m) (hy₁n₂ : y₁ ≤ y₂ + n₂) (hy₂n₁ : y₂ ≤ y₁ + n₁) :
    ¬NonIntersecting (northThenEastList m n₁) (northThenEastList m n₂)
      m y₁ y₂ n₁ n₂ := by
  intro ⟨hcols, _⟩
  have h0 := hcols 0 hm
  -- colEntry at 0 is 0, colEntry at 0+1 is n for northThenEast
  have hce1_0 : colEntry (northThenEastList m n₁) 0 = 0 := by simp [colEntry]
  have hce2_0 : colEntry (northThenEastList m n₂) 0 = 0 := by simp [colEntry]
  have hce1_1 : colEntry (northThenEastList m n₁) (0 + 1) = n₁ := by
    show colEntry (northThenEastList m n₁) 1 = n₁
    exact northThenEast_colEntry_one m n₁ hm
  have hce2_1 : colEntry (northThenEastList m n₂) (0 + 1) = n₂ := by
    show colEntry (northThenEastList m n₂) 1 = n₂
    exact northThenEast_colEntry_one m n₂ hm
  rw [hce1_1, hce2_1, hce1_0, hce2_0] at h0
  omega

-- ============================================================
-- PART 7h: GV Involution (using northThenEast for membership)
-- ============================================================

/-- The new permutation under the GV involution.
    Uses RIGHT multiplication σ * swap(i,j). -/
private noncomputable def gvNewPerm {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) : Equiv.Perm (Fin r) :=
  t.1 * Equiv.swap (crossingI cfg hwf t ht) (crossingJ cfg hwf t ht)

/-- The GV involution function on cancellable tagged tuples.
    Maps (σ, paths) to (σ * swap(i,j), new_paths) where (i,j) is the
    crossing pair.

    Path construction: uses northThenEast paths for all indices.
    This ensures the image is always cancellable (northThenEast paths
    cross at column 0 under wellFormed). The self-inverse property
    requires more sophisticated tail-swapped path construction. -/
private noncomputable def gvInvolutionFn {r : ℕ} (cfg : LGVConfig r)
    (hwf : cfg.wellFormed) (t : TaggedPathTuple cfg)
    (ht : ¬isNonCancellable t) : TaggedPathTuple cfg :=
  ⟨gvNewPerm cfg hwf t ht, fun k =>
    northThenEastPath cfg.m (cfg.targets ((gvNewPerm cfg hwf t ht) k) - cfg.sources k)⟩

/-- The first component of gvInvolutionFn is gvNewPerm. -/
private theorem gvInvolutionFn_fst {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    (gvInvolutionFn cfg hwf t ht).1 = gvNewPerm cfg hwf t ht := rfl

/-- The GV involution reverses the sign: taggedWeight(t) + taggedWeight(gv t) = 0. -/
private theorem gvInvolution_sign_reversal {r : ℕ} (cfg : LGVConfig r)
    (hwf : cfg.wellFormed) (t : TaggedPathTuple cfg)
    (ht : t ∈ Finset.univ.filter (fun t : TaggedPathTuple cfg => ¬isNonCancellable t)) :
    taggedWeight t + taggedWeight (gvInvolutionFn cfg hwf t
      ((Finset.mem_filter.mp ht).2)) = 0 := by
  simp only [taggedWeight, gvInvolutionFn_fst, gvNewPerm]
  have hht := (Finset.mem_filter.mp ht).2
  have hij := crossingI_lt_J cfg hwf t hht
  have hsign : Equiv.Perm.sign
      (t.fst * Equiv.swap (crossingI cfg hwf t hht) (crossingJ cfg hwf t hht)) =
      -Equiv.Perm.sign t.fst := by
    rw [map_mul, Equiv.Perm.sign_swap (ne_of_lt hij), mul_neg, mul_one]
  rw [hsign]
  simp [Units.val_neg, add_neg_cancel]

/-- The GV involution has no fixed points on cancellable tuples. -/
private theorem gvInvolution_no_fixed {r : ℕ} (cfg : LGVConfig r)
    (hwf : cfg.wellFormed) (t : TaggedPathTuple cfg)
    (ht : t ∈ Finset.univ.filter (fun t : TaggedPathTuple cfg => ¬isNonCancellable t))
    (hw : taggedWeight t ≠ 0) :
    gvInvolutionFn cfg hwf t ((Finset.mem_filter.mp ht).2) ≠ t := by
  intro heq
  have hht := (Finset.mem_filter.mp ht).2
  have hij := crossingI_lt_J cfg hwf t hht
  have h1 : (gvInvolutionFn cfg hwf t hht).1 = t.1 := congr_arg Sigma.fst heq
  rw [gvInvolutionFn_fst] at h1
  simp only [gvNewPerm] at h1
  have hswap : Equiv.swap (crossingI cfg hwf t hht) (crossingJ cfg hwf t hht) = 1 := by
    have : t.1⁻¹ * (t.1 * Equiv.swap (crossingI cfg hwf t hht) (crossingJ cfg hwf t hht)) =
        t.1⁻¹ * t.1 := by rw [h1]
    rwa [inv_mul_cancel_left, inv_mul_cancel] at this
  have heval : (Equiv.swap (crossingI cfg hwf t hht) (crossingJ cfg hwf t hht))
      (crossingI cfg hwf t hht) = crossingI cfg hwf t hht := by
    rw [hswap]; rfl
  rw [Equiv.swap_apply_left] at heval
  exact absurd heval (ne_of_gt hij)

/-- The GV involution image is cancellable: ¬isNonCancellable(g(t)).
    If σ' = σ * swap(i,j) ≠ 1, the image is trivially cancellable.
    If σ' = 1, the northThenEast paths cross at column 0 (by wellFormed). -/
private theorem gvInvolution_membership {r : ℕ} (cfg : LGVConfig r)
    (hwf : cfg.wellFormed) (t : TaggedPathTuple cfg)
    (ht : ¬isNonCancellable t) :
    ¬isNonCancellable (gvInvolutionFn cfg hwf t ht) := by
  simp only [isNonCancellable, IsGVFixedPoint, not_exists]
  intro hσ hni
  simp only [IsNonIntersecting] at hni
  have hij := crossingI_lt_J cfg hwf t ht
  set ci := crossingI cfg hwf t ht
  set cj := crossingJ cfg hwf t ht
  have hpair := hni ci cj hij
  -- gvNewPerm = 1 from hσ
  have hperm_eq : gvNewPerm cfg hwf t ht = 1 := hσ
  -- The n parameters of the paths match after substitution
  have hn_eq : ∀ k : Fin r, cfg.targets ((gvNewPerm cfg hwf t ht) k) - cfg.sources k =
      cfg.targets k - cfg.sources k := by
    intro k; congr 1; simp [hperm_eq]
  -- Show that the underlying lists in the toPathTuple are northThenEastList
  -- toPathTuple applies cast, gvInvolutionFn gives northThenEastPath
  have hval : ∀ k : Fin r,
      ((gvInvolutionFn cfg hwf t ht).snd.toPathTuple hσ k).val =
      northThenEastList cfg.m (cfg.targets k - cfg.sources k) := by
    intro k
    unfold PermPathTuple.toPathTuple
    simp only [gvInvolutionFn]
    rw [cast_pathMN_val (hn_eq k)]
    simp only [northThenEastPath]
    congr 1; exact hn_eq k
  -- Rewrite hpair using hval
  rw [hval ci, hval cj] at hpair
  -- wellFormed gives overlap conditions
  have hwf_ij : cfg.sources ci ≤ cfg.targets cj := hwf ci cj
  have hwf_ji : cfg.sources cj ≤ cfg.targets ci := hwf cj ci
  -- Case split on m > 0
  have h_ci := cfg.source_le_target ci
  have h_cj := cfg.source_le_target cj
  by_cases hm : 0 < cfg.m
  · -- northThenEast_not_NI needs: y₁ ≤ y₂ + n₂ and y₂ ≤ y₁ + n₁
    -- where y₁ = sources ci, n₁ = targets ci - sources ci, etc.
    -- sources(ci) + (targets(ci) - sources(ci)) = targets(ci) since sources ≤ targets
    have hy₁n₂ : cfg.sources ci ≤ cfg.sources cj + (cfg.targets cj - cfg.sources cj) := by omega
    have hy₂n₁ : cfg.sources cj ≤ cfg.sources ci + (cfg.targets ci - cfg.sources ci) := by omega
    exact northThenEast_not_NI hm hy₁n₂ hy₂n₁ hpair
  · -- m = 0 case: NonIntersecting final condition contradicts wellFormed
    push_neg at hm
    simp only [NonIntersecting] at hpair
    obtain ⟨_, h_final⟩ := hpair
    have hm0 : cfg.m = 0 := by omega
    rw [hm0] at h_final
    simp only [colEntry] at h_final
    have h_ci := cfg.source_le_target ci
    have h_cj := cfg.source_le_target cj
    rcases h_final with h | h <;> omega

-- ============================================================
-- PART 7i: Prefix Lemma for Self-Inverse Proof
-- ============================================================

/-- northBeforeEast depends only on the prefix when the prefix contains > k East steps.
    Key lemma for the GV tail-swap involution: swapping suffixes after a crossing
    point doesn't change colEntry at earlier columns. -/
private lemma northBeforeEast_prefix (pfx sfx₁ sfx₂ : LPath) (k : ℕ)
    (hk : pfx.countP (· = false) > k) :
    northBeforeEast (pfx ++ sfx₁) k = northBeforeEast (pfx ++ sfx₂) k := by
  induction pfx generalizing k with
  | nil => simp only [List.countP_nil] at hk; omega
  | cons b xs ih =>
    cases b with
    | false =>
      cases k with
      | zero => simp [northBeforeEast]
      | succ k' =>
        simp only [List.cons_append, northBeforeEast]
        apply ih k'
        rw [countP_false_cons_false] at hk; omega
    | true =>
      simp only [List.cons_append, northBeforeEast]
      have := ih k (by rw [countP_false_cons_true] at hk; exact hk)
      omega

/-- colEntry at column k+1 depends only on the prefix when it has > k East steps. -/
private lemma colEntry_prefix_eq (pfx sfx₁ sfx₂ : LPath) (k : ℕ)
    (hk : pfx.countP (· = false) > k) :
    colEntry (pfx ++ sfx₁) (k + 1) = colEntry (pfx ++ sfx₂) (k + 1) := by
  exact northBeforeEast_prefix pfx sfx₁ sfx₂ k hk

/-- When a prefix has exactly c East steps, northBeforeEast of the concatenation at c
    is at least the number of North steps in the prefix. This is because scanning the
    prefix accumulates all its North steps, and the suffix can only add more. -/
private lemma northBeforeEast_ge_prefix_true (pfx sfx : LPath) (c : ℕ)
    (hc : pfx.countP (· = false) = c) :
    northBeforeEast (pfx ++ sfx) c ≥ pfx.countP (· = true) := by
  induction pfx generalizing c with
  | nil => simp
  | cons b rest ih =>
    cases b with
    | false =>
      cases c with
      | zero => rw [countP_false_cons_false] at hc; omega
      | succ c' =>
        simp only [List.cons_append, northBeforeEast]
        have htrue : (false :: rest).countP (· = true) = rest.countP (· = true) :=
          List.countP_cons_of_neg (by decide)
        rw [htrue]
        exact ih c' (by rw [countP_false_cons_false] at hc; omega)
    | true =>
      simp only [List.cons_append, northBeforeEast]
      have htrue : (true :: rest).countP (· = true) = rest.countP (· = true) + 1 :=
        List.countP_cons_of_pos (by decide)
      rw [htrue]
      have := ih c (by rw [countP_false_cons_true] at hc; exact hc)
      omega

/-- The North step count in a prefix equals length minus East count. -/
private lemma take_countP_true_eq {m n : ℕ} (P : PathMN m n) (k c' : ℕ)
    (hk : k ≤ P.val.length)
    (heast : (P.val.take k).countP (· = false) = c') :
    (P.val.take k).countP (· = true) = k - c' := by
  have hlen : (P.val.take k).length = k := List.length_take_of_le hk
  have hsum := bool_countP_sum' (P.val.take k)
  omega

/-- toPathTuple preserves .val when σ = 1 (cast doesn't change underlying list). -/
private lemma toPathTuple_val_eq {r : ℕ} {cfg : LGVConfig r} {σ : Equiv.Perm (Fin r)}
    (hσ : σ = 1) (p : PermPathTuple cfg σ) (k : Fin r) :
    (p.toPathTuple hσ k).val = (p k).val := by
  unfold PermPathTuple.toPathTuple
  subst hσ; rfl

-- ============================================================
-- PART 7j: Canonical GV Involution with Tail-Swap (Self-Inverse)
-- ============================================================

/-- Paths i and j share a lattice point at column c: their y-ranges overlap.
    At column c < m, the range is [source + colEntry(c), source + colEntry(c+1)].
    At column c = m, the range is [source + colEntry(m), target(σ(·))]. -/
private def pathsShareCol {r : ℕ} (cfg : LGVConfig r) (t : TaggedPathTuple cfg)
    (c : ℕ) (i j : Fin r) : Prop :=
  let lo_i := cfg.sources i + colEntry (t.2 i).val c
  let hi_i := if c < cfg.m then cfg.sources i + colEntry (t.2 i).val (c + 1)
              else cfg.targets (t.1 i)
  let lo_j := cfg.sources j + colEntry (t.2 j).val c
  let hi_j := if c < cfg.m then cfg.sources j + colEntry (t.2 j).val (c + 1)
              else cfg.targets (t.1 j)
  lo_j ≤ hi_i ∧ lo_i ≤ hi_j

/-- Upper bound on y-values at any shared lattice point.
    Since paths reach at most target(σ(k)) ≤ max(targets), y < yBound. -/
private noncomputable def yBound {r : ℕ} (cfg : LGVConfig r) : ℕ :=
  Finset.univ.sup cfg.targets + 1

/-- Two paths share a specific lattice point (c, y): both visit row y at column c. -/
private def pathsSharePoint {r : ℕ} (cfg : LGVConfig r) (t : TaggedPathTuple cfg)
    (c y : ℕ) (i j : Fin r) : Prop :=
  let lo_i := cfg.sources i + colEntry (t.2 i).val c
  let hi_i := if c < cfg.m then cfg.sources i + colEntry (t.2 i).val (c + 1)
              else cfg.targets (t.1 i)
  let lo_j := cfg.sources j + colEntry (t.2 j).val c
  let hi_j := if c < cfg.m then cfg.sources j + colEntry (t.2 j).val (c + 1)
              else cfg.targets (t.1 j)
  lo_i ≤ y ∧ y ≤ hi_i ∧ lo_j ≤ y ∧ y ≤ hi_j

/-- pathsSharePoint implies pathsShareCol (range overlap). -/
private theorem sharePoint_imp_shareCol {r : ℕ} (cfg : LGVConfig r) (t : TaggedPathTuple cfg)
    (c y : ℕ) (i j : Fin r) (h : pathsSharePoint cfg t c y i j) :
    pathsShareCol cfg t c i j := by
  obtain ⟨hlo_i, hhi_i, hlo_j, hhi_j⟩ := h
  exact ⟨by omega, by omega⟩

/-- pathsShareCol implies existence of a shared point (max of lower bounds). -/
private theorem shareCol_imp_sharePoint {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg)
    (c : ℕ) (i j : Fin r) (h : pathsShareCol cfg t c i j) :
    ∃ y, pathsSharePoint cfg t c y i j := by
  obtain ⟨h1, h2⟩ := h
  let lo_i := cfg.sources i + colEntry (t.2 i).val c
  let lo_j := cfg.sources j + colEntry (t.2 j).val c
  have hii : lo_i ≤ (if c < cfg.m then cfg.sources i + colEntry (t.2 i).val (c + 1)
                    else cfg.targets (t.1 i)) := by
    split_ifs with hc
    · exact Nat.add_le_add_left (colEntry_mono (t.2 i).val c) _
    · have hle := colEntry_le_north (t.2 i) c
      have hsl := hwf i (t.1 i)
      omega
  have hjj : lo_j ≤ (if c < cfg.m then cfg.sources j + colEntry (t.2 j).val (c + 1)
                    else cfg.targets (t.1 j)) := by
    split_ifs with hc
    · exact Nat.add_le_add_left (colEntry_mono (t.2 j).val c) _
    · have hle := colEntry_le_north (t.2 j) c
      have hsl := hwf j (t.1 j)
      omega
  exact ⟨max lo_i lo_j, le_max_left _ _, max_le hii h1, le_max_right _ _, max_le h2 hjj⟩

/-- Crossing code predicate. Encodes (c, y, i, j) as
    n = c * (B * r²) + y * r² + i * r + j, where B = yBound.
    Nat.find on this yields the lex-minimum crossing 4-tuple.
    Scanning y bottom-up ensures the canonical crossing is preserved under tail-swap. -/
private def crossingCode {r : ℕ} (cfg : LGVConfig r) (t : TaggedPathTuple cfg)
    (n : ℕ) : Prop :=
  0 < r ∧
  let B := yBound cfg
  let rr := r * r
  let c := n / (B * rr)
  let yv := (n / rr) % B
  let iv := (n / r) % r
  let jv := n % r
  c ≤ cfg.m ∧ iv < jv ∧
  ∃ (hiv : iv < r) (hjv : jv < r),
    pathsSharePoint cfg t c yv ⟨iv, hiv⟩ ⟨jv, hjv⟩

private noncomputable instance crossingCode.dec {r : ℕ} {cfg : LGVConfig r}
    {t : TaggedPathTuple cfg} : DecidablePred (crossingCode cfg t) :=
  fun _ => Classical.dec _

/-- From ¬NonIntersecting, extract a column where paths overlap. -/
private theorem notNI_gives_overlap {r : ℕ} (cfg : LGVConfig r)
    (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (i j : Fin r) (hij : i < j)
    (hni : ¬NonIntersecting (t.2 i).val (t.2 j).val cfg.m
      (cfg.sources i) (cfg.sources j)
      (cfg.targets (t.1 i) - cfg.sources i) (cfg.targets (t.1 j) - cfg.sources j)) :
    ∃ c, c ≤ cfg.m ∧ pathsShareCol cfg t c i j := by
  simp only [NonIntersecting, not_and_or] at hni
  rcases hni with hinterior | hfinal
  · simp only [not_forall] at hinterior
    obtain ⟨x, hx⟩ := hinterior
    push_neg at hx
    obtain ⟨hxm, hoverlap⟩ := hx
    exact ⟨x, le_of_lt hxm, by
      unfold pathsShareCol
      simp only [if_pos hxm]
      exact hoverlap⟩
  · push_neg at hfinal
    refine ⟨cfg.m, le_refl _, ?_⟩
    unfold pathsShareCol
    simp only [lt_irrefl, ite_false]
    constructor
    · have := hfinal.1
      have h1 := hwf i (t.1 i)
      have h2 := Nat.sub_add_cancel h1
      omega
    · have := hfinal.2
      have h1 := hwf j (t.1 j)
      have h2 := Nat.sub_add_cancel h1
      omega

/-- Encoding (c, y, i, j) as c * (B * r²) + y * r² + i * r + j. -/
private theorem encode4_decode_c (r B c yv iv jv : ℕ) (hr : 0 < r) (hB : 0 < B)
    (hyv : yv < B) (hiv : iv < r) (hjv : jv < r) :
    (c * (B * (r * r)) + yv * (r * r) + iv * r + jv) / (B * (r * r)) = c := by
  have hrr : 0 < r * r := by positivity
  have hBrr : 0 < B * (r * r) := by positivity
  have h1 : yv * (r * r) + iv * r + jv < B * (r * r) := by nlinarith
  have h2 : c * (B * (r * r)) + (yv * (r * r) + iv * r + jv) =
      c * (B * (r * r)) + yv * (r * r) + iv * r + jv := by ring
  exact Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)

private theorem encode4_decode_y (r B c yv iv jv : ℕ) (hr : 0 < r) (hB : 0 < B)
    (hyv : yv < B) (hiv : iv < r) (hjv : jv < r) :
    ((c * (B * (r * r)) + yv * (r * r) + iv * r + jv) / (r * r)) % B = yv := by
  have hrr : 0 < r * r := by positivity
  have h1 : iv * r + jv < r * r := by nlinarith
  have hdiv : (c * (B * (r * r)) + yv * (r * r) + iv * r + jv) / (r * r) = c * B + yv :=
    Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  rw [hdiv, show c * B + yv = yv + B * c from by ring, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hyv

private theorem encode4_decode_i (r B c yv iv jv : ℕ) (hr : 0 < r) (hB : 0 < B)
    (hyv : yv < B) (hiv : iv < r) (hjv : jv < r) :
    ((c * (B * (r * r)) + yv * (r * r) + iv * r + jv) / r) % r = iv := by
  have hdiv : (c * (B * (r * r)) + yv * (r * r) + iv * r + jv) / r =
      c * B * r + yv * r + iv :=
    Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  rw [hdiv, show c * B * r + yv * r + iv = iv + r * (c * B + yv) from by ring,
      Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hiv

private theorem encode4_decode_j (r B c yv iv jv : ℕ) (hr : 0 < r) (hB : 0 < B)
    (hyv : yv < B) (hiv : iv < r) (hjv : jv < r) :
    (c * (B * (r * r)) + yv * (r * r) + iv * r + jv) % r = jv := by
  have : c * (B * (r * r)) + yv * (r * r) + iv * r + jv =
      jv + r * (c * B * r + yv * r + iv) := by ring
  rw [this, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hjv

/-- y at any shared point is < yBound (needed for encoding). -/
private theorem y_lt_yBound {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (c y : ℕ) (i j : Fin r)
    (h : pathsSharePoint cfg t c y i j) : y < yBound cfg := by
  obtain ⟨_, hhi, _, _⟩ := h
  have : y ≤ cfg.targets (t.1 i) := by
    split_ifs at hhi with hcm
    · -- c < m: y ≤ source + colEntry(c+1) ≤ source + n = target
      have hle := colEntry_le_north (t.2 i) (c + 1)
      have hsrc := hwf i (t.1 i)
      omega
    · exact hhi
  calc y ≤ cfg.targets (t.1 i) := this
    _ ≤ Finset.univ.sup cfg.targets := Finset.le_sup (Finset.mem_univ _)
    _ < yBound cfg := by unfold yBound; omega

/-- A crossing code exists for every cancellable tagged tuple. -/
private theorem crossingCode_exists {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    ∃ n, crossingCode cfg t n := by
  obtain ⟨i, j, hij, hni⟩ := cancellable_has_crossing cfg hwf t ht
  obtain ⟨c, hcm, hoverlap⟩ := notNI_gives_overlap cfg hwf t i j hij hni
  obtain ⟨y, hshare⟩ := shareCol_imp_sharePoint cfg hwf t c i j hoverlap
  have hr : 0 < r := by omega
  have hB : 0 < yBound cfg := by unfold yBound; omega
  have hyB := y_lt_yBound cfg hwf t c y i j hshare
  set B := yBound cfg
  refine ⟨c * (B * (r * r)) + y * (r * r) + i.val * r + j.val, hr, ?_, ?_, ?_⟩
  · rwa [encode4_decode_c r B c y i.val j.val hr hB hyB i.isLt j.isLt]
  · rw [encode4_decode_i r B c y i.val j.val hr hB hyB i.isLt j.isLt,
        encode4_decode_j r B c y i.val j.val hr hB hyB i.isLt j.isLt]
    exact hij
  · rw [encode4_decode_c r B c y i.val j.val hr hB hyB i.isLt j.isLt,
        encode4_decode_y r B c y i.val j.val hr hB hyB i.isLt j.isLt,
        encode4_decode_i r B c y i.val j.val hr hB hyB i.isLt j.isLt,
        encode4_decode_j r B c y i.val j.val hr hB hyB i.isLt j.isLt]
    exact ⟨i.isLt, j.isLt, hshare⟩

/-- The canonical crossing code for a cancellable tagged tuple. -/
private noncomputable def canonCrossN {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) : ℕ :=
  Nat.find (crossingCode_exists cfg hwf t ht)

/-- The canonical crossing satisfies the crossing predicate. -/
private theorem canonCross_spec {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    crossingCode cfg t (canonCrossN cfg hwf t ht) :=
  Nat.find_spec (crossingCode_exists cfg hwf t ht)

/-- The canonical crossing is minimal. -/
private theorem canonCross_min {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    ∀ n, crossingCode cfg t n → canonCrossN cfg hwf t ht ≤ n :=
  fun n hn => Nat.find_min' (crossingCode_exists cfg hwf t ht) hn

/-- Extract the canonical crossing column from (c, y, i, j) encoding. -/
private noncomputable def canonCol {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) : ℕ :=
  canonCrossN cfg hwf t ht / (yBound cfg * (r * r))

/-- Extract the canonical shared y-value from the encoding. -/
private noncomputable def canonY {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) : ℕ :=
  (canonCrossN cfg hwf t ht / (r * r)) % yBound cfg

/-- Extract the canonical first crossing index. -/
private noncomputable def canonI {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) : Fin r :=
  ⟨(canonCrossN cfg hwf t ht / r) % r,
    (canonCross_spec cfg hwf t ht).2.2.2.choose⟩

/-- Extract the canonical second crossing index. -/
private noncomputable def canonJ {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) : Fin r :=
  ⟨canonCrossN cfg hwf t ht % r,
    (canonCross_spec cfg hwf t ht).2.2.2.choose_spec.choose⟩

private theorem canonI_lt_canonJ {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    canonI cfg hwf t ht < canonJ cfg hwf t ht := by
  have h := canonCross_spec cfg hwf t ht
  exact h.2.2.1

private theorem canonCol_le_m {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    canonCol cfg hwf t ht ≤ cfg.m := by
  have h := canonCross_spec cfg hwf t ht
  exact h.2.1

/-- The canonical crossing is a shared point (not just range overlap). -/
private theorem canon_sharePoint {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    pathsSharePoint cfg t (canonCol cfg hwf t ht) (canonY cfg hwf t ht)
      (canonI cfg hwf t ht) (canonJ cfg hwf t ht) := by
  have h := canonCross_spec cfg hwf t ht
  exact h.2.2.2.choose_spec.choose_spec

private theorem canon_overlap {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    pathsShareCol cfg t (canonCol cfg hwf t ht)
      (canonI cfg hwf t ht) (canonJ cfg hwf t ht) :=
  sharePoint_imp_shareCol _ _ _ _ _ _ (canon_sharePoint cfg hwf t ht)

-- ============================================================
-- PART 7k: Tail-Swap PathMN Construction
-- ============================================================

/-- Construct a new PathMN by taking a prefix from one path and suffix from another.
    Given paths P (m East, n₁ North) and Q (m East, n₂ North), and split positions
    k_p in P, k_q in Q where both have seen exactly c East steps:
    Result: take(P, k_p) ++ drop(Q, k_q) is a valid PathMN m n'
    where n' = k_p - c + (n₂ - (k_q - c)) = (k_p + n₂ + c - k_q - c) = k_p + n₂ - k_q.
    Actually n' depends on the North step counts. -/
private noncomputable def tailSwapPath {m n₁ n₂ : ℕ}
    (P : PathMN m n₁) (Q : PathMN m n₂) (kp kq : ℕ)
    (hkp_east : (P.val.take kp).countP (· = false) = (Q.val.take kq).countP (· = false))
    (hkp_le : kp ≤ P.val.length) (hkq_le : kq ≤ Q.val.length) :
    PathMN m (kp + n₂ - kq) where
  val := P.val.take kp ++ Q.val.drop kq
  property := by
    constructor
    · -- Length: kp + (m + n₂ - kq) = m + (kp + n₂ - kq)
      rw [List.length_append, List.length_take, List.length_drop,
          min_eq_left hkp_le]
      have hlen_q := Q.property.1
      -- Need kq ≤ kp + n₂ (north steps in take Q kq ≤ n₂)
      have heast_q := Q.property.2
      have htake_len_p : (P.val.take kp).length = kp :=
        List.length_take_of_le hkp_le
      have htake_len_q : (Q.val.take kq).length = kq :=
        List.length_take_of_le hkq_le
      have hsum_take_p := bool_countP_sum' (P.val.take kp)
      have hsum_take_q := bool_countP_sum' (Q.val.take kq)
      have hsum_all_q := bool_countP_sum' Q.val
      -- true count in take Q kq ≤ n₂ (total true count)
      have htrue_split : Q.val.countP (· = true) =
          (Q.val.take kq).countP (· = true) + (Q.val.drop kq).countP (· = true) := by
        conv_lhs => rw [show Q.val = Q.val.take kq ++ Q.val.drop kq from
          (List.take_append_drop kq Q.val).symm]
        exact List.countP_append
      omega
    · -- East count: prefix has c East steps, suffix has m - c East steps
      have heast_p := P.property.2
      have heast_q := Q.property.2
      -- Split East count of Q into take + drop
      have hfalse_split_q : Q.val.countP (· = false) =
          (Q.val.take kq).countP (· = false) + (Q.val.drop kq).countP (· = false) := by
        conv_lhs => rw [show Q.val = Q.val.take kq ++ Q.val.drop kq from
          (List.take_append_drop kq Q.val).symm]
        exact List.countP_append
      have hdrop : (Q.val.drop kq).countP (· = false) = m - (Q.val.take kq).countP (· = false) := by
        omega
      -- The concatenated path has countP = take_P + drop_Q
      have : (P.val.take kp ++ Q.val.drop kq).countP (· = false) =
          (P.val.take kp).countP (· = false) + (Q.val.drop kq).countP (· = false) :=
        List.countP_append
      rw [this, hdrop, hkp_east]
      omega

/-- Split position in path k at shared point (c, y): c + (y - source(k)) -/
private noncomputable def splitPosAt {r : ℕ} (cfg : LGVConfig r) (t : TaggedPathTuple cfg)
    (c y : ℕ) (k : Fin r) : ℕ :=
  c + (y - cfg.sources k)

/-- The canonical new permutation. -/
private noncomputable def canonNewPerm {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) : Equiv.Perm (Fin r) :=
  t.1 * Equiv.swap (canonI cfg hwf t ht) (canonJ cfg hwf t ht)

/-- For PathMN m n, colEntry at m+1 equals n (total North steps).
    northBeforeEast l m counts all North steps when l has exactly m East steps. -/
private lemma colEntry_at_end {m n : ℕ} (P : PathMN m n) :
    colEntry P.val (m + 1) = n := by
  simp only [colEntry]
  -- northBeforeEast P.val m = n: counts all North steps since there are exactly m East steps
  have heast := P.property.2
  have hlen := P.property.1
  -- Proof by induction on the list
  suffices ∀ (l : LPath) (k : ℕ), l.countP (· = false) = k →
      northBeforeEast l k = l.countP (· = true) by
    rw [this P.val m heast, pathMN_countP_true P]
  intro l k hk
  induction l generalizing k with
  | nil => simp [northBeforeEast]
  | cons b xs ih =>
    cases b with
    | false =>
      cases k with
      | zero => rw [countP_false_cons_false] at hk; omega
      | succ k' =>
        simp only [northBeforeEast]
        have htrue : (false :: xs).countP (· = true) = xs.countP (· = true) :=
          List.countP_cons_of_neg (by decide)
        rw [htrue]
        exact ih k' (by rw [countP_false_cons_false] at hk; omega)
    | true =>
      simp only [northBeforeEast]
      have htrue : (true :: xs).countP (· = true) = xs.countP (· = true) + 1 :=
        List.countP_cons_of_pos (by decide)
      have hk' : xs.countP (· = false) = k := by rw [countP_false_cons_true] at hk; exact hk
      rw [htrue, ih k hk']; omega

/-- The shared y-value is within path i's y-range at the canonical crossing column. -/
private theorem canonY_in_range_i {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    let ci := canonI cfg hwf t ht
    let c := canonCol cfg hwf t ht
    let y := canonY cfg hwf t ht
    colEntry (t.2 ci).val c ≤ y - cfg.sources ci ∧
    y - cfg.sources ci ≤ colEntry (t.2 ci).val (c + 1) := by
  have hsp := canon_sharePoint cfg hwf t ht
  set ci := canonI cfg hwf t ht
  set c := canonCol cfg hwf t ht
  set y := canonY cfg hwf t ht
  obtain ⟨hlo_i, hhi_i, _, _⟩ := hsp
  constructor
  · omega
  · split_ifs at hhi_i with hcm
    · omega
    · have hcm' := canonCol_le_m cfg hwf t ht
      have hceq : c = cfg.m := by omega
      rw [hceq, colEntry_at_end (t.2 ci)]
      have h_le := hwf ci (t.1 ci)
      omega

/-- The shared y-value is within path j's y-range at the canonical crossing column. -/
private theorem canonY_in_range_j {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    let cj := canonJ cfg hwf t ht
    let c := canonCol cfg hwf t ht
    let y := canonY cfg hwf t ht
    colEntry (t.2 cj).val c ≤ y - cfg.sources cj ∧
    y - cfg.sources cj ≤ colEntry (t.2 cj).val (c + 1) := by
  have hsp := canon_sharePoint cfg hwf t ht
  set cj := canonJ cfg hwf t ht
  set c := canonCol cfg hwf t ht
  set y := canonY cfg hwf t ht
  obtain ⟨_, _, hlo_j, hhi_j⟩ := hsp
  constructor
  · omega
  · split_ifs at hhi_j with hcm
    · omega
    · have hcm' := canonCol_le_m cfg hwf t ht
      have hceq : c = cfg.m := by omega
      rw [hceq, colEntry_at_end (t.2 cj)]
      have h_le := hwf cj (t.1 cj)
      omega

/-- Split position is within path bounds. -/
private theorem splitPos_le_length {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t)
    (k : Fin r) (hk : k = canonI cfg hwf t ht ∨ k = canonJ cfg hwf t ht) :
    splitPosAt cfg t (canonCol cfg hwf t ht) (canonY cfg hwf t ht) k ≤
      (t.2 k).val.length := by
  set c := canonCol cfg hwf t ht
  set y := canonY cfg hwf t ht
  simp only [splitPosAt]
  have hlen := (t.2 k).property.1
  have hce := colEntry_le_north (t.2 k) (c + 1)
  have hcm := canonCol_le_m cfg hwf t ht
  rcases hk with rfl | rfl
  · have ⟨_, hhi⟩ := canonY_in_range_i cfg hwf t ht
    have hwf_k := hwf (canonI cfg hwf t ht) (t.1 (canonI cfg hwf t ht))
    -- y - sources ≤ colEntry ≤ targets - sources, c ≤ m
    have hbound : y - cfg.sources (canonI cfg hwf t ht) ≤
        cfg.targets (t.1 (canonI cfg hwf t ht)) - cfg.sources (canonI cfg hwf t ht) :=
      le_trans hhi hce
    omega
  · have ⟨_, hhi⟩ := canonY_in_range_j cfg hwf t ht
    have hwf_k := hwf (canonJ cfg hwf t ht) (t.1 (canonJ cfg hwf t ht))
    have hbound : y - cfg.sources (canonJ cfg hwf t ht) ≤
        cfg.targets (t.1 (canonJ cfg hwf t ht)) - cfg.sources (canonJ cfg hwf t ht) :=
      le_trans hhi hce
    omega

/-- Both split positions have the same East count (= canonical column). -/
private theorem splitPos_east_eq {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    let ci := canonI cfg hwf t ht
    let cj := canonJ cfg hwf t ht
    let c := canonCol cfg hwf t ht
    let y := canonY cfg hwf t ht
    let ki := splitPosAt cfg t c y ci
    let kj := splitPosAt cfg t c y cj
    ((t.2 ci).val.take ki).countP (· = false) =
    ((t.2 cj).val.take kj).countP (· = false) := by
  set ci := canonI cfg hwf t ht
  set cj := canonJ cfg hwf t ht
  set c := canonCol cfg hwf t ht
  set y := canonY cfg hwf t ht
  simp only [splitPosAt]
  have hc_le := canonCol_le_m cfg hwf t ht
  have ⟨hlo_i, hhi_i⟩ := canonY_in_range_i cfg hwf t ht
  have ⟨hlo_j, hhi_j⟩ := canonY_in_range_j cfg hwf t ht
  have hlen_ci : (t.2 ci).val.length = cfg.m + (cfg.targets (t.1 ci) - cfg.sources ci) :=
    (t.2 ci).property.1
  have hlen_cj : (t.2 cj).val.length = cfg.m + (cfg.targets (t.1 cj) - cfg.sources cj) :=
    (t.2 cj).property.1
  have hce_ci := colEntry_le_north (t.2 ci) (c + 1)
  have hce_cj := colEntry_le_north (t.2 cj) (c + 1)
  have heast_ci_eq := (t.2 ci).property.2
  have heast_cj_eq := (t.2 cj).property.2
  have heast_ci := take_east_count_within_column (t.2 ci).val c (y - cfg.sources ci)
    (by omega) hlo_i hhi_i
  have heast_cj := take_east_count_within_column (t.2 cj).val c (y - cfg.sources cj)
    (by omega) hlo_j hhi_j
  rw [heast_ci, heast_cj]

/-- The tail-swap n parameter for path ci matches what PermPathTuple expects. -/
private theorem tailSwap_n_ci {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    let ci := canonI cfg hwf t ht
    let cj := canonJ cfg hwf t ht
    let c := canonCol cfg hwf t ht
    let y := canonY cfg hwf t ht
    let ki := splitPosAt cfg t c y ci
    let kj := splitPosAt cfg t c y cj
    ki + (cfg.targets (t.1 cj) - cfg.sources cj) - kj =
      cfg.targets (t.1 cj) - cfg.sources ci := by
  have hsp := canon_sharePoint cfg hwf t ht
  obtain ⟨hlo_i, _, hlo_j, _⟩ := hsp
  have hwfij := hwf (canonI cfg hwf t ht) (t.1 (canonJ cfg hwf t ht))
  have hwfjj := hwf (canonJ cfg hwf t ht) (t.1 (canonJ cfg hwf t ht))
  simp only [splitPosAt]; omega

/-- The tail-swap n parameter for path cj matches what PermPathTuple expects. -/
private theorem tailSwap_n_cj {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    let ci := canonI cfg hwf t ht
    let cj := canonJ cfg hwf t ht
    let c := canonCol cfg hwf t ht
    let y := canonY cfg hwf t ht
    let ki := splitPosAt cfg t c y ci
    let kj := splitPosAt cfg t c y cj
    kj + (cfg.targets (t.1 ci) - cfg.sources ci) - ki =
      cfg.targets (t.1 ci) - cfg.sources cj := by
  have hsp := canon_sharePoint cfg hwf t ht
  obtain ⟨hlo_i, _, hlo_j, _⟩ := hsp
  have hwfji := hwf (canonJ cfg hwf t ht) (t.1 (canonI cfg hwf t ht))
  have hwfii := hwf (canonI cfg hwf t ht) (t.1 (canonI cfg hwf t ht))
  simp only [splitPosAt]; omega

private lemma cast_PathMN_val {m n₁ n₂ : ℕ} (h : n₁ = n₂) (e : PathMN m n₁) :
    (cast (congrArg (PathMN m) h) e).val = e.val := by
  cases h; rfl

/-- The canonical GV involution: tail-swap at the lex-min crossing point.
    For paths ci and cj, we swap suffixes at the shared lattice point (c, y).
    Other paths are unchanged (with cast for type compatibility). -/
private noncomputable def gvCanonInv {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) : TaggedPathTuple cfg :=
  let ci := canonI cfg hwf t ht
  let cj := canonJ cfg hwf t ht
  let c := canonCol cfg hwf t ht
  let y := canonY cfg hwf t ht
  let σ' := canonNewPerm cfg hwf t ht
  let ki := splitPosAt cfg t c y ci
  let kj := splitPosAt cfg t c y cj
  ⟨σ', fun k =>
    if hk_ci : k = ci then
      cast (congrArg (PathMN cfg.m) (by
          subst hk_ci
          have hσ'ci : σ' ci = t.1 cj := by
            simp only [show σ' = t.1 * Equiv.swap ci cj from rfl,
              Equiv.Perm.mul_apply, Equiv.swap_apply_left]
          rw [hσ'ci]
          exact tailSwap_n_ci cfg hwf t ht)) <|
        tailSwapPath (t.2 ci) (t.2 cj) ki kj
          (splitPos_east_eq cfg hwf t ht)
          (splitPos_le_length cfg hwf t ht ci (Or.inl rfl))
          (splitPos_le_length cfg hwf t ht cj (Or.inr rfl))
    else if hk_cj : k = cj then
      cast (congrArg (PathMN cfg.m) (by
          subst hk_cj
          have hσ'cj : σ' cj = t.1 ci := by
            simp only [show σ' = t.1 * Equiv.swap ci cj from rfl,
              Equiv.Perm.mul_apply, Equiv.swap_apply_right]
          rw [hσ'cj]
          exact tailSwap_n_cj cfg hwf t ht)) <|
        tailSwapPath (t.2 cj) (t.2 ci) kj ki
          (by rw [splitPos_east_eq cfg hwf t ht])
          (splitPos_le_length cfg hwf t ht cj (Or.inr rfl))
          (splitPos_le_length cfg hwf t ht ci (Or.inl rfl))
    else
      cast (congrArg (PathMN cfg.m) (by
          have hσ'k : σ' k = t.1 k := by
            simp only [show σ' = t.1 * Equiv.swap ci cj from rfl,
              Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hk_ci hk_cj]
          rw [hσ'k])) (t.2 k)⟩

-- ============================================================
-- PART 7l: Involution Properties
-- ============================================================

-- Helper lemmas for gvCanonInv path value extraction.
-- Using let-bound variables (not `set`) so that simp's zeta-reduction
-- makes the dite conditions syntactically identical, enabling dif_pos/neg to fire.

private lemma gvCanonInv_val_ci {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    ((gvCanonInv cfg hwf t ht).2 (canonI cfg hwf t ht)).val =
    (t.2 (canonI cfg hwf t ht)).val.take
      (splitPosAt cfg t (canonCol cfg hwf t ht) (canonY cfg hwf t ht) (canonI cfg hwf t ht)) ++
    (t.2 (canonJ cfg hwf t ht)).val.drop
      (splitPosAt cfg t (canonCol cfg hwf t ht) (canonY cfg hwf t ht) (canonJ cfg hwf t ht)) := by
  simp only [gvCanonInv, dite_true, tailSwapPath, cast_PathMN_val, Subtype.coe_mk]

private lemma gvCanonInv_val_cj {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) :
    ((gvCanonInv cfg hwf t ht).2 (canonJ cfg hwf t ht)).val =
    (t.2 (canonJ cfg hwf t ht)).val.take
      (splitPosAt cfg t (canonCol cfg hwf t ht) (canonY cfg hwf t ht) (canonJ cfg hwf t ht)) ++
    (t.2 (canonI cfg hwf t ht)).val.drop
      (splitPosAt cfg t (canonCol cfg hwf t ht) (canonY cfg hwf t ht) (canonI cfg hwf t ht)) := by
  have hij := canonI_lt_canonJ cfg hwf t ht
  simp only [gvCanonInv, dif_neg (Fin.ne_of_gt hij), dite_true, tailSwapPath, cast_PathMN_val,
    Subtype.coe_mk]

private lemma gvCanonInv_val_other {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) (k : Fin r)
    (hk_ci : k ≠ canonI cfg hwf t ht) (hk_cj : k ≠ canonJ cfg hwf t ht) :
    ((gvCanonInv cfg hwf t ht).2 k).val = (t.2 k).val := by
  simp only [gvCanonInv, dif_neg hk_ci, dif_neg hk_cj]
  exact cast_PathMN_val _ _

/-- Sign reversal: canonNewPerm has opposite sign. -/
private theorem gvCanon_sign_reversal {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg)
    (ht : t ∈ Finset.univ.filter (fun t : TaggedPathTuple cfg => ¬isNonCancellable t)) :
    taggedWeight t + taggedWeight (gvCanonInv cfg hwf t
      ((Finset.mem_filter.mp ht).2)) = 0 := by
  simp only [taggedWeight, gvCanonInv]
  have hht := (Finset.mem_filter.mp ht).2
  have hij := canonI_lt_canonJ cfg hwf t hht
  simp only [canonNewPerm]
  rw [map_mul, Equiv.Perm.sign_swap (ne_of_lt hij), mul_neg, mul_one]
  simp [Units.val_neg, add_neg_cancel]

/-- No fixed points: the image differs from the input. -/
private theorem gvCanon_no_fixed {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg)
    (ht : t ∈ Finset.univ.filter (fun t : TaggedPathTuple cfg => ¬isNonCancellable t))
    (hw : taggedWeight t ≠ 0) :
    gvCanonInv cfg hwf t ((Finset.mem_filter.mp ht).2) ≠ t := by
  intro heq
  have hht := (Finset.mem_filter.mp ht).2
  have hij := canonI_lt_canonJ cfg hwf t hht
  have h1 : (gvCanonInv cfg hwf t hht).1 = t.1 := congr_arg Sigma.fst heq
  simp only [gvCanonInv, canonNewPerm] at h1
  have hswap : Equiv.swap (canonI cfg hwf t hht) (canonJ cfg hwf t hht) = 1 := by
    have : t.1⁻¹ * (t.1 * Equiv.swap (canonI cfg hwf t hht) (canonJ cfg hwf t hht)) =
        t.1⁻¹ * t.1 := by rw [h1]
    rwa [inv_mul_cancel_left, inv_mul_cancel] at this
  have heval : (Equiv.swap (canonI cfg hwf t hht) (canonJ cfg hwf t hht))
      (canonI cfg hwf t hht) = canonI cfg hwf t hht := by
    rw [hswap]; rfl
  rw [Equiv.swap_apply_left] at heval
  exact absurd heval (ne_of_gt hij)

/-- The GV canonical involution image is cancellable. -/
private theorem gvCanon_membership {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg)
    (ht : t ∈ Finset.univ.filter (fun t : TaggedPathTuple cfg => ¬isNonCancellable t)) :
    gvCanonInv cfg hwf t ((Finset.mem_filter.mp ht).2) ∈
      Finset.univ.filter (fun t : TaggedPathTuple cfg => ¬isNonCancellable t) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hht := (Finset.mem_filter.mp ht).2
  -- Need: ¬isNonCancellable(g(t))
  -- i.e., ¬(σ' = 1 ∧ paths NI)
  simp only [isNonCancellable, IsGVFixedPoint, not_exists]
  intro hσ' hni
  -- We have σ' = σ * swap(ci, cj)
  set ci := canonI cfg hwf t hht
  set cj := canonJ cfg hwf t hht
  have hij := canonI_lt_canonJ cfg hwf t hht
  -- σ' = 1 means σ = swap(ci, cj)
  simp only [gvCanonInv, canonNewPerm] at hσ'
  have hσ_eq : t.1 = Equiv.swap ci cj := by
    have h1 : t.1 * Equiv.swap ci cj = 1 := hσ'
    have h2 : t.1 = (Equiv.swap ci cj)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
    rw [h2, Equiv.swap_inv]
  -- The tail-swapped paths share the canonical crossing point (c, y),
  -- contradicting NI. Both image paths have y in their y-range at column c:
  -- prefix preservation gives colEntry(img, c) = colEntry(orig, c) ≤ y - src,
  -- and northBeforeEast_ge_prefix_true gives colEntry(img, c+1) ≥ y - src.
  set c := canonCol cfg hwf t hht
  set y := canonY cfg hwf t hht
  set ki := splitPosAt cfg t c y ci
  set kj := splitPosAt cfg t c y cj
  have ⟨hlo_i, hhi_i⟩ := canonY_in_range_i cfg hwf t hht
  have ⟨hlo_j, hhi_j⟩ := canonY_in_range_j cfg hwf t hht
  have hcm := canonCol_le_m cfg hwf t hht
  -- Extract NonIntersecting at (ci, cj) and unfold to conjunction
  have hpair := hni ci cj hij
  simp only [NonIntersecting] at hpair
  obtain ⟨hinterior, hfinal⟩ := hpair
  -- Rewrite image paths to tail-swap lists via toPathTuple_val_eq + gvCanonInv unfolding
  have hval_ci := toPathTuple_val_eq hσ' (gvCanonInv cfg hwf t hht).2 ci
  have hval_cj := toPathTuple_val_eq hσ' (gvCanonInv cfg hwf t hht).2 cj
  have himg_ci : ((gvCanonInv cfg hwf t hht).2 ci).val =
      (t.2 ci).val.take ki ++ (t.2 cj).val.drop kj :=
    gvCanonInv_val_ci cfg hwf t hht
  have himg_cj : ((gvCanonInv cfg hwf t hht).2 cj).val =
      (t.2 cj).val.take kj ++ (t.2 ci).val.drop ki :=
    gvCanonInv_val_cj cfg hwf t hht
  -- Establish prefix East counts = c (from take_east_count_within_column)
  have hlen_ci' : (t.2 ci).val.length = cfg.m + (cfg.targets (t.1 ci) - cfg.sources ci) :=
    (t.2 ci).property.1
  have hlen_cj' : (t.2 cj).val.length = cfg.m + (cfg.targets (t.1 cj) - cfg.sources cj) :=
    (t.2 cj).property.1
  have hce_ci' := colEntry_le_north (t.2 ci) (c + 1)
  have hce_cj' := colEntry_le_north (t.2 cj) (c + 1)
  have heast_ci_eq' := (t.2 ci).property.2
  have heast_cj_eq' := (t.2 cj).property.2
  have heast_ci := take_east_count_within_column (t.2 ci).val c (y - cfg.sources ci)
    (by omega) hlo_i hhi_i
  have heast_cj := take_east_count_within_column (t.2 cj).val c (y - cfg.sources cj)
    (by omega) hlo_j hhi_j
  -- Prefix North count = ki - c = y - src (from bool_countP_sum')
  have htrue_ci := take_countP_true_eq (t.2 ci) ki c
    (splitPos_le_length cfg hwf t hht ci (Or.inl rfl))
    heast_ci
  have htrue_cj := take_countP_true_eq (t.2 cj) kj c
    (splitPos_le_length cfg hwf t hht cj (Or.inr rfl))
    heast_cj
  have hpfx_ci : (List.take ki (t.2 ci).val).countP (· = false) = c := heast_ci
  have hpfx_cj : (List.take kj (t.2 cj).val).countP (· = false) = c := heast_cj
  -- Key bounds: colEntry(img, c+1) ≥ y - src (from northBeforeEast_ge_prefix_true)
  have hge_ci := northBeforeEast_ge_prefix_true _ _ c hpfx_ci
  have hge_cj := northBeforeEast_ge_prefix_true _ _ c hpfx_cj
  rw [htrue_ci] at hge_ci; rw [htrue_cj] at hge_cj
  -- Rewrite hinterior and hfinal to use tail-swap lists
  rw [hval_ci, himg_ci, hval_cj, himg_cj] at hinterior hfinal
  -- Case split on c < m (interior) vs c = m (final column)
  by_cases hc_lt : c < cfg.m
  · -- Interior: NonIntersecting at x = c fails (both disjuncts impossible)
    have hcol := hinterior c hc_lt
    simp only [colEntry] at hcol
    cases c with
    | zero =>
      simp only [splitPosAt] at ki kj
      rcases hcol with h | h <;> omega
    | succ c' =>
      -- colEntry at c'+1 preserved: northBeforeEast_prefix (prefix has c'+1 > c' East)
      have heq_ci : northBeforeEast ((t.2 ci).val.take ki ++ (t.2 cj).val.drop kj) c' =
          northBeforeEast (t.2 ci).val c' := by
        rw [show (t.2 ci).val = (t.2 ci).val.take ki ++ (t.2 ci).val.drop ki from
          (List.take_append_drop ki (t.2 ci).val).symm]
        exact northBeforeEast_prefix _ _ _ c' (by rw [hpfx_ci]; omega)
      have heq_cj : northBeforeEast ((t.2 cj).val.take kj ++ (t.2 ci).val.drop ki) c' =
          northBeforeEast (t.2 cj).val c' := by
        rw [show (t.2 cj).val = (t.2 cj).val.take kj ++ (t.2 cj).val.drop kj from
          (List.take_append_drop kj (t.2 cj).val).symm]
        exact northBeforeEast_prefix _ _ _ c' (by rw [hpfx_cj]; omega)
      simp only [splitPosAt] at ki kj
      rcases hcol with h | h <;> omega
  · -- Final column: c = m
    push_neg at hc_lt; have hceq : c = cfg.m := by omega; subst hceq
    -- y ≤ targets(ci) and y ≤ targets(cj) from canonY_in_range with σ = swap
    have hy_le_ti : y ≤ cfg.targets ci := by
      have h := (canonY_in_range_j cfg hwf t hht).2
      split_ifs at h with hcm; · omega
      rw [colEntry_at_end, hσ_eq, Equiv.swap_apply_right] at h; omega
    have hy_le_tj : y ≤ cfg.targets cj := by
      have h := (canonY_in_range_i cfg hwf t hht).2
      split_ifs at h with hcm; · omega
      rw [colEntry_at_end, hσ_eq, Equiv.swap_apply_left] at h; omega
    cases cfg.m with
    | zero =>
      simp only [colEntry] at hfinal
      rcases hfinal with h | h <;> omega
    | succ m' =>
      have heq_ci : northBeforeEast ((t.2 ci).val.take ki ++ (t.2 cj).val.drop kj) m' =
          northBeforeEast (t.2 ci).val m' := by
        rw [show (t.2 ci).val = (t.2 ci).val.take ki ++ (t.2 ci).val.drop ki from
          (List.take_append_drop ki (t.2 ci).val).symm]
        exact northBeforeEast_prefix _ _ _ m' (by rw [hpfx_ci]; omega)
      have heq_cj : northBeforeEast ((t.2 cj).val.take kj ++ (t.2 ci).val.drop ki) m' =
          northBeforeEast (t.2 cj).val m' := by
        rw [show (t.2 cj).val = (t.2 cj).val.take kj ++ (t.2 cj).val.drop kj from
          (List.take_append_drop kj (t.2 cj).val).symm]
        exact northBeforeEast_prefix _ _ _ m' (by rw [hpfx_cj]; omega)
      simp only [colEntry] at hfinal
      simp only [splitPosAt] at ki kj
      rcases hfinal with h | h <;> omega

/-- Helper: take of a concat where the prefix has the right length. -/
private lemma take_take_append {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).take l₁.length = l₁ := by
  rw [List.take_append, Nat.sub_self, List.take_length, List.take_zero,
      List.append_nil]

/-- Helper: drop of a concat where the prefix has the right length. -/
private lemma drop_take_append {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).drop l₁.length = l₂ := by
  rw [List.drop_append, Nat.sub_self, List.drop_length, List.nil_append,
      List.drop_zero]

/-- When two codes have the same column component and n < N, decoded y of n ≤ decoded y of N. -/
private lemma decoded_y_le {rr B n N : ℕ} (hrr : 0 < rr) (hBrr : 0 < B * rr)
    (hn : n < N) (hc : n / (B * rr) = N / (B * rr)) :
    (n / rr) % B ≤ (N / rr) % B := by
  have h1 : n / rr ≤ N / rr := Nat.div_le_div_right (le_of_lt hn)
  have h2 : n / rr / B = N / rr / B := by
    simp only [Nat.div_div_eq_div_mul, mul_comm rr B]; exact hc
  have h3 := Nat.div_add_mod (n / rr) B
  have h4 := Nat.div_add_mod (N / rr) B
  -- B * q is nonlinear so omega can't handle it; use linarith with B*(n/rr/B) = B*(N/rr/B)
  have hc_eq : B * (n / rr / B) = B * (N / rr / B) := by rw [h2]
  linarith [h1, h3, h4, hc_eq]

/-- The canonical crossing code is preserved under the GV involution.
    Key insight: with the (c, y, i, j) encoding scanning y bottom-up,
    the tail swap at point (c₀, y₀) preserves all crossings at (c', y', i', j')
    with code ≤ canonCrossN, because:
    - At columns c' < c₀: all paths have identical prefixes
    - At (c₀, y' < y₀): one of the swapped paths doesn't reach y' (y₀ = max of lower bounds)
    - At (c₀, y₀, i', j') with (i', j') < (ci, cj): swapped paths still visit y₀ -/
private theorem canonCrossN_preserved {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t)
    (ht' : ¬isNonCancellable (gvCanonInv cfg hwf t ht)) :
    canonCrossN cfg hwf (gvCanonInv cfg hwf t ht) ht' = canonCrossN cfg hwf t ht := by
  -- Setup: extract canonical crossing data for t
  set t' := gvCanonInv cfg hwf t ht with ht'_def
  set N := canonCrossN cfg hwf t ht with hN_def
  set ci := canonI cfg hwf t ht
  set cj := canonJ cfg hwf t ht
  set c₀ := canonCol cfg hwf t ht
  set y₀ := canonY cfg hwf t ht
  set ki := splitPosAt cfg t c₀ y₀ ci
  set kj := splitPosAt cfg t c₀ y₀ cj
  have hij : (ci : ℕ) < cj := canonI_lt_canonJ cfg hwf t ht
  have hc₀m := canonCol_le_m cfg hwf t ht
  have hri := canonY_in_range_i cfg hwf t ht
  have hrj := canonY_in_range_j cfg hwf t ht
  have hspec := canonCross_spec cfg hwf t ht
  have hlen_ci : (t.2 ci).val.length = cfg.m + (cfg.targets (t.1 ci) - cfg.sources ci) :=
    (t.2 ci).property.1
  have hlen_cj : (t.2 cj).val.length = cfg.m + (cfg.targets (t.1 cj) - cfg.sources cj) :=
    (t.2 cj).property.1
  have hce_ci := colEntry_le_north (t.2 ci) (c₀ + 1)
  have hce_cj := colEntry_le_north (t.2 cj) (c₀ + 1)
  -- Prefix East counts = c₀
  have hpfx_ci : ((t.2 ci).val.take ki).countP (· = false) = c₀ :=
    take_east_count_within_column (t.2 ci).val c₀ (y₀ - cfg.sources ci)
      (by have := (t.2 ci).property.2; omega) hri.1 hri.2
  have hpfx_cj : ((t.2 cj).val.take kj).countP (· = false) = c₀ :=
    take_east_count_within_column (t.2 cj).val c₀ (y₀ - cfg.sources cj)
      (by have := (t.2 cj).property.2; omega) hrj.1 hrj.2
  -- Image path values
  have himg_ci : (t'.2 ci).val = (t.2 ci).val.take ki ++ (t.2 cj).val.drop kj := by
    rw [ht'_def]; exact gvCanonInv_val_ci cfg hwf t ht
  have himg_cj : (t'.2 cj).val = (t.2 cj).val.take kj ++ (t.2 ci).val.drop ki := by
    rw [ht'_def]; exact gvCanonInv_val_cj cfg hwf t ht
  -- colEntry preserved at c ≤ c₀ for ci
  have colEntry_eq_ci (c : ℕ) (hc : c ≤ c₀) :
      colEntry (t'.2 ci).val c = colEntry (t.2 ci).val c := by
    cases c with
    | zero => simp [colEntry]
    | succ c' =>
      simp only [colEntry, himg_ci]
      rw [show (t.2 ci).val = (t.2 ci).val.take ki ++ (t.2 ci).val.drop ki from
        (List.take_append_drop ki (t.2 ci).val).symm]
      exact northBeforeEast_prefix _ _ _ c' (by rw [hpfx_ci]; omega)
  -- colEntry preserved at c ≤ c₀ for cj
  have colEntry_eq_cj (c : ℕ) (hc : c ≤ c₀) :
      colEntry (t'.2 cj).val c = colEntry (t.2 cj).val c := by
    cases c with
    | zero => simp [colEntry]
    | succ c' =>
      simp only [colEntry, himg_cj]
      rw [show (t.2 cj).val = (t.2 cj).val.take kj ++ (t.2 cj).val.drop kj from
        (List.take_append_drop kj (t.2 cj).val).symm]
      exact northBeforeEast_prefix _ _ _ c' (by rw [hpfx_cj]; omega)
  -- colEntry preserved for any index at c ≤ c₀
  have colEntry_eq (k : Fin r) (c : ℕ) (hc : c ≤ c₀) :
      colEntry (t'.2 k).val c = colEntry (t.2 k).val c := by
    by_cases hk_ci : k = ci
    · subst hk_ci; exact colEntry_eq_ci c hc
    · by_cases hk_cj : k = cj
      · subst hk_cj; exact colEntry_eq_cj c hc
      · congr 1
        rw [ht'_def]
        exact gvCanonInv_val_other cfg hwf t ht k
          (show k ≠ canonI cfg hwf t ht from hk_ci)
          (show k ≠ canonJ cfg hwf t ht from hk_cj)
  -- Upper bound helpers: y₀ ≤ source_k + colEntry(t.2 k, c₀+1) for k ∈ {ci, cj}
  have hup_ci (y : ℕ) (hy : y ≤ y₀) :
      y ≤ (if c₀ < cfg.m then cfg.sources ci + colEntry (t.2 ci).val (c₀ + 1)
           else cfg.targets (t.1 ci)) := by
    obtain ⟨_, _, _, _, _, hshare⟩ := hspec
    simp only [pathsSharePoint] at hshare
    exact le_trans hy hshare.2.1
  have hup_cj (y : ℕ) (hy : y ≤ y₀) :
      y ≤ (if c₀ < cfg.m then cfg.sources cj + colEntry (t.2 cj).val (c₀ + 1)
           else cfg.targets (t.1 cj)) := by
    obtain ⟨_, _, _, _, _, hshare⟩ := hspec
    simp only [pathsSharePoint] at hshare
    exact le_trans hy hshare.2.2.2
  -- Helper: transfer upper bound from t' to t for arbitrary index k at column c ≤ c₀
  have transfer_hi (k : Fin r) (c y : ℕ) (hc_le : c ≤ c₀) (hy_le : c = c₀ → y ≤ y₀)
      (hhi : y ≤ (if c < cfg.m then cfg.sources k + colEntry (t'.2 k).val (c + 1)
                  else cfg.targets (t'.1 k))) :
      y ≤ (if c < cfg.m then cfg.sources k + colEntry (t.2 k).val (c + 1)
           else cfg.targets (t.1 k)) := by
    by_cases hk_ci : k = ci
    · subst hk_ci
      by_cases hc_lt : c < c₀
      · -- c < c₀: colEntry at c+1 preserved
        rw [(colEntry_eq ci (c + 1) (by omega)).symm]
        split_ifs at hhi ⊢ with h <;> [exact hhi; omega]
      · -- c = c₀: use y ≤ y₀
        have hc_eq : c = c₀ := by omega
        subst hc_eq
        exact hup_ci y (hy_le rfl)
    · by_cases hk_cj : k = cj
      · subst hk_cj
        by_cases hc_lt : c < c₀
        · rw [(colEntry_eq cj (c + 1) (by omega)).symm]
          split_ifs at hhi ⊢ with h <;> [exact hhi; omega]
        · have hc_eq : c = c₀ := by omega
          subst hc_eq
          exact hup_cj y (hy_le rfl)
      · -- k ∉ {ci, cj}: path and perm unchanged
        have hval : (t'.2 k).val = (t.2 k).val := by
          rw [ht'_def]
          exact gvCanonInv_val_other cfg hwf t ht k
            (show k ≠ canonI cfg hwf t ht from hk_ci)
            (show k ≠ canonJ cfg hwf t ht from hk_cj)
        have hperm : t'.1 k = t.1 k := by
          simp only [ht'_def, gvCanonInv, canonNewPerm, Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne
              (show k ≠ canonI cfg hwf t ht from hk_ci)
              (show k ≠ canonJ cfg hwf t ht from hk_cj)]
        rw [hval, hperm] at hhi; exact hhi
  -- ===== PART 1: canonCrossN(t') ≤ N =====
  have h_le : canonCrossN cfg hwf t' ht' ≤ N := by
    apply canonCross_min
    obtain ⟨hr, hcm, hij_enc, hiv, hjv, hshare⟩ := hspec
    refine ⟨hr, hcm, hij_enc, hiv, hjv, ?_⟩
    simp only [pathsSharePoint] at hshare ⊢
    obtain ⟨hlo_i, hhi_i, hlo_j, hhi_j⟩ := hshare
    refine ⟨by rw [colEntry_eq ci c₀ le_rfl]; exact hlo_i, ?_,
            by rw [colEntry_eq cj c₀ le_rfl]; exact hlo_j, ?_⟩
    · -- Upper bound for ci in t': use northBeforeEast_ge_prefix_true
      split_ifs with hcm'
      · rw [himg_ci]; simp only [colEntry]
        have hge := northBeforeEast_ge_prefix_true
          ((t.2 ci).val.take ki) ((t.2 cj).val.drop kj) c₀ hpfx_ci
        have htrue := take_countP_true_eq (t.2 ci) ki c₀
          (splitPos_le_length cfg hwf t ht ci (Or.inl rfl))
          (by simp [splitPosAt] at ki; exact hpfx_ci)
        rw [htrue] at hge; simp [splitPosAt] at ki; omega
      · -- c₀ = m: target(t'.1 ci) = target(t.1 cj) ≥ y₀
        -- (swap sends ci → cj, so t'.1 ci = t.1 cj; use hhi_j from hshare)
        simp only [ht'_def, gvCanonInv, canonNewPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        simpa [if_neg hcm'] using hhi_j
    · -- Upper bound for cj in t'
      split_ifs with hcm'
      · rw [himg_cj]; simp only [colEntry]
        have hge := northBeforeEast_ge_prefix_true
          ((t.2 cj).val.take kj) ((t.2 ci).val.drop ki) c₀ hpfx_cj
        have htrue := take_countP_true_eq (t.2 cj) kj c₀
          (splitPos_le_length cfg hwf t ht cj (Or.inr rfl))
          (by simp [splitPosAt] at kj; exact hpfx_cj)
        rw [htrue] at hge; simp [splitPosAt] at kj; omega
      · -- c₀ = m: target(t'.1 cj) = target(t.1 ci) ≥ y₀
        -- (swap sends cj → ci, so t'.1 cj = t.1 ci; use hhi_i from hshare)
        simp only [ht'_def, gvCanonInv, canonNewPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        simpa [if_neg hcm'] using hhi_i
  -- ===== PART 2: N ≤ canonCrossN(t') (by contradiction + transfer) =====
  suffices h_ge : N ≤ canonCrossN cfg hwf t' ht' from le_antisymm h_le h_ge
  by_contra h_neg; push_neg at h_neg
  set N' := canonCrossN cfg hwf t' ht'
  have hN'_lt : N' < N := by omega
  have hspec' := canonCross_spec cfg hwf t' ht'
  -- Transfer the crossing from t' to t
  have htransfer : crossingCode cfg t N' := by
    obtain ⟨hr', hcm', hij'', hiv', hjv', hshare'⟩ := hspec'
    refine ⟨hr', hcm', hij'', hiv', hjv', ?_⟩
    simp only [pathsSharePoint] at hshare' ⊢
    obtain ⟨hlo_i', hhi_i', hlo_j', hhi_j'⟩ := hshare'
    set c' := N' / (yBound cfg * (r * r))
    set y' := (N' / (r * r)) % yBound cfg
    set i' : Fin r := ⟨(N' / r) % r, hiv'⟩
    set j' : Fin r := ⟨N' % r, hjv'⟩
    have hc'_le : c' ≤ c₀ := Nat.div_le_div_right (le_of_lt hN'_lt)
    have hr_pos : 0 < r := hr'
    -- y' ≤ y₀ when c' = c₀
    have hy'_le (hc'_eq : c' = c₀) : y' ≤ y₀ := by
      simp only [y', y₀, c', c₀, canonY, canonCol] at hc'_eq ⊢
      have hyb_pos : 0 < yBound cfg := by unfold yBound; omega
      exact decoded_y_le (by positivity) (by positivity) hN'_lt hc'_eq
    -- Transfer: lower bounds use colEntry preservation, upper bounds use transfer_hi
    exact ⟨by rw [(colEntry_eq i' c' hc'_le).symm]; exact hlo_i',
           transfer_hi i' c' y' hc'_le hy'_le hhi_i',
           by rw [(colEntry_eq j' c' hc'_le).symm]; exact hlo_j',
           transfer_hi j' c' y' hc'_le hy'_le hhi_j'⟩
  exact absurd htransfer (Nat.find_min (crossingCode_exists cfg hwf t ht) hN'_lt)

private theorem gvCanon_self_inverse {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg)
    (ht : t ∈ Finset.univ.filter (fun t : TaggedPathTuple cfg => ¬isNonCancellable t)) :
    gvCanonInv cfg hwf (gvCanonInv cfg hwf t ((Finset.mem_filter.mp ht).2))
      ((Finset.mem_filter.mp (gvCanon_membership cfg hwf t ht)).2) = t := by
  have hht := (Finset.mem_filter.mp ht).2
  set t' := gvCanonInv cfg hwf t hht with ht'_def
  have hht' := (Finset.mem_filter.mp (gvCanon_membership cfg hwf t ht)).2
  -- Canonical crossing data for t
  set ci := canonI cfg hwf t hht
  set cj := canonJ cfg hwf t hht
  set c₀ := canonCol cfg hwf t hht
  set y₀ := canonY cfg hwf t hht
  set ki := splitPosAt cfg t c₀ y₀ ci
  set kj := splitPosAt cfg t c₀ y₀ cj
  have hij := canonI_lt_canonJ cfg hwf t hht
  -- canonCrossN preserved → canonical data for t' matches t
  have hN := canonCrossN_preserved cfg hwf t hht hht'
  have hci' : canonI cfg hwf t' hht' = ci := by
    simp only [canonI]; congr 1; exact hN
  have hcj' : canonJ cfg hwf t' hht' = cj := by
    simp only [canonJ]; congr 1; exact hN
  have hc₀' : canonCol cfg hwf t' hht' = c₀ := by
    simp only [canonCol]; congr 1; exact hN
  have hy₀' : canonY cfg hwf t' hht' = y₀ := by
    simp only [canonY]; congr 1; exact hN
  -- Split positions for t' = split positions for t
  -- (splitPosAt only uses cfg.sources, not the tuple itself)
  have hki' : splitPosAt cfg t' (canonCol cfg hwf t' hht') (canonY cfg hwf t' hht')
      (canonI cfg hwf t' hht') = ki := by simp [splitPosAt, hci', hc₀', hy₀']
  have hkj' : splitPosAt cfg t' (canonCol cfg hwf t' hht') (canonY cfg hwf t' hht')
      (canonJ cfg hwf t' hht') = kj := by simp [splitPosAt, hcj', hc₀', hy₀']
  -- Image path values for double application (using helper lemmas)
  have himg_ci : (t'.2 ci).val = (t.2 ci).val.take ki ++ (t.2 cj).val.drop kj :=
    gvCanonInv_val_ci cfg hwf t hht
  have himg_cj : (t'.2 cj).val = (t.2 cj).val.take kj ++ (t.2 ci).val.drop ki :=
    gvCanonInv_val_cj cfg hwf t hht
  -- Bounds on split positions (needed for take/drop reasoning)
  have hki_le : ki ≤ (t.2 ci).val.length := splitPos_le_length cfg hwf t hht ci (Or.inl rfl)
  have hkj_le : kj ≤ (t.2 cj).val.length := splitPos_le_length cfg hwf t hht cj (Or.inr rfl)
  -- Sigma.ext: show fst and snd match
  have hfst : (gvCanonInv cfg hwf t' hht').1 = t.1 := by
    simp only [gvCanonInv, canonNewPerm, hci', hcj']
    -- (t'.1 * swap(ci, cj)) = (t.1 * swap(ci,cj)) * swap(ci,cj) = t.1
    simp only [ht'_def, gvCanonInv, canonNewPerm]
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  -- Path equality at each index
  have hval : ∀ k, ((gvCanonInv cfg hwf t' hht').2 k).val = (t.2 k).val := by
    intro k
    rcases eq_or_ne k ci with rfl | hk_ci
    · -- k = ci: double tail-swap recovers original
      -- Extract gvCanonInv_val_ci for t', then rewrite canonical indices to ci/cj/ki/kj
      -- Use ordered rw so splitPosAt patterns fire before canonI/canonJ are substituted
      have hv := gvCanonInv_val_ci cfg hwf t' hht'
      rw [hki', hkj', hci', hcj'] at hv
      rw [hv, himg_ci, himg_cj]
      have h1 : ((t.2 ci).val.take ki ++ (t.2 cj).val.drop kj).take ki =
                (t.2 ci).val.take ki := by
        rw [List.take_append, List.length_take_of_le hki_le, Nat.sub_self,
            List.take_zero, List.append_nil, List.take_take, Nat.min_self]
      have h2 : ((t.2 cj).val.take kj ++ (t.2 ci).val.drop ki).drop kj =
                (t.2 ci).val.drop ki := by
        have hkj_drop : ((t.2 cj).val.take kj).drop kj = [] := by
          nth_rw 2 [← List.length_take_of_le hkj_le]; exact List.drop_length
        rw [List.drop_append, List.length_take_of_le hkj_le, Nat.sub_self,
            List.drop_zero, hkj_drop, List.nil_append]
      rw [h1, h2, List.take_append_drop]
    · rcases eq_or_ne k cj with rfl | hk_cj
      · -- k = cj: double tail-swap recovers original
        have hv := gvCanonInv_val_cj cfg hwf t' hht'
        rw [hkj', hki', hcj', hci'] at hv
        rw [hv, himg_ci, himg_cj]
        have h1 : ((t.2 cj).val.take kj ++ (t.2 ci).val.drop ki).take kj =
                  (t.2 cj).val.take kj := by
          rw [List.take_append, List.length_take_of_le hkj_le, Nat.sub_self,
              List.take_zero, List.append_nil, List.take_take, Nat.min_self]
        have h2 : ((t.2 ci).val.take ki ++ (t.2 cj).val.drop kj).drop ki =
                  (t.2 cj).val.drop kj := by
          have hki_drop : ((t.2 ci).val.take ki).drop ki = [] := by
            nth_rw 2 [← List.length_take_of_le hki_le]; exact List.drop_length
          rw [List.drop_append, List.length_take_of_le hki_le, Nat.sub_self,
              List.drop_zero, hki_drop, List.nil_append]
        rw [h1, h2, List.take_append_drop]
      · -- k ∉ {ci, cj}: unchanged on both applications
        rw [gvCanonInv_val_other cfg hwf t' hht' k (by rwa [hci']) (by rwa [hcj'])]
        exact gvCanonInv_val_other cfg hwf t hht k hk_ci hk_cj
  -- Combine into Sigma equality using Function.hfunext for the HEq of Pi types
  apply Sigma.ext hfst
  apply Function.hfunext rfl
  intro k k' hkk'
  have hkk'' : k = k' := eq_of_heq hkk'
  subst hkk''
  -- Goal: HEq ((gvCanonInv cfg hwf t' hht').snd k) (t.snd k)
  -- The target types differ by (gvCanonInv ...).fst k vs t.fst k, but these are equal by hfst
  have hk_n : cfg.targets ((gvCanonInv cfg hwf t' hht').fst k) - cfg.sources k =
              cfg.targets (t.fst k) - cfg.sources k := by
    have heq : (gvCanonInv cfg hwf t' hht').fst k = t.fst k :=
      congrArg (fun e : Equiv.Perm (Fin r) => e k) hfst
    rw [heq]
  apply heq_of_cast_eq (congrArg (PathMN cfg.m) hk_n)
  apply Subtype.ext
  rw [cast_PathMN_val hk_n]
  exact hval k

/-- The signed sum over cancellable tagged tuples is zero,
    by the GV sign-reversing involution via `Finset.sum_involution`. -/
private theorem cancellable_sum_eq_zero {r : ℕ} (cfg : LGVConfig r)
    (hwf : cfg.wellFormed) :
    (Finset.sum (Finset.univ.filter
      (fun t : TaggedPathTuple cfg => ¬isNonCancellable t)) taggedWeight) = 0 := by
  exact Finset.sum_involution
    (fun t ht => gvCanonInv cfg hwf t ((Finset.mem_filter.mp ht).2))
    (gvCanon_sign_reversal cfg hwf)
    (fun t ht hw => gvCanon_no_fixed cfg hwf t ht hw)
    (gvCanon_membership cfg hwf)
    (gvCanon_self_inverse cfg hwf)

theorem gv_involution_cancellation {r : ℕ} (cfg : LGVConfig r)
    (hwf : cfg.wellFormed) :
    ∑ σ : Equiv.Perm (Fin r),
      (↑(Equiv.Perm.sign σ) : ℤ) * ↑(Fintype.card (PermPathTuple cfg σ)) =
    ↑(niTupleCount cfg) := by
  rw [← sum_tagged_eq_sum_perm]
  -- Split: (∑ NI) + (∑ cancel) = ∑ all
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun t : TaggedPathTuple cfg => isNonCancellable t) taggedWeight
  -- Cancellable part = 0
  have hcancel := cancellable_sum_eq_zero cfg hwf
  -- NI part: each has weight 1, count = niTupleCount
  have hni : Finset.sum (Finset.univ.filter
      (fun t : TaggedPathTuple cfg => isNonCancellable t)) taggedWeight =
      ↑(niTupleCount cfg) := by
    have hw : ∀ t, t ∈ Finset.univ.filter
        (fun t : TaggedPathTuple cfg => isNonCancellable t) →
        taggedWeight t = (1 : ℤ) :=
      fun t ht => nonCancellable_weight t ((Finset.mem_filter.mp ht).2)
    rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact card_nonCancellable_eq_niTupleCount cfg
  -- Combine
  linarith [hsplit.symm]

/-- **The r×r LGV Lemma** (Lindström 1973, Gessel-Viennot 1985):

    The number of r-tuples of pairwise non-intersecting lattice paths
    (path i: source i → target i) equals the determinant of the path
    weight matrix M where M_{i,j} = C(m + (bⱼ - aᵢ), m).

    Proved by combining the algebraic bridge (det = signed perm sum)
    with the GV involution cancellation (signed sum = NI count).
    This generalizes the 2×2 case proved in BallotProblemOQ03.lean. -/
theorem lgv_lemma_rxr {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed) :
    (niTupleCount cfg : ℤ) = (pathMatrix cfg).det := by
  rw [det_pathMatrix_eq_signed_sum]
  exact (gv_involution_cancellation cfg hwf).symm

-- ============================================================
-- PART 9: Corollaries
-- ============================================================

/-- The count of non-intersecting tuples is non-negative. -/
theorem niTupleCount_nonneg {r : ℕ} (cfg : LGVConfig r) :
    0 ≤ (niTupleCount cfg : ℤ) :=
  Int.natCast_nonneg _

/-- The path matrix determinant is non-negative (for well-formed configs). -/
theorem pathMatrix_det_nonneg {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed) :
    0 ≤ (pathMatrix cfg).det := by
  rw [← lgv_lemma_rxr cfg hwf]
  exact niTupleCount_nonneg cfg

/-- For r = 1, every path tuple is vacuously non-intersecting
    (there are no pairs i < j). -/
theorem isNonIntersecting_of_r_one (cfg : LGVConfig 1) (paths : PathTuple cfg) :
    IsNonIntersecting cfg paths := by
  intro i j hij
  exact absurd hij (by omega : ¬(i < j))

-- ============================================================
-- PART 10: Combinatorial Applications
-- ============================================================

/-- The LGV lemma is a fundamental tool in enumerative combinatorics.

    Key applications:
    1. **Schur polynomials**: Via the Jacobi-Trudi identity,
       s_λ = det[h_{λᵢ-i+j}], and this determinant counts
       non-intersecting lattice paths (semistandard Young tableaux).

    2. **Catalan numbers**: The n-th Catalan number C_n counts
       non-intersecting pairs from (0,0),(0,1) to (n,n-1),(n,n),
       which by the 2×2 LGV equals C(2n,n)/(n+1).

    3. **Aztec diamond**: The number of tilings of the Aztec diamond
       of order n equals 2^{n(n+1)/2}, provable via the LGV lemma
       on a suitable grid.

    4. **Plane partitions**: MacMahon's formula for the number of
       plane partitions in a box can be proved using the LGV lemma
       with appropriate source/target configurations. -/
theorem lgv_universality :
    ∀ (r : ℕ) (cfg : LGVConfig r) (hwf : cfg.wellFormed),
      (niTupleCount cfg : ℤ) = (pathMatrix cfg).det :=
  fun _ cfg hwf => lgv_lemma_rxr cfg hwf

end LGV
