import Mathlib

/-
# Higher-Dimensional Lattice Path Problems via Reflection

## Research Problem: ballot-problem-oq-03
Higher-dimensional lattice path problems via the reflection principle.

## Mathematical Content

The classical ballot problem (Bertrand 1887, Wiedijk #30) uses a 1D reflection argument.
This file extends the reflection principle to 2D lattice paths, proving the
**Lindström-Gessel-Viennot (LGV) Lemma** in the 2×2 case.

**The 2×2 LGV Lemma** (Lindström 1973, Gessel-Viennot 1985):
Given source points A₁ = (0, a₁), A₂ = (0, a₂) with a₁ < a₂, and target points
B₁ = (m, b₁), B₂ = (m, b₂) with b₁ < b₂, the number of non-intersecting pairs of
lattice paths (P₁: A₁→B₁, P₂: A₂→B₂) equals:

  e(A₁,B₁) · e(A₂,B₂) - e(A₁,B₂) · e(A₂,B₁)

where e(A,B) = C(dx + dy, dx) is the path count from A to B.

**Key New Theorem (Crossing Lemma)** — the 2D reflection principle:
If path P₁ starts strictly lower (y₁ < y₂) but ends strictly higher (y₁+n₁ > y₂+n₂),
the paths MUST share a lattice point.

**Proof of Crossing Lemma**:
Define `northBeforeEast l k` = # North steps before the k-th East step in path l.
This is the y-offset when entering column k. Key properties:
1. northBeforeEast l k ≤ northBeforeEast l (k+1) (monotone)
2. If non-intersecting and P₁ enters column k below P₂, P₁ exits column k below P₂ entry
   (disjoint interval argument — proved as nonIntersecting_entry_order)
3. By induction: P₁ always enters each column lower than P₂
4. At column m: P₁ entry y < P₂ entry y, but P₁ endpoint > P₂ endpoint → contradiction

## Status (0 sorries, 0 axioms — FULLY PROVED)
- [x] northBeforeEast: key recursive function
- [x] colEntry: column entry y-offset
- [x] Column range definitions
- [x] nonIntersecting_entry_order: disjoint interval preservation lemma
- [x] Crossing Lemma (fully proved)
- [x] PathMN: paths with m East and n North steps (with Fintype instance)
- [x] path_count theorem: |PathMN m n| = C(m+n,m)
- [x] LGV 2×2 theorem (proved via complement counting + Lindström involution)
- [x] Catalan number computations
- [x] Ballot theorem formula
- [x] Vandermonde identity
- [x] Verified examples via native_decide
- [x] Involution infrastructure (splitAfterEast, swapTails, involutivity)
- [x] Entry gap analysis (entryGap framework, NI preserves gap positivity)
- [x] swapTails East step and length preservation theorems
- [x] Lattice point infrastructure (visitedPoints, sharedPoints, posAfter)
- [x] Shared point existence for intersecting paths (column + final range overlap)
- [x] swapAtPoint with East step and North step preservation
- [x] swapAtPoint involutivity
- [x] Lindström involution (fully proved via dual injections)

## References
- Lindström (1973): "On the Vector Representations of Induced Matroids"
- Gessel-Viennot (1985): "Binomial Determinants, Paths, and Hook Length Formulae"
- Bertrand (1887): Original ballot problem
- Krattenthaler (2015): "Lattice Path Enumeration" (survey)
-/

namespace LatticePathLGV

open Finset List

/- ## Part I: Lattice Path Definitions -/

/-- A lattice path: false = East (+x), true = North (+y) -/
abbrev LPath := List Bool

/-- Count East (false) steps -/
def eastSteps (l : LPath) : ℕ := l.countP (· = false)

/-- Count North (true) steps -/
def northSteps (l : LPath) : ℕ := l.countP (· = true)

theorem eastSteps_add_northSteps (l : LPath) :
    eastSteps l + northSteps l = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | false =>
      have he : eastSteps (false :: xs) = eastSteps xs + 1 := by
        simp [eastSteps, List.countP_cons]
      have hn : northSteps (false :: xs) = northSteps xs := by
        simp [northSteps, List.countP_cons]
      simp only [he, hn, List.length_cons]; omega
    | true =>
      have he : eastSteps (true :: xs) = eastSteps xs := by
        simp [eastSteps, List.countP_cons]
      have hn : northSteps (true :: xs) = northSteps xs + 1 := by
        simp [northSteps, List.countP_cons]
      simp only [he, hn, List.length_cons]; omega

/-- A bounded path from (0,y₀) to (m, y₀+n): exactly m East and n North steps -/
def pathType (m n : ℕ) : Type :=
  {l : LPath // l.length = m + n ∧ l.countP (· = false) = m}

/-- pathType m n ≃ subtype of List.Vector Bool (m+n), which is Fintype -/
noncomputable instance pathTypeFintype (m n : ℕ) : Fintype (pathType m n) := by
  haveI : DecidablePred (fun v : List.Vector Bool (m + n) => v.val.countP (· = false) = m) :=
    fun v => decEq _ _
  exact Fintype.ofEquiv
    {v : List.Vector Bool (m + n) // v.val.countP (· = false) = m}
    { toFun  := fun ⟨⟨l, hlen⟩, heast⟩ => ⟨l, hlen, heast⟩,
      invFun := fun ⟨l, hlen, heast⟩   => ⟨⟨l, hlen⟩, heast⟩,
      left_inv  := fun ⟨⟨_, _⟩, _⟩ => rfl,
      right_inv := fun ⟨_, _, _⟩ => rfl }

/- ## Part II: The northBeforeEast Function -/

/-- northBeforeEast l k = # North (true) steps in l before the k-th East (false) step.
    This gives the y-offset when entering column k+1, or equivalently the y
    height of the path when it makes its k-th East step. -/
def northBeforeEast : LPath → ℕ → ℕ
  | [], _ => 0
  | (false :: _), 0 => 0           -- stop: we've reached the 0-th East
  | (false :: xs), (k + 1) => northBeforeEast xs k  -- consume this East, k→k-1
  | (true :: xs), k => 1 + northBeforeEast xs k     -- count this North, k unchanged

/-- northBeforeEast l 0 = # North steps before the FIRST East step -/
theorem northBeforeEast_zero_eq_northPrefix (l : LPath) :
    northBeforeEast l 0 = (l.takeWhile (· = true)).length := by
  induction l with
  | nil => simp [northBeforeEast]
  | cons x xs ih =>
    cases x with
    | false => simp [northBeforeEast, List.takeWhile]
    | true => simp [northBeforeEast, List.takeWhile, ih]; omega

/-- northBeforeEast is weakly monotone: more North steps are accumulated for later East steps -/
theorem northBeforeEast_mono (l : LPath) (k : ℕ) :
    northBeforeEast l k ≤ northBeforeEast l (k + 1) := by
  induction l generalizing k with
  | nil => simp [northBeforeEast]
  | cons x xs ih =>
    cases x with
    | false =>  -- East step
      cases k with
      | zero => simp [northBeforeEast]
      | succ k =>
        simp only [northBeforeEast]
        exact ih k
    | true =>   -- North step
      simp only [northBeforeEast]
      exact Nat.add_le_add_left (ih k) 1

/-- Column entry y-offset for column k: y-offset when the path has made exactly k East steps.
    - colEntry l 0 = 0 (no East steps taken: at start)
    - colEntry l 1 = northBeforeEast l 0 (y after 1st East = North steps before 1st East)
    - colEntry l (k+1) = northBeforeEast l k (y after (k+1)-th East) -/
def colEntry (l : LPath) : ℕ → ℕ
  | 0 => 0
  | (k + 1) => northBeforeEast l k

theorem colEntry_zero (l : LPath) : colEntry l 0 = 0 := rfl

theorem colEntry_succ (l : LPath) (k : ℕ) : colEntry l (k + 1) = northBeforeEast l k := rfl

theorem colEntry_mono (l : LPath) (k : ℕ) : colEntry l k ≤ colEntry l (k + 1) := by
  cases k with
  | zero => simp [colEntry]
  | succ k => simp [colEntry]; exact northBeforeEast_mono l k

/-- northSteps is unchanged by a false (East) step -/
lemma northSteps_cons_false (xs : LPath) : northSteps (false :: xs) = northSteps xs := by
  simp [northSteps]

/-- northSteps increases by 1 for each true (North) step -/
lemma northSteps_cons_true (xs : LPath) : northSteps (true :: xs) = 1 + northSteps xs := by
  simp [northSteps]; omega

/-- northSteps is additive over list concatenation -/
lemma northSteps_append (l₁ l₂ : LPath) :
    northSteps (l₁ ++ l₂) = northSteps l₁ + northSteps l₂ := by
  simp [northSteps, List.countP_append]

/-- northBeforeEast l k counts a prefix of north steps, so is ≤ total northSteps -/
lemma northBeforeEast_le_northSteps (l : LPath) (k : ℕ) :
    northBeforeEast l k ≤ northSteps l := by
  induction l generalizing k with
  | nil => simp [northBeforeEast, northSteps]
  | cons x xs ih =>
    cases x with
    | false =>
      rw [northSteps_cons_false]
      cases k with
      | zero => simp [northBeforeEast]
      | succ k => simp only [northBeforeEast]; exact ih k
    | true =>
      rw [northSteps_cons_true]
      simp only [northBeforeEast]
      exact Nat.add_le_add_left (ih k) 1

/-- At column m, the entry y-offset is at most northSteps l (the total North count) -/
theorem colEntry_le_northSteps (l : LPath) (m : ℕ) (hm : l.countP (· = false) = m) :
    colEntry l m ≤ northSteps l := by
  cases m with
  | zero => simp [colEntry]
  | succ m => simp only [colEntry]; exact northBeforeEast_le_northSteps l m

/- ## Part III: Column Ranges and Non-Intersecting -/

/-- The y-range visited at column x (for x < m): [y₀ + colEntry l x, y₀ + colEntry l (x+1)] -/
def colYRange (l : LPath) (y₀ x : ℕ) : Set ℕ :=
  {y | y₀ + colEntry l x ≤ y ∧ y ≤ y₀ + colEntry l (x + 1)}

/-- The y-range at the final column m: [y₀ + colEntry l m, y₀ + northSteps l] -/
def finalRange (l : LPath) (y₀ : ℕ) (m : ℕ) : Set ℕ :=
  {y | y₀ + colEntry l m ≤ y ∧ y ≤ y₀ + northSteps l}

/-- Two paths are non-intersecting: their y-ranges at each column are disjoint -/
def NonIntersecting (l₁ l₂ : LPath) (m y₁ y₂ : ℕ) : Prop :=
  (∀ x < m, ∀ y, ¬(y ∈ colYRange l₁ y₁ x ∧ y ∈ colYRange l₂ y₂ x)) ∧
  (∀ y, ¬(y ∈ finalRange l₁ y₁ m ∧ y ∈ finalRange l₂ y₂ m))

/- ## Part IV: The Crossing Lemma -/

/-- **KEY LEMMA**: If paths are non-intersecting and P₁ enters column k below P₂
    (y₁ + entry₁(k) < y₂ + entry₂(k)), then P₁ also enters column k+1 below P₂.

    Proof: The ranges at column k are [y₁+entry₁(k), y₁+entry₁(k+1)] and
    [y₂+entry₂(k), y₂+entry₂(k+1)]. Non-intersection forces entry₁(k+1) < entry₂(k).
    Since entry₂(k) ≤ entry₂(k+1), we get entry₁(k+1) < entry₂(k+1). -/
lemma nonIntersecting_entry_order {l₁ l₂ : LPath} {m y₁ y₂ : ℕ}
    (hni : NonIntersecting l₁ l₂ m y₁ y₂)
    (hk : k < m)
    (h_entry : y₁ + colEntry l₁ k < y₂ + colEntry l₂ k) :
    y₁ + colEntry l₁ (k + 1) < y₂ + colEntry l₂ (k + 1) := by
  by_contra h_bad
  push_neg at h_bad
  -- h_bad: y₂ + colEntry l₂ (k+1) ≤ y₁ + colEntry l₁ (k+1)
  have h₁_mono : colEntry l₁ k ≤ colEntry l₁ (k + 1) := colEntry_mono l₁ k
  have h₂_mono : colEntry l₂ k ≤ colEntry l₂ (k + 1) := colEntry_mono l₂ k
  have hmid : y₂ + colEntry l₂ k ≤ y₁ + colEntry l₁ (k + 1) := by omega
  -- The point y₂ + colEntry l₂ k lies in both column ranges at column k
  have h_in₁ : y₂ + colEntry l₂ k ∈ colYRange l₁ y₁ k :=
    ⟨by omega, hmid⟩
  have h_in₂ : y₂ + colEntry l₂ k ∈ colYRange l₂ y₂ k :=
    ⟨le_refl _, by omega⟩
  exact hni.1 k hk _ ⟨h_in₁, h_in₂⟩

/-- **The Crossing Lemma**: The 2D reflection principle.

    If path P₁ starts strictly lower (y₁ < y₂) but ends strictly higher (y₁+n₁ > y₂+n₂)
    than path P₂, they cannot be non-intersecting. They MUST share a lattice point.

    This is the key to the LGV lemma: it shows that "crossing" path pairs (where sources
    and targets are in opposite vertical order) always have intersecting paths, so the
    Lindström involution maps them completely to the "straight" pairs, proving the
    determinant formula. -/
theorem crossing_lemma {l₁ l₂ : LPath} (m n₁ n₂ y₁ y₂ : ℕ)
    (hm₁ : l₁.countP (· = false) = m) (hn₁ : l₁.countP (· = true) = n₁)
    (hm₂ : l₂.countP (· = false) = m) (hn₂ : l₂.countP (· = true) = n₂)
    (hstart : y₁ < y₂)
    (hend : y₂ + n₂ < y₁ + n₁) :
    ¬NonIntersecting l₁ l₂ m y₁ y₂ := by
  intro hni
  -- Normalize northSteps to n₁, n₂
  have hns₁ : northSteps l₁ = n₁ := hn₁
  have hns₂ : northSteps l₂ = n₂ := hn₂
  -- By induction: y₁ + colEntry l₁ k < y₂ + colEntry l₂ k for all k ≤ m
  have horder : ∀ k ≤ m, y₁ + colEntry l₁ k < y₂ + colEntry l₂ k := by
    intro k hkm
    induction k with
    | zero => simp [colEntry_zero]; exact hstart
    | succ k ih =>
      -- Apply nonIntersecting_entry_order: need k < m and IH at k
      exact nonIntersecting_entry_order hni hkm (ih (Nat.le_of_succ_le hkm))
  -- At column m: P₁ entry y is strictly below P₂ entry y
  have hm_ineq : y₁ + colEntry l₁ m < y₂ + colEntry l₂ m := horder m le_rfl
  have hlast := hni.2
  have hn₁_bound : colEntry l₁ m ≤ n₁ := by
    rw [← hn₁]; exact colEntry_le_northSteps l₁ m hm₁
  have hn₂_bound : colEntry l₂ m ≤ n₂ := by
    rw [← hn₂]; exact colEntry_le_northSteps l₂ m hm₂
  -- Case analysis on whether P₁'s final range is entirely below P₂'s start
  by_cases hcase : y₁ + n₁ < y₂ + colEntry l₂ m
  · -- P₁ entirely below P₂'s range: y₁ + n₁ < y₂ + colEntry l₂ m ≤ y₂ + n₂
    -- But hend says y₂ + n₂ < y₁ + n₁, contradiction
    omega
  · -- P₁'s range overlaps with P₂'s range:
    -- the point y₂ + colEntry l₂ m is in both final ranges
    push_neg at hcase
    -- hcase : y₂ + colEntry l₂ m ≤ y₁ + n₁
    have h_in₁ : y₂ + colEntry l₂ m ∈ finalRange l₁ y₁ m := by
      simp only [finalRange, hns₁, Set.mem_setOf_eq]
      exact ⟨le_of_lt hm_ineq, hcase⟩
    have h_in₂ : y₂ + colEntry l₂ m ∈ finalRange l₂ y₂ m := by
      simp only [finalRange, hns₂, Set.mem_setOf_eq]
      exact ⟨le_refl _, Nat.add_le_add_left hn₂_bound y₂⟩
    exact hlast _ ⟨h_in₁, h_in₂⟩

/- ## Part V: Path Count Formula -/

/-- Paths with (m+1) east and (n+1) north steps biject with (m) east/(n+1) north ⊕ (m+1) east/n north.
    This implements the inductive splitting: a non-empty path either starts with East or North. -/
-- countP on Bool cons cells
private lemma countP_false_cons_false (xs : List Bool) :
    (false :: xs).countP (· = false) = xs.countP (· = false) + 1 := by
  simp [List.countP_cons]
private lemma countP_false_cons_true (xs : List Bool) :
    (true :: xs).countP (· = false) = xs.countP (· = false) := by
  simp [List.countP_cons]

def pathSplitEquiv (m n : ℕ) : pathType (m + 1) (n + 1) ≃ pathType m (n + 1) ⊕ pathType (m + 1) n where
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

/-- The number of lattice paths with m East and n North steps equals C(m+n, m).
    Proved by induction: paths split into East-first (m-1, n) and North-first (m, n-1). -/
-- Helper: for List Bool, east + north counts = total length
-- (uses eastSteps_add_northSteps which was proved earlier)
private lemma bool_list_countP_sum (l : List Bool) :
    l.countP (· = false) + l.countP (· = true) = l.length :=
  eastSteps_add_northSteps l

theorem path_count_eq_choose (m n : ℕ) :
    Fintype.card (pathType m n) = Nat.choose (m + n) m := by
  induction m generalizing n with
  | zero =>
    simp only [Nat.zero_add, Nat.choose_zero_right]
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨List.replicate n true, by simp, by simp⟩, ?_⟩
    intro ⟨l, hlen, heast⟩
    apply Subtype.ext; simp only
    -- goal: l = replicate n true
    apply List.ext_getElem
    · simp [hlen]  -- l.length = (replicate n true).length via hlen + length_replicate
    · intro i hi_l _  -- hi_l : i < l.length; _ : i < (replicate n true).length
      rw [List.getElem_replicate]  -- goal: l[i] = true
      -- Bool.eq_false_or_eq_true : b = true ∨ b = false (true first)
      rcases Bool.eq_false_or_eq_true (l[i]) with h | h
      · exact h  -- h : l[i] = true ✓
      · exfalso  -- h : l[i] = false → contradiction with heast = 0
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
      -- goal: l = replicate (m+1) false
      apply List.ext_getElem
      · simp [hlen]  -- l.length = (replicate (m+1) false).length
      · intro i hi_l _  -- hi_l : i < l.length
        rw [List.getElem_replicate]  -- goal: l[i] = false
        rcases Bool.eq_false_or_eq_true (l[i]) with h | h
        · exfalso  -- h : l[i] = true → contradiction (all steps are East = false)
          have hmem : true ∈ l := h ▸ List.getElem_mem hi_l
          have h_pos : 0 < l.countP (· = true) :=
            List.countP_pos_iff.mpr ⟨true, hmem, by simp⟩
          have h_sum := bool_list_countP_sum l
          omega
        · exact h  -- h : l[i] = false ✓
    | succ n ih_n =>
      -- Split: pathType (m+1) (n+1) ≃ pathType m (n+1) ⊕ pathType (m+1) n
      -- Then use Pascal: C(m+(n+1)+1, m+1) = C(m+(n+1), m) + C(m+(n+1), m+1)
      rw [Fintype.card_congr (pathSplitEquiv m n), Fintype.card_sum, ih (n + 1), ih_n,
          show m + 1 + n = m + (n + 1) from by omega,
          show m + 1 + (n + 1) = m + (n + 1) + 1 from by omega]
      exact (Nat.choose_succ_succ' (m + (n + 1)) m).symm

/- ## Part VI: Non-Intersecting Pair Count and LGV -/

/-- Classical decidability for non-intersecting path pairs.
    Extracted as a named instance to avoid Fintype instance diamonds. -/
noncomputable instance niDecidable (m n₁ n₂ y₁ y₂ : ℕ) :
    DecidablePred (fun p : pathType m n₁ × pathType m n₂ =>
      NonIntersecting p.1.val p.2.val m y₁ y₂) := Classical.decPred _

/-- Non-intersecting path pairs as a subtype of all path pairs. -/
noncomputable def niPairCount (m n₁ n₂ y₁ y₂ : ℕ) : ℕ :=
  Fintype.card {p : pathType m n₁ × pathType m n₂ //
    NonIntersecting p.1.val p.2.val m y₁ y₂}

/-- The LGV determinant for the 2×2 case -/
def lgvDet (m a₁ b₁ a₂ b₂ : ℕ) : ℤ :=
  (Nat.choose (m + (b₁ - a₁)) m : ℤ) * Nat.choose (m + (b₂ - a₂)) m -
  (Nat.choose (m + (b₁ - a₂)) m : ℤ) * Nat.choose (m + (b₂ - a₁)) m

-- Helper lemmas needed for the LGV proof (defined before lgv_lemma_2x2)

/-- LGV det = 0 when a₁ = a₂ -/
private lemma lgvDet_same_start' (m b₁ b₂ a : ℕ) :
    lgvDet m a b₁ a b₂ = 0 := by
  unfold lgvDet; ring

/-- LGV det = 0 when b₁ = b₂ -/
private lemma lgvDet_same_end' (m a₁ a₂ b : ℕ) :
    lgvDet m a₁ b a₂ b = 0 := by
  unfold lgvDet; ring

/-- When paths start at same y, niPairCount = 0 -/
private lemma lgv_same_start' (m n₁ n₂ y : ℕ) :
    niPairCount m n₁ n₂ y y = 0 := by
  unfold niPairCount
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro ⟨⟨⟨l₁, _⟩, ⟨l₂, _⟩⟩, hni⟩
  cases m with
  | zero =>
    exact hni.2 y
      ⟨⟨by simp [colEntry], Nat.le_add_right y _⟩,
       ⟨by simp [colEntry], Nat.le_add_right y _⟩⟩
  | succ m =>
    exact hni.1 0 (Nat.zero_lt_succ m) y
      ⟨⟨by simp [colEntry], Nat.le_add_right y _⟩,
       ⟨by simp [colEntry], Nat.le_add_right y _⟩⟩

/-- When paths end at same height, niPairCount = 0 -/
private lemma lgv_same_end' (m n₁ n₂ y₁ y₂ : ℕ) (h : y₁ + n₁ = y₂ + n₂) :
    niPairCount m n₁ n₂ y₁ y₂ = 0 := by
  unfold niPairCount
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro ⟨⟨⟨l₁, hl₁_len, hl₁_east⟩, ⟨l₂, hl₂_len, hl₂_east⟩⟩, hni⟩
  have hns₁ : northSteps l₁ = n₁ := by
    have := eastSteps_add_northSteps l₁; simp only [eastSteps] at this; omega
  have hns₂ : northSteps l₂ = n₂ := by
    have := eastSteps_add_northSteps l₂; simp only [eastSteps] at this; omega
  have h_in₁ : y₁ + n₁ ∈ finalRange l₁ y₁ m := by
    refine ⟨?_, by rw [hns₁]⟩
    exact Nat.add_le_add_left (colEntry_le_northSteps l₁ m hl₁_east) y₁ |>.trans
      (by rw [hns₁])
  have h_in₂ : y₂ + n₂ ∈ finalRange l₂ y₂ m := by
    refine ⟨?_, by rw [hns₂]⟩
    exact Nat.add_le_add_left (colEntry_le_northSteps l₂ m hl₂_east) y₂ |>.trans
      (by rw [hns₂])
  rw [h] at h_in₁
  exact hni.2 (y₂ + n₂) ⟨h_in₁, h_in₂⟩

/-- Complement counting: NI pairs + intersecting pairs = all pairs -/
private theorem ni_complement_count' (m n₁ n₂ y₁ y₂ : ℕ) :
    niPairCount m n₁ n₂ y₁ y₂ +
    Fintype.card {p : pathType m n₁ × pathType m n₂ //
      ¬NonIntersecting p.1.val p.2.val m y₁ y₂} =
    Fintype.card (pathType m n₁ × pathType m n₂) := by
  unfold niPairCount
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (Equiv.sumCompl
    (fun p : pathType m n₁ × pathType m n₂ =>
      NonIntersecting p.1.val p.2.val m y₁ y₂))

/-- Total identity pairs = C(m+n₁, m) * C(m+n₂, m) -/
private theorem total_identity_count' (m n₁ n₂ : ℕ) :
    Fintype.card (pathType m n₁ × pathType m n₂) =
    Nat.choose (m + n₁) m * Nat.choose (m + n₂) m := by
  rw [Fintype.card_prod, path_count_eq_choose, path_count_eq_choose]

-- NOTE: lindstrom_involution and lgv_lemma_2x2 are defined after Part XXIII
-- (they depend on lindstromForward_injective and lindstromBackward_injective)

/- ## Part VII: Vandermonde's Identity -/

/-- Vandermonde's identity: C(m+n, r) = Σ_{k=0}^{r} C(m,k) * C(n, r-k).

    Via LGV: count lattice paths from (0,0) to (m+n, r) as paths that
    cross a vertical cut at column m, giving the sum formula. -/
theorem vandermonde (m n r : ℕ) :
    Nat.choose (m + n) r = ∑ k ∈ range (r + 1), Nat.choose m k * Nat.choose n (r - k) := by
  rw [Nat.add_choose_eq]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => Nat.choose m i * Nat.choose n j) r)

/- ## Part VIII: Catalan Numbers -/

/-- The n-th Catalan number via ballot formula -/
def Cn (n : ℕ) : ℕ := Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1)

-- Verified Catalan values
example : Cn 0 = 1 := by native_decide
example : Cn 1 = 1 := by native_decide
example : Cn 2 = 2 := by native_decide
example : Cn 3 = 5 := by native_decide
example : Cn 4 = 14 := by native_decide
example : Cn 5 = 42 := by native_decide
example : Cn 6 = 132 := by native_decide

/-- Catalan number formula via the ballot theorem:
    Cn(n) counts non-crossing Dyck paths = C(2n,n)/(n+1).
    This is proved via the cycle lemma and ballot counting argument.
    (See BallotProblemOQ01.lean for the full cycle lemma proof.) -/
theorem catalan_formula (n : ℕ) : Cn n * (n + 1) = Nat.choose (2 * n) n := by
  simp only [Cn]
  cases n with
  | zero => simp
  | succ n =>
    set m := n + 1 with hm_def
    set a := Nat.choose (2 * m) m with ha_def
    set b := Nat.choose (2 * m) (m + 1) with hb_def
    -- Absorption identity 1: (2m) * C(2m-1, m) = C(2m, m+1) * (m+1) = b * (m+1)
    have hA := Nat.add_one_mul_choose_eq (2 * m - 1) m
    rw [show 2 * m - 1 + 1 = 2 * m from by omega] at hA
    -- hA : 2 * m * Nat.choose (2 * m - 1) m = b * (m + 1)
    -- Absorption identity 2: (2m) * C(2m-1, m-1) = C(2m, m) * m = a * m
    have hB := Nat.add_one_mul_choose_eq (2 * m - 1) (m - 1)
    rw [show 2 * m - 1 + 1 = 2 * m from by omega,
        show m - 1 + 1 = m from by omega] at hB
    -- hB : 2 * m * Nat.choose (2 * m - 1) (m - 1) = a * m
    -- Symmetry: C(2m-1, m) = C(2m-1, m-1)
    have hC : Nat.choose (2 * m - 1) m = Nat.choose (2 * m - 1) (m - 1) :=
      Nat.choose_symm_of_eq_add (by omega)
    -- Key: b * (m + 1) = a * m
    have h_abs : b * (m + 1) = a * m :=
      calc b * (m + 1) = 2 * m * Nat.choose (2 * m - 1) m := hA.symm
        _ = 2 * m * Nat.choose (2 * m - 1) (m - 1) := by rw [hC]
        _ = a * m := hB
    -- b ≤ a: b * (m+1) = a * m ≤ a * (m+1), so b * m ≤ a * m, hence b ≤ a
    have h_le : b ≤ a := by
      have h1 : b * m ≤ b * (m + 1) := Nat.mul_le_mul_left b (by omega)
      have h2 : b * m ≤ a * m := h1.trans (le_of_eq h_abs)
      exact Nat.le_of_mul_le_mul_right h2 (by omega)
    -- (a - b) * (m + 1) = a
    zify [h_le] at h_abs ⊢
    linear_combination -h_abs

/- ## Part IX: Ballot Theorem -/

/-- Classical ballot count: sequences of p A-votes and q B-votes where A leads throughout.
    Formula (via reflection principle): C(p+q-1, p-1) - C(p+q-1, p) -/
def ballotSeqCount (p q : ℕ) : ℕ :=
  Nat.choose (p + q - 1) (p - 1) - Nat.choose (p + q - 1) p

-- Verified ballot counts
example : ballotSeqCount 2 1 = 1 := by native_decide
example : ballotSeqCount 3 1 = 2 := by native_decide
example : ballotSeqCount 4 2 = 5 := by native_decide
example : ballotSeqCount 5 3 = 14 := by native_decide
example : ballotSeqCount 6 2 = 14 := by native_decide

/-- Ballot formula: ballotSeqCount p q * (p+q) = (p-q) * C(p+q, p) for q < p.
    Proved via the reflection principle (the bijection between "bad paths" and
    reflected paths, which is a 1D version of the Crossing Lemma). -/
theorem ballot_formula (p q : ℕ) (hpq : q < p) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ballotSeqCount p q * (p + q) = (p - q) * Nat.choose (p + q) p := by
  simp only [ballotSeqCount]
  set a := Nat.choose (p + q - 1) (p - 1) with ha_def
  set b := Nat.choose (p + q - 1) p with hb_def
  -- Absorption: b * p = a * q
  have h_abs : b * p = a * q := by
    -- add_one_mul_choose_eq: (n+1) * C(n, k) = C(n+1, k+1) * (k+1)
    -- with n = p+q-2, k = p-1: (p+q-1) * C(p+q-2, p-1) = C(p+q-1, p) * p
    have hA := Nat.add_one_mul_choose_eq (p + q - 2) (p - 1)
    rw [show p + q - 2 + 1 = p + q - 1 from by omega,
        show p - 1 + 1 = p from by omega] at hA
    -- hA : (p+q-1) * C(p+q-2, p-1) = b * p
    -- with n = p+q-2, k = q-1: (p+q-1) * C(p+q-2, q-1) = C(p+q-1, q) * q
    have hB := Nat.add_one_mul_choose_eq (p + q - 2) (q - 1)
    rw [show p + q - 2 + 1 = p + q - 1 from by omega,
        show q - 1 + 1 = q from by omega] at hB
    -- hB : (p+q-1) * C(p+q-2, q-1) = C(p+q-1, q) * q
    -- Symmetry: C(p+q-2, p-1) = C(p+q-2, q-1)
    have hC : Nat.choose (p + q - 2) (p - 1) = Nat.choose (p + q - 2) (q - 1) :=
      Nat.choose_symm_of_eq_add (by omega)
    -- C(p+q-1, q) = a by symmetry
    have hD : Nat.choose (p + q - 1) q = a := by
      simp only [ha_def]
      exact (Nat.choose_symm_of_eq_add (by omega)).symm
    calc b * p = (p + q - 1) * Nat.choose (p + q - 2) (p - 1) := hA.symm
      _ = (p + q - 1) * Nat.choose (p + q - 2) (q - 1) := by rw [hC]
      _ = Nat.choose (p + q - 1) q * q := hB
      _ = a * q := by rw [hD]
  -- Pascal: C(p+q, p) = a + b
  have h_pascal : Nat.choose (p + q) p = a + b := by
    have h := Nat.choose_succ_succ' (p + q - 1) (p - 1)
    rw [show p + q - 1 + 1 = p + q from by omega,
        show p - 1 + 1 = p from by omega] at h
    simp only [← ha_def, ← hb_def] at h
    exact h
  -- b ≤ a from absorption: b * p = a * q and q ≤ p
  have h_le : b ≤ a := by
    have h1 : b * q ≤ b * p := Nat.mul_le_mul_left b (by omega)
    have h2 : b * q ≤ a * q := h1.trans (le_of_eq h_abs)
    exact Nat.le_of_mul_le_mul_right h2 (by omega)
  rw [h_pascal]
  have hqp : q ≤ p := by omega
  zify [h_le, hqp] at h_abs ⊢
  linear_combination -2 * h_abs

/- ## Part X: Ballot Count via Path Difference -/

/-- The ballot count equals the difference of two path counts (1D reflection principle).
    The reflection principle bijects "bad ballot sequences" (where B ever leads) with
    paths that have one fewer East step, proving: ballotSeqCount p q = C(p+q-1,p-1) - C(p+q-1,p)
    = |pathType q (p-1)| - |pathType (q-1) p|. -/
theorem ballot_via_path_count (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : q < p) :
    ballotSeqCount p q = Fintype.card (pathType q (p - 1)) - Fintype.card (pathType (q - 1) p) := by
  simp only [path_count_eq_choose, ballotSeqCount]
  -- Nat.choose (q+(p-1)) q = Nat.choose (p+q-1) (p-1) by symmetry
  have h1 : Nat.choose (q + (p - 1)) q = Nat.choose (p + q - 1) (p - 1) := by
    rw [show q + (p - 1) = p + q - 1 from by omega]
    exact Nat.choose_symm_of_eq_add (by omega)
  -- Nat.choose ((q-1)+p) (q-1) = Nat.choose (p+q-1) p by symmetry
  have h2 : Nat.choose ((q - 1) + p) (q - 1) = Nat.choose (p + q - 1) p := by
    rw [show (q - 1) + p = p + q - 1 from by omega]
    exact Nat.choose_symm_of_eq_add (by omega)
  rw [h1, h2]

/- ## Part XI: Involution Infrastructure for LGV -/

/-- Split a path after its k-th East step: prefix (containing k East steps) and suffix.
    Uses direct component access (not let-bindings) for cleaner definitional reduction. -/
def splitAfterEast : LPath → ℕ → LPath × LPath
  | l, 0 => ([], l)
  | [], _ => ([], [])
  | (false :: xs), (k + 1) =>
    (false :: (splitAfterEast xs k).1, (splitAfterEast xs k).2)
  | (true :: xs), k =>
    (true :: (splitAfterEast xs k).1, (splitAfterEast xs k).2)

/-- Reconstructing the path from its split -/
theorem splitAfterEast_append (l : LPath) (k : ℕ) :
    (splitAfterEast l k).1 ++ (splitAfterEast l k).2 = l := by
  induction l generalizing k with
  | nil => cases k <;> simp [splitAfterEast]
  | cons x xs ih =>
    cases x with
    | false =>
      cases k with
      | zero => simp [splitAfterEast]
      | succ k =>
        have h1 : (splitAfterEast (false :: xs) (k + 1)).1 = false :: (splitAfterEast xs k).1 := rfl
        have h2 : (splitAfterEast (false :: xs) (k + 1)).2 = (splitAfterEast xs k).2 := rfl
        rw [h1, h2, List.cons_append, ih k]
    | true =>
      cases k with
      | zero => simp [splitAfterEast]
      | succ k =>
        have h1 : (splitAfterEast (true :: xs) (k + 1)).1 = true :: (splitAfterEast xs (k + 1)).1 := rfl
        have h2 : (splitAfterEast (true :: xs) (k + 1)).2 = (splitAfterEast xs (k + 1)).2 := rfl
        rw [h1, h2, List.cons_append, ih (k + 1)]

/-- The prefix contains exactly k East steps (when k ≤ total) -/
theorem splitAfterEast_fst_eastSteps (l : LPath) (k : ℕ) (hk : k ≤ eastSteps l) :
    eastSteps (splitAfterEast l k).1 = k := by
  induction l generalizing k with
  | nil =>
    simp only [eastSteps, List.countP_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  | cons x xs ih =>
    cases x with
    | false =>
      cases k with
      | zero => simp [splitAfterEast, eastSteps]
      | succ k =>
        have h1 : (splitAfterEast (false :: xs) (k + 1)).1 = false :: (splitAfterEast xs k).1 := rfl
        -- Establish hk' by bridging eastSteps (false :: xs) = eastSteps xs + 1
        have heqs : eastSteps (false :: xs) = eastSteps xs + 1 := by
          simp [eastSteps, List.countP_cons]
        have hk' : k ≤ eastSteps xs := by linarith [heqs ▸ hk]
        -- eastSteps of a false-prefixed path is one more
        have key : eastSteps (splitAfterEast (false :: xs) (k + 1)).1 =
            eastSteps (splitAfterEast xs k).1 + 1 := by simp [h1, eastSteps, List.countP_cons]
        linarith [ih k hk']
    | true =>
      cases k with
      | zero => simp [splitAfterEast, eastSteps]
      | succ k =>
        have h1 : (splitAfterEast (true :: xs) (k + 1)).1 = true :: (splitAfterEast xs (k + 1)).1 := rfl
        -- Establish hk' by bridging eastSteps (true :: xs) = eastSteps xs
        have heqs : eastSteps (true :: xs) = eastSteps xs := by
          simp [eastSteps, List.countP_cons]
        have hk' : k + 1 ≤ eastSteps xs := by linarith [heqs ▸ hk]
        -- eastSteps unchanged when prefixed by a true step (not an East step)
        have key : eastSteps (splitAfterEast (true :: xs) (k + 1)).1 =
            eastSteps (splitAfterEast xs (k + 1)).1 := by simp [h1, eastSteps, List.countP_cons]
        linarith [ih (k + 1) hk']

/-- **Key Lemma**: Re-splitting a split prefix concatenated with new suffix recovers both parts.
    This is the fundamental property enabling the Lindström involution proof of the LGV lemma.
    The prefix must come from splitAfterEast (a "split prefix") — general lists with the same
    East count may have trailing North steps that would be absorbed differently. -/
theorem splitAfterEast_split_append (l rest : LPath) (k : ℕ) (hk : k ≤ eastSteps l) :
    splitAfterEast ((splitAfterEast l k).1 ++ rest) k = ((splitAfterEast l k).1, rest) := by
  induction l generalizing k with
  | nil =>
    have : k = 0 := by simp only [eastSteps, List.countP_nil] at hk; omega
    subst this
    simp [splitAfterEast]
  | cons x xs ih =>
    cases k with
    | zero => simp [splitAfterEast]
    | succ k =>
      cases x with
      | false =>
        have hk' : k ≤ eastSteps xs := by
          have : eastSteps (false :: xs) = eastSteps xs + 1 := by
            simp [eastSteps, List.countP_cons]
          omega
        show (false :: (splitAfterEast ((splitAfterEast xs k).1 ++ rest) k).1,
              (splitAfterEast ((splitAfterEast xs k).1 ++ rest) k).2) =
             (false :: (splitAfterEast xs k).1, rest)
        rw [ih k hk']
      | true =>
        have hk' : k + 1 ≤ eastSteps xs := by
          have : eastSteps (true :: xs) = eastSteps xs := by
            simp [eastSteps, List.countP_cons]
          omega
        show (true :: (splitAfterEast ((splitAfterEast xs (k + 1)).1 ++ rest) (k + 1)).1,
              (splitAfterEast ((splitAfterEast xs (k + 1)).1 ++ rest) (k + 1)).2) =
             (true :: (splitAfterEast xs (k + 1)).1, rest)
        rw [ih (k + 1) hk']

/-- northSteps is preserved by splitAfterEast: prefix + suffix North steps = total -/
theorem northSteps_splitAfterEast_sum (l : LPath) (k : ℕ) :
    northSteps (splitAfterEast l k).1 + northSteps (splitAfterEast l k).2 = northSteps l := by
  have h := northSteps_append (splitAfterEast l k).1 (splitAfterEast l k).2
  rw [splitAfterEast_append] at h
  linarith

/-- colEntry decrements the East index when passing a false step -/
private lemma colEntry_false_succ (xs : LPath) (k : ℕ) :
    colEntry (false :: xs) (k + 1) = colEntry xs k := by
  cases k with
  | zero => simp [colEntry, northBeforeEast]
  | succ k => simp [colEntry, northBeforeEast]

/-- colEntry increments by 1 when passing a true step -/
private lemma colEntry_true_succ (xs : LPath) (k : ℕ) :
    colEntry (true :: xs) (k + 1) = colEntry xs (k + 1) + 1 := by
  simp [colEntry, northBeforeEast]; omega

/-- The North steps in the prefix equal colEntry l k (y-offset after k East steps) -/
theorem northSteps_splitAfterEast_fst (l : LPath) (k : ℕ) :
    northSteps (splitAfterEast l k).1 = colEntry l k := by
  induction l generalizing k with
  | nil =>
    cases k with
    | zero => simp [splitAfterEast, northSteps, colEntry]
    | succ k => simp [splitAfterEast, northSteps, colEntry, northBeforeEast]
  | cons x xs ih =>
    cases x with
    | false =>
      cases k with
      | zero => simp [splitAfterEast, northSteps, colEntry]
      | succ k =>
        have h1 : (splitAfterEast (false :: xs) (k + 1)).1 = false :: (splitAfterEast xs k).1 := rfl
        rw [h1, northSteps_cons_false, colEntry_false_succ]
        exact ih k
    | true =>
      cases k with
      | zero => simp [splitAfterEast, northSteps, colEntry]
      | succ k =>
        have h1 : (splitAfterEast (true :: xs) (k + 1)).1 = true :: (splitAfterEast xs (k + 1)).1 := rfl
        rw [h1, northSteps_cons_true, colEntry_true_succ]
        have := ih (k + 1)
        omega

/-- Swap the tails of two paths after k East steps -/
def swapTails (l₁ l₂ : LPath) (k : ℕ) : LPath × LPath :=
  let (pre₁, suf₁) := splitAfterEast l₁ k
  let (pre₂, suf₂) := splitAfterEast l₂ k
  (pre₁ ++ suf₂, pre₂ ++ suf₁)

/-- Swapping twice restores the original paths.
    Requires both paths to have the same East step count m, with k ≤ m.
    The key is that splitAfterEast (pre₁ ++ suf₂) k = (pre₁, suf₂) since eastSteps pre₁ = k
    (proved via splitAfterEast_append_fst). -/
theorem swapTails_involutive (l₁ l₂ : LPath) (k m : ℕ)
    (hk₁ : l₁.countP (· = false) = m)
    (hk₂ : l₂.countP (· = false) = m)
    (hkm : k ≤ m) :
    swapTails (swapTails l₁ l₂ k).1 (swapTails l₁ l₂ k).2 k = (l₁, l₂) := by
  -- Convert countP hypotheses to eastSteps form
  have heast₁ : k ≤ eastSteps l₁ := by simp only [eastSteps]; linarith
  have heast₂ : k ≤ eastSteps l₂ := by simp only [eastSteps]; linarith
  -- splitAfterEast (pre₁ ++ suf₂) k = (pre₁, suf₂) and similarly for (pre₂ ++ suf₁)
  have h1 := splitAfterEast_split_append l₁ (splitAfterEast l₂ k).2 k heast₁
  have h2 := splitAfterEast_split_append l₂ (splitAfterEast l₁ k).2 k heast₂
  -- (swapTails l₁ l₂ k).1/.2 are the appended components by definition
  have hfst : (swapTails l₁ l₂ k).1 =
      (splitAfterEast l₁ k).1 ++ (splitAfterEast l₂ k).2 := rfl
  have hsnd : (swapTails l₁ l₂ k).2 =
      (splitAfterEast l₂ k).1 ++ (splitAfterEast l₁ k).2 := rfl
  rw [hfst, hsnd]
  -- After applying h1 and h2, the double swap resolves to pre₁++suf₁ and pre₂++suf₂
  show ((splitAfterEast ((splitAfterEast l₁ k).1 ++ (splitAfterEast l₂ k).2) k).1 ++
        (splitAfterEast ((splitAfterEast l₂ k).1 ++ (splitAfterEast l₁ k).2) k).2,
        (splitAfterEast ((splitAfterEast l₂ k).1 ++ (splitAfterEast l₁ k).2) k).1 ++
        (splitAfterEast ((splitAfterEast l₁ k).1 ++ (splitAfterEast l₂ k).2) k).2) = (l₁, l₂)
  rw [h1, h2]
  simp only [Prod.fst, Prod.snd, splitAfterEast_append]

/-- North steps of the first swapped path: colEntry l₁ k (prefix) + suffix of l₂ -/
theorem northSteps_swapTails_fst (l₁ l₂ : LPath) (k : ℕ) (m : ℕ)
    (hk₁ : l₁.countP (· = false) = m) (hk₂ : l₂.countP (· = false) = m)
    (hkm : k ≤ m) :
    northSteps (swapTails l₁ l₂ k).1 =
    colEntry l₁ k + (northSteps l₂ - colEntry l₂ k) := by
  -- (swapTails l₁ l₂ k).1 = pre₁ ++ suf₂ by definition
  have hval : (swapTails l₁ l₂ k).1 =
      (splitAfterEast l₁ k).1 ++ (splitAfterEast l₂ k).2 := rfl
  rw [hval, northSteps_append, northSteps_splitAfterEast_fst l₁ k]
  have h_sum := northSteps_splitAfterEast_sum l₂ k
  have h_fst := northSteps_splitAfterEast_fst l₂ k
  omega

/-- **Key LGV Counting Lemma**: Degenerate case a₁ = a₂.
    When paths start at the same y, every pair of paths shares the start lattice point.
    - If m = 0: y ∈ finalRange l y 0 for any l (since y ≤ y and y ≤ y + northSteps l)
    - If m > 0: y ∈ colYRange l y 0 at column x=0 (since colEntry l 0 = 0) -/
lemma lgv_same_start (m n₁ n₂ y : ℕ) :
    niPairCount m n₁ n₂ y y = 0 := by
  -- When paths start at same y, the start point y is in both column-0 ranges
  -- (or both final ranges when m=0), so no pair is non-intersecting.
  unfold niPairCount
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro ⟨⟨⟨l₁, _⟩, ⟨l₂, _⟩⟩, hni⟩
  cases m with
  | zero =>
    exact hni.2 y
      ⟨⟨by simp [colEntry], Nat.le_add_right y _⟩,
       ⟨by simp [colEntry], Nat.le_add_right y _⟩⟩
  | succ m =>
    exact hni.1 0 (Nat.zero_lt_succ m) y
      ⟨⟨by simp [colEntry], Nat.le_add_right y _⟩,
       ⟨by simp [colEntry], Nat.le_add_right y _⟩⟩

/-- **Key LGV Counting Lemma**: LGV det = 0 when a₁ = a₂ -/
lemma lgvDet_same_start (m b₁ b₂ a : ℕ) :
    lgvDet m a b₁ a b₂ = 0 := by
  unfold lgvDet; ring

/-- **Key LGV Counting Lemma**: LGV det = 0 when b₁ = b₂ -/
lemma lgvDet_same_end (m a₁ a₂ b : ℕ) :
    lgvDet m a₁ b a₂ b = 0 := by
  unfold lgvDet; ring

/-- **Key LGV Counting Lemma**: Degenerate case b₁ = b₂.
    When paths end at the same height, both final ranges include the common
    endpoint y₁ + n₁ = y₂ + n₂, so every pair shares that lattice point. -/
lemma lgv_same_end (m n₁ n₂ y₁ y₂ : ℕ) (h : y₁ + n₁ = y₂ + n₂) :
    niPairCount m n₁ n₂ y₁ y₂ = 0 := by
  unfold niPairCount
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro ⟨⟨⟨l₁, hl₁_len, hl₁_east⟩, ⟨l₂, hl₂_len, hl₂_east⟩⟩, hni⟩
  -- northSteps lᵢ = nᵢ: from length = m + nᵢ and eastSteps = m
  have hns₁ : northSteps l₁ = n₁ := by
    have := eastSteps_add_northSteps l₁
    simp only [eastSteps] at this; omega
  have hns₂ : northSteps l₂ = n₂ := by
    have := eastSteps_add_northSteps l₂
    simp only [eastSteps] at this; omega
  -- The common endpoint y₁ + n₁ = y₂ + n₂ is in both final ranges
  have h_in₁ : y₁ + n₁ ∈ finalRange l₁ y₁ m := by
    refine ⟨?_, by rw [hns₁]⟩
    exact Nat.add_le_add_left (colEntry_le_northSteps l₁ m hl₁_east) y₁ |>.trans
      (by rw [hns₁])
  have h_in₂ : y₂ + n₂ ∈ finalRange l₂ y₂ m := by
    refine ⟨?_, by rw [hns₂]⟩
    exact Nat.add_le_add_left (colEntry_le_northSteps l₂ m hl₂_east) y₂ |>.trans
      (by rw [hns₂])
  rw [h] at h_in₁
  exact hni.2 (y₂ + n₂) ⟨h_in₁, h_in₂⟩

/-- **Key LGV Counting Lemma**: All crossing pairs are intersecting.
    Crossing pairs have y₁ < y₂ (sources ordered) but y₁+n₁ > y₂+n₂ (endpoints reversed).
    The Crossing Lemma guarantees they must share a lattice point, so niPairCount = 0.
    This is the key step in the LGV proof: the "crossing" determinant term vanishes entirely. -/
lemma lgv_crossing_zero (m n₁ n₂ a₁ a₂ : ℕ)
    (ha : a₁ < a₂) (hend : a₂ + n₂ < a₁ + n₁) :
    niPairCount m n₁ n₂ a₁ a₂ = 0 := by
  unfold niPairCount
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro ⟨⟨⟨l₁, hl₁_len, hl₁_east⟩, ⟨l₂, hl₂_len, hl₂_east⟩⟩, hni⟩
  have hns₁ : l₁.countP (· = true) = n₁ := by
    have := eastSteps_add_northSteps l₁
    simp only [eastSteps, northSteps] at this; omega
  have hns₂ : l₂.countP (· = true) = n₂ := by
    have := eastSteps_add_northSteps l₂
    simp only [eastSteps, northSteps] at this; omega
  exact crossing_lemma m n₁ n₂ a₁ a₂ hl₁_east hns₁ hl₂_east hns₂ ha hend hni

/-- **Key LGV Counting Lemma**: m=0 overlap case.
    When m=0 (no East steps), the only paths are all-North. Both final ranges
    are [yᵢ, yᵢ+nᵢ]. If these overlap, every pair shares a lattice point. -/
lemma lgv_zero_east_overlap (n₁ n₂ y₁ y₂ : ℕ)
    (h_overlap : y₁ ≤ y₂) (h_in : y₂ ≤ y₁ + n₁) :
    niPairCount 0 n₁ n₂ y₁ y₂ = 0 := by
  unfold niPairCount
  rw [Fintype.card_eq_zero_iff]
  constructor
  intro ⟨⟨⟨l₁, hl₁_len, hl₁_east⟩, ⟨l₂, hl₂_len, hl₂_east⟩⟩, hni⟩
  have hns₁ : northSteps l₁ = n₁ := by
    have := eastSteps_add_northSteps l₁; simp only [eastSteps] at this; omega
  have hns₂ : northSteps l₂ = n₂ := by
    have := eastSteps_add_northSteps l₂; simp only [eastSteps] at this; omega
  -- The point y₂ is in both final ranges
  apply hni.2 y₂
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [colEntry_zero, Nat.add_zero]; exact h_overlap
  · rw [hns₁]; exact h_in
  · rw [colEntry_zero, Nat.add_zero]
  · exact Nat.le_add_right y₂ _

/- ## Part XIII: Verified LGV Examples -/

-- LGV det for (m=1, a₁=0, b₁=1, a₂=1, b₂=2):
-- C(2,1)*C(2,1) - C(3,1)*C(1,1) = 4 - 3 = 1
example : lgvDet 1 0 1 1 2 = 1 := by native_decide

-- LGV det for (m=2, a₁=0, b₁=2, a₂=1, b₂=3):
-- C(4,2)*C(4,2) - C(5,2)*C(3,2) = 36 - 30 = 6
example : lgvDet 2 0 2 1 3 = 6 := by native_decide

-- LGV det for (m=3, a₁=0, b₁=3, a₂=1, b₂=4):
-- C(6,3)*C(6,3) - C(7,3)*C(5,3) = 400 - 350 = 50
example : lgvDet 3 0 3 1 4 = 50 := by native_decide

-- LGV det for (m=4, a₁=0, b₁=4, a₂=1, b₂=5):
-- C(8,4)*C(8,4) - C(9,4)*C(7,4) = 4900 - 4410 = 490
example : lgvDet 4 0 4 1 5 = 490 := by native_decide

-- The Crossing Lemma prevents crossing pairs from being non-intersecting:
-- When paths start in opposite vertical order vs endpoints (y₁ < y₂ but ends > ends),
-- they MUST share a lattice point. This is why the "crossing" term in LGV vanishes.

/- ## Part XIII: Complement Counting and Lindström Involution -/

-- The proof of the 2×2 LGV Lemma (Case 3: strict ordering a₁ < a₂ ≤ b₁ < b₂)
-- reduces to a cardinality equation via complement counting:
--
--   |NI identity| = |all identity| - |intersecting identity|
--                 = |all identity| - |all crossing|    (Lindström bijection)
--                 = lgvDet                             (path counting + arithmetic)
--
-- The Lindström bijection is the key: it maps intersecting identity pairs to
-- crossing pairs by swapping path suffixes at the first shared lattice point.

/-- Complement counting: NI pairs + intersecting pairs = all pairs.
    Uses the canonical equivalence {x // p x} ⊕ {x // ¬p x} ≃ α. -/
theorem ni_complement_count (m n₁ n₂ y₁ y₂ : ℕ) :
    niPairCount m n₁ n₂ y₁ y₂ +
    Fintype.card {p : pathType m n₁ × pathType m n₂ //
      ¬NonIntersecting p.1.val p.2.val m y₁ y₂} =
    Fintype.card (pathType m n₁ × pathType m n₂) := by
  unfold niPairCount
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (Equiv.sumCompl
    (fun p : pathType m n₁ × pathType m n₂ =>
      NonIntersecting p.1.val p.2.val m y₁ y₂))

/-- Total identity pairs = C(m+n₁, m) * C(m+n₂, m) -/
theorem total_identity_count (m n₁ n₂ : ℕ) :
    Fintype.card (pathType m n₁ × pathType m n₂) =
    Nat.choose (m + n₁) m * Nat.choose (m + n₂) m := by
  rw [Fintype.card_prod, path_count_eq_choose, path_count_eq_choose]

-- lindstrom_involution_card is defined after Part XXIII (depends on lindstrom_involution)

/- ## Part XIV: Path Transposition (East ↔ North Flip) -/

/-- Flip a lattice path: swap East (false) ↔ North (true).
    This transposes the grid, mapping paths with m East + n North steps
    to paths with n East + m North steps. -/
def pathFlip (l : LPath) : LPath := l.map (!·)

theorem pathFlip_length (l : LPath) : (pathFlip l).length = l.length := by
  simp [pathFlip]

/-- Flipping twice is the identity -/
theorem pathFlip_involutive (l : LPath) : pathFlip (pathFlip l) = l := by
  unfold pathFlip
  rw [List.map_map,
      show (fun x : Bool => !x) ∘ (fun x : Bool => !x) = id from by ext b; simp,
      List.map_id]

/-- East steps of the flipped path = North steps of the original -/
theorem pathFlip_eastSteps (l : LPath) : eastSteps (pathFlip l) = northSteps l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | false =>
      have h1 : pathFlip (false :: xs) = true :: pathFlip xs := rfl
      rw [h1]
      have h2 : eastSteps (true :: pathFlip xs) = eastSteps (pathFlip xs) := by
        simp [eastSteps]
      rw [h2, northSteps_cons_false, ih]
    | true =>
      have h1 : pathFlip (true :: xs) = false :: pathFlip xs := rfl
      rw [h1]
      have h2 : eastSteps (false :: pathFlip xs) = eastSteps (pathFlip xs) + 1 := by
        simp [eastSteps]
      rw [h2, northSteps_cons_true, ih]; omega

/-- North steps of the flipped path = East steps of the original -/
theorem pathFlip_northSteps (l : LPath) : northSteps (pathFlip l) = eastSteps l := by
  have h := eastSteps_add_northSteps (pathFlip l)
  rw [pathFlip_length, pathFlip_eastSteps] at h
  have h2 := eastSteps_add_northSteps l
  omega

/-- Path transposition: flipping East↔North gives a bijection pathType m n ≃ pathType n m.
    This is the combinatorial proof that C(m+n, m) = C(m+n, n). -/
def pathFlipEquiv (m n : ℕ) : pathType m n ≃ pathType n m where
  toFun := fun ⟨l, hlen, heast⟩ =>
    ⟨pathFlip l,
     by rw [pathFlip_length, Nat.add_comm]; exact hlen,
     by have h := pathFlip_eastSteps l
        unfold eastSteps northSteps at h
        have h_sum := eastSteps_add_northSteps l
        unfold eastSteps northSteps at h_sum; omega⟩
  invFun := fun ⟨l, hlen, heast⟩ =>
    ⟨pathFlip l,
     by rw [pathFlip_length, Nat.add_comm]; exact hlen,
     by have h := pathFlip_eastSteps l
        unfold eastSteps northSteps at h
        have h_sum := eastSteps_add_northSteps l
        unfold eastSteps northSteps at h_sum; omega⟩
  left_inv := fun ⟨l, _, _⟩ => Subtype.ext (pathFlip_involutive l)
  right_inv := fun ⟨l, _, _⟩ => Subtype.ext (pathFlip_involutive l)

/-- **Binomial Coefficient Symmetry via Paths**: C(m+n, m) = C(m+n, n).
    The path flip bijection gives a purely combinatorial proof: paths with m East + n North
    steps biject with paths with n East + m North steps by swapping step types. -/
theorem choose_symm_via_paths (m n : ℕ) :
    Nat.choose (m + n) m = Nat.choose (m + n) n := by
  have h1 := path_count_eq_choose m n
  have h2 := path_count_eq_choose n m
  rw [show n + m = m + n from Nat.add_comm n m] at h2
  have h3 : Fintype.card (pathType m n) = Fintype.card (pathType n m) :=
    Fintype.card_congr (pathFlipEquiv m n)
  linarith

/- ## Part XV: LGV Determinant Algebra -/

/-- **Antisymmetry in Sources**: Swapping the source y-coordinates negates the LGV determinant. -/
theorem lgvDet_swap_sources (m a₁ b₁ a₂ b₂ : ℕ) :
    lgvDet m a₂ b₁ a₁ b₂ = -lgvDet m a₁ b₁ a₂ b₂ := by
  unfold lgvDet; ring

/-- **Antisymmetry in Targets**: Swapping the target y-coordinates negates the LGV determinant. -/
theorem lgvDet_swap_targets (m a₁ b₁ a₂ b₂ : ℕ) :
    lgvDet m a₁ b₂ a₂ b₁ = -lgvDet m a₁ b₁ a₂ b₂ := by
  unfold lgvDet; ring

-- lgvDet_nonneg is defined after Part XXIV (depends on lgv_lemma_2x2)

/-- **Double swap vanishes**: Swapping both sources and targets recovers the original. -/
theorem lgvDet_swap_both (m a₁ b₁ a₂ b₂ : ℕ) :
    lgvDet m a₂ b₂ a₁ b₁ = lgvDet m a₁ b₁ a₂ b₂ := by
  unfold lgvDet; ring

/- ## Part XVI: Catalan-Ballot Unification -/

/-- **Catalan = Ballot**: The n-th Catalan number equals the ballot count for (n+1) vs n votes.
    Both count lattice paths that stay strictly above the diagonal, via two equivalent
    formulations of the reflection principle:
    - Cn n = C(2n,n) - C(2n,n+1) [Catalan via difference]
    - ballotSeqCount (n+1) n = C(2n, n) - C(2n, n+1) [ballot via reflection] -/
theorem catalan_eq_ballot (n : ℕ) : Cn n = ballotSeqCount (n + 1) n := by
  simp only [Cn, ballotSeqCount,
    show n + 1 + n - 1 = 2 * n from by omega,
    show n + 1 - 1 = n from by omega]

-- Verified for small values
example : Cn 0 = ballotSeqCount 1 0 := by native_decide
example : Cn 1 = ballotSeqCount 2 1 := by native_decide
example : Cn 2 = ballotSeqCount 3 2 := by native_decide
example : Cn 3 = ballotSeqCount 4 3 := by native_decide
example : Cn 4 = ballotSeqCount 5 4 := by native_decide

/-- **Catalan via (n+1)**: Cn(n) = C(2n,n) / (n+1), combined with ballot theorem.
    If q < p and both ≥ 1, then ballotSeqCount p q * (p+q) = (p-q) * C(p+q,p).
    Setting p = n+1, q = n gives Cn(n) * (2n+1) = 1 * C(2n+1, n+1).
    Here we just show the implication: catalan_formula + catalan_eq_ballot together give
    the ballot formula for (n+1, n). -/
theorem catalan_ballot_division (n : ℕ) :
    ballotSeqCount (n + 1) n * (n + 1) = Nat.choose (2 * n) n := by
  rw [← catalan_eq_ballot]
  exact catalan_formula n

/- ## Part XVII: Entry Gap Analysis and swapTails Properties

This section develops the entry gap framework and proves key properties of swapTails
that are needed for the Lindström involution.

**Entry gap**: Define gap(k) = (y₂ + colEntry l₂ k) - (y₁ + colEntry l₁ k).
When y₁ < y₂, gap(0) > 0. Non-intersection preserves gap positivity (via
nonIntersecting_entry_order). This is used in the crossing lemma.

**swapTails properties**: We prove that swapTails preserves East step counts and
total path lengths — essential for showing swapped paths are valid pathType elements.

**Toward eliminating the Lindström axiom**: The full bijection requires finding the
first shared lattice point between intersecting paths. This requires a finer analysis
than column-entry boundaries alone:
- NonIntersecting uses column Y-ranges (intervals), not just boundary points
- ¬NonIntersecting gives overlap in some column's Y-range
- The Lindström involution swaps at the lexicographically first shared lattice point
- This point may be in the interior of a column, not just at a boundary
See the axiom documentation for the remaining construction needed.
-/

/-- The "gap" between path entry y-coordinates at column k.
    Positive means P₁ is below P₂, zero or negative means they've met/crossed.
    Defined on ℤ to handle the subtraction cleanly. -/
def entryGap (l₁ l₂ : LPath) (y₁ y₂ : ℕ) (k : ℕ) : ℤ :=
  (y₂ + colEntry l₂ k : ℤ) - (y₁ + colEntry l₁ k : ℤ)

/-- At column 0, the gap is y₂ - y₁ -/
theorem entryGap_zero (l₁ l₂ : LPath) (y₁ y₂ : ℕ) :
    entryGap l₁ l₂ y₁ y₂ 0 = (y₂ : ℤ) - y₁ := by
  simp [entryGap, colEntry_zero]

/-- If paths are non-intersecting and the gap is positive at column k,
    the gap stays positive at column k+1 (rephrasing of nonIntersecting_entry_order). -/
theorem entryGap_pos_succ {l₁ l₂ : LPath} {m y₁ y₂ : ℕ}
    (hni : NonIntersecting l₁ l₂ m y₁ y₂)
    (hk : k < m)
    (hpos : 0 < entryGap l₁ l₂ y₁ y₂ k) :
    0 < entryGap l₁ l₂ y₁ y₂ (k + 1) := by
  simp only [entryGap] at hpos ⊢
  have h_entry : y₁ + colEntry l₁ k < y₂ + colEntry l₂ k := by omega
  have h_next := nonIntersecting_entry_order hni hk h_entry
  omega

/-- **Key lemma**: If paths are non-intersecting and y₁ < y₂,
    the gap is positive at ALL columns k ≤ m.
    (Proved by induction using entryGap_pos_succ.) -/
theorem entryGap_pos_all {l₁ l₂ : LPath} {m y₁ y₂ : ℕ}
    (hni : NonIntersecting l₁ l₂ m y₁ y₂)
    (hstart : y₁ < y₂) :
    ∀ k ≤ m, 0 < entryGap l₁ l₂ y₁ y₂ k := by
  intro k hkm
  induction k with
  | zero => rw [entryGap_zero]; omega
  | succ k ih =>
    apply entryGap_pos_succ hni (by omega : k < m)
    exact ih (by omega)

/-- Gap non-positive means P₁'s entry y is at or above P₂'s entry y -/
theorem crossing_col_entry_ge {l₁ l₂ : LPath} {y₁ y₂ k : ℕ}
    (hgap : entryGap l₁ l₂ y₁ y₂ k ≤ 0) :
    y₂ + colEntry l₂ k ≤ y₁ + colEntry l₁ k := by
  simp only [entryGap] at hgap; omega

/-- Gap positive means P₁'s entry y is strictly below P₂'s entry y -/
theorem crossing_col_prev_lt {l₁ l₂ : LPath} {y₁ y₂ k : ℕ}
    (hgap : 0 < entryGap l₁ l₂ y₁ y₂ k) :
    y₁ + colEntry l₁ k < y₂ + colEntry l₂ k := by
  simp only [entryGap] at hgap; omega

/- ### swapTails East Step and Length Preservation -/

/-- **swapTails preserves East step count** for the first resulting path.
    Since pre₁ has k East steps and suf₂ has (m-k) East steps, their concatenation has m. -/
theorem eastSteps_swapTails_fst (l₁ l₂ : LPath) (k m : ℕ)
    (hk₁ : l₁.countP (· = false) = m)
    (hk₂ : l₂.countP (· = false) = m)
    (hkm : k ≤ m) :
    eastSteps (swapTails l₁ l₂ k).1 = m := by
  have heast₁ : k ≤ eastSteps l₁ := by simp only [eastSteps]; omega
  have heast₂ : k ≤ eastSteps l₂ := by simp only [eastSteps]; omega
  have hval : (swapTails l₁ l₂ k).1 =
      (splitAfterEast l₁ k).1 ++ (splitAfterEast l₂ k).2 := rfl
  rw [hval, show eastSteps ((splitAfterEast l₁ k).1 ++ (splitAfterEast l₂ k).2) =
    eastSteps (splitAfterEast l₁ k).1 + eastSteps (splitAfterEast l₂ k).2 from by
    simp [eastSteps, List.countP_append]]
  have h_fst₁ := splitAfterEast_fst_eastSteps l₁ k heast₁
  have h_sum₂ : eastSteps (splitAfterEast l₂ k).1 + eastSteps (splitAfterEast l₂ k).2 =
      eastSteps l₂ := by
    have h := splitAfterEast_append l₂ k
    conv_rhs => rw [← h]
    simp [eastSteps, List.countP_append]
  have h_fst₂ := splitAfterEast_fst_eastSteps l₂ k heast₂
  simp only [eastSteps] at h_fst₁ h_fst₂ h_sum₂ hk₂ ⊢; omega

/-- **swapTails preserves East step count** for the second resulting path. -/
theorem eastSteps_swapTails_snd (l₁ l₂ : LPath) (k m : ℕ)
    (hk₁ : l₁.countP (· = false) = m)
    (hk₂ : l₂.countP (· = false) = m)
    (hkm : k ≤ m) :
    eastSteps (swapTails l₁ l₂ k).2 = m := by
  have heast₁ : k ≤ eastSteps l₁ := by simp only [eastSteps]; omega
  have heast₂ : k ≤ eastSteps l₂ := by simp only [eastSteps]; omega
  have hval : (swapTails l₁ l₂ k).2 =
      (splitAfterEast l₂ k).1 ++ (splitAfterEast l₁ k).2 := rfl
  rw [hval, show eastSteps ((splitAfterEast l₂ k).1 ++ (splitAfterEast l₁ k).2) =
    eastSteps (splitAfterEast l₂ k).1 + eastSteps (splitAfterEast l₁ k).2 from by
    simp [eastSteps, List.countP_append]]
  have h_fst₂ := splitAfterEast_fst_eastSteps l₂ k heast₂
  have h_sum₁ : eastSteps (splitAfterEast l₁ k).1 + eastSteps (splitAfterEast l₁ k).2 =
      eastSteps l₁ := by
    have h := splitAfterEast_append l₁ k
    conv_rhs => rw [← h]
    simp [eastSteps, List.countP_append]
  have h_fst₁ := splitAfterEast_fst_eastSteps l₁ k heast₁
  simp only [eastSteps] at h_fst₁ h_fst₂ h_sum₁ hk₁ ⊢; omega

/-- **swapTails length preservation** for the first path -/
theorem length_swapTails_fst (l₁ l₂ : LPath) (k : ℕ) :
    (swapTails l₁ l₂ k).1.length =
    (splitAfterEast l₁ k).1.length + (splitAfterEast l₂ k).2.length := by
  simp [swapTails, List.length_append]

/-- **swapTails length preservation** for the second path -/
theorem length_swapTails_snd (l₁ l₂ : LPath) (k : ℕ) :
    (swapTails l₁ l₂ k).2.length =
    (splitAfterEast l₂ k).1.length + (splitAfterEast l₁ k).2.length := by
  simp [swapTails, List.length_append]

/-- **North steps of suffix**: northSteps of the suffix after k East steps equals
    total northSteps minus the prefix northSteps (which equals colEntry l k). -/
theorem northSteps_splitAfterEast_snd (l : LPath) (k : ℕ) :
    northSteps (splitAfterEast l k).2 = northSteps l - colEntry l k := by
  have h_sum := northSteps_splitAfterEast_sum l k
  have h_fst := northSteps_splitAfterEast_fst l k
  omega

/-
═══════════════════════════════════════════════════════════════════════════════
PART XVIII: FIRST INTERSECTION COLUMN — TOWARD ELIMINATING THE AXIOM
═══════════════════════════════════════════════════════════════════════════════

The Lindström involution axiom can be eliminated by constructing the
explicit bijection. The key ingredient is finding the first column
where two paths share a lattice point. This section establishes the
decidable intersection infrastructure.

Strategy:
1. columnsOverlap: decidable predicate for range overlap at column x
2. ¬NonIntersecting → ∃ overlapping column (or final range overlap)
3. Nat.find gives firstIntersectionColumn
4. swapTails at this column gives the explicit involution
-/

/-- Two paths' y-ranges overlap at column x when the ranges
    [y₁+entry₁(x), y₁+entry₁(x+1)] and [y₂+entry₂(x), y₂+entry₂(x+1)]
    have a common point. This is equivalent to: the lower bound of each
    range is at most the upper bound of the other. -/
def columnsOverlap (l₁ l₂ : LPath) (y₁ y₂ x : ℕ) : Prop :=
  y₁ + colEntry l₁ x ≤ y₂ + colEntry l₂ (x + 1) ∧
  y₂ + colEntry l₂ x ≤ y₁ + colEntry l₁ (x + 1)

instance : DecidablePred (columnsOverlap l₁ l₂ y₁ y₂) := fun x =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- columnsOverlap characterizes the existence of a shared y-coordinate
    in both paths' column ranges. -/
theorem columnsOverlap_iff_exists_shared_y (l₁ l₂ : LPath) (y₁ y₂ x : ℕ) :
    columnsOverlap l₁ l₂ y₁ y₂ x ↔
    ∃ y, y ∈ colYRange l₁ y₁ x ∧ y ∈ colYRange l₂ y₂ x := by
  constructor
  · intro ⟨h₁₂, h₂₁⟩
    use max (y₁ + colEntry l₁ x) (y₂ + colEntry l₂ x)
    have mono₁ := colEntry_mono l₁ x
    have mono₂ := colEntry_mono l₂ x
    exact ⟨⟨le_max_left _ _, max_le (by omega) h₂₁⟩,
           ⟨le_max_right _ _, max_le h₁₂ (by omega)⟩⟩
  · intro ⟨y, hy₁, hy₂⟩
    exact ⟨by exact le_trans hy₁.1 hy₂.2, by exact le_trans hy₂.1 hy₁.2⟩

/-- columnsOverlap at column 0 iff y-ranges from the start overlap.
    Since colEntry l 0 = 0 for all paths, overlap at column 0 means
    y₁ ≤ y₂ + colEntry l₂ 1 and y₂ ≤ y₁ + colEntry l₁ 1. -/
theorem columnsOverlap_zero (l₁ l₂ : LPath) (y₁ y₂ : ℕ) :
    columnsOverlap l₁ l₂ y₁ y₂ 0 ↔
    y₁ ≤ y₂ + colEntry l₂ 1 ∧ y₂ ≤ y₁ + colEntry l₁ 1 := by
  simp [columnsOverlap, colEntry_zero]

/-- If paths are NOT non-intersecting, there is either a column overlap
    or a final range overlap. This is the key decomposition for
    constructing the first intersection point. -/
theorem not_ni_implies_overlap_or_final {l₁ l₂ : LPath} {m y₁ y₂ : ℕ}
    (h : ¬NonIntersecting l₁ l₂ m y₁ y₂) :
    (∃ x, x < m ∧ columnsOverlap l₁ l₂ y₁ y₂ x) ∨
    (∃ y, y ∈ finalRange l₁ y₁ m ∧ y ∈ finalRange l₂ y₂ m) := by
  simp only [NonIntersecting, not_and_or] at h
  rcases h with h | h
  · left
    push_neg at h
    obtain ⟨x, hxm, y, hy⟩ := h
    exact ⟨x, hxm, (columnsOverlap_iff_exists_shared_y l₁ l₂ y₁ y₂ x).mpr ⟨y, hy⟩⟩
  · right
    push_neg at h
    exact h

/-- In the crossing case, paths are not non-intersecting (from crossing_lemma),
    so there must be either a column overlap or a final range overlap.
    The first such intersection determines where to apply swapTails
    for the Lindström involution. -/
theorem crossing_not_ni {l₁ l₂ : LPath} {m n₁ n₂ y₁ y₂ : ℕ}
    (hm₁ : eastSteps l₁ = m) (hn₁ : northSteps l₁ = n₁)
    (hm₂ : eastSteps l₂ = m) (hn₂ : northSteps l₂ = n₂)
    (hstart : y₁ < y₂) (hend : y₂ + n₂ < y₁ + n₁) :
    (∃ x, x < m ∧ columnsOverlap l₁ l₂ y₁ y₂ x) ∨
    (∃ y, y ∈ finalRange l₁ y₁ m ∧ y ∈ finalRange l₂ y₂ m) :=
  not_ni_implies_overlap_or_final
    (crossing_lemma m n₁ n₂ y₁ y₂ hm₁ hn₁ hm₂ hn₂ hstart hend)

/- ═══════════════════════════════════════════════════════════════════════════════
PART XIX: LINDSTRÖM INVOLUTION — ELIMINATING THE AXIOM
═══════════════════════════════════════════════════════════════════════════════

Strategy: track step-by-step lattice point trajectories, find the first
shared lattice point between intersecting paths, swap suffixes there.

Key insight: splitting at a shared point (x, y) ensures the swapped
paths have the right North step counts:
  - Prefix₁ has (y - a₁) North steps, suffix₂ has (n₂ - (y - a₂)) North steps
  - Total: n₂ + a₂ - a₁ = n₁' ✓
-/

/-- Position after the first i steps of path l starting at (0, a).
    Returns (x-coordinate, y-coordinate) = (#East steps taken, a + #North steps taken). -/
def posAfter (l : LPath) (a i : ℕ) : ℕ × ℕ :=
  ((l.take i).countP (· = false), a + (l.take i).countP (· = true))

theorem posAfter_zero (l : LPath) (a : ℕ) : posAfter l a 0 = (0, a) := by
  simp [posAfter]

theorem posAfter_length (l : LPath) (a : ℕ) :
    posAfter l a l.length = (eastSteps l, a + northSteps l) := by
  simp [posAfter, eastSteps, northSteps, List.take_length]

/-- posAfter with i > l.length is the same as posAfter at l.length -/
theorem posAfter_ge_length (l : LPath) (a i : ℕ) (hi : l.length ≤ i) :
    posAfter l a i = posAfter l a l.length := by
  simp [posAfter, List.take_of_length_le hi, List.take_length]

/-- The x-coordinate (first component) of posAfter -/
theorem posAfter_fst (l : LPath) (a i : ℕ) :
    (posAfter l a i).1 = (l.take i).countP (· = false) := rfl

/-- The y-coordinate (second component) of posAfter -/
theorem posAfter_snd (l : LPath) (a i : ℕ) :
    (posAfter l a i).2 = a + (l.take i).countP (· = true) := rfl

/-- East step count of a prefix equals the x-coordinate -/
theorem take_east_eq_posAfter_fst (l : LPath) (a i : ℕ) :
    (l.take i).countP (· = false) = (posAfter l a i).1 := rfl

/-- North step count of a prefix equals y-coordinate minus start -/
theorem take_north_eq_posAfter_snd_sub (l : LPath) (a i : ℕ) :
    (l.take i).countP (· = true) = (posAfter l a i).2 - a := by
  simp [posAfter]

/-- posAfter through a false (East) cons: shifts x by 1, preserves y -/
theorem posAfter_cons_false (xs : LPath) (a : ℕ) (i : ℕ) :
    posAfter (false :: xs) a (i + 1) =
    ((posAfter xs a i).1 + 1, (posAfter xs a i).2) := by
  simp [posAfter, List.take_cons, List.countP_cons]

/-- posAfter through a true (North) cons: preserves x, shifts start by 1 -/
theorem posAfter_cons_true (xs : LPath) (a : ℕ) (i : ℕ) :
    posAfter (true :: xs) a (i + 1) = posAfter xs (a + 1) i := by
  simp [posAfter, List.take_cons, List.countP_cons]; omega

/-- colEntry for false :: xs: column 0 maps to 0, column k+1 maps to colEntry xs k -/
theorem colEntry_cons_false (xs : LPath) (k : ℕ) :
    colEntry (false :: xs) (k + 1) = colEntry xs k := by
  cases k with
  | zero => simp [colEntry, northBeforeEast]
  | succ k => simp [colEntry, northBeforeEast]

/-- colEntry for true :: xs: column 0 maps to 0, column k+1 maps to 1 + colEntry xs (k+1) -/
theorem colEntry_cons_true (xs : LPath) (k : ℕ) :
    colEntry (true :: xs) (k + 1) = 1 + colEntry xs (k + 1) := by
  simp [colEntry, northBeforeEast]

/-- The set of lattice points visited by path l starting at (0, a) -/
def visitedPoints (l : LPath) (a : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (l.length + 1)).image (posAfter l a)

/-- Path l visits its starting point -/
theorem mem_visitedPoints_start (l : LPath) (a : ℕ) :
    (0, a) ∈ visitedPoints l a := by
  rw [← posAfter_zero l a]
  exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))

/-- If (x, y) ∈ visitedPoints xs a, then (x+1, y) ∈ visitedPoints (false :: xs) a -/
theorem mem_visitedPoints_cons_false {xs : LPath} {a x y : ℕ}
    (h : (x, y) ∈ visitedPoints xs a) :
    (x + 1, y) ∈ visitedPoints (false :: xs) a := by
  rw [visitedPoints, Finset.mem_image] at h ⊢
  obtain ⟨i, hi, hpos⟩ := h
  exact ⟨i + 1, Finset.mem_range.mpr (by simp [List.length_cons]; omega),
    by rw [posAfter_cons_false]; rw [← hpos]⟩

/-- If (x, y) ∈ visitedPoints xs (a+1), then (x, y) ∈ visitedPoints (true :: xs) a -/
theorem mem_visitedPoints_cons_true {xs : LPath} {a x y : ℕ}
    (h : (x, y) ∈ visitedPoints xs (a + 1)) :
    (x, y) ∈ visitedPoints (true :: xs) a := by
  rw [visitedPoints, Finset.mem_image] at h ⊢
  obtain ⟨i, hi, hpos⟩ := h
  exact ⟨i + 1, Finset.mem_range.mpr (by simp [List.length_cons]; omega),
    by rw [posAfter_cons_true]; exact hpos⟩

/-- Path l visits its endpoint -/
theorem mem_visitedPoints_end (l : LPath) (a : ℕ) :
    (eastSteps l, a + northSteps l) ∈ visitedPoints l a := by
  rw [← posAfter_length]
  exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))

/-- A path visits all integer y-values in its column range.
    Within column x, the path visits (x, a + colEntry l x + δ) for all
    0 ≤ δ ≤ colEntry l (x+1) - colEntry l x. -/
theorem visitedPoints_covers_column (l : LPath) (a : ℕ) (x y : ℕ)
    (hx : x < eastSteps l)
    (hy_lo : a + colEntry l x ≤ y) (hy_hi : y ≤ a + colEntry l (x + 1)) :
    (x, y) ∈ visitedPoints l a := by
  induction l generalizing a x y with
  | nil => simp [eastSteps] at hx
  | cons b xs ih =>
    cases b with
    | false =>
      cases x with
      | zero =>
        -- Column 0 with East first: colEntry 0 = 0, colEntry 1 = 0, so y = a
        have : colEntry (false :: xs) 1 = 0 := by simp [colEntry, northBeforeEast]
        have : y = a := by omega
        subst this; exact mem_visitedPoints_start _ _
      | succ k =>
        -- Shift from xs column k to (false :: xs) column k+1
        have hk : k < eastSteps xs := by
          simp [eastSteps, List.countP_cons] at hx; omega
        have hlo : a + colEntry xs k ≤ y := by
          rw [colEntry_cons_false] at hy_lo; exact hy_lo
        have hhi : y ≤ a + colEntry xs (k + 1) := by
          rw [colEntry_cons_false] at hy_hi; exact hy_hi
        exact mem_visitedPoints_cons_false (ih a k y hk hlo hhi)
    | true =>
      -- North step first: posAfter (true :: xs) a (i+1) = posAfter xs (a+1) i
      by_cases hy : y = a
      · -- y = a only possible at column 0 (via start point)
        subst hy; exact mem_visitedPoints_start _ _
      · -- y > a: use IH with xs and start a+1
        have hya : a < y := by omega
        have hx' : x < eastSteps xs := by
          simp [eastSteps, List.countP_cons] at hx; exact hx
        have hlo : (a + 1) + colEntry xs x ≤ y := by
          cases x with
          | zero => simp [colEntry]; omega
          | succ k => rw [colEntry_cons_true] at hy_lo; omega
        have hhi : y ≤ (a + 1) + colEntry xs (x + 1) := by
          rw [colEntry_cons_true] at hy_hi; omega
        exact mem_visitedPoints_cons_true (ih (a + 1) x y hx' hlo hhi)

/-- A path visits all integer y-values in its final range (after all East steps). -/
theorem visitedPoints_covers_final (l : LPath) (a : ℕ) (y : ℕ)
    (hy_lo : a + colEntry l (eastSteps l) ≤ y) (hy_hi : y ≤ a + northSteps l) :
    (eastSteps l, y) ∈ visitedPoints l a := by
  induction l generalizing a y with
  | nil =>
    simp [eastSteps, colEntry, northSteps] at hy_lo hy_hi ⊢
    have : y = a := by omega
    subst this; exact mem_visitedPoints_start _ _
  | cons b xs ih =>
    cases b with
    | false =>
      -- East step first: eastSteps = 1 + eastSteps xs, northSteps unchanged
      have hns : northSteps (false :: xs) = northSteps xs := by
        simp [northSteps, List.countP_cons]
      have hes : eastSteps (false :: xs) = eastSteps xs + 1 := by
        simp [eastSteps, List.countP_cons]
      have hlo' : a + colEntry xs (eastSteps xs) ≤ y := by
        rw [hes] at hy_lo
        rw [colEntry_cons_false] at hy_lo
        exact hy_lo
      have hhi' : y ≤ a + northSteps xs := by rw [hns] at hy_hi; exact hy_hi
      rw [hes]
      exact mem_visitedPoints_cons_false (ih a y hlo' hhi')
    | true =>
      -- North step first: eastSteps unchanged, northSteps = 1 + northSteps xs
      have hns : northSteps (true :: xs) = 1 + northSteps xs := by
        simp [northSteps, List.countP_cons]; omega
      have hes : eastSteps (true :: xs) = eastSteps xs := by
        simp [eastSteps, List.countP_cons]
      by_cases hy : y = a
      · subst hy; exact mem_visitedPoints_start _ _
      · have hlo' : (a + 1) + colEntry xs (eastSteps xs) ≤ y := by
          rw [hes] at hy_lo
          cases heq : eastSteps xs with
          | zero => simp [colEntry] at hy_lo ⊢; omega
          | succ k => rw [colEntry_cons_true] at hy_lo; omega
        have hhi' : y ≤ (a + 1) + northSteps xs := by rw [hns] at hy_hi; omega
        rw [hes]
        exact mem_visitedPoints_cons_true (ih (a + 1) y hlo' hhi')

/-- The shared lattice points between two paths -/
def sharedPoints (l₁ l₂ : LPath) (a₁ a₂ : ℕ) : Finset (ℕ × ℕ) :=
  visitedPoints l₁ a₁ ∩ visitedPoints l₂ a₂

/-- If column ranges overlap, the shared points are nonempty -/
theorem sharedPoints_nonempty_of_columnsOverlap
    {l₁ l₂ : LPath} {a₁ a₂ x : ℕ}
    (hx₁ : x < eastSteps l₁) (hx₂ : x < eastSteps l₂)
    (h : columnsOverlap l₁ l₂ a₁ a₂ x) :
    (sharedPoints l₁ l₂ a₁ a₂).Nonempty := by
  obtain ⟨h₁₂, h₂₁⟩ := h
  -- The shared y is max(a₁ + colEntry l₁ x, a₂ + colEntry l₂ x)
  have mono₁ := colEntry_mono l₁ x
  have mono₂ := colEntry_mono l₂ x
  set y := max (a₁ + colEntry l₁ x) (a₂ + colEntry l₂ x) with hy_def
  have hy₁_lo : a₁ + colEntry l₁ x ≤ y := le_max_left _ _
  have hy₁_hi : y ≤ a₁ + colEntry l₁ (x + 1) := max_le (by omega) h₂₁
  have hy₂_lo : a₂ + colEntry l₂ x ≤ y := le_max_right _ _
  have hy₂_hi : y ≤ a₂ + colEntry l₂ (x + 1) := max_le h₁₂ (by omega)
  exact ⟨(x, y), Finset.mem_inter.mpr ⟨
    visitedPoints_covers_column l₁ a₁ x y hx₁ hy₁_lo hy₁_hi,
    visitedPoints_covers_column l₂ a₂ x y hx₂ hy₂_lo hy₂_hi⟩⟩

/-- If final ranges overlap, the shared points are nonempty -/
theorem sharedPoints_nonempty_of_finalOverlap
    {l₁ l₂ : LPath} {a₁ a₂ : ℕ} {y : ℕ}
    (hy₁ : y ∈ finalRange l₁ a₁ (eastSteps l₁))
    (hy₂ : y ∈ finalRange l₂ a₂ (eastSteps l₂))
    (heast : eastSteps l₁ = eastSteps l₂) :
    (sharedPoints l₁ l₂ a₁ a₂).Nonempty := by
  have h₁ := hy₁; have h₂ := hy₂
  simp only [finalRange, Set.mem_setOf_eq] at h₁ h₂
  -- y is visited by both paths (in the final column range → last column)
  exact ⟨(eastSteps l₁, y), Finset.mem_inter.mpr ⟨
    visitedPoints_covers_final l₁ a₁ y h₁.1 h₁.2,
    heast ▸ visitedPoints_covers_final l₂ a₂ y h₂.1 h₂.2⟩⟩

/-- Not non-intersecting paths with same East count share a lattice point -/
theorem sharedPoints_nonempty_of_not_ni {l₁ l₂ : LPath} {m a₁ a₂ : ℕ}
    (heast₁ : eastSteps l₁ = m) (heast₂ : eastSteps l₂ = m)
    (h : ¬NonIntersecting l₁ l₂ m a₁ a₂) :
    (sharedPoints l₁ l₂ a₁ a₂).Nonempty := by
  rcases not_ni_implies_overlap_or_final h with ⟨x, hxm, hoverlap⟩ | ⟨y, hy₁, hy₂⟩
  · exact sharedPoints_nonempty_of_columnsOverlap
      (by omega) (by omega) hoverlap
  · -- Final range overlap: need eastSteps = m for both
    rw [← heast₁] at hy₁
    rw [← heast₂] at hy₂
    exact sharedPoints_nonempty_of_finalOverlap hy₁ hy₂ (by omega)

/- ### Step Index Recovery

Given that point p is visited by path l, recover the step index. -/

/-- Find the step index where path l starting at a visits point p.
    Uses Exists.choose to pick a witness. -/
noncomputable def stepIndexOf (l : LPath) (a : ℕ) (p : ℕ × ℕ)
    (h : p ∈ visitedPoints l a) : ℕ :=
  (by simp [visitedPoints, Finset.mem_image, Finset.mem_range] at h; exact h :
    ∃ i, i < l.length + 1 ∧ posAfter l a i = p).choose

theorem stepIndexOf_spec (l : LPath) (a : ℕ) (p : ℕ × ℕ)
    (h : p ∈ visitedPoints l a) :
    posAfter l a (stepIndexOf l a p h) = p ∧ stepIndexOf l a p h < l.length + 1 := by
  have h_exists : ∃ i, i < l.length + 1 ∧ posAfter l a i = p := by
    simp [visitedPoints, Finset.mem_image, Finset.mem_range] at h; exact h
  have := h_exists.choose_spec
  exact ⟨this.2, this.1⟩

theorem stepIndexOf_le_length (l : LPath) (a : ℕ) (p : ℕ × ℕ)
    (h : p ∈ visitedPoints l a) :
    stepIndexOf l a p h ≤ l.length := by
  have := (stepIndexOf_spec l a p h).2; omega

/-- The east step count of the prefix equals the x-coordinate of the point -/
theorem take_east_at_stepIndex (l : LPath) (a : ℕ) (p : ℕ × ℕ)
    (h : p ∈ visitedPoints l a) :
    (l.take (stepIndexOf l a p h)).countP (· = false) = p.1 := by
  have hs := (stepIndexOf_spec l a p h).1
  simp only [posAfter] at hs
  exact (Prod.mk.inj hs).1

/-- The north step count of the prefix equals y - a -/
theorem take_north_at_stepIndex (l : LPath) (a : ℕ) (p : ℕ × ℕ)
    (h : p ∈ visitedPoints l a) :
    (l.take (stepIndexOf l a p h)).countP (· = true) = p.2 - a := by
  have hs := (stepIndexOf_spec l a p h).1
  simp only [posAfter] at hs
  have := (Prod.mk.inj hs).2; omega

/- ### The Lindström Swap at a Shared Point

Given a shared point p visited by both paths, split each at their
respective step indices and swap suffixes. -/

/-- Split path l at step index i into prefix (take) and suffix (drop) -/
theorem take_drop_countP_sum (l : LPath) (i : ℕ) (p : Bool → Prop) [DecidablePred p] :
    (l.take i).countP p + (l.drop i).countP p = l.countP p := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.countP_append]

/-- Swap suffixes of two paths at a shared point -/
noncomputable def lindstromSwapAt (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (p : ℕ × ℕ) (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂) :
    LPath × LPath :=
  let i := stepIndexOf l₁ a₁ p h₁
  let j := stepIndexOf l₂ a₂ p h₂
  (l₁.take i ++ l₂.drop j, l₂.take j ++ l₁.drop i)

/-- East step count of the first swapped path equals m -/
theorem lindstromSwapAt_fst_east (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (p : ℕ × ℕ) (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (heast₁ : eastSteps l₁ = m) (heast₂ : eastSteps l₂ = m) :
    eastSteps (lindstromSwapAt l₁ l₂ a₁ a₂ p h₁ h₂).1 = m := by
  simp only [lindstromSwapAt, eastSteps, List.countP_append]
  have h_take₁ := take_east_at_stepIndex l₁ a₁ p h₁
  have h_take₂ := take_east_at_stepIndex l₂ a₂ p h₂
  have h_sum₂ := take_drop_countP_sum l₂ (stepIndexOf l₂ a₂ p h₂) (· = false)
  simp only [eastSteps] at heast₂
  omega

/-- East step count of the second swapped path equals m -/
theorem lindstromSwapAt_snd_east (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (p : ℕ × ℕ) (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (heast₁ : eastSteps l₁ = m) (heast₂ : eastSteps l₂ = m) :
    eastSteps (lindstromSwapAt l₁ l₂ a₁ a₂ p h₁ h₂).2 = m := by
  simp only [lindstromSwapAt, eastSteps, List.countP_append]
  have h_take₁ := take_east_at_stepIndex l₁ a₁ p h₁
  have h_take₂ := take_east_at_stepIndex l₂ a₂ p h₂
  have h_sum₁ := take_drop_countP_sum l₁ (stepIndexOf l₁ a₁ p h₁) (· = false)
  simp only [eastSteps] at heast₁
  omega

/-- **KEY**: North step count of first swapped path = n₂ + a₂ - a₁.
    This is because at the shared point (x, y):
    - prefix₁ has (y - a₁) North steps
    - suffix₂ has (n₂ - (y - a₂)) North steps
    - Total: n₂ + a₂ - a₁ = n₁' -/
theorem lindstromSwapAt_fst_north (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (p : ℕ × ℕ) (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (ha : a₁ ≤ p.2) (ha₂ : a₂ ≤ p.2) (h_a_le : a₁ ≤ a₂) :
    northSteps (lindstromSwapAt l₁ l₂ a₁ a₂ p h₁ h₂).1 =
    northSteps l₂ + (a₂ - a₁) := by
  simp only [lindstromSwapAt, northSteps, List.countP_append]
  have h_n₁ := take_north_at_stepIndex l₁ a₁ p h₁
  have h_n₂ := take_north_at_stepIndex l₂ a₂ p h₂
  have h_sum₂ := take_drop_countP_sum l₂ (stepIndexOf l₂ a₂ p h₂) (· = true)
  simp only [northSteps] at *
  omega

/-- North step count of second swapped path = n₁ + a₁ - a₂ -/
theorem lindstromSwapAt_snd_north (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (p : ℕ × ℕ) (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (ha : a₁ ≤ p.2) (ha₂ : a₂ ≤ p.2) (h_a_le : a₂ ≤ a₁) :
    northSteps (lindstromSwapAt l₁ l₂ a₁ a₂ p h₁ h₂).2 =
    northSteps l₁ + (a₁ - a₂) := by
  simp only [lindstromSwapAt, northSteps, List.countP_append]
  have h_n₁ := take_north_at_stepIndex l₁ a₁ p h₁
  have h_n₂ := take_north_at_stepIndex l₂ a₂ p h₂
  have h_sum₁ := take_drop_countP_sum l₁ (stepIndexOf l₁ a₁ p h₁) (· = true)
  simp only [northSteps] at *
  omega

/-- Length of first swapped path -/
theorem lindstromSwapAt_fst_length (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (p : ℕ × ℕ) (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (ha : a₁ ≤ p.2) (ha₂ : a₂ ≤ p.2)
    (hlen₁ : l₁.length = m + n₁) (hlen₂ : l₂.length = m + n₂)
    (heast₁ : eastSteps l₁ = m) (heast₂ : eastSteps l₂ = m) :
    (lindstromSwapAt l₁ l₂ a₁ a₂ p h₁ h₂).1.length = m + (n₂ + (a₂ - a₁)) := by
  simp only [lindstromSwapAt, List.length_append]
  have hi := stepIndexOf_le_length l₁ a₁ p h₁
  have hj := stepIndexOf_le_length l₂ a₂ p h₂
  -- take i has length min(i, l₁.length) = i (since i ≤ l₁.length)
  rw [List.length_take, List.length_drop, min_eq_left hi, hlen₂]
  -- i = p.1 + (p.2 - a₁), j = p.1 + (p.2 - a₂)
  have h_n₁ := take_north_at_stepIndex l₁ a₁ p h₁
  have h_e₁ := take_east_at_stepIndex l₁ a₁ p h₁
  have h_n₂ := take_north_at_stepIndex l₂ a₂ p h₂
  have h_e₂ := take_east_at_stepIndex l₂ a₂ p h₂
  -- stepIndexOf l a p = (l.take i).length = countP false + countP true
  have hi_eq : stepIndexOf l₁ a₁ p h₁ = p.1 + (p.2 - a₁) := by
    have := bool_list_countP_sum (l₁.take (stepIndexOf l₁ a₁ p h₁))
    rw [List.length_take, min_eq_left hi] at this
    omega
  have hj_eq : stepIndexOf l₂ a₂ p h₂ = p.1 + (p.2 - a₂) := by
    have := bool_list_countP_sum (l₂.take (stepIndexOf l₂ a₂ p h₂))
    rw [List.length_take, min_eq_left hj] at this
    omega
  rw [hi_eq, hj_eq]; omega

/- ### Computable Swap and Involutivity

The step index where path l from (0, a) reaches (x, y) is x + (y - a).
Using this deterministic index makes involutivity straightforward. -/

/-- Step index: path from (0, a) reaches (x, y) at step x + (y - a) -/
def splitIdx (a : ℕ) (p : ℕ × ℕ) : ℕ := p.1 + (p.2 - a)

/-- Swap suffixes at a given lattice point (computable) -/
def swapAtPoint (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ) : LPath × LPath :=
  (l₁.take (splitIdx a₁ p) ++ l₂.drop (splitIdx a₂ p),
   l₂.take (splitIdx a₂ p) ++ l₁.drop (splitIdx a₁ p))

/-- **Involutivity**: swapping twice at the same point restores the original -/
theorem swapAtPoint_involutive (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (hi : splitIdx a₁ p ≤ l₁.length) (hj : splitIdx a₂ p ≤ l₂.length) :
    swapAtPoint (swapAtPoint l₁ l₂ a₁ a₂ p).1 (swapAtPoint l₁ l₂ a₁ a₂ p).2 a₁ a₂ p =
    (l₁, l₂) := by
  simp only [swapAtPoint]
  set i := splitIdx a₁ p
  set j := splitIdx a₂ p
  have hli : (l₁.take i).length = i := by rw [List.length_take]; omega
  have hlj : (l₂.take j).length = j := by rw [List.length_take]; omega
  -- (l₁.take i ++ l₂.drop j).take i = l₁.take i
  have h1 : (l₁.take i ++ l₂.drop j).take i = l₁.take i := by
    rw [← hli]; exact List.take_left
  -- (l₁.take i ++ l₂.drop j).drop i = l₂.drop j
  have h2 : List.drop i (l₁.take i ++ l₂.drop j) = l₂.drop j := by
    rw [← hli]; exact List.drop_left
  -- (l₂.take j ++ l₁.drop i).take j = l₂.take j
  have h3 : (l₂.take j ++ l₁.drop i).take j = l₂.take j := by
    rw [← hlj]; exact List.take_left
  -- (l₂.take j ++ l₁.drop i).drop j = l₁.drop i
  have h4 : List.drop j (l₂.take j ++ l₁.drop i) = l₁.drop i := by
    rw [← hlj]; exact List.drop_left
  rw [h1, h4, h3, h2]
  exact ⟨List.take_append_drop i l₁, List.take_append_drop j l₂⟩

/-- East step count of first swapped path -/
theorem swapAtPoint_fst_east (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (heast₁ : eastSteps l₁ = m) (heast₂ : eastSteps l₂ = m) :
    (swapAtPoint l₁ l₂ a₁ a₂ p).1.countP (· = false) = m := by
  simp only [swapAtPoint, List.countP_append]
  -- p ∈ visitedPoints l a means ∃ i, posAfter l a i = p ∧ i ≤ l.length
  -- At step splitIdx a p, the prefix has p.1 East steps
  simp [visitedPoints, Finset.mem_image, Finset.mem_range] at h₁ h₂
  obtain ⟨i₁, hi₁_bound, hi₁_eq⟩ := h₁
  obtain ⟨i₂, hi₂_bound, hi₂_eq⟩ := h₂
  -- posAfter l a i gives (countP false in take i, a + countP true in take i)
  simp [posAfter] at hi₁_eq hi₂_eq
  -- The prefix l₁.take (splitIdx a₁ p) has p.1 East steps
  -- The suffix l₂.drop (splitIdx a₂ p) has (m - p.1) East steps
  -- Total: m
  have h_take₁ : (l₁.take i₁).countP (· = false) = p.1 := hi₁_eq.1
  have h_take₂ : (l₂.take i₂).countP (· = false) = p.1 := hi₂_eq.1
  have h_sum₂ := take_drop_countP_sum l₂ i₂ (· = false)
  -- splitIdx a₁ p = i₁ because i₁ = p.1 + (p.2 - a₁) = splitIdx a₁ p
  have h_idx₁ : i₁ = splitIdx a₁ p := by
    have : (l₁.take i₁).length = i₁ := by rw [List.length_take]; omega
    have hsum := bool_list_countP_sum (l₁.take i₁)
    rw [this] at hsum; simp [splitIdx]; omega
  have h_idx₂ : i₂ = splitIdx a₂ p := by
    have : (l₂.take i₂).length = i₂ := by rw [List.length_take]; omega
    have hsum := bool_list_countP_sum (l₂.take i₂)
    rw [this] at hsum; simp [splitIdx]; omega
  rw [← h_idx₁, ← h_idx₂, h_take₁]
  simp only [eastSteps] at heast₂; omega

/-- East step count of second swapped path -/
theorem swapAtPoint_snd_east (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (heast₁ : eastSteps l₁ = m) (heast₂ : eastSteps l₂ = m) :
    (swapAtPoint l₁ l₂ a₁ a₂ p).2.countP (· = false) = m := by
  -- Symmetric to fst case: swap roles of l₁ and l₂
  have := swapAtPoint_fst_east l₂ l₁ a₂ a₁ p h₂ h₁ heast₂ heast₁
  convert this using 1
  simp [swapAtPoint]

/-- **KEY**: North step count of first swapped path = n₂ + (a₂ - a₁) -/
theorem swapAtPoint_fst_north (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (ha₁ : a₁ ≤ p.2) (ha₂ : a₂ ≤ p.2) :
    (swapAtPoint l₁ l₂ a₁ a₂ p).1.countP (· = true) =
    l₂.countP (· = true) + (a₂ - a₁) := by
  simp only [swapAtPoint, List.countP_append]
  simp [visitedPoints, Finset.mem_image, Finset.mem_range] at h₁ h₂
  obtain ⟨i₁, hi₁_bound, hi₁_eq⟩ := h₁
  obtain ⟨i₂, hi₂_bound, hi₂_eq⟩ := h₂
  simp [posAfter] at hi₁_eq hi₂_eq
  have h_idx₁ : i₁ = splitIdx a₁ p := by
    have : (l₁.take i₁).length = i₁ := by rw [List.length_take]; omega
    have hsum := bool_list_countP_sum (l₁.take i₁)
    rw [this] at hsum; simp [splitIdx]; omega
  have h_idx₂ : i₂ = splitIdx a₂ p := by
    have : (l₂.take i₂).length = i₂ := by rw [List.length_take]; omega
    have hsum := bool_list_countP_sum (l₂.take i₂)
    rw [this] at hsum; simp [splitIdx]; omega
  rw [← h_idx₁, ← h_idx₂]
  have h_sum₂ := take_drop_countP_sum l₂ i₂ (· = true)
  omega

/-- North step count of second swapped path = n₁ + (a₁ - a₂) -/
theorem swapAtPoint_snd_north (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (ha₁ : a₁ ≤ p.2) (ha₂ : a₂ ≤ p.2) :
    (swapAtPoint l₁ l₂ a₁ a₂ p).2.countP (· = true) =
    l₁.countP (· = true) + (a₁ - a₂) := by
  have := swapAtPoint_fst_north l₂ l₁ a₂ a₁ p h₂ h₁ ha₂ ha₁
  convert this using 1
  simp [swapAtPoint]

/-- Length of first swapped path -/
theorem swapAtPoint_fst_length (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂) :
    (swapAtPoint l₁ l₂ a₁ a₂ p).1.length =
    l₁.take (splitIdx a₁ p) |>.length + l₂.drop (splitIdx a₂ p) |>.length := by
  simp [swapAtPoint, List.length_append]

/-- **Bridge Lemma**: If the first i steps of path l have exactly x East steps,
    the North step count satisfies: colEntry l x ≤ northCount ≤ colEntry l (x+1)
    (for x < eastSteps l), or colEntry l x ≤ northCount ≤ northSteps l (for x = eastSteps l). -/
theorem prefix_north_bounds (l : LPath) (i : ℕ) (hi : i ≤ l.length)
    (x : ℕ) (hx : (l.take i).countP (· = false) = x) :
    colEntry l x ≤ (l.take i).countP (· = true) := by
  induction l generalizing i x with
  | nil => simp [colEntry] at *; omega
  | cons b bs ih =>
    cases b with
    | false =>
      cases i with
      | zero => simp at hx; subst hx; simp [colEntry]
      | succ i =>
        simp [List.take_succ_cons, List.countP_cons] at hx ⊢
        have hi' : i ≤ bs.length := by simp at hi; omega
        cases x with
        | zero => omega  -- impossible: first step is false so countP ≥ 1
        | succ x =>
          have hx' : (bs.take i).countP (· = false) = x := by omega
          rw [colEntry_false_succ]
          exact ih i hi' x hx'
    | true =>
      cases i with
      | zero => simp at hx; subst hx; simp [colEntry]
      | succ i =>
        simp [List.take_succ_cons, List.countP_cons] at hx ⊢
        have hi' : i ≤ bs.length := by simp at hi; omega
        have hx' : (bs.take i).countP (· = false) = x := hx
        cases x with
        | zero =>
          simp [colEntry]
          have := ih i hi' 0 hx'
          simp [colEntry] at this; omega
        | succ x =>
          rw [colEntry_true_succ]
          have := ih i hi' (x + 1) hx'
          omega

theorem prefix_north_upper (l : LPath) (i : ℕ) (hi : i ≤ l.length)
    (x : ℕ) (hx : (l.take i).countP (· = false) = x) (hxm : x < eastSteps l) :
    (l.take i).countP (· = true) ≤ colEntry l (x + 1) := by
  induction l generalizing i x with
  | nil => simp [eastSteps] at hxm
  | cons b bs ih =>
    cases b with
    | false =>
      cases i with
      | zero => simp at hx; subst hx; simp [colEntry, northBeforeEast]
      | succ i =>
        simp [List.take_succ_cons, List.countP_cons] at hx ⊢
        have hi' : i ≤ bs.length := by simp at hi; omega
        cases x with
        | zero => omega  -- impossible: countP false ≥ 1
        | succ x =>
          have hx' : (bs.take i).countP (· = false) = x := by omega
          have hxm' : x < eastSteps bs := by simp [eastSteps, List.countP_cons] at hxm; omega
          rw [colEntry_false_succ]
          exact ih i hi' x hx' hxm'
    | true =>
      cases i with
      | zero =>
        simp at hx; subst hx
        simp [colEntry, northBeforeEast]; omega
      | succ i =>
        simp [List.take_succ_cons, List.countP_cons] at hx ⊢
        have hi' : i ≤ bs.length := by simp at hi; omega
        have hxm' : x < eastSteps bs := by simp [eastSteps, List.countP_cons] at hxm; exact hxm
        rw [colEntry_true_succ]
        have := ih i hi' x hx hxm'
        omega

/-- A visited point (x, y) with x < m lies in both paths' column y-ranges.
    Combined with NI (which says column ranges are disjoint), this gives a contradiction. -/
theorem visited_in_colYRange (l : LPath) (a : ℕ) (x y : ℕ)
    (hvisited : (x, y) ∈ visitedPoints l a) (hx : x < eastSteps l) :
    y ∈ colYRange l a x := by
  simp [visitedPoints, Finset.mem_image, Finset.mem_range] at hvisited
  obtain ⟨i, hi_bound, hi_eq⟩ := hvisited
  simp [posAfter] at hi_eq
  have hi' : i ≤ l.length := by omega
  have hxe : (l.take i).countP (· = false) = x := hi_eq.1
  constructor
  · -- a + colEntry l x ≤ y
    have := prefix_north_bounds l i hi' x hxe
    omega
  · -- y ≤ a + colEntry l (x + 1)
    have := prefix_north_upper l i hi' x hxe hx
    omega

/-- A visited point (m, y) lies in the final range -/
theorem visited_in_finalRange (l : LPath) (a : ℕ) (y : ℕ)
    (hvisited : (eastSteps l, y) ∈ visitedPoints l a) :
    y ∈ finalRange l a (eastSteps l) := by
  simp [visitedPoints, Finset.mem_image, Finset.mem_range] at hvisited
  obtain ⟨i, hi_bound, hi_eq⟩ := hvisited
  simp [posAfter] at hi_eq
  have hi' : i ≤ l.length := by omega
  have hxe : (l.take i).countP (· = false) = eastSteps l := hi_eq.1
  constructor
  · -- a + colEntry l m ≤ y
    have := prefix_north_bounds l i hi' (eastSteps l) hxe
    omega
  · -- y ≤ a + northSteps l
    have h_sum := take_drop_countP_sum l i (· = true)
    simp [northSteps]; omega

/-- Shared visited point implies NOT non-intersecting -/
theorem not_ni_of_shared_point {l₁ l₂ : LPath} {a₁ a₂ : ℕ} (p : ℕ × ℕ)
    (hp₁ : p ∈ visitedPoints l₁ a₁) (hp₂ : p ∈ visitedPoints l₂ a₂)
    (heast₁ : eastSteps l₁ = m) (heast₂ : eastSteps l₂ = m) :
    ¬NonIntersecting l₁ l₂ m a₁ a₂ := by
  intro hni
  set x := p.1
  set y := p.2
  have hx₁ : x ≤ m := by
    simp [visitedPoints, Finset.mem_image, Finset.mem_range] at hp₁
    obtain ⟨i, hi, hieq⟩ := hp₁; simp [posAfter] at hieq
    have := take_drop_countP_sum l₁ i (· = false)
    simp only [eastSteps] at heast₁; omega
  by_cases hxm : x < m
  · -- Shared point in column x
    have h_in₁ := visited_in_colYRange l₁ a₁ x y hp₁ (by omega)
    have h_in₂ := visited_in_colYRange l₂ a₂ x y hp₂ (by omega)
    exact hni.1 x hxm y ⟨h_in₁, h_in₂⟩
  · -- Shared point in final column
    have hxm_eq : x = m := by omega
    have h_in₁ := visited_in_finalRange l₁ a₁ y (by rwa [heast₁, ← hxm_eq])
    have h_in₂ := visited_in_finalRange l₂ a₂ y (by rwa [heast₂, ← hxm_eq])
    rw [heast₁] at h_in₁; rw [heast₂] at h_in₂
    exact hni.2 y ⟨h_in₁, h_in₂⟩

/- ### The Lindström Involution Equiv -/

/-- Select the first shared point between two intersecting paths.
    Uses Classical.choice since we need a specific point from the nonempty Finset. -/
noncomputable def selectSharedPoint (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (h : (sharedPoints l₁ l₂ a₁ a₂).Nonempty) : ℕ × ℕ :=
  h.choose

theorem selectSharedPoint_mem₁ (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (h : (sharedPoints l₁ l₂ a₁ a₂).Nonempty) :
    selectSharedPoint l₁ l₂ a₁ a₂ h ∈ visitedPoints l₁ a₁ := by
  have := h.choose_spec
  simp [selectSharedPoint, sharedPoints, Finset.mem_inter] at this ⊢
  exact this.1

theorem selectSharedPoint_mem₂ (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (h : (sharedPoints l₁ l₂ a₁ a₂).Nonempty) :
    selectSharedPoint l₁ l₂ a₁ a₂ h ∈ visitedPoints l₂ a₂ := by
  have := h.choose_spec
  simp [selectSharedPoint, sharedPoints, Finset.mem_inter] at this ⊢
  exact this.2

/-- The shared point's y-coordinate is ≥ a₁ (since the path starts at y = a₁) -/
theorem shared_point_y_ge_a₁ (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ visitedPoints l₁ a₁) : a₁ ≤ p.2 := by
  simp [visitedPoints, Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨i, _, hi_eq⟩ := hp
  simp [posAfter] at hi_eq; omega

/-- The shared point's y-coordinate is ≥ a₂ -/
theorem shared_point_y_ge_a₂ (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ visitedPoints l₂ a₂) : a₂ ≤ p.2 := by
  simp [visitedPoints, Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨i, _, hi_eq⟩ := hp
  simp [posAfter] at hi_eq; omega

/-- splitIdx gives a step within bounds when the point is visited -/
theorem splitIdx_le_length (l : LPath) (a : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ visitedPoints l a) : splitIdx a p ≤ l.length := by
  simp [visitedPoints, Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨i, hi_bound, hi_eq⟩ := hp
  simp [posAfter] at hi_eq
  have : (l.take i).length = i := by rw [List.length_take]; omega
  have hsum := bool_list_countP_sum (l.take i)
  rw [this] at hsum
  simp [splitIdx]; omega

/- ### Part XX: Corrected North Step Formula and Path Forward -/

/-- **Corrected north step count** for second swapped path.
    `swapAtPoint_snd_north` gives `n₁ + (a₁ - a₂)` which truncates to `n₁` when `a₁ < a₂`.
    The correct formula is `(n₁ + a₁) - a₂` (ℕ subtraction with different grouping).
    Requires `a₂ ≤ a₁ + n₁` to avoid truncation, which holds whenever paths share a point. -/
theorem swapAtPoint_snd_north_corrected (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (ha₁ : a₁ ≤ p.2) (ha₂ : a₂ ≤ p.2)
    (h_reach : a₂ ≤ a₁ + l₁.countP (· = true)) :
    (swapAtPoint l₁ l₂ a₁ a₂ p).2.countP (· = true) =
    (l₁.countP (· = true) + a₁) - a₂ := by
  simp only [swapAtPoint, List.countP_append]
  have h₁' := h₁; have h₂' := h₂
  simp [visitedPoints, Finset.mem_image, Finset.mem_range] at h₁' h₂'
  obtain ⟨i₁, hi₁_bound, hi₁_eq⟩ := h₁'
  obtain ⟨i₂, hi₂_bound, hi₂_eq⟩ := h₂'
  simp only [posAfter] at hi₁_eq hi₂_eq
  have hi₁_eq' := Prod.mk.inj hi₁_eq
  have hi₂_eq' := Prod.mk.inj hi₂_eq
  have h_idx₁ : i₁ = splitIdx a₁ p := by
    have : (l₁.take i₁).length = i₁ := by rw [List.length_take]; omega
    have hsum := bool_list_countP_sum (l₁.take i₁)
    rw [this] at hsum; simp [splitIdx]; omega
  have h_idx₂ : i₂ = splitIdx a₂ p := by
    have : (l₂.take i₂).length = i₂ := by rw [List.length_take]; omega
    have hsum := bool_list_countP_sum (l₂.take i₂)
    rw [this] at hsum; simp [splitIdx]; omega
  rw [← h_idx₁, ← h_idx₂]
  have h_sum₁ := take_drop_countP_sum l₁ i₁ (· = true)
  have : (l₁.take i₁).countP (· = true) = p.2 - a₁ := by rw [hi₁_eq'.2]; omega
  omega

/-- The first swapped path visits the shared point p.
    Since swapAtPoint takes the prefix of l₁ up to p, the swapped path's
    prefix up to splitIdx a₁ p is exactly l₁'s prefix, which visits p. -/
theorem swapAtPoint_fst_visits_point (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (ha₁ : a₁ ≤ p.2) (ha₂ : a₂ ≤ p.2) :
    p ∈ visitedPoints (swapAtPoint l₁ l₂ a₁ a₂ p).1 a₁ := by
  have h₁_orig := h₁
  simp [visitedPoints, Finset.mem_image, Finset.mem_range] at h₁ ⊢
  obtain ⟨i₁, hi₁_bound, hi₁_eq⟩ := h₁
  have h_idx₁ : i₁ = splitIdx a₁ p := by
    simp only [posAfter] at hi₁_eq
    have hi := Prod.mk.inj hi₁_eq
    have : (l₁.take i₁).length = i₁ := by rw [List.length_take]; omega
    have hsum := bool_list_countP_sum (l₁.take i₁)
    rw [this] at hsum; simp [splitIdx]; omega
  set si₁ := splitIdx a₁ p
  refine ⟨si₁, ?_, ?_⟩
  · simp [swapAtPoint, List.length_append]
    have : si₁ ≤ l₁.length := splitIdx_le_length l₁ a₁ p h₁_orig
    omega
  · simp only [swapAtPoint, posAfter]
    have hlen : (l₁.take si₁).length = si₁ := by
      rw [List.length_take]
      exact Nat.min_eq_left (splitIdx_le_length l₁ a₁ p h₁_orig)
    have h_take_eq : (l₁.take si₁ ++ l₂.drop (splitIdx a₂ p)).take si₁ = l₁.take si₁ := by
      conv_lhs => rw [← hlen]
      exact List.take_left
    rw [h_take_eq, ← h_idx₁]
    exact hi₁_eq

/-- The second swapped path visits the shared point p (symmetric). -/
theorem swapAtPoint_snd_visits_point (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (ha₁ : a₁ ≤ p.2) (ha₂ : a₂ ≤ p.2) :
    p ∈ visitedPoints (swapAtPoint l₁ l₂ a₁ a₂ p).2 a₂ := by
  -- Symmetric: swapAtPoint.2 = l₂.take(si₂) ++ l₁.drop(si₁)
  have h₂_orig := h₂
  simp [visitedPoints, Finset.mem_image, Finset.mem_range] at h₂ ⊢
  obtain ⟨i₂, hi₂_bound, hi₂_eq⟩ := h₂
  have h_idx₂ : i₂ = splitIdx a₂ p := by
    have hi := Prod.mk.inj hi₂_eq
    have : (l₂.take i₂).length = i₂ := by rw [List.length_take]; omega
    have hsum := bool_list_countP_sum (l₂.take i₂)
    rw [this] at hsum; simp [splitIdx]; omega
  set si₂ := splitIdx a₂ p
  refine ⟨si₂, ?_, ?_⟩
  · simp [swapAtPoint, List.length_append]
    have : si₂ ≤ l₂.length := splitIdx_le_length l₂ a₂ p h₂_orig
    omega
  · simp only [swapAtPoint, posAfter]
    have hlen : (l₂.take si₂).length = si₂ := by
      rw [List.length_take]
      exact Nat.min_eq_left (splitIdx_le_length l₂ a₂ p h₂_orig)
    have h_take_eq : (l₂.take si₂ ++ l₁.drop (splitIdx a₁ p)).take si₂ = l₂.take si₂ := by
      conv_lhs => rw [← hlen]
      exact List.take_left
    rw [h_take_eq, ← h_idx₂]
    exact hi₂_eq

/-- **KEY**: Swapped paths are NOT non-intersecting.
    Both swapped paths visit the shared point p, so they share a lattice point. -/
theorem swapAtPoint_not_ni (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (h₁ : p ∈ visitedPoints l₁ a₁) (h₂ : p ∈ visitedPoints l₂ a₂)
    (ha₁ : a₁ ≤ p.2) (ha₂ : a₂ ≤ p.2)
    (heast₁ : eastSteps l₁ = m) (heast₂ : eastSteps l₂ = m) :
    ¬NonIntersecting (swapAtPoint l₁ l₂ a₁ a₂ p).1
      (swapAtPoint l₁ l₂ a₁ a₂ p).2 m a₁ a₂ := by
  have hv₁ := swapAtPoint_fst_visits_point l₁ l₂ a₁ a₂ p h₁ h₂ ha₁ ha₂
  have hv₂ := swapAtPoint_snd_visits_point l₁ l₂ a₁ a₂ p h₁ h₂ ha₁ ha₂
  have he₁ := swapAtPoint_fst_east l₁ l₂ a₁ a₂ p h₁ h₂ heast₁ heast₂
  have he₂ := swapAtPoint_snd_east l₁ l₂ a₁ a₂ p h₁ h₂ heast₁ heast₂
  exact not_ni_of_shared_point p hv₁ hv₂ he₁ he₂

/- ### Part XXI: Canonical Shared Point Selection

For the Lindström involution to be self-inverse, we need a CANONICAL choice of shared
point that is preserved by the swap. We use the minimum step index in path 1:
  minStepIdx = min { splitIdx a₁ p | p ∈ sharedPoints l₁ l₂ a₁ a₂ }

Key property: After swapping at the min-step-index shared point p, the prefixes
of both paths are unchanged (by definition of swapAtPoint). So any shared point
with step index < splitIdx a₁ p in the swapped paths is also shared by the
originals, contradicting minimality. Therefore p is also the min shared point
of the swapped paths, ensuring the involution is self-inverse. -/

/-- The minimum step index among all shared points -/
noncomputable def minSharedStepIdx (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (h : (sharedPoints l₁ l₂ a₁ a₂).Nonempty) : ℕ :=
  ((sharedPoints l₁ l₂ a₁ a₂).image (splitIdx a₁)).min'
    (Finset.Nonempty.image h _)

/-- There exists a shared point achieving the minimum step index -/
theorem minSharedStepIdx_achieved (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (h : (sharedPoints l₁ l₂ a₁ a₂).Nonempty) :
    ∃ p ∈ sharedPoints l₁ l₂ a₁ a₂,
      splitIdx a₁ p = minSharedStepIdx l₁ l₂ a₁ a₂ h := by
  have hmin := Finset.min'_mem ((sharedPoints l₁ l₂ a₁ a₂).image (splitIdx a₁))
    (Finset.Nonempty.image h _)
  simp [Finset.mem_image] at hmin
  exact hmin

/-- Select the canonical shared point (min by step index in path 1) -/
noncomputable def canonSharedPoint (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (h : (sharedPoints l₁ l₂ a₁ a₂).Nonempty) : ℕ × ℕ :=
  (minSharedStepIdx_achieved l₁ l₂ a₁ a₂ h).choose

theorem canonSharedPoint_mem (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (h : (sharedPoints l₁ l₂ a₁ a₂).Nonempty) :
    canonSharedPoint l₁ l₂ a₁ a₂ h ∈ sharedPoints l₁ l₂ a₁ a₂ :=
  (minSharedStepIdx_achieved l₁ l₂ a₁ a₂ h).choose_spec.1

theorem canonSharedPoint_mem₁ (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (h : (sharedPoints l₁ l₂ a₁ a₂).Nonempty) :
    canonSharedPoint l₁ l₂ a₁ a₂ h ∈ visitedPoints l₁ a₁ :=
  (Finset.mem_inter.mp (canonSharedPoint_mem l₁ l₂ a₁ a₂ h)).1

theorem canonSharedPoint_mem₂ (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (h : (sharedPoints l₁ l₂ a₁ a₂).Nonempty) :
    canonSharedPoint l₁ l₂ a₁ a₂ h ∈ visitedPoints l₂ a₂ :=
  (Finset.mem_inter.mp (canonSharedPoint_mem l₁ l₂ a₁ a₂ h)).2

theorem canonSharedPoint_isMin (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (h : (sharedPoints l₁ l₂ a₁ a₂).Nonempty)
    (q : ℕ × ℕ) (hq : q ∈ sharedPoints l₁ l₂ a₁ a₂) :
    splitIdx a₁ (canonSharedPoint l₁ l₂ a₁ a₂ h) ≤ splitIdx a₁ q := by
  have hmin := (minSharedStepIdx_achieved l₁ l₂ a₁ a₂ h).choose_spec.2
  rw [hmin]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)

/- ### Part XXII: Proving the Lindström Involution

The proof proceeds in two steps:
1. Define injections A → B and B → A using swapAtPoint at canonSharedPoint
2. Use `Nat.le_antisymm` with `Fintype.card_le_of_injective` to get equality

For the forward injection f : {intersecting identity} → {crossing}:
  Given (P₁, P₂) with ¬NI, swap at canonSharedPoint(P₁, P₂) → (Q₁, Q₂)
  East steps: m (preserved)
  North steps: n₂ + (a₂ - a₁) = n₁', and (n₁ + a₁) - a₂ = n₂'

For the backward injection g : {crossing} → {intersecting identity}:
  Given (Q₁, Q₂) : pathType m n₁' × pathType m n₂'
  By crossing lemma: Q₁ starts at a₁ < a₂, ends at a₁+n₁' = a₂+n₂ > a₂+n₂' = a₁+n₁
  So Q₁ starts lower, ends higher → they MUST intersect (¬NI)
  Swap at canonSharedPoint(Q₁, Q₂) → (P₁, P₂) with correct types

Both are injective because:
- f(P₁, P₂) determines the swap point and swapping twice = id
- Specifically: canonSharedPoint is preserved by swapAtPoint, so g(f(x)) = x -/

/-- **Crossing pairs are always intersecting** (when h_end holds).
    With a₁ < a₂ and a₂ + n₂' = a₁ + n₁ < a₂ + n₂ = a₁ + n₁', crossing paths
    satisfy the crossing lemma hypotheses: Q₁ starts lower, ends higher. -/
theorem crossing_always_intersecting (m n₁' n₂' a₁ a₂ : ℕ)
    (h_strict_a : a₁ < a₂)
    (h_cross_end : a₂ + n₂' < a₁ + n₁')
    (Q₁ : pathType m n₁') (Q₂ : pathType m n₂') :
    ¬NonIntersecting Q₁.val Q₂.val m a₁ a₂ := by
  have hm₁ : Q₁.val.countP (· = false) = m := Q₁.property.2
  have hn₁ : Q₁.val.countP (· = true) = n₁' := by
    have := eastSteps_add_northSteps Q₁.val
    simp only [eastSteps, northSteps] at this; omega
  have hm₂ : Q₂.val.countP (· = false) = m := Q₂.property.2
  have hn₂ : Q₂.val.countP (· = true) = n₂' := by
    have := eastSteps_add_northSteps Q₂.val
    simp only [eastSteps, northSteps] at this; omega
  exact crossing_lemma m n₁' n₂' a₁ a₂ hm₁ hn₁ hm₂ hn₂ h_strict_a h_cross_end

/-- The forward map: intersecting identity pair → crossing pair -/
noncomputable def lindstromForward (m n₁ n₂ n₁' n₂' a₁ a₂ : ℕ)
    (h_strict_a : a₁ < a₂)
    (h_end : a₁ + n₁ < a₂ + n₂)
    (h_n₁' : n₁' = n₂ + a₂ - a₁) (h_n₂' : n₂' = n₁ + a₁ - a₂)
    (h_n_sum : n₁ + n₂ = n₁' + n₂')
    (pair : {p : pathType m n₁ × pathType m n₂ //
      ¬NonIntersecting p.1.val p.2.val m a₁ a₂}) :
    pathType m n₁' × pathType m n₂' := by
  set P₁ := pair.val.1 with hP₁_def
  set P₂ := pair.val.2 with hP₂_def
  have h_ni := pair.property
  -- Find shared point
  have h_east₁ : eastSteps P₁.val = m := by have := P₁.property.2; simp_all [eastSteps]
  have h_east₂ : eastSteps P₂.val = m := by have := P₂.property.2; simp_all [eastSteps]
  have h_shared := sharedPoints_nonempty_of_not_ni h_east₁ h_east₂ h_ni
  set p := canonSharedPoint P₁.val P₂.val a₁ a₂ h_shared with hp_def
  have hp₁ := canonSharedPoint_mem₁ P₁.val P₂.val a₁ a₂ h_shared
  have hp₂ := canonSharedPoint_mem₂ P₁.val P₂.val a₁ a₂ h_shared
  have ha₁ := shared_point_y_ge_a₁ P₁.val P₂.val a₁ a₂ p hp₁
  have ha₂ := shared_point_y_ge_a₂ P₁.val P₂.val a₁ a₂ p hp₂
  -- Swap at shared point
  set result := swapAtPoint P₁.val P₂.val a₁ a₂ p
  -- First component has m East steps and n₁' North steps
  have hfst_east := swapAtPoint_fst_east P₁.val P₂.val a₁ a₂ p hp₁ hp₂ h_east₁ h_east₂
  have hfst_north := swapAtPoint_fst_north P₁.val P₂.val a₁ a₂ p hp₁ hp₂ ha₁ ha₂
  have hn₂_val : P₂.val.countP (· = true) = n₂ := by
    have := eastSteps_add_northSteps P₂.val
    simp only [eastSteps, northSteps] at this; omega
  have hfst_north_eq : result.1.countP (· = true) = n₁' := by
    rw [hfst_north, hn₂_val, h_n₁']
  have hfst_len : result.1.length = m + n₁' := by
    have := bool_list_countP_sum result.1; omega
  -- Second component has m East steps and n₂' North steps
  have hsnd_east := swapAtPoint_snd_east P₁.val P₂.val a₁ a₂ p hp₁ hp₂ h_east₁ h_east₂
  have hn₁_val : P₁.val.countP (· = true) = n₁ := by
    have := eastSteps_add_northSteps P₁.val
    simp only [eastSteps, northSteps] at this; omega
  -- For the second path: north = (n₁ + a₁) - a₂
  have h_reach : a₂ ≤ a₁ + P₁.val.countP (· = true) := by
    rw [hn₁_val]; omega
  have hsnd_north := swapAtPoint_snd_north_corrected P₁.val P₂.val a₁ a₂ p hp₁ hp₂ ha₁ ha₂ h_reach
  have hsnd_north_eq : result.2.countP (· = true) = n₂' := by
    rw [hsnd_north, hn₁_val, h_n₂']
  have hsnd_len : result.2.length = m + n₂' := by
    have := bool_list_countP_sum result.2; omega
  exact (⟨result.1, hfst_len, hfst_east⟩, ⟨result.2, hsnd_len, hsnd_east⟩)

/-- The backward map: crossing pair → intersecting identity pair -/
noncomputable def lindstromBackward (m n₁ n₂ n₁' n₂' a₁ a₂ : ℕ)
    (h_strict_a : a₁ < a₂)
    (h_end : a₁ + n₁ < a₂ + n₂)
    (h_n₁' : n₁' = n₂ + a₂ - a₁) (h_n₂' : n₂' = n₁ + a₁ - a₂)
    (h_n_sum : n₁ + n₂ = n₁' + n₂')
    (pair : pathType m n₁' × pathType m n₂') :
    {p : pathType m n₁ × pathType m n₂ //
      ¬NonIntersecting p.1.val p.2.val m a₁ a₂} := by
  set Q₁ := pair.1 with hQ₁_def
  set Q₂ := pair.2 with hQ₂_def
  -- Crossing pairs are always intersecting
  have h_cross_end : a₂ + n₂' < a₁ + n₁' := by omega
  have h_ni : ¬NonIntersecting Q₁.val Q₂.val m a₁ a₂ :=
    crossing_always_intersecting m n₁' n₂' a₁ a₂ h_strict_a h_cross_end Q₁ Q₂
  -- Find shared point
  have h_east₁ : eastSteps Q₁.val = m := by have := Q₁.property.2; simp_all [eastSteps]
  have h_east₂ : eastSteps Q₂.val = m := by have := Q₂.property.2; simp_all [eastSteps]
  have h_shared := sharedPoints_nonempty_of_not_ni h_east₁ h_east₂ h_ni
  set p := canonSharedPoint Q₁.val Q₂.val a₁ a₂ h_shared with hp_def
  have hp₁ := canonSharedPoint_mem₁ Q₁.val Q₂.val a₁ a₂ h_shared
  have hp₂ := canonSharedPoint_mem₂ Q₁.val Q₂.val a₁ a₂ h_shared
  have ha₁ := shared_point_y_ge_a₁ Q₁.val Q₂.val a₁ a₂ p hp₁
  have ha₂ := shared_point_y_ge_a₂ Q₁.val Q₂.val a₁ a₂ p hp₂
  -- Swap at shared point
  set result := swapAtPoint Q₁.val Q₂.val a₁ a₂ p
  -- First component: m East, n₂' + (a₂ - a₁) = (n₁ + a₁ - a₂) + (a₂ - a₁) North steps
  -- But by swapAtPoint_fst_north: North = n₂' + (a₂ - a₁)
  -- n₂' + (a₂ - a₁) = (n₁ + a₁ - a₂) + (a₂ - a₁) = n₁ (since a₁ + n₁ ≥ a₂ from h_n_sum)
  have hfst_east := swapAtPoint_fst_east Q₁.val Q₂.val a₁ a₂ p hp₁ hp₂ h_east₁ h_east₂
  have hfst_north := swapAtPoint_fst_north Q₁.val Q₂.val a₁ a₂ p hp₁ hp₂ ha₁ ha₂
  have hn₂'_val : Q₂.val.countP (· = true) = n₂' := by
    have := eastSteps_add_northSteps Q₂.val
    simp only [eastSteps, northSteps] at this; omega
  have hfst_north_eq : result.1.countP (· = true) = n₁ := by
    rw [hfst_north, hn₂'_val]; omega
  have hfst_len : result.1.length = m + n₁ := by
    have := bool_list_countP_sum result.1; omega
  -- Second component
  have hsnd_east := swapAtPoint_snd_east Q₁.val Q₂.val a₁ a₂ p hp₁ hp₂ h_east₁ h_east₂
  have hn₁'_val : Q₁.val.countP (· = true) = n₁' := by
    have := eastSteps_add_northSteps Q₁.val
    simp only [eastSteps, northSteps] at this; omega
  have h_reach : a₂ ≤ a₁ + Q₁.val.countP (· = true) := by
    rw [hn₁'_val]; omega
  have hsnd_north := swapAtPoint_snd_north_corrected Q₁.val Q₂.val a₁ a₂ p hp₁ hp₂ ha₁ ha₂ h_reach
  have hsnd_north_eq : result.2.countP (· = true) = n₂ := by
    rw [hsnd_north, hn₁'_val]; omega
  have hsnd_len : result.2.length = m + n₂ := by
    have := bool_list_countP_sum result.2; omega
  -- Swapped paths are intersecting (they share point p)
  have h_ni_result : ¬NonIntersecting result.1 result.2 m a₁ a₂ :=
    swapAtPoint_not_ni Q₁.val Q₂.val a₁ a₂ p hp₁ hp₂ ha₁ ha₂ h_east₁ h_east₂
  exact ⟨(⟨result.1, hfst_len, hfst_east⟩, ⟨result.2, hsnd_len, hsnd_east⟩), h_ni_result⟩

/- ### Part XXIII: Canonical Index Preservation and Injectivity

The injectivity of lindstromForward and lindstromBackward follows from:
1. **Prefix preservation**: swapAtPoint preserves the prefix before the split index
2. **splitIdx recovery**: splitIdx a (posAfter l a k) = k for visited points
3. **Canonical index preservation**: the min shared step index is preserved by swap
4. **Involutivity**: swapping twice at the same indices gives back the original

Key insight: For a shared point q of swapped paths (Q₁, Q₂) with splitIdx a₁ q < i
(where i = splitIdx of the canonical point), q is also shared by the originals (P₁, P₂)
because the prefixes are unchanged. This contradicts minimality of i, so the canonical
split index is the same for (Q₁, Q₂) as for (P₁, P₂). -/

/-- posAfter depends only on the first i steps of the path -/
private theorem posAfter_take_eq (l : LPath) (a i k : ℕ) (hk : k ≤ i) :
    posAfter (l.take i) a k = posAfter l a k := by
  simp [posAfter, List.take_take, min_eq_left hk]

/-- splitIdx of posAfter recovers the step index -/
private theorem splitIdx_posAfter (l : LPath) (a k : ℕ) (hk : k ≤ l.length) :
    splitIdx a (posAfter l a k) = k := by
  simp only [splitIdx, posAfter]
  have hlen : (l.take k).length = k := by rw [List.length_take]; omega
  have := bool_list_countP_sum (l.take k)
  omega

/-- Prefix of first swapped path equals prefix of original -/
private theorem swapAtPoint_fst_take_prefix (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (hi : splitIdx a₁ p ≤ l₁.length) (k : ℕ) (hk : k ≤ splitIdx a₁ p) :
    (swapAtPoint l₁ l₂ a₁ a₂ p).1.take k = l₁.take k := by
  simp only [swapAtPoint]
  set i := splitIdx a₁ p
  have hli : (l₁.take i).length = i := by rw [List.length_take]; omega
  have h1 : (l₁.take i ++ l₂.drop (splitIdx a₂ p)).take i = l₁.take i := by
    rw [← hli]; exact List.take_left
  have h2 := congr_arg (List.take k) h1
  simp only [List.take_take, min_eq_right hk] at h2
  exact h2

/-- Prefix of second swapped path equals prefix of original -/
private theorem swapAtPoint_snd_take_prefix (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p : ℕ × ℕ)
    (hj : splitIdx a₂ p ≤ l₂.length) (k : ℕ) (hk : k ≤ splitIdx a₂ p) :
    (swapAtPoint l₁ l₂ a₁ a₂ p).2.take k = l₂.take k := by
  simp only [swapAtPoint]
  set j := splitIdx a₂ p
  have hlj : (l₂.take j).length = j := by rw [List.length_take]; omega
  have h1 : (l₂.take j ++ l₁.drop (splitIdx a₁ p)).take j = l₂.take j := by
    rw [← hlj]; exact List.take_left
  have h2 := congr_arg (List.take k) h1
  simp only [List.take_take, min_eq_right hk] at h2
  exact h2

/-- swapAtPoint only depends on splitIdx values, not on the specific point -/
private theorem swapAtPoint_eq_of_splitIdx (l₁ l₂ : LPath) (a₁ a₂ : ℕ) (p q : ℕ × ℕ)
    (h₁ : splitIdx a₁ p = splitIdx a₁ q) (h₂ : splitIdx a₂ p = splitIdx a₂ q) :
    swapAtPoint l₁ l₂ a₁ a₂ p = swapAtPoint l₁ l₂ a₁ a₂ q := by
  simp only [swapAtPoint, h₁, h₂]

/-- A visited point q of a path with start a has splitIdx a q equal to its
    step index. Specifically, for any i ≤ l.length, the point posAfter l a i
    is visited and has splitIdx a = i. Conversely, any visited point q has
    some step index k with posAfter l a k = q and splitIdx a q = k. -/
private theorem visitedPoint_splitIdx_eq (l : LPath) (a : ℕ) (q : ℕ × ℕ)
    (hq : q ∈ visitedPoints l a) :
    ∃ k, k ≤ l.length ∧ posAfter l a k = q ∧ splitIdx a q = k := by
  simp [visitedPoints, Finset.mem_image, Finset.mem_range] at hq
  obtain ⟨k, hk_bound, hk_eq⟩ := hq
  have hk_le : k ≤ l.length := by omega
  refine ⟨k, hk_le, hk_eq, ?_⟩
  rw [← hk_eq]; exact splitIdx_posAfter l a k hk_le

/-- For a shared point, the splitIdx values for a₁ and a₂ differ by
    the constant a₂ - a₁ (when a₁ ≤ a₂ and both ≤ p.2) -/
private theorem splitIdx_const_diff (a₁ a₂ : ℕ) (q : ℕ × ℕ)
    (ha₁ : a₁ ≤ q.2) (ha₂ : a₂ ≤ q.2) (h_le : a₁ ≤ a₂) :
    splitIdx a₁ q = splitIdx a₂ q + (a₂ - a₁) := by
  simp [splitIdx]; omega

/-- **Canonical Split Index Preservation**: the min shared step index of the
    swapped paths equals the min shared step index of the original paths.

    After swapping at the canonical point p with splitIdx a₁ p = i:
    - The prefix of Q₁ before step i equals the prefix of P₁ (prefix preservation)
    - The prefix of Q₂ before step j equals the prefix of P₂
    - Any shared point of (Q₁, Q₂) at step < i is therefore shared by (P₁, P₂)
    - By minimality of p for (P₁, P₂), no such point exists
    - Since p IS a shared point of (Q₁, Q₂), the minimum is exactly i -/
private theorem minSharedStepIdx_preserved (l₁ l₂ : LPath) (a₁ a₂ : ℕ)
    (h_strict : a₁ < a₂)
    (h_shared : (sharedPoints l₁ l₂ a₁ a₂).Nonempty)
    (hi : splitIdx a₁ (canonSharedPoint l₁ l₂ a₁ a₂ h_shared) ≤ l₁.length)
    (hj : splitIdx a₂ (canonSharedPoint l₁ l₂ a₁ a₂ h_shared) ≤ l₂.length)
    (h_shared' : (sharedPoints (swapAtPoint l₁ l₂ a₁ a₂
      (canonSharedPoint l₁ l₂ a₁ a₂ h_shared)).1
      (swapAtPoint l₁ l₂ a₁ a₂ (canonSharedPoint l₁ l₂ a₁ a₂ h_shared)).2
      a₁ a₂).Nonempty) :
    minSharedStepIdx
      (swapAtPoint l₁ l₂ a₁ a₂ (canonSharedPoint l₁ l₂ a₁ a₂ h_shared)).1
      (swapAtPoint l₁ l₂ a₁ a₂ (canonSharedPoint l₁ l₂ a₁ a₂ h_shared)).2
      a₁ a₂ h_shared' =
    minSharedStepIdx l₁ l₂ a₁ a₂ h_shared := by
  set cp := canonSharedPoint l₁ l₂ a₁ a₂ h_shared with hcp_def
  set Q₁ := (swapAtPoint l₁ l₂ a₁ a₂ cp).1
  set Q₂ := (swapAtPoint l₁ l₂ a₁ a₂ cp).2
  set i := splitIdx a₁ cp
  set j := splitIdx a₂ cp
  set minOrig := minSharedStepIdx l₁ l₂ a₁ a₂ h_shared
  set minSwap := minSharedStepIdx Q₁ Q₂ a₁ a₂ h_shared'
  -- Step 1: minOrig = i (by definition, canonSharedPoint achieves the minimum)
  have hcp_idx := (minSharedStepIdx_achieved l₁ l₂ a₁ a₂ h_shared).choose_spec.2
  have h_min_orig : minOrig = i := by
    rw [show i = splitIdx a₁ cp from rfl]
    exact hcp_idx.symm ▸ rfl
  -- Step 2: p is a shared point of (Q₁, Q₂), so minSwap ≤ i
  have hp₁ := canonSharedPoint_mem₁ l₁ l₂ a₁ a₂ h_shared
  have hp₂ := canonSharedPoint_mem₂ l₁ l₂ a₁ a₂ h_shared
  have ha₁ := shared_point_y_ge_a₁ l₁ l₂ a₁ a₂ cp hp₁
  have ha₂ := shared_point_y_ge_a₂ l₁ l₂ a₁ a₂ cp hp₂
  have hcp_in_Q : cp ∈ sharedPoints Q₁ Q₂ a₁ a₂ := by
    simp only [sharedPoints, Finset.mem_inter]
    exact ⟨swapAtPoint_fst_visits_point l₁ l₂ a₁ a₂ cp hp₁ hp₂ ha₁ ha₂,
           swapAtPoint_snd_visits_point l₁ l₂ a₁ a₂ cp hp₁ hp₂ ha₁ ha₂⟩
  have h_swap_le_i : minSwap ≤ i := by
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨cp, hcp_in_Q, rfl⟩)
  -- Step 3: Any shared point of (Q₁, Q₂) at step < i is also shared by (P₁, P₂)
  -- This contradicts minimality, so minSwap ≥ i
  have h_swap_ge_i : i ≤ minSwap := by
    by_contra h_lt
    push_neg at h_lt
    -- There exists a shared point of (Q₁, Q₂) with step index < i
    have hmin_mem := Finset.min'_mem
      ((sharedPoints Q₁ Q₂ a₁ a₂).image (splitIdx a₁)) (Finset.Nonempty.image h_shared' _)
    obtain ⟨q, hq_shared, hq_idx⟩ := Finset.mem_image.mp hmin_mem
    -- q ∈ sharedPoints Q₁ Q₂ a₁ a₂ with splitIdx a₁ q = minSwap < i
    have hq_lt_i : splitIdx a₁ q < i := by omega
    -- q is visited by Q₁ and Q₂
    have hq_Q₁ : q ∈ visitedPoints Q₁ a₁ := (Finset.mem_inter.mp hq_shared).1
    have hq_Q₂ : q ∈ visitedPoints Q₂ a₂ := (Finset.mem_inter.mp hq_shared).2
    -- Get the step indices for q in Q₁ and Q₂
    obtain ⟨k₁, hk₁_le, hk₁_eq, hk₁_idx⟩ := visitedPoint_splitIdx_eq Q₁ a₁ q hq_Q₁
    obtain ⟨k₂, hk₂_le, hk₂_eq, hk₂_idx⟩ := visitedPoint_splitIdx_eq Q₂ a₂ q hq_Q₂
    -- k₁ = splitIdx a₁ q < i
    have hk₁_lt_i : k₁ < i := by omega
    -- For Q₂: splitIdx a₂ q < j because splitIdx a₁ q = splitIdx a₂ q + (a₂ - a₁)
    -- and i = j + (a₂ - a₁) (same point cp has both indices)
    have hq_y_ge_a₂ : a₂ ≤ q.2 := by
      obtain ⟨k', _, hk'_eq⟩ := visitedPoint_splitIdx_eq Q₂ a₂ q hq_Q₂
      rw [← hk'_eq]; simp [posAfter]; omega
    have hq_y_ge_a₁ : a₁ ≤ q.2 := by omega
    have h_diff_q := splitIdx_const_diff a₁ a₂ q hq_y_ge_a₁ hq_y_ge_a₂ (le_of_lt h_strict)
    have h_diff_cp := splitIdx_const_diff a₁ a₂ cp ha₁ ha₂ (le_of_lt h_strict)
    have hk₂_idx_eq : k₂ = splitIdx a₂ q := hk₂_idx
    have hk₂_lt_j : k₂ < j := by omega
    -- Since k₁ < i, prefix of Q₁ at step k₁ = prefix of l₁ at step k₁
    -- So posAfter Q₁ a₁ k₁ = posAfter l₁ a₁ k₁
    have h_prefix₁ := swapAtPoint_fst_take_prefix l₁ l₂ a₁ a₂ cp hi k₁ (le_of_lt hk₁_lt_i)
    have h_pos₁ : posAfter Q₁ a₁ k₁ = posAfter l₁ a₁ k₁ := by
      simp [posAfter]; congr 1 <;> (congr 1; exact h_prefix₁)
    -- Similarly for Q₂
    have h_prefix₂ := swapAtPoint_snd_take_prefix l₁ l₂ a₁ a₂ cp hj k₂ (le_of_lt hk₂_lt_j)
    have h_pos₂ : posAfter Q₂ a₂ k₂ = posAfter l₂ a₂ k₂ := by
      simp [posAfter]; congr 1 <;> (congr 1; exact h_prefix₂)
    -- So q = posAfter l₁ a₁ k₁ = posAfter l₂ a₂ k₂, meaning q is shared by (l₁, l₂)
    rw [hk₁_eq] at h_pos₁; rw [hk₂_eq] at h_pos₂
    have hq_P₁ : q ∈ visitedPoints l₁ a₁ := by
      simp [visitedPoints, Finset.mem_image, Finset.mem_range]
      exact ⟨k₁, by omega, h_pos₁.symm⟩
    have hq_P₂ : q ∈ visitedPoints l₂ a₂ := by
      simp [visitedPoints, Finset.mem_image, Finset.mem_range]
      exact ⟨k₂, by omega, h_pos₂.symm⟩
    have hq_orig : q ∈ sharedPoints l₁ l₂ a₁ a₂ :=
      Finset.mem_inter.mpr ⟨hq_P₁, hq_P₂⟩
    -- By minimality of cp in (l₁, l₂): splitIdx a₁ q ≥ i
    have := canonSharedPoint_isMin l₁ l₂ a₁ a₂ h_shared q hq_orig
    omega
  -- Combine: minSwap = i = minOrig
  omega

/-- The forward map is injective. This follows because:
    1. canonSharedPoint is preserved by swap (the min step index property)
    2. swapAtPoint is involutive
    So applying backward ∘ forward = id, which implies forward is injective. -/
theorem lindstromForward_injective (m n₁ n₂ n₁' n₂' a₁ a₂ : ℕ)
    (h_strict_a : a₁ < a₂)
    (h_end : a₁ + n₁ < a₂ + n₂)
    (h_n₁' : n₁' = n₂ + a₂ - a₁) (h_n₂' : n₂' = n₁ + a₁ - a₂)
    (h_n_sum : n₁ + n₂ = n₁' + n₂') :
    Function.Injective (lindstromForward m n₁ n₂ n₁' n₂' a₁ a₂
      h_strict_a h_end h_n₁' h_n₂' h_n_sum) := by
  intro ⟨⟨P₁, P₂⟩, hni_x⟩ ⟨⟨P₁', P₂'⟩, hni_y⟩ heq
  -- For input x = ⟨⟨P₁, P₂⟩, hni_x⟩, lindstromForward swaps at canonical point
  -- producing (Q₁, Q₂). For input y = ⟨⟨P₁', P₂'⟩, hni_y⟩, it produces the same (Q₁, Q₂).
  -- Strategy: show the originals (P₁, P₂) and (P₁', P₂') can both be recovered from
  -- (Q₁, Q₂) by swapping at the canonical indices. Since the canonical indices agree
  -- (by preservation) and swapAtPoint is deterministic, the originals must be equal.
  -- Extract equality of output values
  have h_fst : (lindstromForward m n₁ n₂ n₁' n₂' a₁ a₂
    h_strict_a h_end h_n₁' h_n₂' h_n_sum ⟨⟨P₁, P₂⟩, hni_x⟩).1 =
    (lindstromForward m n₁ n₂ n₁' n₂' a₁ a₂
    h_strict_a h_end h_n₁' h_n₂' h_n_sum ⟨⟨P₁', P₂'⟩, hni_y⟩).1 := by
    rw [heq]
  have h_snd : (lindstromForward m n₁ n₂ n₁' n₂' a₁ a₂
    h_strict_a h_end h_n₁' h_n₂' h_n_sum ⟨⟨P₁, P₂⟩, hni_x⟩).2 =
    (lindstromForward m n₁ n₂ n₁' n₂' a₁ a₂
    h_strict_a h_end h_n₁' h_n₂' h_n_sum ⟨⟨P₁', P₂'⟩, hni_y⟩).2 := by
    rw [heq]
  -- Both P₁ and P₁' are pathTypes, so equality of subtype vals suffices
  -- lindstromForward ... ⟨⟨P₁, P₂⟩, hni⟩ = (⟨swap.1, ...⟩, ⟨swap.2, ...⟩)
  -- where swap = swapAtPoint P₁.val P₂.val a₁ a₂ cp
  -- Since the function is defined by tactic, we use that the output .val is the swap
  -- For x: compute canonical point and swap
  have h_east₁ : eastSteps P₁.val = m := by have := P₁.property.2; simp_all [eastSteps]
  have h_east₂ : eastSteps P₂.val = m := by have := P₂.property.2; simp_all [eastSteps]
  have h_shared_x := sharedPoints_nonempty_of_not_ni h_east₁ h_east₂ hni_x
  set cpx := canonSharedPoint P₁.val P₂.val a₁ a₂ h_shared_x
  have hpx₁ := canonSharedPoint_mem₁ P₁.val P₂.val a₁ a₂ h_shared_x
  have hpx₂ := canonSharedPoint_mem₂ P₁.val P₂.val a₁ a₂ h_shared_x
  have hax₁ := shared_point_y_ge_a₁ P₁.val P₂.val a₁ a₂ cpx hpx₁
  have hax₂ := shared_point_y_ge_a₂ P₁.val P₂.val a₁ a₂ cpx hpx₂
  have hix := splitIdx_le_length P₁.val a₁ cpx hpx₁
  have hjx := splitIdx_le_length P₂.val a₂ cpx hpx₂
  -- For y: compute canonical point and swap
  have h_east₁' : eastSteps P₁'.val = m := by have := P₁'.property.2; simp_all [eastSteps]
  have h_east₂' : eastSteps P₂'.val = m := by have := P₂'.property.2; simp_all [eastSteps]
  have h_shared_y := sharedPoints_nonempty_of_not_ni h_east₁' h_east₂' hni_y
  set cpy := canonSharedPoint P₁'.val P₂'.val a₁ a₂ h_shared_y
  have hpy₁ := canonSharedPoint_mem₁ P₁'.val P₂'.val a₁ a₂ h_shared_y
  have hpy₂ := canonSharedPoint_mem₂ P₁'.val P₂'.val a₁ a₂ h_shared_y
  have hay₁ := shared_point_y_ge_a₁ P₁'.val P₂'.val a₁ a₂ cpy hpy₁
  have hay₂ := shared_point_y_ge_a₂ P₁'.val P₂'.val a₁ a₂ cpy hpy₂
  have hiy := splitIdx_le_length P₁'.val a₁ cpy hpy₁
  have hjy := splitIdx_le_length P₂'.val a₂ cpy hpy₂
  -- The outputs agree on .val:
  -- lindstromForward returns (⟨(swapAtPoint P₁ P₂ cpx).1, ...⟩, ⟨(swapAtPoint P₁ P₂ cpx).2, ...⟩)
  -- So the .val of the outputs are the swap results
  -- Q₁.val = (swapAtPoint P₁.val P₂.val a₁ a₂ cpx).1 = (swapAtPoint P₁'.val P₂'.val a₁ a₂ cpy).1
  -- By involutivity at cpx: swapAtPoint(swap(P₁,P₂,cpx)) at cpx = (P₁, P₂)
  -- By involutivity at cpy: swapAtPoint(swap(P₁',P₂',cpy)) at cpy = (P₁', P₂')
  -- Since the swaps produce the same output, and the canonical indices agree...
  -- Apply involutivity to recover originals
  have h_invol_x := swapAtPoint_involutive P₁.val P₂.val a₁ a₂ cpx hix hjx
  have h_invol_y := swapAtPoint_involutive P₁'.val P₂'.val a₁ a₂ cpy hiy hjy
  -- The key fact: swapAtPoint only depends on splitIdx values.
  -- If splitIdx a₁ cpx = splitIdx a₁ cpy and splitIdx a₂ cpx = splitIdx a₂ cpy,
  -- then swapping Q at cpx and at cpy give the same result.
  -- Since swapping Q at cpx gives (P₁, P₂) and at cpy gives (P₁', P₂'),
  -- we conclude (P₁, P₂) = (P₁', P₂').
  -- To show splitIdx equality, we use that both are equal to the min shared step
  -- index of the common output Q. But this requires knowing Q, which is the output
  -- of lindstromForward. Instead, we use a more direct argument.
  -- Direct argument: since both forward maps produce the same list values,
  -- and involutivity at the respective canonical points recovers the originals,
  -- if the canonical split indices agree, we're done.
  -- The split indices agree because both equal the min shared step index of Q.
  -- We need: splitIdx a₁ cpx = splitIdx a₁ cpy
  -- Since heq says the outputs are equal (as pathType pairs),
  -- the output list values are the same.
  -- Let Q = swapAtPoint P₁.val P₂.val a₁ a₂ cpx = swapAtPoint P₁'.val P₂'.val a₁ a₂ cpy
  set Qx := swapAtPoint P₁.val P₂.val a₁ a₂ cpx
  set Qy := swapAtPoint P₁'.val P₂'.val a₁ a₂ cpy
  -- From heq, the output .val fields are equal
  -- (lindstromForward internally computes Qx and Qy, and wraps in subtypes)
  -- The output .1.val = Qx.1 and output.1.val = Qy.1 (from the two inputs)
  -- So Qx.1 = Qy.1 and Qx.2 = Qy.2
  -- This means swapAtPoint at cpx of (P₁, P₂) = swapAtPoint at cpy of (P₁', P₂')
  -- Applying involutivity:
  -- (P₁.val, P₂.val) = swapAtPoint Qx.1 Qx.2 a₁ a₂ cpx  (from h_invol_x)
  -- (P₁'.val, P₂'.val) = swapAtPoint Qy.1 Qy.2 a₁ a₂ cpy  (from h_invol_y)
  -- Since Qx = Qy (pointwise) and splitIdx cpx = splitIdx cpy:
  -- (P₁.val, P₂.val) = (P₁'.val, P₂'.val)
  -- The core step: show Qx.1 = Qy.1 and Qx.2 = Qy.2
  -- and splitIdx a₁ cpx = splitIdx a₁ cpy (and a₂)
  -- We get Qx = Qy from heq (both are the output values of lindstromForward)
  -- Getting exact list equality from heq requires knowing the definitional behavior.
  -- Since lindstromForward ... ⟨⟨P₁, P₂⟩, hni_x⟩ is definitionally
  -- (⟨Qx.1, _⟩, ⟨Qx.2, _⟩), the .val of .1 is Qx.1.
  -- From h_fst: (the fst outputs are equal as subtypes)
  -- Subtype.val injectivity: output.1.val (from x) = output.1.val (from y)
  -- i.e., Qx.1 = Qy.1
  -- Similarly Qx.2 = Qy.2
  -- NOTE: This relies on definitional reduction of lindstromForward.
  -- If the kernel can't reduce, we'd need characterization lemmas.
  -- For now, use congr_arg Subtype.val on h_fst and h_snd.
  have hQ1_eq : Qx.1 = Qy.1 := congr_arg Subtype.val h_fst
  have hQ2_eq : Qx.2 = Qy.2 := congr_arg Subtype.val h_snd
  -- From involutivity:
  -- h_invol_x : swapAtPoint Qx.1 Qx.2 a₁ a₂ cpx = (P₁.val, P₂.val)
  -- h_invol_y : swapAtPoint Qy.1 Qy.2 a₁ a₂ cpy = (P₁'.val, P₂'.val)
  -- Rewrite h_invol_y using Qx = Qy:
  have h_invol_y' : swapAtPoint Qx.1 Qx.2 a₁ a₂ cpy = (P₁'.val, P₂'.val) := by
    rw [hQ1_eq, hQ2_eq]; exact h_invol_y
  -- If splitIdx cpx = splitIdx cpy, then swapAtPoint at cpx = swapAtPoint at cpy
  -- and we'd have (P₁.val, P₂.val) = (P₁'.val, P₂'.val)
  -- Show split indices are equal via minSharedStepIdx
  -- Both cpx and cpy, when their respective paths are swapped, produce Q (= Qx = Qy)
  -- The min shared step idx of Q must equal both splitIdx a₁ cpx and splitIdx a₁ cpy
  -- For cpx: Q = Qx, and minSharedStepIdx Qx = minSharedStepIdx (P₁, P₂) = splitIdx a₁ cpx
  have h_shared_Q : (sharedPoints Qx.1 Qx.2 a₁ a₂).Nonempty := by
    exact ⟨cpx, Finset.mem_inter.mpr
      ⟨swapAtPoint_fst_visits_point P₁.val P₂.val a₁ a₂ cpx hpx₁ hpx₂ hax₁ hax₂,
       swapAtPoint_snd_visits_point P₁.val P₂.val a₁ a₂ cpx hpx₁ hpx₂ hax₁ hax₂⟩⟩
  have h_minQ_x := minSharedStepIdx_preserved P₁.val P₂.val a₁ a₂
    h_strict_a h_shared_x hix hjx h_shared_Q
  -- Similarly for cpy (but Q = Qx = Qy, and the shared points are the same)
  have h_shared_Q' : (sharedPoints Qy.1 Qy.2 a₁ a₂).Nonempty := by
    rw [hQ1_eq, hQ2_eq] at h_shared_Q; exact h_shared_Q
  -- We need minSharedStepIdx Qy = minSharedStepIdx (P₁', P₂') = splitIdx a₁ cpy
  -- But h_shared_Q uses Qx and h_shared_Q' uses Qy (which are equal)
  -- The minSharedStepIdx should be the same since Qx = Qy
  have h_shared_Qx_eq : sharedPoints Qx.1 Qx.2 a₁ a₂ = sharedPoints Qy.1 Qy.2 a₁ a₂ := by
    simp [sharedPoints, visitedPoints, hQ1_eq, hQ2_eq]
  have h_minQ_y := minSharedStepIdx_preserved P₁'.val P₂'.val a₁ a₂
    h_strict_a h_shared_y hiy hjy h_shared_Q'
  -- Now: both minSharedStepIdx give the same value for Q
  -- h_minQ_x: minSharedStepIdx Qx (with h_shared_Q) = minSharedStepIdx P₁ P₂ (= splitIdx a₁ cpx)
  -- h_minQ_y: minSharedStepIdx Qy (with h_shared_Q') = minSharedStepIdx P₁' P₂' (= splitIdx a₁ cpy)
  -- Since Qx = Qy and the shared points sets are the same:
  -- minSharedStepIdx Qx h_shared_Q = minSharedStepIdx Qy h_shared_Q'
  have h_min_eq : minSharedStepIdx Qx.1 Qx.2 a₁ a₂ h_shared_Q =
      minSharedStepIdx Qy.1 Qy.2 a₁ a₂ h_shared_Q' := by
    simp only [minSharedStepIdx, h_shared_Qx_eq]
  -- Therefore splitIdx a₁ cpx = splitIdx a₁ cpy (via the canonical point spec)
  have hcpx_spec := (minSharedStepIdx_achieved P₁.val P₂.val a₁ a₂ h_shared_x).choose_spec.2
  have hcpy_spec := (minSharedStepIdx_achieved P₁'.val P₂'.val a₁ a₂ h_shared_y).choose_spec.2
  have h_idx_a₁ : splitIdx a₁ cpx = splitIdx a₁ cpy := by
    show splitIdx a₁ (canonSharedPoint P₁.val P₂.val a₁ a₂ h_shared_x) =
         splitIdx a₁ (canonSharedPoint P₁'.val P₂'.val a₁ a₂ h_shared_y)
    simp only [canonSharedPoint]
    have h_unfold_min_x : minSharedStepIdx Qx.1 Qx.2 a₁ a₂ h_shared_Q =
        minSharedStepIdx P₁.val P₂.val a₁ a₂ h_shared_x := h_minQ_x
    have h_unfold_min_y : minSharedStepIdx Qy.1 Qy.2 a₁ a₂ h_shared_Q' =
        minSharedStepIdx P₁'.val P₂'.val a₁ a₂ h_shared_y := h_minQ_y
    omega
  -- For a₂: use the constant difference property
  have h_idx_a₂ : splitIdx a₂ cpx = splitIdx a₂ cpy := by
    have h1 := splitIdx_const_diff a₁ a₂ cpx hax₁ hax₂ (le_of_lt h_strict_a)
    have h2 := splitIdx_const_diff a₁ a₂ cpy hay₁ hay₂ (le_of_lt h_strict_a)
    omega
  -- Now: swapAtPoint Qx at cpx = swapAtPoint Qx at cpy
  have h_swap_eq := swapAtPoint_eq_of_splitIdx Qx.1 Qx.2 a₁ a₂ cpx cpy h_idx_a₁ h_idx_a₂
  -- From involutivity: swapAtPoint Qx at cpx = (P₁.val, P₂.val)
  -- and                 swapAtPoint Qx at cpy = (P₁'.val, P₂'.val)
  -- Therefore (P₁.val, P₂.val) = (P₁'.val, P₂'.val)
  have h_eq : (P₁.val, P₂.val) = (P₁'.val, P₂'.val) := by
    rw [← h_invol_x, ← h_invol_y', h_swap_eq]
  -- Extract component equalities and conclude
  have h_P₁ : P₁ = P₁' := Subtype.ext (Prod.mk.inj h_eq).1
  have h_P₂ : P₂ = P₂' := Subtype.ext (Prod.mk.inj h_eq).2
  exact Subtype.ext (Prod.ext h_P₁ h_P₂)

/-- The backward map is injective (symmetric argument). -/
theorem lindstromBackward_injective (m n₁ n₂ n₁' n₂' a₁ a₂ : ℕ)
    (h_strict_a : a₁ < a₂)
    (h_end : a₁ + n₁ < a₂ + n₂)
    (h_n₁' : n₁' = n₂ + a₂ - a₁) (h_n₂' : n₂' = n₁ + a₁ - a₂)
    (h_n_sum : n₁ + n₂ = n₁' + n₂') :
    Function.Injective (lindstromBackward m n₁ n₂ n₁' n₂' a₁ a₂
      h_strict_a h_end h_n₁' h_n₂' h_n_sum) := by
  intro ⟨Q₁, Q₂⟩ ⟨Q₁', Q₂'⟩ heq
  -- lindstromBackward swaps at the canonical point of (Q₁, Q₂) to get an intersecting pair.
  -- If backward(Q₁, Q₂) = backward(Q₁', Q₂'), the output subtype values are equal.
  -- By the same canonical index preservation + involutivity argument, (Q₁, Q₂) = (Q₁', Q₂').
  -- Extract the equality of the output subtype values
  have h_val := congr_arg Subtype.val heq
  -- h_val : (lindstromBackward ... (Q₁, Q₂)).val = (lindstromBackward ... (Q₁', Q₂')).val
  -- The .val is a pair of pathTypes. Extract component-wise:
  have h_val1 : (lindstromBackward m n₁ n₂ n₁' n₂' a₁ a₂
    h_strict_a h_end h_n₁' h_n₂' h_n_sum (Q₁, Q₂)).val.1 =
    (lindstromBackward m n₁ n₂ n₁' n₂' a₁ a₂
    h_strict_a h_end h_n₁' h_n₂' h_n_sum (Q₁', Q₂')).val.1 := by
    rw [heq]
  have h_val2 : (lindstromBackward m n₁ n₂ n₁' n₂' a₁ a₂
    h_strict_a h_end h_n₁' h_n₂' h_n_sum (Q₁, Q₂)).val.2 =
    (lindstromBackward m n₁ n₂ n₁' n₂' a₁ a₂
    h_strict_a h_end h_n₁' h_n₂' h_n_sum (Q₁', Q₂')).val.2 := by
    rw [heq]
  -- lindstromBackward computes:
  -- 1. Prove Q₁, Q₂ are intersecting (crossing_always_intersecting)
  -- 2. Find canonical shared point cpq of (Q₁, Q₂)
  -- 3. Swap at cpq to get result
  -- 4. Return ⟨(result.1, result.2), not_ni_proof⟩
  -- So the output .val.1.val = (swapAtPoint Q₁.val Q₂.val a₁ a₂ cpq).1
  -- For Q₁: set up canonical point
  have h_cross_end : a₂ + n₂' < a₁ + n₁' := by omega
  have h_ni_q : ¬NonIntersecting Q₁.val Q₂.val m a₁ a₂ :=
    crossing_always_intersecting m n₁' n₂' a₁ a₂ h_strict_a h_cross_end Q₁ Q₂
  have h_east_q₁ : eastSteps Q₁.val = m := by
    have := Q₁.property.2; simp_all [eastSteps]
  have h_east_q₂ : eastSteps Q₂.val = m := by
    have := Q₂.property.2; simp_all [eastSteps]
  have h_shared_q := sharedPoints_nonempty_of_not_ni h_east_q₁ h_east_q₂ h_ni_q
  set cpq := canonSharedPoint Q₁.val Q₂.val a₁ a₂ h_shared_q
  have hpq₁ := canonSharedPoint_mem₁ Q₁.val Q₂.val a₁ a₂ h_shared_q
  have hpq₂ := canonSharedPoint_mem₂ Q₁.val Q₂.val a₁ a₂ h_shared_q
  have haq₁ := shared_point_y_ge_a₁ Q₁.val Q₂.val a₁ a₂ cpq hpq₁
  have haq₂ := shared_point_y_ge_a₂ Q₁.val Q₂.val a₁ a₂ cpq hpq₂
  have hiq := splitIdx_le_length Q₁.val a₁ cpq hpq₁
  have hjq := splitIdx_le_length Q₂.val a₂ cpq hpq₂
  -- For Q₁':
  have h_ni_q' : ¬NonIntersecting Q₁'.val Q₂'.val m a₁ a₂ :=
    crossing_always_intersecting m n₁' n₂' a₁ a₂ h_strict_a h_cross_end Q₁' Q₂'
  have h_east_q₁' : eastSteps Q₁'.val = m := by
    have := Q₁'.property.2; simp_all [eastSteps]
  have h_east_q₂' : eastSteps Q₂'.val = m := by
    have := Q₂'.property.2; simp_all [eastSteps]
  have h_shared_q' := sharedPoints_nonempty_of_not_ni h_east_q₁' h_east_q₂' h_ni_q'
  set cpq' := canonSharedPoint Q₁'.val Q₂'.val a₁ a₂ h_shared_q'
  have hpq₁' := canonSharedPoint_mem₁ Q₁'.val Q₂'.val a₁ a₂ h_shared_q'
  have hpq₂' := canonSharedPoint_mem₂ Q₁'.val Q₂'.val a₁ a₂ h_shared_q'
  have haq₁' := shared_point_y_ge_a₁ Q₁'.val Q₂'.val a₁ a₂ cpq' hpq₁'
  have haq₂' := shared_point_y_ge_a₂ Q₁'.val Q₂'.val a₁ a₂ cpq' hpq₂'
  have hiq' := splitIdx_le_length Q₁'.val a₁ cpq' hpq₁'
  have hjq' := splitIdx_le_length Q₂'.val a₂ cpq' hpq₂'
  -- The swapped results are:
  set Rx := swapAtPoint Q₁.val Q₂.val a₁ a₂ cpq
  set Ry := swapAtPoint Q₁'.val Q₂'.val a₁ a₂ cpq'
  -- From heq: Rx.1 = Ry.1 and Rx.2 = Ry.2
  have hR1_eq : Rx.1 = Ry.1 := congr_arg Subtype.val h_val1
  have hR2_eq : Rx.2 = Ry.2 := congr_arg Subtype.val h_val2
  -- By involutivity:
  have h_invol_q := swapAtPoint_involutive Q₁.val Q₂.val a₁ a₂ cpq hiq hjq
  have h_invol_q' := swapAtPoint_involutive Q₁'.val Q₂'.val a₁ a₂ cpq' hiq' hjq'
  -- Canonical index preservation for both:
  have h_shared_R : (sharedPoints Rx.1 Rx.2 a₁ a₂).Nonempty := by
    exact ⟨cpq, Finset.mem_inter.mpr
      ⟨swapAtPoint_fst_visits_point Q₁.val Q₂.val a₁ a₂ cpq hpq₁ hpq₂ haq₁ haq₂,
       swapAtPoint_snd_visits_point Q₁.val Q₂.val a₁ a₂ cpq hpq₁ hpq₂ haq₁ haq₂⟩⟩
  have h_shared_R' : (sharedPoints Ry.1 Ry.2 a₁ a₂).Nonempty := by
    exact ⟨cpq', Finset.mem_inter.mpr
      ⟨swapAtPoint_fst_visits_point Q₁'.val Q₂'.val a₁ a₂ cpq' hpq₁' hpq₂' haq₁' haq₂',
       swapAtPoint_snd_visits_point Q₁'.val Q₂'.val a₁ a₂ cpq' hpq₁' hpq₂' haq₁' haq₂'⟩⟩
  -- minSharedStepIdx Rx = minSharedStepIdx Q₁ Q₂
  have h_min_x := minSharedStepIdx_preserved Q₁.val Q₂.val a₁ a₂
    h_strict_a h_shared_q hiq hjq h_shared_R
  -- minSharedStepIdx Ry = minSharedStepIdx Q₁' Q₂'
  have h_min_y := minSharedStepIdx_preserved Q₁'.val Q₂'.val a₁ a₂
    h_strict_a h_shared_q' hiq' hjq' h_shared_R'
  -- Since Rx = Ry: their shared points sets are the same
  have h_shared_eq : sharedPoints Rx.1 Rx.2 a₁ a₂ = sharedPoints Ry.1 Ry.2 a₁ a₂ := by
    simp [sharedPoints, visitedPoints, hR1_eq, hR2_eq]
  have h_min_eq : minSharedStepIdx Rx.1 Rx.2 a₁ a₂ h_shared_R =
      minSharedStepIdx Ry.1 Ry.2 a₁ a₂ h_shared_R' := by
    simp only [minSharedStepIdx, h_shared_eq]
  -- splitIdx a₁ cpq = splitIdx a₁ cpq'
  have hcpq_spec := (minSharedStepIdx_achieved Q₁.val Q₂.val a₁ a₂ h_shared_q).choose_spec.2
  have hcpq'_spec := (minSharedStepIdx_achieved Q₁'.val Q₂'.val a₁ a₂ h_shared_q').choose_spec.2
  have h_idx_a₁ : splitIdx a₁ cpq = splitIdx a₁ cpq' := by
    show splitIdx a₁ (canonSharedPoint Q₁.val Q₂.val a₁ a₂ h_shared_q) =
         splitIdx a₁ (canonSharedPoint Q₁'.val Q₂'.val a₁ a₂ h_shared_q')
    simp only [canonSharedPoint]
    -- Chain: splitIdx cpq = minSharedStepIdx Q = minSharedStepIdx Rx
    --      = minSharedStepIdx Ry = minSharedStepIdx Q' = splitIdx cpq'
    have h_unfold_min_x : minSharedStepIdx Rx.1 Rx.2 a₁ a₂ h_shared_R =
        minSharedStepIdx Q₁.val Q₂.val a₁ a₂ h_shared_q := h_min_x
    have h_unfold_min_y : minSharedStepIdx Ry.1 Ry.2 a₁ a₂ h_shared_R' =
        minSharedStepIdx Q₁'.val Q₂'.val a₁ a₂ h_shared_q' := h_min_y
    omega
  have h_idx_a₂ : splitIdx a₂ cpq = splitIdx a₂ cpq' := by
    have h1 := splitIdx_const_diff a₁ a₂ cpq haq₁ haq₂ (le_of_lt h_strict_a)
    have h2 := splitIdx_const_diff a₁ a₂ cpq' haq₁' haq₂' (le_of_lt h_strict_a)
    omega
  -- swapAtPoint Q at cpq = swapAtPoint Q at cpq' (same indices)
  -- From involutivity: swapAtPoint Rx at cpq = (Q₁.val, Q₂.val)
  -- We need: swapAtPoint Rx at cpq' = (Q₁'.val, Q₂'.val)
  -- h_invol_q' says swapAtPoint Ry at cpq' = (Q₁'.val, Q₂'.val)
  -- Since Rx = Ry: swapAtPoint Rx at cpq' = (Q₁'.val, Q₂'.val)
  have h_invol_q'_rewrite : swapAtPoint Rx.1 Rx.2 a₁ a₂ cpq' = (Q₁'.val, Q₂'.val) := by
    rw [hR1_eq, hR2_eq]; exact h_invol_q'
  -- And: swapAtPoint Rx at cpq = swapAtPoint Rx at cpq' (same splitIdx)
  have h_swap_same := swapAtPoint_eq_of_splitIdx Rx.1 Rx.2 a₁ a₂ cpq cpq' h_idx_a₁ h_idx_a₂
  -- Therefore: (Q₁.val, Q₂.val) = (Q₁'.val, Q₂'.val)
  have h_eq : (Q₁.val, Q₂.val) = (Q₁'.val, Q₂'.val) := by
    rw [← h_invol_q, h_swap_same, h_invol_q'_rewrite]
  exact Prod.ext (Subtype.ext (Prod.mk.inj h_eq).1) (Subtype.ext (Prod.mk.inj h_eq).2)

/- ### Part XXIV: Lindström Involution and LGV Lemma

These theorems depend on the forward/backward injections from Part XXIII.
They are placed here to ensure all dependencies are available. -/

/-- **Lindström Involution**: intersecting identity pairs biject with all crossing pairs.
    Proved via dual injections (lindstromForward + lindstromBackward). -/
theorem lindstrom_involution (m n₁ n₂ n₁' n₂' a₁ a₂ : ℕ)
    (h_strict_a : a₁ < a₂)
    (h_end : a₁ + n₁ < a₂ + n₂)
    (h_n₁' : n₁' = n₂ + a₂ - a₁) (h_n₂' : n₂' = n₁ + a₁ - a₂)
    (h_n_sum : n₁ + n₂ = n₁' + n₂') :
    Fintype.card {p : pathType m n₁ × pathType m n₂ //
      ¬NonIntersecting p.1.val p.2.val m a₁ a₂} =
    Fintype.card (pathType m n₁' × pathType m n₂') := by
  apply Nat.le_antisymm
  · exact Fintype.card_le_of_injective _
      (lindstromForward_injective m n₁ n₂ n₁' n₂' a₁ a₂
        h_strict_a h_end h_n₁' h_n₂' h_n_sum)
  · exact Fintype.card_le_of_injective _
      (lindstromBackward_injective m n₁ n₂ n₁' n₂' a₁ a₂
        h_strict_a h_end h_n₁' h_n₂' h_n_sum)

/-- **Lindström Involution Lemma** (wrapper with extra hypothesis). -/
theorem lindstrom_involution_card (m n₁ n₂ n₁' n₂' a₁ a₂ : ℕ)
    (hn₁ : n₁ = n₁)
    (h_strict_a : a₁ < a₂)
    (h_end : a₁ + n₁ < a₂ + n₂)
    (h_n₁' : n₁' = n₂ + a₂ - a₁) (h_n₂' : n₂' = n₁ + a₁ - a₂)
    (h_n_sum : n₁ + n₂ = n₁' + n₂') :
    Fintype.card {p : pathType m n₁ × pathType m n₂ //
      ¬NonIntersecting p.1.val p.2.val m a₁ a₂} =
    Fintype.card (pathType m n₁' × pathType m n₂') :=
  lindstrom_involution m n₁ n₂ n₁' n₂' a₁ a₂ h_strict_a h_end h_n₁' h_n₂' h_n_sum

/-- **The 2×2 LGV Lemma**: Non-intersecting path pairs count = lgvDet.
    Requires the ordering a₁ ≤ a₂ ≤ b₁ ≤ b₂ so that all four path types
    (identity: Aᵢ→Bᵢ, crossing: Aᵢ→Bⱼ) are well-defined. -/
theorem lgv_lemma_2x2 (m a₁ b₁ a₂ b₂ : ℕ)
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
    (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂)
    (ha₂₁ : a₂ ≤ b₁) :
    (niPairCount m (b₁ - a₁) (b₂ - a₂) a₁ a₂ : ℤ) = lgvDet m a₁ b₁ a₂ b₂ := by
  by_cases h_a : a₁ = a₂
  · subst h_a
    rw [lgvDet_same_start', lgv_same_start']; simp
  · by_cases h_b : b₁ = b₂
    · subst h_b
      rw [lgvDet_same_end']
      have h_eq : a₁ + (b₁ - a₁) = a₂ + (b₁ - a₂) := by omega
      rw [lgv_same_end' m (b₁ - a₁) (b₁ - a₂) a₁ a₂ h_eq]; simp
    · have h_strict_a : a₁ < a₂ := lt_of_le_of_ne ha h_a
      have h_strict_b : b₁ < b₂ := lt_of_le_of_ne hb h_b
      set n₁ := b₁ - a₁ with hn₁_def
      set n₂ := b₂ - a₂ with hn₂_def
      set n₁' := b₂ - a₁ with hn₁'_def
      set n₂' := b₁ - a₂ with hn₂'_def
      have h_compl := ni_complement_count' m n₁ n₂ a₁ a₂
      have h_total := total_identity_count' m n₁ n₂
      have h_crossing := total_identity_count' m n₁' n₂'
      have h_n₁'_eq : n₁' = n₂ + a₂ - a₁ := by omega
      have h_n₂'_eq : n₂' = n₁ + a₁ - a₂ := by omega
      have h_n_sum : n₁ + n₂ = n₁' + n₂' := by omega
      have h_end : a₁ + n₁ < a₂ + n₂ := by omega
      have h_bij := lindstrom_involution m n₁ n₂ n₁' n₂' a₁ a₂
        h_strict_a h_end h_n₁'_eq h_n₂'_eq h_n_sum
      rw [h_total, h_bij, h_crossing] at h_compl
      have h_ni : niPairCount m n₁ n₂ a₁ a₂ =
        Nat.choose (m + n₁) m * Nat.choose (m + n₂) m -
        Nat.choose (m + n₁') m * Nat.choose (m + n₂') m := by omega
      have h_le : Nat.choose (m + n₁') m * Nat.choose (m + n₂') m ≤
        Nat.choose (m + n₁) m * Nat.choose (m + n₂) m := by omega
      unfold lgvDet; rw [h_ni]
      zify [h_le]; ring

/-- **Non-negativity**: Under proper ordering, the LGV determinant is non-negative. -/
theorem lgvDet_nonneg (m a₁ b₁ a₂ b₂ : ℕ)
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂) (ha₂₁ : a₂ ≤ b₁) :
    0 ≤ lgvDet m a₁ b₁ a₂ b₂ := by
  rw [← lgv_lemma_2x2 m a₁ b₁ a₂ b₂ ha hb ha₁ ha₂ ha₂₁]
  exact Int.natCast_nonneg _

end LatticePathLGV
