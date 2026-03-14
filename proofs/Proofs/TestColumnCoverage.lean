import Mathlib

/-
  Test file for visitedPoints_covers_column and visitedPoints_covers_final proofs.
  Extracts minimal definitions from BallotProblemOQ03.lean.
-/

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

lemma northSteps_cons_false (xs : LPath) : northSteps (false :: xs) = northSteps xs := by
  simp [northSteps, List.countP_cons]

lemma northSteps_cons_true (xs : LPath) : northSteps (true :: xs) = 1 + northSteps xs := by
  simp [northSteps, List.countP_cons]; omega

/-- northBeforeEast l k = # North (true) steps in l before the k-th East (false) step. -/
def northBeforeEast : LPath → ℕ → ℕ
  | [], _ => 0
  | (false :: _), 0 => 0
  | (false :: xs), (k + 1) => northBeforeEast xs k
  | (true :: xs), k => 1 + northBeforeEast xs k

theorem northBeforeEast_mono (l : LPath) (k : ℕ) :
    northBeforeEast l k ≤ northBeforeEast l (k + 1) := by
  induction l generalizing k with
  | nil => simp [northBeforeEast]
  | cons x xs ih =>
    cases x with
    | false =>
      cases k with
      | zero => simp [northBeforeEast]
      | succ k => simp only [northBeforeEast]; exact ih k
    | true =>
      simp only [northBeforeEast]
      exact Nat.add_le_add_left (ih k) 1

/-- Column entry y-offset for column k -/
def colEntry (l : LPath) : ℕ → ℕ
  | 0 => 0
  | (k + 1) => northBeforeEast l k

theorem colEntry_mono (l : LPath) (k : ℕ) : colEntry l k ≤ colEntry l (k + 1) := by
  cases k with
  | zero => simp [colEntry]
  | succ k => simp [colEntry]; exact northBeforeEast_mono l k

private lemma colEntry_false_succ (xs : LPath) (k : ℕ) :
    colEntry (false :: xs) (k + 1) = colEntry xs k := by
  cases k with
  | zero => simp [colEntry, northBeforeEast]
  | succ k => simp [colEntry, northBeforeEast]

private lemma colEntry_true_succ (xs : LPath) (k : ℕ) :
    colEntry (true :: xs) (k + 1) = colEntry xs (k + 1) + 1 := by
  simp [colEntry, northBeforeEast]; omega

/-- Position after the first i steps of path l starting at (0, a). -/
def posAfter (l : LPath) (a i : ℕ) : ℕ × ℕ :=
  ((l.take i).countP (· = false), a + (l.take i).countP (· = true))

theorem posAfter_zero (l : LPath) (a : ℕ) : posAfter l a 0 = (0, a) := by
  simp [posAfter]

theorem posAfter_length (l : LPath) (a : ℕ) :
    posAfter l a l.length = (eastSteps l, a + northSteps l) := by
  simp [posAfter, eastSteps, northSteps, List.take_length]

/-- Key stepping lemma: after a false (East) step, x-coord increments -/
private lemma posAfter_false_succ (xs : LPath) (a i : ℕ) :
    posAfter (false :: xs) a (i + 1) =
    ((posAfter xs a i).1 + 1, (posAfter xs a i).2) := by
  simp only [posAfter, List.take_succ_cons, List.countP_cons]
  simp [Prod.ext_iff]; omega

/-- Key stepping lemma: after a true (North) step, y-coord increments -/
private lemma posAfter_true_succ (xs : LPath) (a i : ℕ) :
    posAfter (true :: xs) a (i + 1) = posAfter xs (a + 1) i := by
  simp only [posAfter, List.take_succ_cons, List.countP_cons]
  simp [Prod.ext_iff]; omega

/-- The set of lattice points visited by path l starting at (0, a) -/
def visitedPoints (l : LPath) (a : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (l.length + 1)).image (posAfter l a)

/-- Path l visits its starting point -/
theorem mem_visitedPoints_start (l : LPath) (a : ℕ) :
    (0, a) ∈ visitedPoints l a := by
  rw [← posAfter_zero l a]
  exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))

private lemma visitedPoints_cons_false_of_mem (xs : LPath) (a : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ visitedPoints xs a) :
    (p.1 + 1, p.2) ∈ visitedPoints (false :: xs) a := by
  simp only [visitedPoints, Finset.mem_image, Finset.mem_range] at hp ⊢
  obtain ⟨i, hi, hpi⟩ := hp
  exact ⟨i + 1, by simp [List.length_cons]; omega,
    by rw [posAfter_false_succ]; rw [← hpi]⟩

private lemma visitedPoints_cons_true_of_mem (xs : LPath) (a : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ visitedPoints xs (a + 1)) :
    p ∈ visitedPoints (true :: xs) a := by
  simp only [visitedPoints, Finset.mem_image, Finset.mem_range] at hp ⊢
  obtain ⟨i, hi, hpi⟩ := hp
  exact ⟨i + 1, by simp [List.length_cons]; omega,
    by rw [posAfter_true_succ]; exact hpi⟩

theorem visitedPoints_covers_column (l : LPath) (a : ℕ) (x y : ℕ)
    (hx : x < eastSteps l)
    (hy_lo : a + colEntry l x ≤ y) (hy_hi : y ≤ a + colEntry l (x + 1)) :
    (x, y) ∈ visitedPoints l a := by
  induction l generalizing a x y with
  | nil => simp [eastSteps, List.countP_nil] at hx
  | cons b xs ih =>
    cases b with
    | false =>
      have heast : eastSteps (false :: xs) = eastSteps xs + 1 := by
        simp [eastSteps, List.countP_cons]
      cases x with
      | zero =>
        -- colEntry (false :: xs) 0 = 0, colEntry (false :: xs) 1 = northBeforeEast (false::xs) 0 = 0
        have h0 : colEntry (false :: xs) 0 = 0 := rfl
        have h1 : colEntry (false :: xs) 1 = 0 := by simp [colEntry, northBeforeEast]
        have : y = a := by omega
        subst this
        exact mem_visitedPoints_start _ _
      | succ x' =>
        have hx' : x' < eastSteps xs := by omega
        have hlo : a + colEntry xs x' ≤ y := by
          have := colEntry_false_succ xs x'; omega
        have hhi : y ≤ a + colEntry xs (x' + 1) := by
          have := colEntry_false_succ xs (x' + 1); omega
        exact visitedPoints_cons_false_of_mem xs a (x', y) (ih a x' y hx' hlo hhi)
    | true =>
      have heast : eastSteps (true :: xs) = eastSteps xs := by
        simp [eastSteps, List.countP_cons]
      have hx' : x < eastSteps xs := by omega
      cases x with
      | zero =>
        have hce0 : colEntry (true :: xs) 0 = 0 := rfl
        have hce1 : colEntry (true :: xs) 1 = colEntry xs 1 + 1 := colEntry_true_succ xs 0
        have hce0' : colEntry xs 0 = 0 := rfl
        have hlo' : (a + 1) + colEntry xs 0 ≤ y := by omega
        have hhi' : y ≤ (a + 1) + colEntry xs 1 := by omega
        exact visitedPoints_cons_true_of_mem xs a (0, y) (ih (a + 1) 0 y hx' hlo' hhi')
      | succ x' =>
        have hce_lo : colEntry (true :: xs) (x' + 1) = colEntry xs (x' + 1) + 1 :=
          colEntry_true_succ xs x'
        have hce_hi : colEntry (true :: xs) (x' + 2) = colEntry xs (x' + 2) + 1 :=
          colEntry_true_succ xs (x' + 1)
        have hlo' : (a + 1) + colEntry xs (x' + 1) ≤ y := by omega
        have hhi' : y ≤ (a + 1) + colEntry xs (x' + 2) := by omega
        exact visitedPoints_cons_true_of_mem xs a (x' + 1, y)
          (ih (a + 1) (x' + 1) y hx' hlo' hhi')

theorem visitedPoints_covers_final (l : LPath) (a : ℕ) (y : ℕ)
    (hy_lo : a + colEntry l (eastSteps l) ≤ y) (hy_hi : y ≤ a + northSteps l) :
    (eastSteps l, y) ∈ visitedPoints l a := by
  induction l generalizing a y with
  | nil =>
    simp [eastSteps, List.countP_nil, colEntry, northSteps] at hy_lo hy_hi ⊢
    have : y = a := by omega
    subst this
    exact mem_visitedPoints_start _ _
  | cons b xs ih =>
    cases b with
    | false =>
      have heast : eastSteps (false :: xs) = eastSteps xs + 1 := by
        simp [eastSteps, List.countP_cons]
      have hnorth : northSteps (false :: xs) = northSteps xs := northSteps_cons_false xs
      have hce : colEntry (false :: xs) (eastSteps (false :: xs)) = colEntry xs (eastSteps xs) := by
        rw [heast]; exact colEntry_false_succ xs (eastSteps xs)
      have hlo' : a + colEntry xs (eastSteps xs) ≤ y := by omega
      have hhi' : y ≤ a + northSteps xs := by omega
      rw [heast]
      exact visitedPoints_cons_false_of_mem xs a (eastSteps xs, y) (ih a y hlo' hhi')
    | true =>
      have heast : eastSteps (true :: xs) = eastSteps xs := by
        simp [eastSteps, List.countP_cons]
      have hnorth : northSteps (true :: xs) = 1 + northSteps xs := northSteps_cons_true xs
      cases hm : eastSteps xs with
      | zero =>
        rw [heast, hm] at hy_lo ⊢
        simp [colEntry] at hy_lo
        have hhi' : y ≤ (a + 1) + northSteps xs := by omega
        have hlo' : (a + 1) + colEntry xs 0 ≤ y := by simp [colEntry]; omega
        exact visitedPoints_cons_true_of_mem xs a (0, y) (ih (a + 1) y hlo' hhi')
      | succ m' =>
        have hce : colEntry (true :: xs) (m' + 1) = colEntry xs (m' + 1) + 1 :=
          colEntry_true_succ xs m'
        rw [heast, hm] at hy_lo ⊢
        have hlo' : (a + 1) + colEntry xs (m' + 1) ≤ y := by
          rw [hce] at hy_lo; omega
        have hhi' : y ≤ (a + 1) + northSteps xs := by omega
        exact visitedPoints_cons_true_of_mem xs a (m' + 1, y) (ih (a + 1) y hlo' hhi')
