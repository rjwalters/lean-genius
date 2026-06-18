import Mathlib

/-!
# Stern–Brocot tree: every node is a positive rational in lowest terms

**Open Question (`stern-brocot-tree-oq-01`)**: the Stern–Brocot tree enumerates
every positive rational exactly once, in lowest terms. Mathlib has **no**
Stern–Brocot tree, mediant, or Farey-sequence development (verified against the
v4.26 checkout), so this file builds the structure from scratch.

## What is proved here (self-contained, pure `ℤ` arithmetic, `0` sorries)

A node of the tree is addressed by a finite path `p : List Bool` of left/right
moves (`false = L`, `true = R`). Following a path maintains the pair of
*boundary fractions* `aL/bL < aR/bR` of the current interval, starting from the
super-interval `0/1 < 1/0`. A left move replaces the right boundary by the
*mediant* `(aL+aR)/(bL+bR)`, a right move replaces the left boundary by it. The
fraction *labelling* a node is the mediant of its current boundaries.

* `sb_det` — the **unimodular invariant** `aL·bR − aR·bL = −1` holds at every
  node (induction over the path; both moves preserve it).
* `sb_pos` — the **positivity invariant** `0 ≤ aL`, `1 ≤ aR`, `1 ≤ bL`, `0 ≤ bR`.
* `sbNum_pos`, `sbDen_pos` — consequently the label `sbNum/sbDen` is a genuine
  **positive** rational (`1 ≤ sbNum`, `1 ≤ sbDen`).
* `sb_isCoprime` — the label is in **lowest terms**: `IsCoprime (sbNum p) (sbDen p)`,
  with the explicit Bézout witness `(-bR)·num + aR·den = 1` extracted from the
  unimodular invariant.
* `sb_root` — the root (empty path) is labelled `1/1`.

Beyond the structural heart, this file now also proves:

* `sb_left_lt_mediant`, `sb_mediant_lt_right` — **mediant separation**: the label
  lies strictly between the two boundary fractions (division-free integer form),
  both reducing to `sb_det`. This is the foundation for injectivity.
* `sb_false_cons`, `sb_true_cons` and the four `sb{Num,Den}_{false,true}_cons`
  **prefix-transfer** lemmas: prepending `L` sends `(num, den) ↦ (num, num+den)`,
  prepending `R` sends `(num, den) ↦ (num+den, den)` — via the conjugation
  homomorphisms `T`, `T'` that intertwine the two boundary folds.
* `sb_surjective` — **surjectivity**: every reduced positive rational `a/b` labels
  some node, by strong induction on `a + b` via the subtractive Euclidean descent.
* `sb_injective` — **injectivity**: a path is determined by its label. The sign of
  `num − den` recovers the first move (`L ⟹ num < den`, `R ⟹ num > den`, root
  `⟹ num = den = 1`) via the transfer lemmas, so a structural induction on the path
  forces equality.
* `sb_bijection` — **the full bijection** (this OQ): `(a, b)` is a reduced positive
  rational `⟺` it is the label of a *unique* Stern–Brocot path. Combines
  surjectivity, injectivity, positivity, and lowest terms.
-/

namespace SternBrocot

/-- A node of the Stern–Brocot tree, stored as its pair of boundary fractions
`aL/bL` (left) and `aR/bR` (right). -/
structure SB where
  aL : ℤ
  bL : ℤ
  aR : ℤ
  bR : ℤ
  deriving Repr, DecidableEq

/-- The super-interval `0/1 < 1/0` at the root of the construction. -/
def SB.start : SB := ⟨0, 1, 1, 0⟩

/-- One move: `false` (L) replaces the right boundary by the mediant,
`true` (R) replaces the left boundary by the mediant. -/
def SB.step (s : SB) : Bool → SB
  | false => ⟨s.aL, s.bL, s.aL + s.aR, s.bL + s.bR⟩
  | true  => ⟨s.aL + s.aR, s.bL + s.bR, s.aR, s.bR⟩

/-- The boundary state reached by following a path `p` from a starting state. -/
def sbFrom (s : SB) (p : List Bool) : SB := p.foldl SB.step s

@[simp] theorem sbFrom_nil (s : SB) : sbFrom s [] = s := rfl

@[simp] theorem sbFrom_cons (s : SB) (b : Bool) (p : List Bool) :
    sbFrom s (b :: p) = sbFrom (s.step b) p := rfl

/-- The boundary state reached by following a path from the root. -/
def sb (p : List Bool) : SB := sbFrom SB.start p

/-- The numerator labelling a node: the mediant numerator `aL + aR`. -/
def sbNum (p : List Bool) : ℤ := (sb p).aL + (sb p).aR

/-- The denominator labelling a node: the mediant denominator `bL + bR`. -/
def sbDen (p : List Bool) : ℤ := (sb p).bL + (sb p).bR

/-! ## Unimodular invariant -/

/-- The unimodular invariant `aL·bR − aR·bL = −1`, as a predicate on states. -/
def Unimod (s : SB) : Prop := s.aL * s.bR - s.aR * s.bL = -1

theorem unimod_start : Unimod SB.start := by
  simp [Unimod, SB.start]

theorem unimod_step {s : SB} (h : Unimod s) (b : Bool) : Unimod (s.step b) := by
  cases b
  · simp only [Unimod, SB.step] at h ⊢; linear_combination h
  · simp only [Unimod, SB.step] at h ⊢; linear_combination h

theorem unimod_sbFrom :
    ∀ (s : SB), Unimod s → ∀ (p : List Bool), Unimod (sbFrom s p) := by
  intro s h p
  induction p generalizing s with
  | nil => simpa using h
  | cons b t ih => simpa using ih (s.step b) (unimod_step h b)

/-- **Unimodular invariant**: at every Stern–Brocot node, `aL·bR − aR·bL = −1`. -/
theorem sb_det (p : List Bool) :
    (sb p).aL * (sb p).bR - (sb p).aR * (sb p).bL = -1 := by
  have h : Unimod (sb p) := unimod_sbFrom SB.start unimod_start p
  exact h

/-! ## Positivity invariant -/

/-- The positivity invariant `0 ≤ aL`, `1 ≤ aR`, `1 ≤ bL`, `0 ≤ bR`. -/
def Pos (s : SB) : Prop := 0 ≤ s.aL ∧ 1 ≤ s.aR ∧ 1 ≤ s.bL ∧ 0 ≤ s.bR

theorem pos_start : Pos SB.start := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [SB.start]

theorem pos_step {s : SB} (h : Pos s) (b : Bool) : Pos (s.step b) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases b
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [SB.step] <;> linarith
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [SB.step] <;> linarith

theorem pos_sbFrom :
    ∀ (s : SB), Pos s → ∀ (p : List Bool), Pos (sbFrom s p) := by
  intro s h p
  induction p generalizing s with
  | nil => simpa using h
  | cons b t ih => simpa using ih (s.step b) (pos_step h b)

/-- **Positivity invariant** at every node. -/
theorem sb_pos (p : List Bool) : Pos (sb p) := pos_sbFrom SB.start pos_start p

/-- The label numerator is a positive integer. -/
theorem sbNum_pos (p : List Bool) : 1 ≤ sbNum p := by
  obtain ⟨h1, h2, _, _⟩ := sb_pos p
  simp only [sbNum]; linarith

/-- The label denominator is a positive integer. -/
theorem sbDen_pos (p : List Bool) : 1 ≤ sbDen p := by
  obtain ⟨_, _, h3, h4⟩ := sb_pos p
  simp only [sbDen]; linarith

/-! ## Lowest terms -/

/-- **Lowest terms**: every node's label `sbNum p / sbDen p` is reduced.
The Bézout witness `(-bR)·num + aR·den = 1` comes straight from `sb_det`. -/
theorem sb_isCoprime (p : List Bool) : IsCoprime (sbNum p) (sbDen p) := by
  refine ⟨-(sb p).bR, (sb p).aR, ?_⟩
  have h := sb_det p
  simp only [sbNum, sbDen]
  linear_combination -h

/-- The root of the tree is labelled `1/1`. -/
theorem sb_root : sbNum [] = 1 ∧ sbDen [] = 1 := by
  refine ⟨?_, ?_⟩ <;> simp [sbNum, sbDen, sb, SB.start]

/-! ## Mediant separation (foundation for injectivity)

The label of a node lies *strictly* between its two boundary fractions. In
cross-multiplied (division-free) integer form, with `bL, bR ≥ 1 > 0`:

* `aL/bL < num/den` ⟺ `aL·den < num·bL`,
* `num/den < aR/bR` ⟺ `num·bR < aR·den`.

Both reduce, after expansion, to `aL·bR − aR·bL = −1 < 0`, i.e. exactly the
unimodular invariant `sb_det`. This strict separation is the key fact behind
injectivity: distinct subtrees occupy disjoint open intervals.
-/

/-- The label strictly exceeds the left boundary: `aL·den < num·bL`. -/
theorem sb_left_lt_mediant (p : List Bool) :
    (sb p).aL * sbDen p < sbNum p * (sb p).bL := by
  have h := sb_det p
  simp only [sbNum, sbDen]
  nlinarith [h]

/-- The label is strictly below the right boundary: `num·bR < aR·den`. -/
theorem sb_mediant_lt_right (p : List Bool) :
    sbNum p * (sb p).bR < (sb p).aR * sbDen p := by
  have h := sb_det p
  simp only [sbNum, sbDen]
  nlinarith [h]

/-! ## Surjectivity: every reduced positive rational labels some node

We show the labelling map `p ↦ sbNum p / sbDen p` hits **every** reduced
positive rational. The proof is a strong induction on `num + den` driven by the
subtractive Euclidean descent (`a/b ↦ (a−b)/b` when `a > b`, mirror when `a < b`),
using two *prefix-transfer* lemmas that describe how prepending a single move
transforms the label:

* prepending `L` (`false`):  `(num, den) ↦ (num, num + den)`;
* prepending `R` (`true`):   `(num, den) ↦ (num + den, den)`.

These are proved via the conjugation homomorphisms `T`, `T'` that intertwine the
two boundary folds — `T` (resp. `T'`) is left-multiplication by the generator
that the leading move contributes, and it commutes with `SB.step`.
-/

/-- `L`-conjugation: left-multiplication by `[[1,0],[1,1]]` on the boundary
state. Intertwines the fold started at `start.step false` with the one at
`start`. -/
def T (s : SB) : SB := ⟨s.aL, s.aL + s.bL, s.aR, s.aR + s.bR⟩

/-- `R`-conjugation: left-multiplication by `[[1,1],[0,1]]`. -/
def T' (s : SB) : SB := ⟨s.aL + s.bL, s.bL, s.aR + s.bR, s.bR⟩

theorem T_step (s : SB) (b : Bool) : (T s).step b = T (s.step b) := by
  cases b <;> cases s <;> simp only [T, SB.step, SB.mk.injEq] <;> omega

theorem T'_step (s : SB) (b : Bool) : (T' s).step b = T' (s.step b) := by
  cases b <;> cases s <;> simp only [T', SB.step, SB.mk.injEq] <;> omega

theorem T_sbFrom (s : SB) (q : List Bool) : sbFrom (T s) q = T (sbFrom s q) := by
  induction q generalizing s with
  | nil => simp only [sbFrom_nil]
  | cons b t ih => rw [sbFrom_cons, T_step, ih (s.step b), sbFrom_cons]

theorem T'_sbFrom (s : SB) (q : List Bool) :
    sbFrom (T' s) q = T' (sbFrom s q) := by
  induction q generalizing s with
  | nil => simp only [sbFrom_nil]
  | cons b t ih => rw [sbFrom_cons, T'_step, ih (s.step b), sbFrom_cons]

/-- Prepending an `L` move conjugates the boundary state by `T`. -/
theorem sb_false_cons (q : List Bool) : sb (false :: q) = T (sb q) := by
  show sbFrom SB.start (false :: q) = T (sbFrom SB.start q)
  rw [sbFrom_cons, show SB.start.step false = T SB.start from by decide, T_sbFrom]

/-- Prepending an `R` move conjugates the boundary state by `T'`. -/
theorem sb_true_cons (q : List Bool) : sb (true :: q) = T' (sb q) := by
  show sbFrom SB.start (true :: q) = T' (sbFrom SB.start q)
  rw [sbFrom_cons, show SB.start.step true = T' SB.start from by decide, T'_sbFrom]

/-- `L`-transfer for the numerator: `num (L :: q) = num q`. -/
theorem sbNum_false_cons (q : List Bool) : sbNum (false :: q) = sbNum q := by
  simp only [sbNum, sb_false_cons, T]

/-- `L`-transfer for the denominator: `den (L :: q) = num q + den q`. -/
theorem sbDen_false_cons (q : List Bool) : sbDen (false :: q) = sbNum q + sbDen q := by
  simp only [sbDen, sbNum, sb_false_cons, T]; ring

/-- `R`-transfer for the numerator: `num (R :: q) = num q + den q`. -/
theorem sbNum_true_cons (q : List Bool) : sbNum (true :: q) = sbNum q + sbDen q := by
  simp only [sbNum, sbDen, sb_true_cons, T']; ring

/-- `R`-transfer for the denominator: `den (R :: q) = den q`. -/
theorem sbDen_true_cons (q : List Bool) : sbDen (true :: q) = sbDen q := by
  simp only [sbDen, sb_true_cons, T']

/-- Auxiliary strong-induction form of surjectivity, recursing on `num + den`. -/
theorem sb_surj_aux : ∀ (n : ℕ) (a b : ℤ), (a + b).toNat = n →
    1 ≤ a → 1 ≤ b → IsCoprime a b →
    ∃ p : List Bool, sbNum p = a ∧ sbDen p = b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn ha hb hcop
    rcases lt_trichotomy a b with hab | hab | hab
    · -- a < b : the value is < 1, descend via the left child to (a, b − a)
      have hcop' : IsCoprime a (b - a) := by
        have hb' : IsCoprime b a := hcop.symm
        rw [show b = (b - a) + a * 1 from by ring] at hb'
        exact (IsCoprime.of_add_mul_left_left hb').symm
      obtain ⟨q, hq1, hq2⟩ :=
        ih b.toNat (by omega) a (b - a) (by omega) ha (by omega) hcop'
      refine ⟨false :: q, ?_, ?_⟩
      · rw [sbNum_false_cons, hq1]
      · rw [sbDen_false_cons, hq1, hq2]; ring
    · -- a = b : coprimality forces a = b = 1, the root
      rw [← hab] at hcop
      have hu : IsUnit a := isCoprime_self.mp hcop
      rcases Int.isUnit_iff.mp hu with h1 | h1
      · refine ⟨[], ?_, ?_⟩
        · rw [sb_root.1, h1]
        · rw [sb_root.2, ← hab, h1]
      · subst h1; exact absurd ha (by norm_num)
    · -- b < a : the value is > 1, descend via the right child to (a − b, b)
      have hcop' : IsCoprime (a - b) b := by
        rw [show a = (a - b) + b * 1 from by ring] at hcop
        exact IsCoprime.of_add_mul_left_left hcop
      obtain ⟨q, hq1, hq2⟩ :=
        ih a.toNat (by omega) (a - b) b (by omega) (by omega) hb hcop'
      refine ⟨true :: q, ?_, ?_⟩
      · rw [sbNum_true_cons, hq1, hq2]; ring
      · rw [sbDen_true_cons, hq2]

/-- **Surjectivity**: every reduced positive rational `a/b` (with `1 ≤ a`,
`1 ≤ b`, `IsCoprime a b`) is the label of some Stern–Brocot node. -/
theorem sb_surjective (a b : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcop : IsCoprime a b) : ∃ p : List Bool, sbNum p = a ∧ sbDen p = b :=
  sb_surj_aux (a + b).toNat a b rfl ha hb hcop

/-! ## Injectivity: distinct paths carry distinct labels

The comparison of `sbNum p` against `sbDen p` recovers the *first* move of `p`.
By the transfer lemmas, with `1 ≤ sbNum`, `1 ≤ sbDen` everywhere:

* prepending `L` (`false`) gives `(num, den) ↦ (num, num + den)`, so `num < den`;
* prepending `R` (`true`)  gives `(num, den) ↦ (num + den, den)`, so `num > den`;
* the root `[]` is the unique node with `num = den = 1`.

Hence two paths with the same label must agree on their first move; stripping it
off and recursing (a structural induction on the path) forces the whole paths to
coincide. No interval/order machinery is needed — the sign of `num − den` alone
pins down each step.
-/

/-- **Injectivity**: a Stern–Brocot path is uniquely determined by its label.
If two paths carry the same numerator *and* denominator, they are equal. -/
theorem sb_injective : ∀ (p q : List Bool),
    sbNum p = sbNum q → sbDen p = sbDen q → p = q := by
  intro p
  induction p with
  | nil =>
    intro q hn hd
    have h1 := sb_root.1
    have h2 := sb_root.2
    cases q with
    | nil => rfl
    | cons c q' =>
      exfalso
      have hnq := sbNum_pos q'
      have hdq := sbDen_pos q'
      cases c with
      | false =>
        rw [sbNum_false_cons] at hn
        rw [sbDen_false_cons] at hd
        omega
      | true =>
        rw [sbNum_true_cons] at hn
        rw [sbDen_true_cons] at hd
        omega
  | cons b p' ih =>
    intro q hn hd
    have hnp := sbNum_pos p'
    have hdp := sbDen_pos p'
    cases b with
    | false =>
      cases q with
      | nil =>
        exfalso
        have h2 := sb_root.2
        rw [sbDen_false_cons] at hd
        omega
      | cons c q' =>
        have hnq := sbNum_pos q'
        have hdq := sbDen_pos q'
        cases c with
        | false =>
          rw [sbNum_false_cons, sbNum_false_cons] at hn
          rw [sbDen_false_cons, sbDen_false_cons] at hd
          have hd' : sbDen p' = sbDen q' := by omega
          rw [ih q' hn hd']
        | true =>
          exfalso
          rw [sbNum_false_cons, sbNum_true_cons] at hn
          rw [sbDen_false_cons, sbDen_true_cons] at hd
          omega
    | true =>
      cases q with
      | nil =>
        exfalso
        have h1 := sb_root.1
        rw [sbNum_true_cons] at hn
        omega
      | cons c q' =>
        have hnq := sbNum_pos q'
        have hdq := sbDen_pos q'
        cases c with
        | false =>
          exfalso
          rw [sbNum_true_cons, sbNum_false_cons] at hn
          rw [sbDen_true_cons, sbDen_false_cons] at hd
          omega
        | true =>
          rw [sbNum_true_cons, sbNum_true_cons] at hn
          rw [sbDen_true_cons, sbDen_true_cons] at hd
          have hn' : sbNum p' = sbNum q' := by omega
          rw [ih q' hn' hd]

/-! ## The full bijection -/

/-- **Full bijection** (the open question, now settled): a pair `(a, b)` of
integers is a reduced positive rational *if and only if* it is the label of a
**unique** Stern–Brocot path. Forward direction packages surjectivity
(`sb_surjective`) with injectivity (`sb_injective`); the reverse repackages
positivity (`sbNum_pos`, `sbDen_pos`) and lowest terms (`sb_isCoprime`). -/
theorem sb_bijection (a b : ℤ) :
    (1 ≤ a ∧ 1 ≤ b ∧ IsCoprime a b) ↔
      ∃! p : List Bool, sbNum p = a ∧ sbDen p = b := by
  constructor
  · rintro ⟨ha, hb, hcop⟩
    obtain ⟨p, hp1, hp2⟩ := sb_surjective a b ha hb hcop
    refine ⟨p, ⟨hp1, hp2⟩, ?_⟩
    rintro q ⟨hq1, hq2⟩
    exact sb_injective q p (by rw [hq1, hp1]) (by rw [hq2, hp2])
  · rintro ⟨p, ⟨hp1, hp2⟩, _⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hp1]; exact sbNum_pos p
    · rw [← hp2]; exact sbDen_pos p
    · rw [← hp1, ← hp2]; exact sb_isCoprime p

end SternBrocot
