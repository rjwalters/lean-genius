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

This is the structural heart of the headline ("every node is a reduced positive
rational"). The two remaining directions — **surjectivity** (every reduced
positive rational labels some node) and **injectivity** (no rational labels two
nodes) — are stated as goals in the research notes; see `## Next steps`.

## Next steps (not in this file)

* Surjectivity: strong induction on `num + den` via the subtractive Euclidean
  descent (`a/b ↦ (a−b)/b` when `a > b`, mirror when `a < b`).
* Injectivity: the mediant strictly separates the two subtrees, so the labelled
  value is strictly monotone along the in-order traversal.
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

end SternBrocot
