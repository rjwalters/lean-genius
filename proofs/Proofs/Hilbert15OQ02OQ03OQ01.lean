import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Proofs.Hilbert15OQ02OQ03

/-!
# Hilbert 15 OQ-02 OQ-03 OQ-01: Combinatorial `lrCoeffN` Scaffold
# (hilbert-15-oq-02-oq-03-oq-01)

## The Goal

Replace the parent file's `axiom lrCoeffN : Partition n → Partition n → Partition n → ℕ`
(`Hilbert15OQ02OQ03.lean:128`) with a concrete computable definition

```
lrCoeffN_def ν λ μ :=
  #{ T : SkewSSYTFin n ν μ // content T = λ ∧ isLatticeWord (reverseRowWord T) }
```

following the classical Littlewood-Richardson rule (Littlewood 1934; Fulton
1997 Ch. 5; Macdonald 1995 §I.9). This file provides the **S2 scaffold**:
five definitions plus the `Decidable` / `Fintype` instances needed to keep
the parent file's `decide`-based `lr_polytime_positivity` going through.

## Contents (S2)

1. `Hilbert15OQ02OQ03.Partition.Subset` — containment relation `μ ⊆ ν` on
   `Partition n`, with `HasSubset` and `Decidable` instances.
2. `SkewSSYTFin n ν μ` — semistandard skew Young tableau filling
   `(i, j)` with `j ∈ [μ.parts i, ν.parts i)` by a value in `Fin n`,
   satisfying row-weak and (skew) column-strict (column index =
   `μ.parts i + j.val`). `Fintype` by `Subtype.fintype` since the
   underlying function space is a `Pi` over finite types.
3. `SkewSSYTFin.content T k` — count of cells of `T` filled with value
   `k : Fin n`. Returns `ℕ` (not `Partition n`) since for a generic
   skew SSYT the count vector need not be weakly decreasing — only
   after restriction to lattice words does sortedness emerge.
4. `SkewSSYTFin.reverseRowWord T` — Fulton-convention reading word:
   each row read **right-to-left**, rows in order **top-to-bottom**.
   Returns `List (Fin n)`. (Stanley reads bottom-to-top; the parent's
   `lrCoeff2` follows Fulton — see `Hilbert15OQ02.lean:131`.)
5. `isLatticeWord w` — at every prefix and every pair `k < k'`, the
   count of `k'` is bounded by the count of `k`. Synonyms: ballot
   word; Yamanouchi word. `Decidable` since the universal can be
   bounded by `Fin (w.length + 1)`.
6. `lrCoeffN_def ν λ μ : ℕ` — the LR count, guarded by the standard
   well-definedness condition `μ ⊆ ν ∧ ν.weight = λ.weight + μ.weight`.
   `Decidable (0 < lrCoeffN_def ν λ μ)` follows from `Nat.decLt`.

## Deferred (S3, S4, S5+)

* **S3 — 2-row anchoring lemma.** Prove
  `lrCoeffN_def_two_eq_lrCoeff2 : ∀ (ν λ μ : Partition 2),
      lrCoeffN_def ν λ μ = lrCoeff2 (toListPair ν) (toListPair λ) (toListPair μ)`
  against the 7 Gr(2,4) Chow ring constants verified in
  `Hilbert15OQ01.lean`. This is the smoke check that the abstract count
  reduces to the existing computable case.

* **S4 — Parent axiom replacement.** Refactor
  `Hilbert15OQ02OQ03.lean:128` from `axiom lrCoeffN` to
  `def lrCoeffN := Hilbert15OQ02OQ03OQ01.lrCoeffN_def`; verify
  `klyachko_theorem` and `lr_polytime_positivity` still typecheck.

* **S5+ — OQ-02 / OQ-03 proper.** Once the axiom is removed, the
  full Klyachko/Horn-inequalities chain in
  `Hilbert15OQ02OQ03.lean:160` can be re-examined; the `admissible`
  axiom remains but is now stated against a concrete `lrCoeffN`.

## Build status

The pinned Mathlib (`v4.26.0`) lacks `SemistandardYoungTableau`, skew
shape encoding, reverse row reading word, and the lattice-word
predicate. All five S2 declarations are pure Mathlib wrappers over
`Finset`, `List`, `Fin`, and `Subtype.fintype`; no auxiliary
infrastructure is introduced. Per the established Hilbert-15 PR
convention this scaffold ships as `(build pending)` since the parent
`Hilbert15OQ02OQ03.lean` is on `origin/main` and the per-file Docker
build is deferred to CI.

## References

* Fulton, W. (1997). *Young Tableaux* (LMS Student Texts 35),
  Cambridge University Press. Chapter 5: "The Littlewood-Richardson
  rule."
* Stanley, R.P. (1999). *Enumerative Combinatorics* Vol. 2, Cambridge
  University Press. Appendix 1 (A.1.3) — reading words and Yamanouchi
  sequences.
* Macdonald, I.G. (1995). *Symmetric Functions and Hall Polynomials*
  (2nd ed.). Oxford University Press. §I.9 "The Littlewood-Richardson
  rule."
* Knutson, A. & Tao, T. (1999). The honeycomb model of `GL_n` tensor
  products I. *J. Amer. Math. Soc.* **12**(4), 1055-1090.
-/

namespace Hilbert15OQ02OQ03OQ01

open Hilbert15OQ02OQ03

/-! ## Part I: Partition Containment (`μ ⊆ ν`) -/

/-- **Pointwise containment of partitions.** `μ ⊆ ν` iff every part of
    `μ` is at most the corresponding part of `ν`. This is the
    standard "Young diagram of `μ` fits inside the Young diagram of
    `ν`" relation; combined with `ν.weight = λ.weight + μ.weight` it
    is the well-definedness condition for the skew shape `ν / μ` of
    content `λ`. -/
def Partition.Subset {n : ℕ} (μ ν : Partition n) : Prop :=
  ∀ i : Fin n, μ.parts i ≤ ν.parts i

instance {n : ℕ} : HasSubset (Partition n) := ⟨Partition.Subset⟩

instance {n : ℕ} (μ ν : Partition n) : Decidable (μ ⊆ ν) :=
  inferInstanceAs (Decidable (∀ i : Fin n, μ.parts i ≤ ν.parts i))

/-! ## Part II: Skew Semistandard Young Tableaux -/

/-- A **semistandard skew Young tableau** of outer shape `ν` and inner
    shape `μ` with entries in `Fin n`, encoded as a function on the
    sigma-type `(i : Fin n) × Fin (ν.parts i - μ.parts i)` (cell in
    row `i`, **inner-relative** column index `j`).

    The **column index** of the cell `(i, j)` in the ambient
    Young-diagram coordinate system is `μ.parts i + j.val` (the
    inner shape's row-`i` length, plus the `j`-offset into the skew
    strip). Truncated subtraction in `ν.parts i - μ.parts i` gives
    the natural empty type when `μ.parts i > ν.parts i`, which is
    why no containment hypothesis is required here.

    Conditions:

    * **Row-weak**: along each row, entries are weakly increasing.
    * **Skew column-strict**: entries with the same ambient column
      index `μ.parts i₁ + j₁.val = μ.parts i₂ + j₂.val` and `i₁ < i₂`
      are strictly increasing.

    Modelled on `BallotProblemOQ03OQ01OQ01OQ01.SSYTFin n k sh` (line
    177), generalised from straight shapes `sh : Fin k → ℕ` to skew
    shapes `(ν, μ)`. -/
def SkewSSYTFin (n : ℕ) (ν μ : Partition n) :=
  { f : ((i : Fin n) × Fin (ν.parts i - μ.parts i)) → Fin n //
    -- Rows are weakly increasing (entries non-decreasing left to right within the skew strip)
    (∀ (i : Fin n) (j₁ j₂ : Fin (ν.parts i - μ.parts i)),
      j₁ < j₂ → f ⟨i, j₁⟩ ≤ f ⟨i, j₂⟩) ∧
    -- Columns are strictly increasing under the **ambient** column index
    -- `μ.parts i + j.val`, which is the correct skew-tableau column key.
    (∀ (i₁ i₂ : Fin n)
       (j₁ : Fin (ν.parts i₁ - μ.parts i₁))
       (j₂ : Fin (ν.parts i₂ - μ.parts i₂)),
      μ.parts i₁ + j₁.val = μ.parts i₂ + j₂.val → i₁ < i₂ →
      f ⟨i₁, j₁⟩ < f ⟨i₂, j₂⟩) }

instance {n : ℕ} {ν μ : Partition n} : Fintype (SkewSSYTFin n ν μ) :=
  Subtype.fintype _

/-- **Content of a skew SSYT** — the count of cells filled with each
    value. `content T k` = number of cells `(i, j)` with `T ⟨i, j⟩ = k`.

    Returns `Fin n → ℕ` (not `Partition n`): for a generic skew SSYT
    the count vector need not be weakly decreasing. Only the
    sub-family of *lattice-word* skew SSYT carries content that is
    naturally a partition (this is part of why the Littlewood-
    Richardson rule restricts to lattice / Yamanouchi reading
    words). -/
def SkewSSYTFin.content {n : ℕ} {ν μ : Partition n}
    (T : SkewSSYTFin n ν μ) (k : Fin n) : ℕ :=
  (Finset.univ.filter
    (fun p : (i : Fin n) × Fin (ν.parts i - μ.parts i) => T.1 p = k)).card

/-! ## Part III: Reverse Row Reading Word (Fulton Convention) -/

/-- **Reverse row reading word** (Fulton 1997 Ch. 5 convention):
    each row of `T` is read **right-to-left**, and rows are
    enumerated **top-to-bottom** (`i = 0` first).

    Matches the convention used by the gallery's existing
    `lrCoeff2` in `Hilbert15OQ02.lean:131` (verified against the 7
    Gr(2,4) Chow ring constants from `Hilbert15OQ01.lean`).

    Stanley (EC v.2 A.1.3) uses the opposite vertical order
    (bottom-to-top). We commit to Fulton here for consistency with
    the 2-row anchor. -/
def SkewSSYTFin.reverseRowWord {n : ℕ} {ν μ : Partition n}
    (T : SkewSSYTFin n ν μ) : List (Fin n) :=
  (List.finRange n).flatMap (fun i =>
    ((List.finRange (ν.parts i - μ.parts i)).reverse).map
      (fun j => T.1 ⟨i, j⟩))

/-! ## Part IV: Lattice (Ballot / Yamanouchi) Word Predicate -/

/-- **Lattice word predicate.** A word `w : List (Fin n)` is a
    *lattice word* (equivalently: ballot word, Yamanouchi word) if
    at every prefix and every pair `k < k'`, the count of `k'` is
    bounded by the count of `k`.

    Restricting the universal to `p : Fin (w.length + 1)` makes the
    predicate decidable; the unbounded version (`∀ p : ℕ`) is
    equivalent since `w.take p = w` for `p ≥ w.length`. -/
def isLatticeWord {n : ℕ} (w : List (Fin n)) : Prop :=
  ∀ p : Fin (w.length + 1), ∀ k k' : Fin n, k < k' →
    (w.take p.val).count k' ≤ (w.take p.val).count k

instance {n : ℕ} (w : List (Fin n)) : Decidable (isLatticeWord w) :=
  inferInstanceAs (Decidable
    (∀ p : Fin (w.length + 1), ∀ k k' : Fin n, k < k' →
      (w.take p.val).count k' ≤ (w.take p.val).count k))

/-! ## Part V: `lrCoeffN_def` — the Computable LR Coefficient -/

/-- **Computable LR coefficient** (Littlewood 1934; Fulton 1997
    Ch. 5 §2). The Littlewood-Richardson coefficient `c^ν_{λ,μ}` is
    the number of skew SSYT of shape `ν / μ` whose content is `λ`
    and whose reverse row reading word is a lattice word.

    Outside the well-definedness range `μ ⊆ ν ∧ ν.weight = λ.weight +
    μ.weight` the coefficient is `0` by convention (no skew shape
    exists, or no content of the prescribed total can fit). The `if`
    guard makes the function definitionally `0` in those cases and
    keeps the count finite and decidable.

    Designed to be `def`-equal to (and ultimately replace) the
    parent file's `axiom lrCoeffN` at
    `Hilbert15OQ02OQ03.lean:128`. The replacement is deferred to
    S4 once the 2-row anchoring lemma (S3) has been proved. -/
def lrCoeffN_def {n : ℕ} (ν lam μ : Partition n) : ℕ :=
  if μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight then
    Fintype.card { T : SkewSSYTFin n ν μ //
                   (∀ k : Fin n, T.content k = lam.parts k) ∧
                   isLatticeWord T.reverseRowWord }
  else 0

instance {n : ℕ} (ν lam μ : Partition n) : Decidable (0 < lrCoeffN_def ν lam μ) :=
  Nat.decLt _ _

/-- **Symmetric pruning lemma**: `lrCoeffN_def` vanishes outside the
    LR support `μ ⊆ ν ∧ ν.weight = λ.weight + μ.weight`. Direct from
    the `if`-guard in the definition; useful for `simp` rewriting in
    downstream proofs. -/
@[simp] theorem lrCoeffN_def_eq_zero_of_not_support {n : ℕ}
    (ν lam μ : Partition n)
    (h : ¬ (μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight)) :
    lrCoeffN_def ν lam μ = 0 := by
  unfold lrCoeffN_def
  exact if_neg h

/-! ## Part VI: 2-Row Anchor — Translation (S3a)

The S2 scaffold's `lrCoeffN_def` is parameterised by `Partition n`.
The existing `LRComplexity.lrCoeff2` (Hilbert15OQ02.lean:131) is
parameterised by the specialised 2-row encoding `LRComplexity.Partition2`
(a triple `(a, b, dec : b ≤ a)`).

To state the S3 anchoring lemma we need a translation
`Partition 2 → LRComplexity.Partition2`. The translation is the
obvious one — `parts 0` and `parts 1` are weakly decreasing by the
`sorted` field — and is bookkeeping rather than mathematics. We
also record the corresponding `size`/`weight` and containment-iff
equivalences as `@[simp]` lemmas so the S3b proof reduces to a pure
combinatorial argument on `Partition2` data.
-/

open LRComplexity in
/-- **Translation `Partition 2 → LRComplexity.Partition2`.** Sends
    the general n-row encoding to the specialised 2-row encoding
    used by `lrCoeff2`. The witness `p.sorted 0 1 (by decide)`
    discharges the `Partition2.dec : b ≤ a` field. -/
def toPartition2 (p : Partition 2) : Partition2 :=
  ⟨p.parts 0, p.parts 1, p.sorted 0 1 (by decide)⟩

@[simp] theorem toPartition2_a (p : Partition 2) :
    (toPartition2 p).a = p.parts 0 := rfl

@[simp] theorem toPartition2_b (p : Partition 2) :
    (toPartition2 p).b = p.parts 1 := rfl

/-- **Size = weight.** The specialised 2-row size matches the
    general partition weight on `Partition 2`. Direct from
    `Fin.sum_univ_two`. -/
@[simp] theorem toPartition2_size (p : Partition 2) :
    (toPartition2 p).size = p.weight := by
  simp only [LRComplexity.Partition2.size, toPartition2_a, toPartition2_b,
             Partition.weight, Fin.sum_univ_two]

/-- **Containment iff.** The specialised `Partition2.contains` and
    the general `Partition.Subset` agree under `toPartition2`. -/
@[simp] theorem toPartition2_contains_iff (ν μ : Partition 2) :
    LRComplexity.Partition2.contains (toPartition2 ν) (toPartition2 μ) ↔ μ ⊆ ν := by
  simp only [LRComplexity.Partition2.contains, toPartition2_a, toPartition2_b]
  refine ⟨?_, ?_⟩
  · rintro ⟨h0, h1⟩
    show ∀ i : Fin 2, μ.parts i ≤ ν.parts i
    intro i
    fin_cases i
    · exact h0
    · exact h1
  · intro h
    refine ⟨?_, ?_⟩
    · exact h 0
    · exact h 1

/-! ## Part VII: 2-Row Anchor — Out-of-Support Discharge (S3b) -/

/-- **`lrCoeff2` vanishes outside the LR support.** The closed-form
    2-row LR coefficient `lrCoeff2 (toPartition2 ν) (toPartition2 lam)
    (toPartition2 μ)` is `0` whenever the support guard
    `μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight` fails. Mirrors
    `lrCoeffN_def_eq_zero_of_not_support` on the abstract count
    side and is the RHS half of the out-of-support case in
    `lrCoeffN_def_two_eq_lrCoeff2`.

    Proof: `lrCoeff2`'s definition is a chain of `if`-guards. The
    first guard is `¬ (μ.a ≤ ν.a ∧ μ.b ≤ ν.b)`, which translates
    via `toPartition2_contains_iff` to `¬ (μ ⊆ ν)`. The second
    guard is `ν.size ≠ λ.size + μ.size`, which translates via
    `toPartition2_size` to `ν.weight ≠ lam.weight + μ.weight`. One
    of the two must hold by hypothesis, so the chain bottoms out
    at `0`. -/
theorem lrCoeff2_eq_zero_of_not_support (ν lam μ : Partition 2)
    (h : ¬ (μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight)) :
    LRComplexity.lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ) = 0 := by
  push_neg at h
  unfold LRComplexity.lrCoeff2
  by_cases hsub : μ ⊆ ν
  · -- Containment holds, so the first `if ¬(...) then 0` guard is FALSE.
    -- The size mismatch then closes the second guard.
    have hcont_p2 :
        (toPartition2 μ).a ≤ (toPartition2 ν).a ∧
        (toPartition2 μ).b ≤ (toPartition2 ν).b := by
      simp only [toPartition2_a, toPartition2_b]
      exact ⟨hsub 0, hsub 1⟩
    have hsz_p2 :
        (toPartition2 ν).size ≠
          (toPartition2 lam).size + (toPartition2 μ).size := by
      simp only [toPartition2_size]
      exact h hsub
    rw [if_neg (not_not_intro hcont_p2), if_pos hsz_p2]
  · -- Containment fails, so the first `if ¬(...) then 0` guard is TRUE.
    have hncont_p2 :
        ¬ ((toPartition2 μ).a ≤ (toPartition2 ν).a ∧
           (toPartition2 μ).b ≤ (toPartition2 ν).b) := by
      simp only [toPartition2_a, toPartition2_b]
      rintro ⟨h0, h1⟩
      apply hsub
      intro i
      fin_cases i
      · exact h0
      · exact h1
    rw [if_pos hncont_p2]

/-! ## Part VIII: 2-Row Anchor — In-Support Sub-Lemma (S3c — DEFERRED) -/

/-- **In-support case of the 2-row anchor (DEFERRED to S3c).** Under
    the LR support guard `μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight`,
    the abstract count `lrCoeffN_def ν lam μ` equals
    `lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ)`.

    This is the constructive heart of the 2-row anchor. The
    `lrCoeff2` value is always `0` or `1` (`lrCoeff2_le_one`,
    `Hilbert15OQ02.lean:258`), and `lrCoeff2 = 1` precisely when
    all four pass-conditions in `lrCoeff2`'s `if`-cascade hold:

    * `lam.parts 0 ≥ r₀` (where `r₀ := ν.parts 0 - μ.parts 0`)
    * `lam.parts 0 - r₀ ≤ r₁` (where `r₁ := ν.parts 1 - μ.parts 1`)
    * Column-strict in overlap: `lam.parts 0 - r₀ ≤ μ.parts 0 - μ.parts 1`
      whenever the overlap is non-empty.
    * Lattice from row 2: `r₀ ≥ lam.parts 1`.

    **Proof sketch (S3c).**

    1. **Row 0 is forced to all zeros.** The reverse row reading
       word starts with row 0 right-to-left. If any cell in row 0
       held `1 : Fin 2`, the rightmost such cell would appear
       first in the word, giving `count 1 ≥ 1` and `count 0 = 0`
       at a prefix where `0 < 1` — violating the lattice
       condition. So every `T ⟨0, j⟩ = 0 : Fin 2`. This forces
       `T.content 0 ≥ r₀`, hence `lam.parts 0 ≥ r₀`.

    2. **Row 1 content is determined.** With row 0 contributing
       `r₀` zeros, the content equation `T.content 0 = lam.parts 0`
       forces `c₀ := lam.parts 0 - r₀` zeros in row 1. The
       remaining `c₁ := r₁ - c₀ = lam.parts 1` cells are ones.

    3. **Row 1 is uniquely determined.** Weakly-increasing row 1
       with `c₀` zeros and `c₁` ones is the function `j ↦
       if j.val < c₀ then 0 else 1`. So there is at most one
       valid `T` and `Fintype.card ≤ 1`.

    4. **The unique candidate's column-strict and lattice
       conditions match `lrCoeff2`'s remaining guards.** Column-
       strictness on overlap requires the row-1 entries in
       columns `[μ.parts 0, ν.parts 1)` to be `> 0`, i.e., `1`.
       That overlap has size `(ν.parts 1 - μ.parts 0)` if
       positive, and the local row-1 indices are `[μ.parts 0 -
       μ.parts 1, r₁)`. The condition that those are all `1`
       is `c₀ ≤ μ.parts 0 - μ.parts 1`. Lattice from row 2:
       at every prefix of row 1 right-to-left, the count of
       `1`'s mustn't exceed `r₀` (zeros from row 0), giving
       `c₁ ≤ r₀`, i.e., `r₀ ≥ lam.parts 1`.

    5. **Bijection between candidates and `lrCoeff2 = 1`.** All
       four guards match exactly; when they hold, the unique
       function above satisfies the SkewSSYTFin conditions,
       giving `Fintype.card = 1`; when any fails, no candidate
       exists, giving `Fintype.card = 0`.

    Targeted at ~150 lines in S3c after the `SkewSSYTFin`
    `Fintype.card` reduction on the 2-row shape is built. -/
theorem lrCoeffN_def_two_eq_lrCoeff2_of_support (ν lam μ : Partition 2)
    (hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight) :
    lrCoeffN_def ν lam μ =
      LRComplexity.lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ) := by
  sorry

/-! ## Part IX: 2-Row Anchor — Main Theorem (S3b) -/

/-- **Main 2-row anchor.** The abstract LR count `lrCoeffN_def` on
    `Partition 2` data agrees with the concrete closed-form
    `LRComplexity.lrCoeff2`.

    This is the S3 load-bearing lemma. Three roles:

    1. **Sanity check.** The abstract `Fintype.card`-based count
       reduces to the existing computable case `lrCoeff2`, verifying
       that the S2 scaffold's `SkewSSYTFin / reverseRowWord /
       isLatticeWord` agree with the textbook
       Fulton (1997 Ch. 5 §2) on the 2-row sub-family.
    2. **API exercise.** Forces a concrete evaluation of
       `reverseRowWord` and `isLatticeWord` on `Partition 2` data,
       surfacing any inconsistencies in the S2 definitions before
       they propagate to the parent file via S4.
    3. **Decidable corollaries.** Once proved, the 7 Gr(2,4)
       structure constants verified in `Hilbert15OQ01.lean` /
       `Hilbert15OQ02.lean` lift mechanically to
       `lrCoeffN_def`-form by rewriting with this theorem.

    **Proof structure (S3b).** Case-split on the support guard:

    * **Out-of-support** (proved here, S3b). The LHS rewrites to
      `0` via `lrCoeffN_def_eq_zero_of_not_support`; the RHS
      rewrites to `0` via the dual
      `lrCoeff2_eq_zero_of_not_support`.

    * **In-support** (deferred to S3c). Delegated to the sub-
      lemma `lrCoeffN_def_two_eq_lrCoeff2_of_support` whose
      docstring records the full bijection sketch. -/
theorem lrCoeffN_def_two_eq_lrCoeff2 (ν lam μ : Partition 2) :
    lrCoeffN_def ν lam μ =
      LRComplexity.lrCoeff2 (toPartition2 ν) (toPartition2 lam) (toPartition2 μ) := by
  by_cases hsupp : μ ⊆ ν ∧ ν.weight = lam.weight + μ.weight
  · exact lrCoeffN_def_two_eq_lrCoeff2_of_support ν lam μ hsupp
  · rw [lrCoeffN_def_eq_zero_of_not_support _ _ _ hsupp]
    exact (lrCoeff2_eq_zero_of_not_support ν lam μ hsupp).symm

/-! ## Part X: S3c-Prep — `reverseRowWord` Decomposition (`n = 2`)

The remaining S3c sorry in `lrCoeffN_def_two_eq_lrCoeff2_of_support`
needs an explicit bijection between the lattice-word `SkewSSYTFin`
subtype and the unique candidate prescribed by `lrCoeff2`'s
`if`-cascade. The first sub-step of the proof sketch (Part VIII) —
"row 0 is forced to all zeros" — requires unpacking the
`reverseRowWord` `flatMap` over `Fin 2` and computing prefixes by
hand. We establish here the two clean structural lemmas that this
unpacking rests on; the lattice-forcing argument itself is deferred
to a follow-up iteration that builds on them.

* `reverseRowWord_two_eq` unfolds the `flatMap` over `Fin 2` into a
  concrete concatenation of row-0 and row-1 reverse-mapped lists.
  Closes by `rfl` after a `show` step rephrasing the `flatMap` over
  the literal `List.finRange 2 = [0, 1]`.
* `reverseRowWord_two_length` evaluates the word length to
  `r₀ + r₁` directly from the decomposition. Useful both for the
  row-0 forcing argument (where the lattice condition is applied at
  prefix length `≤ r₀`) and for the eventual `Fintype.card`
  bijection (where the content equation gives
  `r₀ + r₁ = lam.weight`).
-/

/-- **Decomposition of `reverseRowWord` for `n = 2`.** The reverse
    row reading word over a `Fin 2`-indexed row index unfolds via
    the `flatMap`-on-`Fin 2` identity into the concatenation of row
    0's reverse mapping and row 1's reverse mapping. Closed by
    `rfl` after a `show` step that rephrases the `flatMap` on the
    literal `List.finRange 2 = [(0 : Fin 2), 1]`. -/
theorem reverseRowWord_two_eq {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) :
    T.reverseRowWord =
      ((List.finRange (ν.parts 0 - μ.parts 0)).reverse.map
          (fun j => T.1 ⟨0, j⟩)) ++
      ((List.finRange (ν.parts 1 - μ.parts 1)).reverse.map
          (fun j => T.1 ⟨1, j⟩)) := by
  show (List.finRange 2).flatMap (fun i =>
      ((List.finRange (ν.parts i - μ.parts i)).reverse).map
        (fun j => T.1 ⟨i, j⟩)) = _
  -- `List.finRange 2 = [(0 : Fin 2), (1 : Fin 2)]`, then `flatMap` on two
  -- elements unfolds to `f 0 ++ f 1 ++ []`; the trailing `[]` is absorbed
  -- by `List.append_nil`.
  rw [show (List.finRange 2 : List (Fin 2)) = [(0 : Fin 2), 1] from by decide]
  simp [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **Length of `reverseRowWord` for `n = 2`.** A direct consequence
    of `reverseRowWord_two_eq` plus `List.length_append`,
    `List.length_map`, and `List.length_reverse`. -/
theorem reverseRowWord_two_length {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) :
    T.reverseRowWord.length =
      (ν.parts 0 - μ.parts 0) + (ν.parts 1 - μ.parts 1) := by
  rw [reverseRowWord_two_eq]
  simp [List.length_append, List.length_map, List.length_reverse,
        List.length_finRange]

/-! ## Part XI: S3c-Prep-2 — Row-0 / Row-1 Prefix Decomposition (`n = 2`)

The S3c proof of `lrCoeffN_def_two_eq_lrCoeff2_of_support` needs to isolate
the row-0 portion of `T.reverseRowWord` and apply the lattice-word
predicate at prefix length `r₀ := ν.parts 0 - μ.parts 0`. Building on
Part X's decomposition `reverseRowWord = L₀ ++ L₁`, we record:

* `reverseRowWord_two_take_r0` — the first `r₀` entries of the word
  are exactly `L₀` (row 0's reverse-mapped list). Direct from
  `List.take_left` after equating `r₀` with `L₀.length` via a
  small `subst`-based helper.
* `reverseRowWord_two_drop_r0` — the entries beyond `r₀` are exactly
  `L₁` (row 1's reverse-mapped list). Dual via `List.drop_left`.
* `reverseRowWord_two_lattice_row0` — instantiates the lattice-word
  predicate at the row-0 / row-1 boundary `p = r₀`, yielding the
  row-0 count bound `count 1 ≤ count 0` over the row-0 sub-list.
  This is Step 1 (row-0 forced to zeros) of the S3c proof sketch,
  reduced to a count bound over an explicit list.

These lemmas leave the underlying row-0 forcing argument
(count-to-pointwise reasoning on a list of `Fin 2` values mapped from
`(List.finRange r₀).reverse`) for S3d / S3e iterations.

The two private helpers `take_left_of_length` / `drop_left_of_length`
sit just above the public theorems. They are the standard "rewrite
the take/drop amount to the prefix length, then close with
`List.take_left` / `List.drop_left`" idiom, packaged so the `subst`
acts on a free variable rather than on a complex sub-expression of
the goal (which would otherwise be ambiguous with the `r₀` that also
appears inside `List.finRange r₀` and the lambda's `Fin r₀` type
annotation). -/

private lemma take_left_of_length {α : Type*} {l₁ l₂ : List α} {n : ℕ}
    (h : l₁.length = n) : (l₁ ++ l₂).take n = l₁ := by
  subst h
  exact List.take_left _ _

private lemma drop_left_of_length {α : Type*} {l₁ l₂ : List α} {n : ℕ}
    (h : l₁.length = n) : (l₁ ++ l₂).drop n = l₂ := by
  subst h
  exact List.drop_left _ _

/-- **First-`r₀` prefix of `reverseRowWord` (`n = 2`)** is row 0's
    reverse-mapped list. Direct from `reverseRowWord_two_eq` and
    the `take_left_of_length` helper which packages
    `List.take_left` with a length-rewrite step. -/
theorem reverseRowWord_two_take_r0 {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) :
    T.reverseRowWord.take (ν.parts 0 - μ.parts 0) =
      (List.finRange (ν.parts 0 - μ.parts 0)).reverse.map
        (fun j => T.1 ⟨0, j⟩) := by
  rw [reverseRowWord_two_eq]
  apply take_left_of_length
  simp [List.length_map, List.length_reverse, List.length_finRange]

/-- **Drop-`r₀` suffix of `reverseRowWord` (`n = 2`)** is row 1's
    reverse-mapped list. Dual to `reverseRowWord_two_take_r0`,
    closed by `drop_left_of_length` after the same length identification. -/
theorem reverseRowWord_two_drop_r0 {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) :
    T.reverseRowWord.drop (ν.parts 0 - μ.parts 0) =
      (List.finRange (ν.parts 1 - μ.parts 1)).reverse.map
        (fun j => T.1 ⟨1, j⟩) := by
  rw [reverseRowWord_two_eq]
  apply drop_left_of_length
  simp [List.length_map, List.length_reverse, List.length_finRange]

/-- **Lattice condition at the row-0 / row-1 boundary (`n = 2`).** If
    `T.reverseRowWord` is a lattice word, instantiating the predicate
    at prefix length `r₀ := ν.parts 0 - μ.parts 0` gives the row-0
    count bound `count 1 ≤ count 0` over the row-0 sub-list.

    This is the cleanest reformulation of Step 1 in the S3c proof
    sketch ("row 0 is forced to all zeros"): the row-0 portion of the
    reverse row word — reading row 0 right-to-left — is a list of
    `Fin 2` values whose count of `1`s is bounded by the count of
    `0`s. Combined with `List.count`-pointwise reasoning, this forces
    every cell in row 0 to be `0`. (That forcing step is left for
    follow-on iterations; this lemma packages the lattice-word
    application cleanly.) -/
theorem reverseRowWord_two_lattice_row0 {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hLW : isLatticeWord T.reverseRowWord) :
    ((List.finRange (ν.parts 0 - μ.parts 0)).reverse.map
        (fun j => T.1 ⟨0, j⟩)).count (1 : Fin 2) ≤
    ((List.finRange (ν.parts 0 - μ.parts 0)).reverse.map
        (fun j => T.1 ⟨0, j⟩)).count (0 : Fin 2) := by
  have hbnd : ν.parts 0 - μ.parts 0 < T.reverseRowWord.length + 1 := by
    rw [reverseRowWord_two_length]
    omega
  -- Annotate the expected type so the `.val` projection on `⟨r₀, hbnd⟩`
  -- reduces to `r₀` during elaboration, letting `rw` find the pattern.
  have hLW' :
      (T.reverseRowWord.take (ν.parts 0 - μ.parts 0)).count (1 : Fin 2) ≤
      (T.reverseRowWord.take (ν.parts 0 - μ.parts 0)).count (0 : Fin 2) :=
    hLW ⟨ν.parts 0 - μ.parts 0, hbnd⟩ 0 1 (by decide)
  rw [reverseRowWord_two_take_r0] at hLW'
  exact hLW'

end Hilbert15OQ02OQ03OQ01
