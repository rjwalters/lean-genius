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

/-! ## Part XII: S3c-Prep-3 — Row-0 Monotonicity & Top-Zero Forcing (`n = 2`)

The S3c proof of `lrCoeffN_def_two_eq_lrCoeff2_of_support` Step 1 ("row 0
is forced to all zeros") splits into two sub-steps:

1. **Row-0 monotonicity adapter** — package the row weakness field of
   `SkewSSYTFin` for row index `0` and the inclusive `j₁ ≤ j₂` form
   (the structure field uses strict `<` only).
2. **Top-zero forces all-zero** — when the largest row-0 cell
   `T ⟨0, ⟨r₀ - 1, _⟩⟩` already equals `0 : Fin 2`, monotonicity propagates
   the zero down to every row-0 cell. This reduces Step 1 to the
   single-cell input "the rightmost cell of row 0 is 0", which the
   lattice condition delivers at prefix length `1` of `T.reverseRowWord`
   (cf. `reverseRowWord_two_lattice_row0`).

Together these convert the S3c-prep-2 prefix count bound into the
pointwise row-0 vanishing conclusion. The lattice → top-zero step itself
(the count-at-prefix-1 argument) is left for a follow-on iteration. -/

/-- **Row-0 monotonicity (inclusive form).** Row weakness on a
    `SkewSSYTFin 2 ν μ` is stated using the strict order `j₁ < j₂` in
    the structure field. For the S3c row-0 analysis we repeatedly need
    the inclusive form `j₁ ≤ j₂ → T ⟨0, j₁⟩ ≤ T ⟨0, j₂⟩`. The proof
    splits on `j₁ < j₂ ∨ j₁ = j₂` and applies the field directly in
    the strict case, closing the equality case by reflexivity after
    substitution. -/
theorem skewSSYTFin_row0_mono {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    {j₁ j₂ : Fin (ν.parts 0 - μ.parts 0)}
    (h : j₁ ≤ j₂) : T.1 ⟨0, j₁⟩ ≤ T.1 ⟨0, j₂⟩ := by
  rcases h.lt_or_eq with hlt | heq
  · exact T.2.1 0 j₁ j₂ hlt
  · subst heq
    exact le_refl _

/-- **Top-zero forces all-zero on row 0 (`n = 2`).** If the rightmost
    row-0 cell `T ⟨0, ⟨r₀ - 1, _⟩⟩` equals `0 : Fin 2`, then every
    row-0 cell `T ⟨0, j⟩` equals `0`. Direct consequence of row-0
    monotonicity: every `j` satisfies `j ≤ r₀ - 1`, so monotonicity
    gives `T ⟨0, j⟩ ≤ T ⟨0, ⟨r₀ - 1, _⟩⟩ = 0` in `Fin 2`, and the only
    `Fin 2` value `≤ 0` is `0` itself.

    The positivity hypothesis `0 < r₀` ensures `⟨r₀ - 1, _⟩` is a
    valid `Fin r₀` index; under `hpos = False` the conclusion is
    vacuous (no `j : Fin 0` exists). -/
theorem skewSSYTFin_row0_eq_zero_of_top_zero {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hpos : 0 < ν.parts 0 - μ.parts 0)
    (hzero : T.1 ⟨0, ⟨ν.parts 0 - μ.parts 0 - 1, by omega⟩⟩ = 0)
    (j : Fin (ν.parts 0 - μ.parts 0)) :
    T.1 ⟨0, j⟩ = 0 := by
  have hjle :
      j ≤ (⟨ν.parts 0 - μ.parts 0 - 1, by omega⟩ :
            Fin (ν.parts 0 - μ.parts 0)) := by
    show j.val ≤ ν.parts 0 - μ.parts 0 - 1
    have := j.isLt
    omega
  have hle := skewSSYTFin_row0_mono T hjle
  rw [hzero] at hle
  -- `hle : T.1 ⟨0, j⟩ ≤ (0 : Fin 2)`. The `Fin 2`-side `LE` unfolds to
  -- `Nat.le` on `.val`; `(0 : Fin 2).val = 0`, so `.val ≤ 0` gives `.val = 0`.
  apply Fin.ext
  have hle_val : (T.1 ⟨0, j⟩).val ≤ ((0 : Fin 2)).val := hle
  have h0 : ((0 : Fin 2)).val = 0 := rfl
  omega

/-! ## Part XIII: S3c-Prep-4 — Row-0 Top-Cell Lattice Forcing (`n = 2`)

The Step 1 ("row 0 is forced to all zeros") chain in Part VIII's
docstring sketch decomposes into two halves:

* **Top-zero forces all-zero** — given the rightmost row-0 cell
  `T ⟨0, ⟨r₀ - 1, _⟩⟩ = 0 : Fin 2`, row-0 monotonicity (Part XII)
  propagates the zero to every row-0 cell.
* **Lattice forces top-zero** — given `isLatticeWord T.reverseRowWord`,
  the rightmost row-0 cell *is* zero.

Part XII supplied the first half. This Part supplies the second: at
prefix length `1` of `T.reverseRowWord`, the count bound `count 1 ≤
count 0` forces the *single* word entry — which is the rightmost row-0
cell when `r₀ > 0` — to equal `0 : Fin 2`.

The chain composes into a clean `skewSSYTFin_row0_forced_zero`
corollary closing Step 1 of the S3c proof sketch entirely under the
positivity hypothesis `0 < r₀`. The `r₀ = 0` branch is vacuous (`Fin 0`
empty) and handled inline by S3c proper.

### Decomposition strategy

The decomposition `reverseRowWord = L₀ ++ L₁` (Part X) plus
`take_append_of_le_length` reduces `T.reverseRowWord.take 1` to
`L₀.take 1`. For `r₀ > 0`, `L₀ = (finRange r₀).reverse.map (fun j =>
T ⟨0, j⟩)` starts with the rightmost cell because
`(finRange (k+1)).reverse = Fin.last k :: ...` via Mathlib's
`List.finRange_succ`. The private helper
`reverse_finRange_take_one_of_pos` extracts that head cleanly. -/

/-- **Take-one head of a reversed-mapped `List.finRange` (`r > 0`).**
    For `r > 0` and any `f : Fin r → α`, the `take 1` prefix of
    `(List.finRange r).reverse.map f` is the singleton `[f ⟨r-1, _⟩]`.
    Proved by case-decomposition `r = k + 1` (via
    `Nat.exists_eq_succ_of_ne_zero`) plus the standard
    `List.finRange_succ = ... ++ [Fin.last k]` identity, after which
    the reversed list cons-decomposes with `Fin.last k` at the head
    and `(k+1) - 1 = k` reduces to that head by proof-irrelevant
    `Fin` equality. -/
private lemma reverse_finRange_take_one_of_pos
    {α : Type*} {r : ℕ} (h : 0 < r) (f : Fin r → α) :
    ((List.finRange r).reverse.map f).take 1 =
      [f ⟨r - 1, Nat.sub_lt h Nat.one_pos⟩] := by
  rcases Nat.exists_eq_succ_of_ne_zero h.ne' with ⟨k, rfl⟩
  rw [List.finRange_succ, List.concat_eq_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.map_cons]
  rfl

/-- **First entry of `reverseRowWord` (`n = 2`, `r₀ > 0`).** When the
    skew strip's row 0 is non-empty, the `take 1` prefix of the reverse
    row reading word is the singleton list containing the rightmost
    row-0 cell `T ⟨0, ⟨r₀ - 1, _⟩⟩`. This is the prefix-length-`1`
    counterpart of `reverseRowWord_two_take_r0` (Part XI's prefix-`r₀`
    decomposition) and isolates the head from the lattice-word
    condition's "first entry" inspection. -/
theorem reverseRowWord_two_take_one_of_pos {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hpos : 0 < ν.parts 0 - μ.parts 0) :
    T.reverseRowWord.take 1 =
      [T.1 ⟨0, ⟨ν.parts 0 - μ.parts 0 - 1, Nat.sub_lt hpos Nat.one_pos⟩⟩] := by
  rw [reverseRowWord_two_eq]
  have hlen :
      (1 : ℕ) ≤ ((List.finRange (ν.parts 0 - μ.parts 0)).reverse.map
                  (fun j => T.1 ⟨(0 : Fin 2), j⟩)).length := by
    simp [List.length_map, List.length_reverse, List.length_finRange]
    exact hpos
  rw [List.take_append_of_le_length hlen]
  exact reverse_finRange_take_one_of_pos hpos _

/-- **Top row-0 cell forced to zero by lattice condition (`n = 2`).**
    When `T.reverseRowWord` is a lattice word and row 0 is non-empty
    (`r₀ > 0`), the rightmost row-0 cell `T ⟨0, ⟨r₀ - 1, _⟩⟩` equals
    `0 : Fin 2`. Proved by instantiating the lattice-word predicate at
    prefix length `1` with `k = 0`, `k' = 1`, getting `[head].count 1 ≤
    [head].count 0` where `head` is the rightmost row-0 cell (via
    `reverseRowWord_two_take_one_of_pos`). For `head : Fin 2` the only
    way this bound holds is `head = 0`: if `head = 1`, the singleton
    counts evaluate to `1 ≤ 0`, contradiction.

    Supplies the missing single-cell hypothesis for Part XII's
    `skewSSYTFin_row0_eq_zero_of_top_zero`, closing Step 1 of the S3c
    proof sketch (row 0 forced to all zeros) modulo the `r₀ > 0`
    positivity branch. -/
theorem skewSSYTFin_row0_top_zero_of_lattice {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hpos : 0 < ν.parts 0 - μ.parts 0)
    (hLW : isLatticeWord T.reverseRowWord) :
    T.1 ⟨0, ⟨ν.parts 0 - μ.parts 0 - 1, Nat.sub_lt hpos Nat.one_pos⟩⟩ = 0 := by
  -- Prefix-1 lattice bound.
  have hbnd : 1 < T.reverseRowWord.length + 1 := by
    rw [reverseRowWord_two_length]; omega
  have hcnt :
      (T.reverseRowWord.take 1).count (1 : Fin 2) ≤
      (T.reverseRowWord.take 1).count (0 : Fin 2) :=
    hLW ⟨1, hbnd⟩ 0 1 (by decide)
  rw [reverseRowWord_two_take_one_of_pos T hpos] at hcnt
  -- `hcnt : [top].count 1 ≤ [top].count 0` where `top` is the rightmost row-0 cell.
  -- For `top : Fin 2`, this forces `top = 0`.
  by_contra hne
  set top := T.1 ⟨0, ⟨ν.parts 0 - μ.parts 0 - 1, Nat.sub_lt hpos Nat.one_pos⟩⟩
  -- `hne : top ≠ 0` and `top : Fin 2` so `top.val ∈ {0, 1}` and `top = 1`.
  have h1 : top = 1 := by
    have hlt : top.val < 2 := top.isLt
    have hne0 : top.val ≠ 0 := fun h => hne (Fin.ext h)
    apply Fin.ext
    show top.val = (1 : Fin 2).val
    have h1_val : ((1 : Fin 2)).val = 1 := rfl
    omega
  rw [h1] at hcnt
  exact absurd hcnt (by decide)

/-- **Row 0 forced to all zeros by lattice condition (`n = 2`).** Step
    1 of the S3c proof sketch fully discharged under the positivity
    hypothesis `0 < r₀`. Composes
    `skewSSYTFin_row0_top_zero_of_lattice` (Part XIII) with
    `skewSSYTFin_row0_eq_zero_of_top_zero` (Part XII): the lattice
    condition forces the rightmost row-0 cell to be zero, then row-0
    monotonicity propagates the zero to every row-0 cell.

    The `r₀ = 0` branch (where `Fin r₀` is empty and the conclusion is
    vacuous) is handled by S3c proper via `Fin.elim0`. -/
theorem skewSSYTFin_row0_forced_zero {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hpos : 0 < ν.parts 0 - μ.parts 0)
    (hLW : isLatticeWord T.reverseRowWord)
    (j : Fin (ν.parts 0 - μ.parts 0)) :
    T.1 ⟨0, j⟩ = 0 :=
  skewSSYTFin_row0_eq_zero_of_top_zero T hpos
    (skewSSYTFin_row0_top_zero_of_lattice T hpos hLW) j

/-! ## Part XIV: Step 2 — Row 1 Content Determined (S3c-prep-5 ACT)

The PREP chain S3c-prep-{5,6} (PRs #18395, #18579) pinned the design and
Mathlib bearer audit for Step 2 of Part VIII's S3c proof sketch:
*"Row 1 content is determined."* This Part discharges that step.

Given Step 1's output `hrow0 : ∀ j : Fin r₀, T ⟨0, j⟩ = 0` and the content
equation `T.content k = lam.parts k`, the row-1 zero-count is forced to
`lam.parts 0 - r₀` and the row-1 one-count to `lam.parts 1`. The key
lemma is the sigma decomposition of `T.content k` over the two rows of
the 2-row skew shape, via `Fintype.sum_sigma` + `Fin.sum_univ_two`.

The vacuous `r₀ = 0` branch is handled at Step 5's call site by the
Step 1 invocation; this Part takes `hrow0` directly so the API is
agnostic to how the row-0 zeros were established.
-/

/-- **Weight on `Partition 2` decomposes into `parts 0 + parts 1`.**
    Adapter for Step 2's `omega` closure. The proof mirrors the inline
    chain used at `toPartition2_size`. -/
@[simp] theorem Partition.weight_two_eq (p : Partition 2) :
    p.weight = p.parts 0 + p.parts 1 := by
  simp [Partition.weight, Fin.sum_univ_two]

/-- **Content decomposition over rows (`n = 2`).** For a 2-row skew SSYT,
    the count of cells with value `k : Fin 2` decomposes as the sum of
    the row-0 and row-1 counts. Direct from `Fintype.sum_sigma` +
    `Fin.sum_univ_two`. -/
theorem SkewSSYTFin.content_two_eq_rows {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) (k : Fin 2) :
    T.content k =
      ((Finset.univ : Finset (Fin (ν.parts 0 - μ.parts 0))).filter
         (fun j => T.1 ⟨0, j⟩ = k)).card +
      ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
         (fun j => T.1 ⟨1, j⟩ = k)).card := by
  unfold SkewSSYTFin.content
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sigma,
      Fin.sum_univ_two, ← Finset.sum_filter, ← Finset.sum_filter,
      ← Finset.card_eq_sum_ones, ← Finset.card_eq_sum_ones]

/-- **Row-0 zero-count under `hrow0`.** Given that every row-0 cell is
    zero, the row-0 zero-count is the full cardinality `r₀`. Building
    block for Step 2's content-equation arithmetic. -/
theorem skewSSYTFin_row0_zero_count_of_row0_zero {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2)) :
    ((Finset.univ : Finset (Fin (ν.parts 0 - μ.parts 0))).filter
       (fun j => T.1 ⟨0, j⟩ = (0 : Fin 2))).card = ν.parts 0 - μ.parts 0 := by
  rw [Finset.filter_true_of_mem (fun j _ => hrow0 j),
      Finset.card_univ, Fintype.card_fin]

/-- **Row-0 one-count vanishes under `hrow0`.** Every row-0 cell is zero,
    so the count of row-0 cells with value `1` is `0`. -/
theorem skewSSYTFin_row0_one_count_zero_of_row0_zero {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2)) :
    ((Finset.univ : Finset (Fin (ν.parts 0 - μ.parts 0))).filter
       (fun j => T.1 ⟨0, j⟩ = (1 : Fin 2))).card = 0 := by
  rw [Finset.filter_false_of_mem, Finset.card_empty]
  intro j _ hj
  rw [hrow0 j] at hj
  exact absurd hj (by decide)

/-- **From `hrow0` + content equation: `lam.parts 0 ≥ r₀`.** The first
    part of `lam` is at least the row-0 length, since row-0 contributes
    `r₀` zeros to `T.content 0 = lam.parts 0`. Non-truncation guard for
    Step 2's `omega` closure on the row-1 zero-count. -/
theorem skewSSYTFin_lam0_ge_r0_of_row0_zero {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (lam : Partition 2)
    (hcont0 : T.content 0 = lam.parts 0) :
    ν.parts 0 - μ.parts 0 ≤ lam.parts 0 := by
  have h := T.content_two_eq_rows 0
  rw [skewSSYTFin_row0_zero_count_of_row0_zero T hrow0, hcont0] at h
  omega

/-- **Step 2 (zero-count): row-1 zero-count from row-0 zeros + content.**
    Under Step 1's output `hrow0` and the content equation on value `0`,
    the row-1 zero-count equals `lam.parts 0 - r₀`. Closes the first
    half of Part VIII's Step 2 sketch. -/
theorem skewSSYTFin_row1_zero_count_of_row0_zero {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (lam : Partition 2)
    (hcont0 : T.content 0 = lam.parts 0) :
    ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
       (fun j => T.1 ⟨1, j⟩ = (0 : Fin 2))).card =
      lam.parts 0 - (ν.parts 0 - μ.parts 0) := by
  have h := T.content_two_eq_rows 0
  rw [skewSSYTFin_row0_zero_count_of_row0_zero T hrow0, hcont0] at h
  omega

/-- **Step 2 (one-count): row-1 one-count from row-0 zeros + content.**
    Under Step 1's output `hrow0` and the content equation on value `1`,
    the row-1 one-count equals `lam.parts 1`. Direct from the
    row-decomposition with row-0-one-count vanishing. -/
theorem skewSSYTFin_row1_one_count_of_row0_zero {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (lam : Partition 2)
    (hcont1 : T.content 1 = lam.parts 1) :
    ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
       (fun j => T.1 ⟨1, j⟩ = (1 : Fin 2))).card = lam.parts 1 := by
  have h := T.content_two_eq_rows 1
  rw [skewSSYTFin_row0_one_count_zero_of_row0_zero T hrow0, hcont1] at h
  omega

/-- **Composite Step 1 + Step 2.** Bundles the row-1 zero-count and
    one-count under the lattice-word hypothesis (Step 1's input form)
    via `skewSSYTFin_row0_forced_zero`. Convenience wrapper for the
    Step 5 Fintype-card collapse; the vacuous `r₀ = 0` branch is
    handled by the caller via `Fin.elim0`. -/
theorem skewSSYTFin_two_row_zero_one_counts {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hLW : isLatticeWord T.reverseRowWord)
    (lam : Partition 2)
    (hcont : ∀ k : Fin 2, T.content k = lam.parts k)
    (hpos : 0 < ν.parts 0 - μ.parts 0) :
    ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
       (fun j => T.1 ⟨1, j⟩ = (0 : Fin 2))).card =
        lam.parts 0 - (ν.parts 0 - μ.parts 0)
    ∧
    ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
       (fun j => T.1 ⟨1, j⟩ = (1 : Fin 2))).card = lam.parts 1 :=
  let hrow0 := skewSSYTFin_row0_forced_zero T hpos hLW
  ⟨skewSSYTFin_row1_zero_count_of_row0_zero T hrow0 lam (hcont 0),
   skewSSYTFin_row1_one_count_of_row0_zero T hrow0 lam (hcont 1)⟩

/-! ## Part XV: Step 3 — Row 1 Uniquely Determined (S3c-prep-7 ACT)

The PREP S3c-prep-7 (PR #18636) pinned the design for Step 3 of Part
VIII's S3c proof sketch: *"Row 1 is uniquely determined."* Concretely,
a weakly-increasing function `f : Fin r → Fin 2` is determined by the
location of its "step" — the unique cutoff `k` with `f j = 0` iff
`j.val < k`. The cutoff is exactly the zero-count
`#{j : Fin r | f j = 0}`. Two functions sharing the count therefore
agree pointwise.

The one-shot Mathlib bearer
`Fin.lt_card_filter_univ_iff_apply_of_imp` (HEAD
`Data/Fintype/Fin.lean:70`, ~92-line file) is **absent** at the
project's pinned Mathlib v4.26.0 (62-line file; both the lemma and
its dependency `Fin.card_filter_val_lt` lie in the post-v4.26.0
delta). This Part inlines a private ~25-LOC backport using only
`Finset.card_le_card` + `Fin.card_Iio`/`Iic`, then ships the four
downstream Step-3 theorems (row-1 monotonicity adapter, zero-cell
downward closure, step-function characterization, and the composite
"two tableaux with equal zero-counts agree on row 1" lemma). All
proofs use only v4.26.0 primitives. -/

/-- **Downward-closed predicate on `Fin n` is determined by its count
    at every index.** Backport of Mathlib HEAD's
    `Fin.lt_card_filter_univ_iff_apply_of_imp`
    (`Data/Fintype/Fin.lean:70` at HEAD; absent at v4.26.0).

    Given a "downward-closed" predicate `p` on `Fin n` (`Antitone p`
    in the form `∀ i k, k ≤ i → p i → p k`), `p` holds for more than
    `j` elements iff `p j` itself holds. -/
private theorem lt_card_filter_univ_iff_apply_of_imp
    {n : ℕ} {j : Fin n}
    (p : Fin n → Prop) [DecidablePred p]
    (hp : ∀ i k, k ≤ i → p i → p k) :
    j.val < (Finset.univ.filter p).card ↔ p j := by
  have h1 : ∀ (k : Fin n), ¬ p k →
      (Finset.univ.filter p).card ≤ k.val := by
    intro k hk
    rw [← Fin.card_Iio]
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_Iio]
    by_contra hne
    push_neg at hne
    exact hk (hp x k hne hx)
  refine ⟨?_, ?_⟩
  · intro hlt
    by_contra hne
    exact absurd hlt (Nat.not_lt.mpr (h1 j hne))
  · intro hj
    have hsub : Finset.Iic j ⊆ Finset.univ.filter p := by
      intro x hx
      simp only [Finset.mem_Iic] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp j x hx hj
    have hcard : (Finset.Iic j).card ≤ (Finset.univ.filter p).card :=
      Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega

/-- **Row-1 monotonicity (inclusive form).** Parallels Part XII's
    `skewSSYTFin_row0_mono`. Row weakness on row 1 of a
    `SkewSSYTFin 2 ν μ` is stated using the strict `j₁ < j₂` in the
    structure field; this adapter gives the inclusive `j₁ ≤ j₂` form
    needed for the downward-closed-predicate argument. -/
theorem skewSSYTFin_row1_mono {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    {j₁ j₂ : Fin (ν.parts 1 - μ.parts 1)}
    (h : j₁ ≤ j₂) : T.1 ⟨1, j₁⟩ ≤ T.1 ⟨1, j₂⟩ := by
  rcases h.lt_or_eq with hlt | heq
  · exact T.2.1 1 j₁ j₂ hlt
  · subst heq
    exact le_refl _

/-- **`T ⟨1, ·⟩ = 0` is downward-closed on row 1.** For
    `T : SkewSSYTFin 2 ν μ` and row-1 indices `j ≤ i`, if
    `T ⟨1, i⟩ = 0` then `T ⟨1, j⟩ = 0`. Direct from row-1
    monotonicity + the `Fin 2`-side "only `0 ≤ 0`" fact. This is the
    antitonicity hypothesis fed into
    `lt_card_filter_univ_iff_apply_of_imp`. -/
theorem skewSSYTFin_row1_eq_zero_downward_closed
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    {i j : Fin (ν.parts 1 - μ.parts 1)}
    (hle : j ≤ i) (hi : T.1 ⟨1, i⟩ = (0 : Fin 2)) :
    T.1 ⟨1, j⟩ = (0 : Fin 2) := by
  have hmono := skewSSYTFin_row1_mono T hle
  rw [hi] at hmono
  apply Fin.ext
  have hle_val : (T.1 ⟨1, j⟩).val ≤ ((0 : Fin 2)).val := hmono
  have h0 : ((0 : Fin 2)).val = 0 := rfl
  omega

/-- **Step 3 main: row 1 is the zero-count step function.** Given a
    `SkewSSYTFin 2 ν μ` and any row-1 index `j`, the cell value
    `T ⟨1, j⟩` equals `0 : Fin 2` exactly when `j.val` is strictly
    below the row-1 zero-count; otherwise it equals `1 : Fin 2`.
    Direct application of
    `lt_card_filter_univ_iff_apply_of_imp` with the predicate
    `p k := T ⟨1, k⟩ = 0`; antitonicity is
    `skewSSYTFin_row1_eq_zero_downward_closed`. The `Fin 2`-side
    case-split (`val ∈ {0, 1}` since `.isLt < 2`) closes the
    `if-then-else` shape. -/
theorem skewSSYTFin_row1_step_function
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (j : Fin (ν.parts 1 - μ.parts 1)) :
    T.1 ⟨1, j⟩ = if j.val < ((Finset.univ : Finset
                              (Fin (ν.parts 1 - μ.parts 1))).filter
                              (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card
                  then (0 : Fin 2)
                  else (1 : Fin 2) := by
  have hkey :
      j.val < ((Finset.univ : Finset
                (Fin (ν.parts 1 - μ.parts 1))).filter
                (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card
      ↔ T.1 ⟨1, j⟩ = (0 : Fin 2) := by
    apply lt_card_filter_univ_iff_apply_of_imp
    intro i k hle hi
    exact skewSSYTFin_row1_eq_zero_downward_closed T hle hi
  by_cases hjlt :
      j.val < ((Finset.univ : Finset
                (Fin (ν.parts 1 - μ.parts 1))).filter
                (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card
  · rw [if_pos hjlt]
    exact hkey.mp hjlt
  · rw [if_neg hjlt]
    have hne : T.1 ⟨1, j⟩ ≠ (0 : Fin 2) := fun h => hjlt (hkey.mpr h)
    apply Fin.ext
    have hlt := (T.1 ⟨1, j⟩).isLt
    have h0 : ((0 : Fin 2)).val = 0 := rfl
    have h1 : ((1 : Fin 2)).val = 1 := rfl
    rw [h1]
    have hne_val : (T.1 ⟨1, j⟩).val ≠ 0 := by
      intro hv
      apply hne
      apply Fin.ext
      rw [h0]
      exact hv
    omega

/-- **Composite: two `SkewSSYTFin 2 ν μ` agree on row 1 if their
    row-1 zero-counts agree.** Direct from
    `skewSSYTFin_row1_step_function` applied to each tableau; the
    common zero-count makes the two step functions definitionally
    equal at every index. This is the load-bearing
    `Fintype.card ≤ 1` input for Step 5's bijection closure. -/
theorem skewSSYTFin_row1_unique_of_zero_count_eq
    {ν μ : Partition 2} (T₁ T₂ : SkewSSYTFin 2 ν μ)
    (hcount :
      ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
        (fun k => T₁.1 ⟨1, k⟩ = (0 : Fin 2))).card =
      ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
        (fun k => T₂.1 ⟨1, k⟩ = (0 : Fin 2))).card)
    (j : Fin (ν.parts 1 - μ.parts 1)) :
    T₁.1 ⟨1, j⟩ = T₂.1 ⟨1, j⟩ := by
  rw [skewSSYTFin_row1_step_function T₁ j,
      skewSSYTFin_row1_step_function T₂ j, hcount]

/-! ## Part XVI: Step 4 — Column-Strict + Row-2 Lattice (S3c-prep-{8,10,13,14} ACT)

    Two main public theorems matching `lrCoeff2`'s Guards C + D from
    `Hilbert15OQ02.lean:131,149`, composed via the canonical
    `reverseRowWord_two_canonical` decomposition. Each leans on
    Steps 1 (`skewSSYTFin_row0_forced_zero`, line 799),
    2 (`skewSSYTFin_row1_zero_count_of_row0_zero`, line 889),
    3 (`skewSSYTFin_row1_step_function`, line 1040).

    The auxiliary `List.reverse_map_finRange_step_function` is added here per
    S3c-prep-10 §3 design (paste-ready proof body, ~39 LOC). Path B
    convention (per S3c-STATE-SYNC #19371 §3.3): the threshold `c₀` is
    **inferred** from `lam.parts 0 - r₀` rather than carried as a free
    parameter.

    Build pending — Docker daemon hung (`docker info` exit 124 at 8s)
    + host disk 100%/6.7 Gi avail at S3c-step4-act author time
    (researcher-4, 2026-05-16T14:35Z). Paste verbatim from
    sessions/2026-05-16-s3c-prep-14-step4-path-b-proof-bodies.md §6
    (researcher-11, merged 2026-05-16T13:51:53Z) modulo this build-
    pending docstring. Bearer pin verified 0-drift at
    `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` per prep-14 §3 5-spot
    recheck.
-/

theorem List.reverse_map_finRange_step_function {α : Type*} (a b : α)
    {c₀ r₁ : ℕ} (hc : c₀ ≤ r₁) :
    ((List.finRange r₁).reverse.map
        (fun j : Fin r₁ => if j.val < c₀ then a else b)) =
      List.replicate (r₁ - c₀) b ++ List.replicate c₀ a := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_reverse, List.length_finRange,
               List.length_append, List.length_replicate]
    omega
  · intro i h1 _h2
    have hir : i < r₁ := by simpa using h1
    have hLHS :
        ((List.finRange r₁).reverse.map
            (fun j : Fin r₁ => if j.val < c₀ then a else b))[i]'h1
          = (if r₁ - 1 - i < c₀ then a else b) := by
      simp only [List.getElem_map, List.getElem_reverse,
                 List.length_reverse, List.length_finRange,
                 List.getElem_finRange, Fin.cast_mk, Fin.val_mk]
    have hRHS :
        (List.replicate (r₁ - c₀) b ++ List.replicate c₀ a)[i]'_h2
          = (if i < r₁ - c₀ then b else a) := by
      rw [List.getElem_append]
      simp only [List.length_replicate]
      split_ifs with hi
      · simp [List.getElem_replicate]
      · simp [List.getElem_replicate]
    rw [hLHS, hRHS]
    by_cases hL : r₁ - 1 - i < c₀
    · by_cases hR : i < r₁ - c₀
      · exfalso; omega
      · simp [hL, hR]
    · by_cases hR : i < r₁ - c₀
      · simp [hL, hR]
      · exfalso; omega

/-- **Canonical 3-replicate form** for `reverseRowWord` under Steps 1+2+3.
    Combines Part X's row-decomposition with Part XIV's row-1 zero-count
    and Part XV's step function. Path B: `c₀ := lam.parts 0 - r₀` is
    inferred from `lam` + `hrow0` + `hcont0` rather than passed as a
    parameter. -/
theorem reverseRowWord_two_canonical {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) (lam : Partition 2)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (hcont0 : T.content 0 = lam.parts 0) :
    T.reverseRowWord =
      List.replicate (ν.parts 0 - μ.parts 0) (0 : Fin 2) ++
      List.replicate (ν.parts 1 - μ.parts 1 -
                       (lam.parts 0 - (ν.parts 0 - μ.parts 0))) (1 : Fin 2) ++
      List.replicate (lam.parts 0 - (ν.parts 0 - μ.parts 0)) (0 : Fin 2) := by
  -- Derive hcount from Part XIV (line 889).
  have hcount :
      ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
         (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card =
      lam.parts 0 - (ν.parts 0 - μ.parts 0) :=
    skewSSYTFin_row1_zero_count_of_row0_zero T hrow0 lam hcont0
  -- Derive hstep from Part XV (line 1040). With #18990 merged, this
  -- is a one-line rewrite — no funext-style bridge needed.
  have hstep : ∀ j : Fin (ν.parts 1 - μ.parts 1),
      T.1 ⟨1, j⟩ = if j.val < lam.parts 0 - (ν.parts 0 - μ.parts 0)
                    then (0 : Fin 2) else (1 : Fin 2) := fun j => by
    rw [skewSSYTFin_row1_step_function T j, hcount]
  -- Discharge `c₀ ≤ r₁` (prep-12 §3.2).
  have hc₀_le_r₁ :
      lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ ν.parts 1 - μ.parts 1 := by
    have hle :
        ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
           (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card ≤
        (Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).card :=
      Finset.card_filter_le _ _
    rw [hcount, Finset.card_univ, Fintype.card_fin] at hle
    exact hle
  -- Decompose reverseRowWord (Part X, line 485).
  rw [reverseRowWord_two_eq]
  -- Replace row-0 map with constant 0 (prep-12 §5 step 1).
  rw [show (fun j => T.1 ⟨(0 : Fin 2), j⟩) = (fun _ => (0 : Fin 2)) from
      funext hrow0]
  rw [List.map_const, List.length_reverse, List.length_finRange]
  -- Replace row-1 map with step-function form (prep-12 §5 step 2).
  rw [show (fun j => T.1 ⟨(1 : Fin 2), j⟩)
        = (fun j => if j.val < lam.parts 0 - (ν.parts 0 - μ.parts 0)
                     then (0 : Fin 2) else (1 : Fin 2)) from
      funext hstep]
  -- Apply the helper.
  rw [List.reverse_map_finRange_step_function (0 : Fin 2) (1 : Fin 2) hc₀_le_r₁]
  -- Reassociate (prep-12 §4.2). Closes by `rfl`.
  rw [← List.append_assoc]

/-- **Guard C (column-strict overlap):** under Step 1 (`hrow0`) and Step 2's
    content equation, row 1 evaluates to 1 above the step-function threshold
    `lam.parts 0 - r₀`. The optional `_hoverlap` hypothesis records the
    column-strict inclusion (forwards-use; not consumed by the proof
    body). See S3c-prep-14 §4 for derivation. -/
theorem skewSSYTFin_row1_one_of_overlap {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) (lam : Partition 2)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (hcont0 : T.content 0 = lam.parts 0)
    (_hoverlap : μ.parts 0 - μ.parts 1 ≤ lam.parts 0 - (ν.parts 0 - μ.parts 0))
    (j : Fin (ν.parts 1 - μ.parts 1))
    (hj : lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ j.val) :
    T.1 ⟨1, j⟩ = (1 : Fin 2) := by
  rw [skewSSYTFin_row1_step_function T j,
      skewSSYTFin_row1_zero_count_of_row0_zero T hrow0 lam hcont0,
      if_neg (Nat.not_lt.mpr hj)]

/-- **Guard D (row-2 lattice):** under Steps 1+2 (via
    `reverseRowWord_two_canonical`) and the lattice-word predicate, the
    row-1 one-count `c₁ = r₁ - c₀` is bounded by the row-0 zero-count `r₀`.
    Mirrors lrCoeff2's Guard D at `Hilbert15OQ02.lean:149` (under the
    renaming `r₀ ↔ r₁`, `c₁ ↔ lam.b`). See S3c-prep-14 §5 for derivation. -/
theorem skewSSYTFin_lattice_bound_row1 {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) (lam : Partition 2)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (hcont0 : T.content 0 = lam.parts 0)
    (hLW : isLatticeWord T.reverseRowWord) :
    ν.parts 1 - μ.parts 1 - (lam.parts 0 - (ν.parts 0 - μ.parts 0)) ≤
    ν.parts 0 - μ.parts 0 := by
  set r₀ := ν.parts 0 - μ.parts 0 with hr₀_def
  set r₁ := ν.parts 1 - μ.parts 1 with hr₁_def
  set c₀ := lam.parts 0 - r₀ with hc₀_def
  have hcan := reverseRowWord_two_canonical T lam hrow0 hcont0
  have hlen : T.reverseRowWord.length = r₀ + r₁ := reverseRowWord_two_length T
  have hbnd : r₀ + (r₁ - c₀) < T.reverseRowWord.length + 1 := by
    rw [hlen]; have : r₁ - c₀ ≤ r₁ := Nat.sub_le _ _; omega
  have hcnt :
      (T.reverseRowWord.take (r₀ + (r₁ - c₀))).count (1 : Fin 2) ≤
      (T.reverseRowWord.take (r₀ + (r₁ - c₀))).count (0 : Fin 2) :=
    hLW ⟨r₀ + (r₁ - c₀), hbnd⟩ 0 1 (by decide)
  rw [hcan] at hcnt
  simp [List.take_append_of_le_length, List.length_replicate, List.length_append,
        List.count_append, List.count_replicate_self,
        (show (0 : Fin 2) ≠ 1 by decide),
        (show (1 : Fin 2) ≠ 0 by decide)] at hcnt
  exact hcnt

end Hilbert15OQ02OQ03OQ01
