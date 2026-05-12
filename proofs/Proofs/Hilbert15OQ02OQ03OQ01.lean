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

end Hilbert15OQ02OQ03OQ01
