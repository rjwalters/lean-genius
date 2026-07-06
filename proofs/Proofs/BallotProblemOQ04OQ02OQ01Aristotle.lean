/-
# First-Return Bijection for Non-Crossing Partitions (Aristotle companion)

Self-contained proof-search target for the sole open obligation of
`ballot-problem-oq-04-oq-02-oq-01` (`Proofs/BallotProblemOQ04OQ02OQ01.lean`):

  `nonCrossingCount = catalan` is reduced there to a single combinatorial recurrence, whose
  counting half is proved and whose *sole remaining `sorry`* is the first-return bijection
  `nonempty_firstReturnEquiv`.

This companion inlines the (self-contained) predicate `IsNonCrossingFp` — it depends only on
Mathlib's `Finpartition`, not on the local `Proofs.BallotProblemOQ04*` files — so the bijection
is a valid, dependency-free target for automated proof search. A successful proof here ports
directly back into `BallotProblemOQ04OQ02OQ01.lean` (the two `IsNonCrossingFp` definitions are
character-for-character identical).

The decomposition is the classical non-crossing-partition Catalan recursion around a
distinguished point; Mathlib has no theory of non-crossing partitions, so this is genuinely
new combinatorial infrastructure.
-/

import Mathlib

open Finset

namespace FirstReturnBijection

/-- Non-crossing predicate on a finite partition of `Fin n`: no two distinct parts interleave.
Whenever `a < b < c < d` with `c ∈ P.part a` and `d ∈ P.part b`, already `b ∈ P.part a`.
(Character-for-character copy of `BallotProblemOQ04OQ02.IsNonCrossingFp`.) -/
def IsNonCrossingFp {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d → c ∈ P.part a → d ∈ P.part b → b ∈ P.part a

/-- Decidability: all quantifiers range over the finite `Fin n`, membership in a `Finset` is
decidable. -/
instance instDecidableIsNonCrossingFp {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) :
    Decidable (IsNonCrossingFp P) := by
  unfold IsNonCrossingFp; infer_instance

/-- **First-return bijection (the sole open obligation).** A non-crossing partition of the
linearly ordered set `Fin (n+1)` decomposes — via the classical "first return" of the block
structure around a distinguished point — into an independent pair of non-crossing partitions of
an `i`-element and a `j`-element interval, with `(i, j)` ranging over `antidiagonal n`.
Existence of the bijection suffices for the count. -/
theorem nonempty_firstReturnEquiv (n : ℕ) :
    Nonempty ({P : Finpartition (univ : Finset (Fin (n + 1))) // IsNonCrossingFp P} ≃
      Σ ij : (antidiagonal n : Finset (ℕ × ℕ)),
        {P : Finpartition (univ : Finset (Fin ij.1.1)) // IsNonCrossingFp P} ×
        {P : Finpartition (univ : Finset (Fin ij.1.2)) // IsNonCrossingFp P}) := by
  sorry

end FirstReturnBijection
