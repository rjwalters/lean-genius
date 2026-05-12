/-
# Bounded Prime Gaps — OQ-03-OQ-02:
# Decidability infrastructure for `IsAdmissible`

This file is the S2 deliverable of the
`bounded-prime-gaps-oq-03-oq-02` research thread (S1 OBSERVE
merged in PR #17774 as a doc-only scaffold). It implements the
§3.1 prerequisite from `research/problems/bounded-prime-gaps-oq-03-oq-02/knowledge.md`:
a `Decidable` instance for `IsAdmissible H`, obtained via a
bounded reformulation that restricts the prime quantifier to
`p ∈ Finset.range (H.card + 1)`.

## Mathematical content

The unbounded definition

```
IsAdmissible H := ∀ p : ℕ, Nat.Prime p → (H.image (· % p)).card < p
```

quantifies over all primes, but the constraint is automatic for
`p > H.card` because `(H.image (· % p)).card ≤ H.card < p` by
`Finset.card_image_le`. So `IsAdmissible H` is equivalent to its
restriction to `p ∈ Finset.range (H.card + 1)`, which is a
`Finset`-bounded `∀`-quantifier and therefore decidable via
`Finset.decidableDforallFinset` (combined with
`Nat.decidablePrime` and `Nat.decLt`).

## Results

* `IsAdmissibleBdd H` — the bounded reformulation
  (an `abbrev` so its body is transparent for instance search).
* `isAdmissible_iff_bdd` — the unbounded/bounded equivalence.
  The non-trivial direction discharges primes `p > H.card` via
  `Finset.card_image_le`.
* `instDecidableIsAdmissible` — `Decidable (IsAdmissible H)`,
  obtained by transport along the equivalence through
  `decidable_of_iff`.

This unblocks the small-case `native_decide` sanity checks
described in §3.3 of `knowledge.md`, and is a hard prerequisite
for the eventual Path-B verified-backtracking work (§4) that
aims to replace the `engelsma_lower_bound` axiom in
`BoundedPrimeGapsOQ03.lean` (line 134).

## Status

Build: pending. The current worktree shares the broken
`proofs/.lake` symlink trap (per memory
`feedback_researcher_lake_symlink_broken.md`), so Docker build
is not run before commit. The proof script consists of
`omega` on a four-term `≤`/`<` chain plus standard Mathlib API
(`Finset.mem_range`, `Nat.lt_succ_of_le`, `Nat.lt_of_not_le`,
`Finset.card_image_le`) — all stable; build risk is low.

Axioms: 0
Sorries: 0

Tags: number-theory, primes, prime-gaps, admissible-tuples,
decidability, certified-computation
-/

import Mathlib
import Proofs.BoundedPrimeGaps

namespace BoundedPrimeGapsOQ03OQ02

open BoundedPrimeGaps Finset

/-- `IsAdmissibleBdd H` is `IsAdmissible H` restricted to primes
`p ∈ Finset.range (H.card + 1)`. Phrased as a `Finset`-bounded
`∀`-quantifier so that decidability follows directly from
`Finset.decidableDforallFinset` together with `Nat.decidablePrime`
and `Nat.decLt`.

Declared as `abbrev` so the body is transparent during instance
search; the wrapping name is just for readability. -/
abbrev IsAdmissibleBdd (H : Finset ℕ) : Prop :=
  ∀ p ∈ Finset.range (H.card + 1), Nat.Prime p →
    (H.image (· % p)).card < p

/-- The unbounded admissibility condition is equivalent to its
bounded form. The forward direction is by restriction; the
backward direction case-splits on `p ≤ H.card`, dispatching the
`p > H.card` case via the chain
`(H.image (· % p)).card ≤ H.card < p` from
`Finset.card_image_le`. -/
theorem isAdmissible_iff_bdd (H : Finset ℕ) :
    IsAdmissible H ↔ IsAdmissibleBdd H := by
  constructor
  · intro h p _hmem hp
    exact h p hp
  · intro h p hp
    by_cases hpcard : p ≤ H.card
    · refine h p ?_ hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hpcard)
    · have hH_lt : H.card < p := Nat.lt_of_not_le hpcard
      have hle : (H.image (· % p)).card ≤ H.card := Finset.card_image_le
      omega

/-- `IsAdmissible H` is decidable. Transports the `abbrev`-level
decidability of `IsAdmissibleBdd H` (which Lean finds via
`Finset.decidableDforallFinset` + `Nat.decidablePrime` + `Nat.decLt`)
along the `isAdmissible_iff_bdd` equivalence. -/
instance instDecidableIsAdmissible (H : Finset ℕ) :
    Decidable (IsAdmissible H) :=
  decidable_of_iff (IsAdmissibleBdd H) (isAdmissible_iff_bdd H).symm

end BoundedPrimeGapsOQ03OQ02
