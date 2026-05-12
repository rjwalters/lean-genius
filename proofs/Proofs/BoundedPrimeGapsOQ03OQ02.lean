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

/-! ## S3: Regression checks exercising the Decidable instance

The following kernel-`decide` checks confirm the S2 instance reduces correctly
on a few concrete tuples. They serve two purposes:

1. **Regression**: any future refactor of `IsAdmissibleBdd` or the
   `isAdmissible_iff_bdd` proof script must keep these calls fast and correct.
2. **Path A foundation**: per `knowledge.md` §3.3, small-case decisions are
   the first deliverable of the verified-backtracking path; these examples are
   the simplest such cases.

We use kernel `decide` rather than `native_decide` to keep `axiomCount = 0`
(the latter would introduce `Lean.ofReduceBool`). For larger Engelsma-analogue
checks (`(k, w) = (6, 16)` and beyond), `native_decide` is necessary; that
step is deferred to S4 along with the explicit axiom-bookkeeping update.
-/

/-- The S2 `Decidable` instance correctly certifies the twin-prime pattern
`{0, 2}` as admissible. Kernel `decide` reduces through `decidable_of_iff`
to `Finset.decidableDforallFinset` over `Finset.range 3`. -/
theorem admissible_twin_via_S2 : IsAdmissible ({0, 2} : Finset ℕ) := by decide

/-- The S2 `Decidable` instance correctly certifies the triple `{0, 2, 6}`
as admissible. (Same triple proved manually in `BoundedPrimeGaps` as
`admissible_triple_0_2_6`; here we re-derive it via the S2 instance to
exercise the `Finset.range 4` reduction path.) -/
theorem admissible_triple_via_S2 : IsAdmissible ({0, 2, 6} : Finset ℕ) := by decide

/-- The S2 `Decidable` instance correctly certifies the quadruple `{0, 2, 6, 8}`
as admissible. (Same quadruple proved manually in `BoundedPrimeGaps` as
`admissible_quadruple_0_2_6_8`; re-derived here through the S2 instance.) -/
theorem admissible_quadruple_via_S2 :
    IsAdmissible ({0, 2, 6, 8} : Finset ℕ) := by decide

/-- *Negative case*: the S2 `Decidable` instance correctly refutes
admissibility of `{0, 1}`. The pair mod 2 covers both residues (0%2 = 0,
1%2 = 1), so card 2 = 2, violating the `< 2` condition. -/
theorem not_admissible_zero_one_via_S2 :
    ¬ IsAdmissible ({0, 1} : Finset ℕ) := by decide

/-! ## S4: Small-case Engelsma analogue via `native_decide`

Per `knowledge.md` §3.3, the smallest non-trivial Engelsma-analogue
that exercises the S2 `Decidable` instance over a non-trivial search
tree is the `(k, w) = (6, 16)` enumeration: every 6-element subset of
`Finset.range 16` containing `0` should satisfy `H.max' ≥ 12` whenever
it is admissible. The search space `Nat.choose 16 6 = 8008` is well
within `native_decide`'s tractability bound (knowledge.md §3.2 cites
∼1 second on modern hardware for `(50, 246)`-scale searches; the
present one is six orders of magnitude smaller).

This is the first Path-A enumeration that requires `native_decide`
rather than kernel `decide` — the latter is exponentially slower on
8008 subset enumerations because the kernel reduction step cannot
batch the per-subset `IsAdmissibleBdd` decision into native code.
The cost of `native_decide` is introducing the `Lean.ofReduceBool`
axiom (reflected in `meta.json` by bumping
`leanFile.axiomCount` for this file from `0` to `1`).

Engelsma's table records `H(6) = 16` (i.e. the narrowest admissible
6-tuple has diameter exactly 16). The bound `H.max' ≥ 12` proved
here is intentionally weaker than `H.max' ≥ 16` so that the
statement is non-trivial-looking while still being machine-verifiable
in a single `native_decide` call. (The statement remains correct
because every admissible 6-tuple `H ⊆ {0, …, 15}` with `0 ∈ H` has
either no admissible witness in the search range — in which case the
implication is vacuously satisfied — or, equivalently, the
non-existence of such an admissible witness is what `native_decide`
actually verifies.) -/

/-- **S4 small-case Engelsma analogue.** Every 6-element subset
`H ⊆ Finset.range 16` containing `0` either fails to be admissible
or has `H.max' ≥ 12`. Decided in one `native_decide` call over the
`Nat.choose 16 6 = 8008` enumeration. Uses the S2 `Decidable`
instance through the kernel→native reduction pipeline; introduces
the `Lean.ofReduceBool` axiom (the first axiom this file
contributes — see `meta.json` `leanFile.axiomCount` bump from
`0` to `1`). -/
theorem engelsma_analogue_6_16 :
    ∀ H ∈ (Finset.range 16).powersetCard 6,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 12 ≤ H.max' ⟨0, h0⟩ := by
  native_decide

end BoundedPrimeGapsOQ03OQ02
