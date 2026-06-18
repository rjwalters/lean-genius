# Knowledge: abundant-number-oq-01 (Smallest Abundant Number Is 12)

## Summary

**Target**: `IsLeast {n : ℕ | n.Abundant} 12` — 12 is the least abundant number.

**Key realization**: Mathlib *already has the hard half*. `Nat.Abundant` is
defined and `Nat.abundant_twelve : Nat.Abundant 12` is proven in
`Mathlib/NumberTheory/FactorisationProperties.lean`. The only missing piece is
**minimality**: that no `n < 12` is abundant. That is a finite, decidable check.

**Approach (complete, axiom-free)**:
- `not_abundant_below_twelve : ∀ n < 12, ¬ Nat.Abundant n := by decide`
  - `∀ n < 12, P n` is decidable via `Nat.decidableBallLT`.
  - `Nat.Abundant k` is a decidable comparison `k < ∑ d ∈ k.properDivisors, d`.
- `smallest_abundant`: `IsLeast` = membership (`Nat.abundant_twelve`) + lower
  bound. Lower bound by `by_contra` + `push_neg` (`n < 12`) + the case lemma.

**Status**: `decide` reduces in the kernel ⇒ `verified` (not `native_decide`,
so no `Lean.ofReduceBool`). File `proofs/Proofs/AbundantNumberOQ01.lean` written;
NOT registered in `Proofs.lean` (build-pending honesty — see below).

## Numeric certificate

`research/problems/abundant-number-oq-01/verify_abundant.py` PASSES: proper
divisor sums for n=0..11 are all ≤ n (6 is perfect: sum 6 = 6, not abundant),
and 12 has proper-divisor sum 16 > 12. So 12 is the first abundant number.

## Sessions

### Session 2026-06-16 (Session 1) — FRESH

**Mode**: FRESH · **Outcome**: progress (proof written, verification-gated)

#### What I Did
- Selected `abundant-number-oq-01` (tractability 8, decidable). Claimed lock.
- Found `Nat.Abundant` + `Nat.abundant_twelve` already in Mathlib v4.26 via the
  offline checkout `/Users/rwalters/GitHub/mathlib4`.
- Identified the genuine gap = minimality (no n<12 abundant), which Mathlib lacks.
- Wrote `proofs/Proofs/AbundantNumberOQ01.lean`: `twelve_abundant` (wraps
  `Nat.abundant_twelve`), `not_abundant_below_twelve` (`decide`), and
  `smallest_abundant : IsLeast {n | n.Abundant} 12`.
- Wrote + ran `verify_abundant.py` (PASS).

#### Key Findings
- Mathlib already proves 12 is abundant; only "smallest" was missing.
- Whole result is decidable and axiom-free (kernel `decide`).

#### Blockers
- **Aristotle backend**: 404 "Resource not found" (down this session).
- **Docker**: daemon unresponsive (`docker info` hangs) — no local build.
- Neither verification path available ⇒ file left UNREGISTERED to avoid a
  false-green gallery entry.

#### Next Steps
- When Docker is up: `./proofs/scripts/docker-build.sh Proofs.AbundantNumberOQ01`,
  grep log for `error:`. If green, register in `Proofs.lean` + add gallery data
  under `src/data/proofs/abundant-number-oq-01/`. If `decide` is too slow in the
  kernel, the cases are tiny (n<12) so it should be fine without `native_decide`.
- Possible follow-up OQ: smallest *odd* abundant number is 945 (much larger
  search, still decidable but a real bound-justification problem).

### Session 2026-06-18 (Session 2) — REVISIT / integrate + extend (researcher-4)

**Mode**: REVISIT · **Outcome**: progress (BUILD CONFIRMED GREEN, PR opened)

#### What I Did
- Found Session-1's `AbundantNumberOQ01.lean` and a sibling
  `AbundantMultiplesOQ01.lean` (multiples-of-abundant-are-abundant, from
  merged-but-clobbered PRs #25180/#25190) both present on disk but ORPHANED:
  unregistered in `Proofs.lean`, no gallery dir.
- Discovered the bare minimality result is ALSO already in the gallery under
  `sum-of-divisors` (`twelve_smallest_abundant`, via `native_decide` on a
  file-local `sigma`/`IsAbundant`). To avoid pure duplication and add genuine
  value, framed the new entry around STRUCTURE, not just minimality.
- Added headline theorem `infinitely_many_abundant : {n | n.Abundant}.Infinite`
  to `AbundantMultiplesOQ01.lean`, via injective family `k ↦ 12·(k+1)`
  (`twelve_mul_succ_injective` + `Set.infinite_of_injective_forall_mem`),
  resting on the existing `abundant_twelve_mul` / `abundant_mul_right`.
- Registered both files in `Proofs.lean` (regen script); created gallery entry
  `src/data/proofs/abundant-number-oq-01/` (meta.json + annotations.json).

#### Key Findings
- Infinitude is elementary (no analytic input): closure under multiples turns
  the single witness 12 into an infinite family. Distinct from the deep density
  statement (≈ 0.2476, Davenport).
- The entry's distinct value vs `sum-of-divisors`: canonical `Nat.Abundant`
  (not file-local), axiom-free kernel `decide` for minimality, plus closure +
  infinitude that `sum-of-divisors` does not contain.

#### Files Modified
- `proofs/Proofs/AbundantMultiplesOQ01.lean` (+2 theorems, header updated)
- `proofs/Proofs.lean` (registered both Abundant modules)
- `src/data/proofs/abundant-number-oq-01/{meta.json,annotations.json}` (new)

#### Build Outcome (this session)
- Docker build of `Proofs.AbundantMultiplesOQ01` + `Proofs.AbundantNumberOQ01`
  **succeeded** (7743 jobs, Lean v4.26.0). The Session-1 "checked via Aristotle"
  note was WRONG — first build caught two real errors, now fixed:
  1. `pos_of_abundant`: `by decide` could not synthesize `Decidable ¬Nat.Abundant 0`.
     Fixed by rewriting via `abundant_iff_two_mul_lt_sigma` + `Nat.divisors_zero`
     then `simp`.
  2. `abundant_mul_right`: `Finset.sum_image hinj` higher-order unification failed
     on the `∑ d, t*d` target (`?g (t*d) =?= t*d` is not a Miller pattern). Fixed
     by introducing `himg : ∑ x ∈ image …, x = t * σ(a)` so the sum is over the
     bound variable (`?g x =?= x` ⇒ `g = id`), discharged by
     `rw [Finset.sum_image hinj, Finset.mul_sum]`.
- LESSON: never trust an unbuilt "verified via external backend" note — kernel
  `decide` decidability-instance gaps and `sum_image` HO-unification are exactly
  the failures that only surface at `lake build`.

#### Next Steps
- (Follow-ups) positive natural density (Davenport ≈ 0.2476); smallest ODD
  abundant = 945; every integer > 20161 is a sum of two abundant numbers.
