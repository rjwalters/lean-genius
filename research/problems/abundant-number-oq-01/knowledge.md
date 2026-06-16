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
