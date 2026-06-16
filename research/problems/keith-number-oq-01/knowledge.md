# Knowledge: keith-number-oq-01 (Smallest Keith Number Is 14)

## Summary

**Target**: `IsLeast {n : ℕ | IsKeith n} 14` — 14 is the least Keith number.

**Key realization**: Mathlib has *nothing* on Keith numbers, so the entry must
both **define** the predicate and **prove** minimality. Both halves are finite
and decidable: define the digit recurrence as a fuel-bounded sliding-window
computation, then check that 14 is Keith and that 10, 11, 12, 13 are not (numbers
< 10 are excluded by the `10 ≤ n` clause).

**Approach (complete, axiom-free)**:
- `lsdDigits (fuel n)`: decimal digits, least-significant first, by *structural*
  recursion on `fuel` (NOT `Nat.digits`, which is well-founded recursion and does
  not reduce under kernel `decide`). `msdDigits n = (lsdDigits n n).reverse`.
- `step w = w.tail ++ [w.sum]`: slide the length-`d` window one Keith step.
- `reaches target fuel w`: iterate `step`, return `true` when the running window
  sum equals `target`, `false` once it exceeds `target` (sum is monotone), bounded
  by `fuel`.
- `IsKeith n := 10 ≤ n ∧ reaches n 40 (msdDigits n) = true`, with an explicit
  `DecidablePred IsKeith` instance via `inferInstanceAs`.
- `keith_fourteen : IsKeith 14 := by decide`.
- `not_keith_below_fourteen : ∀ n < 14, ¬ IsKeith n := by decide`
  (`∀ n < 14` decidable via `Nat.decidableBallLT`).
- `smallest_keith : IsLeast {n | IsKeith n} 14` via `refine ⟨keith_fourteen, ?_⟩`
  + `by_contra` + `push_neg` (`n < 14`) + the case lemma. Identical shape to the
  `smallest_abundant` proof in `AbundantNumberOQ01.lean`.

**Status**: `decide` reduces in the kernel ⇒ intended `verified` (no
`native_decide`/`Lean.ofReduceBool`). File `proofs/Proofs/KeithNumberOQ01.lean`
written; NOT registered in `Proofs.lean` (build-pending honesty — see below).

## Numeric certificate

`research/problems/keith-number-oq-01/verify_keith.py` PASSES: `is_keith(n)` is
false for n=0..13 and true for 14 (sequence 1,4,5,9,14); first Keith numbers
14, 19, 28, 47 match OEIS A007629.

## Design risk addressed

The obvious encoding via `Nat.digits 10 n` would likely make `decide` fail or
hang: `Nat.digits`/`Nat.digitsAux` use well-founded recursion (`Acc.rec`), which
the kernel struggles to reduce. Replacing it with the fuel-structural `lsdDigits`
keeps every computation in kernel-reducible territory (Nat div/mod on literals are
kernel-accelerated), preserving the axiom-free `decide` proof.

## Sessions

### Session 2026-06-16 (Session 1) — FRESH

**Mode**: FRESH · **Outcome**: progress (proof written, build-gated)

#### What I Did
- Selected `keith-number-oq-01` (tractability 7, tagged `decidable`). Claimed lock.
  No existing proof, no competing PR, no sibling process.
- Verified the math in Python: 14 is the smallest Keith number; 10–13 overshoot.
- Designed a kernel-`decide`-friendly formalization: custom structural-recursion
  digit function + sliding-window recurrence, avoiding `Nat.digits`.
- Wrote `proofs/Proofs/KeithNumberOQ01.lean` (`IsKeith`, `DecidablePred` instance,
  `keith_fourteen`, `not_keith_below_fourteen`, `smallest_keith`).
- Wrote + ran `verify_keith.py` (PASS, matches OEIS A007629).

#### Key Findings
- Mathlib has no Keith-number infrastructure; whole entry is self-contained.
- Whole result is decidable and intended axiom-free (kernel `decide`).
- `Nat.digits` is a `decide` hazard (WF recursion) — used a structural digit fn.

#### Blockers
- **Docker**: daemon unresponsive this session (`docker ps -a` returns empty with
  ~10 stuck `docker-build.sh` peers and 0 running containers; build attempt stalls
  at container creation) — no local build verification.
- File left UNREGISTERED in `Proofs.lean` to avoid a false-green gallery entry.

#### Next Steps
- When Docker is up: `./proofs/scripts/docker-build.sh Proofs.KeithNumberOQ01`,
  grep log for `error:`. The cases are tiny (n ≤ 14, fuel ≤ ~10 steps) so kernel
  `decide` should suffice without `native_decide`. If `inferInstanceAs` complains,
  fall back to `deriving DecidableEq`/`decidable_of_iff`.
- If green: register in `Proofs.lean` + add gallery data under
  `src/data/proofs/keith-number-oq-01/`.
- Possible follow-up OQ: smallest *3-digit* Keith number is 197, or characterize
  why 2-digit Keith numbers are exactly {14,19,28,47,61,75} (finite, decidable).
