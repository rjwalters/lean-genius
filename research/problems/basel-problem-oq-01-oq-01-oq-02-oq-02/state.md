# Current State

**Phase**: ORIENT
**Since**: 2026-05-08T03:50:00Z
**Iteration**: 4

## Current Focus

Sessions 1-3 (research-9 et al) built the lcm-divisibility infrastructure
(`lcmRange`, `dvd_lcmRange`, `pow_dvd_lcmRange_pow`) and the harmonic-cubed
infrastructure (`harmonicCubed`, base values, non-negativity, monotonicity)
in `Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean` (route F — van der Poorten
closed-form denominator analysis). Session 3 noted the main divisibility
theorem `harmonicCubed_lcm_clear` was scaffolded but ran out of Docker
build time on the per-term `Nat.cast_div`/`push_cast` rewrite chain.

## Active Approach

Continue route (F): supply the *isolable* per-term integrality bridge
that bypasses the per-term `Nat.cast_div`/`push_cast` issue documented in
session 3, leaving the next session a clean induction on `n` for the full
`harmonicCubed_lcm_clear`.

## Blockers

None for this session — the per-term bridge compiles fast (no Finset
aggregation, no `push_cast` through `Int.ofNat_div`).

The full `harmonicCubed_lcm_clear` still needs:
1. The local `lcmRange n ∣ lcmRange (n+1)` step lemma (or import from sibling
   `BaselProblemOQ01OQ01OQ02OQ03.lcmRange_dvd_lcmRange_of_le`); and
2. The induction-step assembly combining `harmonicCubed_succ` with
   `term_lcm_clear_cube_nat` to lift the IH across the new term.

## Next Action

Session 5: prove `harmonicCubed_lcm_clear : ∃ m : ℤ, (lcmRange n : ℚ)^3 *
harmonicCubed n = m` by induction on `n`, using
`harmonicCubed_succ` + `term_lcm_clear_cube_nat` (now available from
session 4) + a structural `lcmRange n ∣ lcmRange (n+1)` lemma.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 3
- Approaches tried: 1 (route F, van der Poorten closed form)

## Iteration 4 Builds (researcher-10, 2026-05-08)

Focus: provide the **per-term integrality bridge** that the next session
needs to compose `harmonicCubed_lcm_clear` cleanly — sidestepping the
`Nat.cast_div`/`push_cast` rewrite chain that timed out the Docker build
in session 3.

- `harmonicCubed_succ : harmonicCubed (n + 1) = harmonicCubed n + 1/(n+1)^3`
  (axiom-free): the inductive-step identity, one-line proof via
  `Finset.sum_range_succ`. Required for any induction on `n` of
  `harmonicCubed_lcm_clear`.
- `harmonicCubed_two : harmonicCubed 2 = 9/8` (axiom-free): numerical
  witness verifying the recurrence at the smallest non-trivial case.
- `lcmRange_pow_eq_mul`: repackages `pow_dvd_lcmRange_pow` with an
  explicit `m : ℕ` witness and the multiplication on the *outside*,
  i.e., `(lcmRange n)^p = m * k^p`. This is the Nat-arithmetic form
  needed to bridge cleanly into ℚ without going through `Int.div`.
- `term_lcm_clear_nat {k n p} (hk : 0 < k) (hkn : k ≤ n)`:
  `∃ m : ℕ, (lcmRange n : ℚ)^p / (k : ℚ)^p = (m : ℚ)`. The per-term
  rational integrality: bypasses session 3's `Nat.cast_div` issue by
  rewriting through the multiplicative form `lcmRange_pow_eq_mul` and
  casting `Nat → ℚ` directly (no intermediate `Int` step that
  `push_cast` would aggressively rewrite).
- `term_lcm_clear_cube_nat`: the `p = 3` specialization for
  `harmonicCubed_lcm_clear`'s recurrence target.
- `term_lcm_clear_int`: integer-witness form (`∃ m : ℤ, …`) matching
  the `denominator_control` axiom's signature, for direct combination
  with the parent's `denominator_control_factorial` API.

**Counts**: lineCount 239 → ~312 (+73), theoremCount 14 → 20 (+6),
axiomCount 0 (unchanged), sorries 0 (unchanged). New theorems: 6
substantive lemmas (1 recurrence, 1 numerical witness, 4 integrality).

**Build**: verified via `./proofs/scripts/docker-build.sh
Proofs.BaselProblemOQ01OQ01OQ02OQ02`.

## Iteration 3 Builds (researcher-9, 2026-05-08)

Earlier session's progress (carried forward):
- Added `harmonicCubed` definition + base values + non-negativity +
  monotonicity (4 lemmas).
- Scaffolded `harmonicCubed_lcm_clear` proof but Docker build timed
  out twice on the `Nat.cast_div`/`push_cast` rewrite chain.

## Iteration 2 Builds (earlier session, 2026-05-08)

- Added `dvd_lcmRange`, `pow_dvd_lcmRange_pow`,
  `cube_dvd_lcmRange_cube`, `succ_cube_dvd_lcmRange_succ_cube`.
- Added numerical witnesses `lcmRange_zero` through `lcmRange_five`.
- Documented gap analysis showing route (P) (recurrence-induction)
  fails at n=2→n=4 step due to cancellation.

## Iteration 1 Builds (earlier session, OBSERVE phase, 2026-05-07)

- Surveyed parent file's `denominator_control_factorial` (axiom-free
  factorial bound).
- Identified route (F) (van der Poorten closed form) as the cleanest
  path forward; route (P) requires per-prime p-adic invariant (heavy).
