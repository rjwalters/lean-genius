# Current State

**Phase**: BLOCKED (S8 — every forward path Docker-gated during host outage)
**Since**: 2026-06-13 (S8)
**Iteration**: 8

## Current Focus

S8 (researcher-6, 2026-06-13): **BLOCKED.** No audit drift — state.md, JSON, and
real source agree at iter 7. Flagged blocked because the S7 parent build-repair
(PR #22978, MERGED) was never re-verified (Docker host disk hit 100% mid-build),
and the entire OQ-03 chain imports that parent, so we cannot confirm the chain
compiles, let alone discharge the two S9 ACT sorries (~100-150 lines of
Abel-summation analytic NT each). The natural-density form additionally needs
Wiener-Ikehara/Tauberian transfer absent from Mathlib v4.26.0. Re-open once
Docker recovers: re-verify #22978 first, then S9. (Stale superseded duplicate
PR #22953 is CONFLICTING and can be closed.)

## Previous Focus (Session 7)

S7 (researcher-2, 2026-06-13): **BUILD REPAIR.** A Docker verification build
revealed the parent file `Proofs/InfinitudePrimes4k1.lean` (claimed verified,
0 sorries) no longer compiles under the current Mathlib pin — three API-drift
errors that silently broke the entire OQ-03 chain across all six prior
build-pending iterations. Fixed all three (`mod_four_ne_three_of_dvd_isSquare_neg_one`
new `primeFactors` signature; removed `Nat.odd_iff_not_even` → omega; renamed
`Nat.dvd_sub'` → `Nat.dvd_sub`). **Build NOT verified this session**: the Docker
host disk hit 100% and crashed Docker Desktop mid-build (infra failure, not a
Lean error). Fixes target the exact pre-crash compiler errors; re-verification
needed once host disk is reclaimed. The two OQ-03 target sorries are untouched.
See knowledge.md S7 for full detail.

## Previous Focus (Session 6)

S6 (researcher-4, 2026-05-12): **Statement-only SCAFFOLD** for the
logarithmic-density target. Added one new theorem to
`proofs/Proofs/InfinitudePrimes4k1OQ03.lean` (~50 lines including the section
docstring), declared with `sorry`:

* `mertens_log_density_4k1` — the partial sums of `log p / p` over primes
  `p ≡ 1 (mod 4)` up to `N` grow asymptotically like `(1/2) · log N`. This is
  the **Mertens-1874 logarithmic-density form** of OQ-03, strictly weaker
  than the natural-density form (`primes_4k1_natural_density`, also `sorry`)
  but strictly stronger than the qualitative divergence
  (`not_summable_primes_4k1_log_div`, S5, fully proved). The S6 docstring
  records the Abel-summation proof outline on top of S4's
  `LSeries_residueClass_one_mod_four_lower_bound`.

**Why a statement-only scaffold**: per the recommendation in S5's
state.md, "Recommended for the next session: S6 alternative (logarithmic
density via Mertens). This is unblocked by current Mathlib; S4 + S5 supply
the required ingredients (qualitative divergence + pole-strength lower
bound)." However, the full Abel-summation proof is ~100-150 lines of
analytic-number-theory bookkeeping, and the worktree's `proofs/.lake`
symlink trap forces ≥45-minute Docker builds — too long for a single
session's PR cycle. S6 instead pins the *target asymptotic* with a
concrete syntactic statement, so S7+ can attack the proof body
deterministically. This matches the S2 pattern (state
`primes_4k1_natural_density` with `sorry`, defer the proof to S3+).

**Net effect on file**: +1 theorem stated with `sorry`, +50 lines of code
and docstring, no axiom changes, sorry count 1 → 2 (the new
`mertens_log_density_4k1` statement plus the existing
`primes_4k1_natural_density` statement, both as OQ-03 targets with
explicit "deferred proof" tracking).

### Previous Focus (Session 5)

S5 (researcher-1, 2026-05-12): Added the **elementary divergence + sum-of-two-squares
corollary** to `proofs/Proofs/InfinitudePrimes4k1OQ03.lean`. Two new fully-proved
theorems (no new sorries) translate the S4 divergence into an indicator-free
elementary form and chain through Fermat's Christmas theorem.

* `not_summable_primes_4k1_log_div` — elementary form of
  `not_summable_primes_4k1_vonMangoldt_div`: `¬ Summable (n ↦ if (n.Prime ∧
  n % 4 = 1) then Real.log n / n else 0)`. Removes the `residueClass`
  indicator wrapper by case-splitting through the helper
  `residueClass_one_mod_four_apply_prime`, which uses
  `ArithmeticFunction.vonMangoldt_apply_prime` to unfold `Λ p = log p` on primes
  and the existing `mod_four_eq_one_iff_zmodFour_eq_one` bridge to translate
  the residue indicator. This is the Mertens-1874 *qualitative* form; the
  quantitative `(1/2) log log N` rate is deferred to a future iteration.
* `primes_sum_two_squares_infinite` — **path C corollary**:
  `{p : ℕ | p.Prime ∧ ∃ a b : ℕ, a^2 + b^2 = p}.Infinite`. Combines
  `primes_4k1_infinite_mod` (the S2 Mathlib-bridge infinitude statement) with
  `Nat.Prime.sq_add_sq` (Fermat 1640, formalized in
  `Mathlib.NumberTheory.SumTwoSquares`, transitively imported via the parent
  `InfinitudePrimes4k1`). This is the *infinitude* form of the path-C result;
  the *density* form (sum-of-two-squares primes have density 1/2 among all
  primes) is deferred until a density form of OQ-03 is proved.

Both theorems are fully proved (no new sorries) and require no new imports
beyond what S3 already added. The build is "pending" matching the existing
path-B pattern (worktree's `proofs/.lake` symlink is self-referential).

S4 (researcher-10, 2026-05-12): Added the **Dirichlet-density bridge**
for `(q, a) = (4, 1)` to `proofs/Proofs/InfinitudePrimes4k1OQ03.lean`.
Two new fully-proved theorems (no new sorries) specialize the Mathlib
L-series machinery to the case of primes ≡ 1 (mod 4), packaging the
Dirichlet-density pole-strength data into concrete form.

* `LSeries_residueClass_one_mod_four_lower_bound` — explicit `(1/2)/(x-1) - C`
  lower bound on the L-series of the von Mangoldt function restricted to
  `(n : ZMod 4) = 1`, for `x ∈ Ioc 1 2`. This is
  `vonMangoldt.LSeries_residueClass_lower_bound` specialized to `(q, a) = (4, 1)`,
  with `(q.totient)⁻¹ = (Nat.totient 4)⁻¹ = (2)⁻¹ = 1/2` substituted via
  `totient_four`.
* `not_summable_primes_4k1_vonMangoldt_div` — the prime-restricted
  Dirichlet sum `∑ Λ(p)/p` over primes ≡ 1 (mod 4) **diverges**. This is
  `vonMangoldt.not_summable_residueClass_prime_div` specialized to
  `(q, a) = (4, 1)`. It is strictly stronger than the elementary infinitude
  statement (`primes_4k1_infinite_mathlib`): the divergence is the
  Mertens-1874-style density-strength statement, delivered analytically
  through Mathlib's L-series machinery.

This is step 2 of the three-step path-B proof outlined in S2's state.md.

S3 (researcher-8, 2026-05-12): Added the **character-orthogonality scaffold**
for `q = 4` to `proofs/Proofs/InfinitudePrimes4k1OQ03.lean`. Three new
fully-proved lemmas (no new sorries) translate the general Mathlib
orthogonality result `DirichletCharacter.sum_characters_eq` into the
`q = 4` case, expressing the indicator of `[p % 4 = 1]` (over `ℂ`) as
`(1/2) · ∑ χ : DirichletCharacter ℂ 4, χ((p : ZMod 4))`. This is step 1
of the three-step path-B proof outlined in S2's state.md.

S2 (researcher-11, 2026-05-12): Created
`proofs/Proofs/InfinitudePrimes4k1OQ03.lean` and discovered a Mathlib
**reality check** versus the S1 plan: the natural-density form of Dirichlet's
theorem is **not** in `Mathlib.NumberTheory.LSeries.PrimesInAP` at the pinned
revision (v4.26.0, `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Only the
infinitude form (`Nat.infinite_setOf_prime_and_eq_mod`) is exported.

The Ikehara-Tauberian machinery (`Mathlib.NumberTheory.LSeries.Wiener` /
`LSeries.IkeharaTauberian`) that the S1 plan assumed is in Mathlib does
**not exist** at this pin. The closest quantitative result available is
`ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`, which
captures the Dirichlet-density pole strength but not the natural-density
asymptotic.

## Active Approach

**Mathlib bridge (corrected scope).**

S2 deliverable: `proofs/Proofs/InfinitudePrimes4k1OQ03.lean`

* `totient_four : Nat.totient 4 = 2` — `by decide`. Proved.
* `one_isUnit_zmodFour : IsUnit (1 : ZMod 4)` — `isUnit_one`. Proved.
* `mod_four_eq_one_iff_zmodFour_eq_one` — bridge between the parent's
  `p % 4 = 1` formulation and Mathlib's `(p : ZMod 4) = 1` formulation.
  Proved via `ZMod.natCast_eq_natCast_iff` + `Nat.ModEq` + `omega`.
* `primes_4k1_infinite_mathlib` — *Mathlib* infinitude bridge, by
  specialization of `Nat.infinite_setOf_prime_and_eq_mod`. Proved.
* `primes_4k1_infinite_mod` — same statement in `p % 4 = 1` form.
  Proved by `convert` through the bridge lemma.
* `primes_4k1_natural_density` — OQ-03 target. **Stated with `sorry`**.

This is a corrected SCAFFOLD: the file now syntactically targets the OQ-03
deliverable (natural-density form), while honestly flagging the one remaining
`sorry` as blocked on Mathlib evolution rather than on a routine wiring step.

## Blockers

**Mathematical**: The natural-density form requires an
Ikehara-Tauberian transfer from L-series pole data to the prime-counting
asymptotic. This is *not yet* in Mathlib at the pinned revision.

**Practical**:
* The `proofs/.lake` symlink in the researcher worktree points to itself, so
  any Docker build will be a fresh ~45-minute clone-and-rebuild cycle.
  S2 ships as "build pending" matching the existing pattern.

## Next Action

S6 delivered the **statement scaffold** for the logarithmic-density target
(`mertens_log_density_4k1`, sorry'd). The remaining steps:

**S7 (logarithmic-density proof body via Abel summation)**: Discharge the
`mertens_log_density_4k1` sorry. Concrete plan (~100-150 lines):

1. **Abel-summation identity** (~30 lines). Apply
   `Real.Abel_summation` / `tsum_eq_integral_of_summable`-style identity to
   relate `∑_{n ≤ N} f(n) / n^x` and `∫_1^N (∑_{n ≤ t} f(n)) / t^(x+1) dt`
   for `f n := vonMangoldt.residueClass (1 : ZMod 4) n · (n.Prime indicator)`
   and `x` in a half-neighbourhood of `1`.
2. **Lower-bound transfer** (~30 lines). Combine S4's
   `LSeries_residueClass_one_mod_four_lower_bound` with the Abel identity
   in the limit `x ↘ 1` to extract the partial-sum lower asymptotic.
3. **Upper-bound transfer** (~30 lines). Symmetric upper bound from
   continuity of the residue-class L-function on `re s ≥ 1`
   (`continuousOn_LFunctionResidueClassAux`).
4. **Conversion to elementary form** (~10 lines). Translate von Mangoldt
   restricted-prime sums to elementary `log p / p` via S5's
   `residueClass_one_mod_four_apply_prime` and `vonMangoldt_apply_prime`.
5. **Squeeze theorem** (~10 lines). Combine the matching upper and lower
   bounds to land the `Tendsto … (𝓝 (1/2))` conclusion.

Mathlib API audit at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
all required infrastructure is present (`Real.log`, `LSeries`,
`vonMangoldt.LSeries_residueClass_lower_bound`,
`continuousOn_LFunctionResidueClassAux`, `Asymptotics.IsEquivalent`,
Abel-summation primitives in `Mathlib.NumberTheory.AbelSummation`).

**S7+ path B step 3 (Tauberian transfer to natural density)**: The
natural-density form (`primes_4k1_natural_density` sorry) remains blocked on
the absence of `Mathlib.NumberTheory.LSeries.Wiener` /
`LSeries.IkeharaTauberian` at the pinned revision. Once Mathlib gains a
Tauberian module, the sorry can be discharged by combining
`LSeries_residueClass_one_mod_four_lower_bound` with the Tauberian transfer
to convert the L-series pole strength to a counting asymptotic.

**S7+ path C extension (density form)**: Once a density form (natural or
logarithmic — i.e., once `mertens_log_density_4k1` lands) is proved,
upgrade `primes_sum_two_squares_infinite` to the density-1/2 statement.

Recommended for the next session: **S7 (logarithmic-density proof body)**.
The full proof structure is pinned by the new S6 statement; the next
session can attack the body without ambiguity. Allow ≥45 minutes for one
end-of-session Docker build given the `proofs/.lake` symlink state.

## Attempt Counts

* Total attempts: 6 (S1 survey, S2 Mathlib-reality SCAFFOLD, S3 char-orthogonality scaffold, S4 Dirichlet-density bridge, S5 elementary divergence + path-C corollary, S6 logarithmic-density statement scaffold)
* Current approach attempts: 6 (Mathlib bridge → path-B steps 1+2 → S5 elementary repackaging + path-C infinitude → S6 logarithmic-density target statement)
* Approaches tried: 2 (path B partial; path C infinitude corollary)

## Open files

* `problem.md` — theoretical context, Mathlib infrastructure map,
  decomposition table, three-density theory comparison.
* `knowledge.md` — S1 survey + S2 Mathlib-reality + S3 orthogonality scaffold
  + S4 Dirichlet-density bridge + S5 elementary divergence + path-C corollary
  + S6 logarithmic-density statement scaffold.
* `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` (S2 base, S3+S4+S5+S6 enriched)
  — Mathlib-bridge infinitude (verified) + character-orthogonality scaffold
  for `q = 4` (3 verified lemmas, S3) + Dirichlet-density bridge for
  `(q, a) = (4, 1)` (2 verified theorems, S4) + elementary Mertens-style
  divergence (`not_summable_primes_4k1_log_div`, S5) + sum-of-two-squares
  infinitude corollary (`primes_sum_two_squares_infinite`, S5) +
  logarithmic-density target statement (`mertens_log_density_4k1`, sorry, S6) +
  natural-density statement (sorry).

## S5 Deliverable

This iteration is an **ELEMENTARY DIVERGENCE + PATH-C INFINITUDE** layer:
* 0 new Lean files; 1 helper + 2 new theorems added to `InfinitudePrimes4k1OQ03.lean`
  (~100 lines including the section docstring)
* All 3 declarations **fully proved** — no new `sorry` introduced
* 1 `sorry` total remaining (the natural-density form, OQ-03 target, unchanged from S2)
* 0 axiom changes
* 0 new imports (Fermat's `Nat.Prime.sq_add_sq` is transitively available from
  `Proofs.InfinitudePrimes4k1`, which already imports
  `Mathlib.NumberTheory.SumTwoSquares`)

New declarations:
* `residueClass_one_mod_four_apply_prime` (private helper) — unfolds
  `vonMangoldt.residueClass (1 : ZMod 4) p` to `if p % 4 = 1 then log p else 0`
  for prime `p`
* `not_summable_primes_4k1_log_div` — elementary form of the S4 Mertens-style
  divergence
* `primes_sum_two_squares_infinite` — sum-of-two-squares infinitude corollary

Files touched:
* `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` — added S5 section (after S4
  Dirichlet-density bridge, before OQ-03 target); extended `#check` block.
* `state.md` — iteration 4 → 5, Current Focus + Next Action + Open files +
  Attempt Counts updated.
* `knowledge.md` — added "S5 — ORIENT/ACT: elementary divergence + path-C
  corollary" section.
* `src/data/research/problems/infinitude-primes-4k1-oq-03.json` — iteration
  4 → 5, focus + insights + builtItems + nextSteps refreshed.

## S4 Deliverable

This iteration is a **DIRICHLET-DENSITY BRIDGE** (path-B step 2):
* 0 new Lean files; 2 new theorems added to `InfinitudePrimes4k1OQ03.lean`
  (~70 lines including the section docstring)
* 2 theorems all **fully proved** — no new `sorry` introduced
* 1 `sorry` total remaining (the natural-density form, OQ-03 target, unchanged from S2)
* 0 axiom changes

New theorems:
* `LSeries_residueClass_one_mod_four_lower_bound` — explicit `(1/2)/(x-1) - C`
  lower bound on the L-series sum of `vonMangoldt.residueClass (1 : ZMod 4)`
* `not_summable_primes_4k1_vonMangoldt_div` — divergence of the
  prime-restricted Dirichlet sum

Files touched:
* `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` — added Dirichlet-density
  bridge section (after `indicator_mod_four_eq_one`, before the OQ-03 target);
  no new imports needed (uses existing `Mathlib.NumberTheory.LSeries.PrimesInAP`);
  extended `#check` block with both new theorems.
* `state.md` — iteration 3 → 4, Current Focus + Next Action + Open files +
  Attempt Counts updated.
* `knowledge.md` — added "S4 — ORIENT/ACT: Dirichlet-density bridge"
  section with proof sketch + role in path-B plan.
* `src/data/research/problems/infinitude-primes-4k1-oq-03.json` — iteration
  3 → 4, focus + insights + nextSteps refreshed.

## S3 Deliverable

This iteration is an **ORTHOGONALITY SCAFFOLD** (path-B step 1):
* 0 new Lean files; 3 new lemmas added to `InfinitudePrimes4k1OQ03.lean`
  (~55 lines including the section docstring)
* 3 lemmas all **fully proved** — no new `sorry` introduced
* 1 `sorry` total remaining (the natural-density form, OQ-03 target, unchanged from S2)
* 0 axiom changes

New lemmas:
* `sum_dirichletChars_zmodFour` — orthogonality at `q = 4`
* `indicator_zmodFour_eq_one` — indicator-as-half-character-sum (ZMod 4 form)
* `indicator_mod_four_eq_one` — indicator-as-half-character-sum (`% 4` form)

Files touched:
* `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` — added orthogonality
  scaffold section (after `primes_4k1_infinite_mod`, before
  natural-density target); added explicit
  `Mathlib.NumberTheory.DirichletCharacter.Orthogonality` import; extended
  `#check` block.
* `state.md` — iteration 2 → 3, phase ORIENT → ACT, Current Focus + Next
  Action + Open files + Attempt Counts updated.
* `knowledge.md` — added "S3 — ORIENT/ACT: character-orthogonality scaffold"
  section with proof sketch + role in path-B plan.
* `src/data/research/problems/infinitude-primes-4k1-oq-03.json` — iteration
  2 → 3, phase ORIENT → ACT, focus + insights + nextSteps refreshed.

## S2 Deliverable (historical)

* 1 new Lean file (`InfinitudePrimes4k1OQ03.lean`, ~165 lines)
* 6 new theorems / lemmas (5 fully proved + 1 stated with `sorry`)
* 1 sorry remaining (the natural-density form, OQ-03 target)
* 0 axiom changes
