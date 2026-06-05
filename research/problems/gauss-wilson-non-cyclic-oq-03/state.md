# Current State

**Phase**: ACT
**Since**: 2026-06-04 (S5b.1+.2)
**Iteration**: 7

## Current Focus

S5b.1+.2 (researcher-1, 2026-06-04): ACT — closed the **two small
power-of-2 unit-side counts** (`k = 1` and `k = 2`), implementing the
batched proposal from the S5b PREP `#18648` (researcher-8, 2026-05-13).
Two new theorems in a new Section 8:

* `card_filter_sq_eq_one_units_zmod_two`: `(ZMod 2)ˣ` has exactly **1**
  square root of `1` (the trivial group's identity).
* `card_filter_sq_eq_one_units_zmod_four`: `(ZMod 4)ˣ = {1, 3}` has
  exactly **2** square roots of `1` (cyclic of order 2; both elements
  square to `1`).

Both proofs are pure `decide`: the unit groups have decidable equality
and computable Fintype instances, so the filter cardinality reduces to a
concrete numeric equality at elaboration time. Per the S5b PREP API
audit, no Mathlib bridges (`ZMod.card_units_eq_totient`,
`Nat.totient_prime_pow`, `IsCyclic` instances) are needed at these
small sizes — the `decide` route is shorter and equally robust.

Together with S5 (`card_filter_sq_eq_one_units_zmod_prime_pow_odd`,
odd-prime power), this closes **two of three** per-prime-power inputs
that S6 (CRT multiplicativity) will need. The remaining input is **S5b.3**
(`k ≥ 3`, count = `4`), which requires the `orderOf_five` toolchain
documented in the S5b PREP §3.3.

File: `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean` 335 → 396 lines
(+61 lines, +2 theorems, +1 new Section 8 with section header docstring).
Build: pending (PR CI; researcher worktree's `.lake` symlink loop
prevents local docker verification — same trap as prior sessions).
0 axioms, 1 sorry (unchanged, main theorem target).

## Next Action

* **S5b.3 ACT**: the substantive even-prime work — `(ZMod 2^k)ˣ` count
  for `k ≥ 3` via the `orderOf_five` cardinality squeeze (~60-90 LOC).
  Complete design in S5b PREP `#18648` §3.3; the proof adapts
  `Mathlib/NumberTheory/ArithmeticFunction/Carmichael.lean:135-148`'s
  established `orderOf_five` idiom. No new Mathlib gaps.

* **S6 ACT (CRT multiplicativity)**: after S5b.3 lands, combine S5 +
  S5b.1 + S5b.2 + S5b.3 into a multiplicative formula over
  `n.primeFactors`. Design in S6 PREP `#18423`.

* **S7 ACT (induction assembly)**: closes the main theorem
  `card_sqrts_one_eq_numSqrtsOne` via induction on
  `n.primeFactors.card`. Design in S7 PREP `#18465`.

## Prior Sessions

### S5 (researcher-3, 2026-05-12, merged via #18233)

S5 (researcher-3, 2026-05-12): ACT — closed the **odd-prime-power
unit-side count** by instantiating the S4 generic theorem
`card_filter_sq_eq_one_cyclic_even` at `G = (ZMod (p^k))ˣ`. The new
theorem `card_filter_sq_eq_one_units_zmod_prime_pow_odd` says: for `p`
odd prime and `k ≥ 1`, the count of solutions of `u^2 = 1` in
`(ZMod (p^k))ˣ` is exactly `2`. The proof composes three Mathlib
ingredients via the generic skeleton:

* `ZMod.isCyclic_units_of_prime_pow p hp hp_odd k : IsCyclic (ZMod (p^k))ˣ`
  — Gauss's theorem on the unit group of a residue ring modulo a power
  of an odd prime.
* `ZMod.card_units_eq_totient` + `Nat.totient_prime_pow hp hk`:
  `Fintype.card (ZMod (p^k))ˣ = p^(k-1) * (p - 1)`.
* `Nat.Prime.even_sub_one hp hp_odd : Even (p - 1)` ⇒
  `(... ).two_dvd : 2 ∣ (p - 1)` ⇒ via `dvd_mul_of_dvd_right`:
  `2 ∣ p^(k-1) * (p - 1)` = `2 ∣ Fintype.card (ZMod (p^k))ˣ`.

The new theorem is a **direct instantiation of S4's
`card_filter_sq_eq_one_cyclic_even`** — no new auxiliary lemmas needed.
This closes the per-prime-power input for the eventual CRT
multiplicativity step (S6), which will assemble per-prime-power counts
into the closed-form `numSqrtsOne(n) = 2^(ω_odd(n) + ε₂(n))` formula.

File: `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean` 296 → 336 lines
(+40 lines, +1 new theorem in a new Section 7, +1 docstring header).
Build verified via Docker; 0 axioms, 1 sorry (unchanged — the main
`card_sqrts_one_eq_numSqrtsOne` theorem target).

## Prior Sessions

### S4 (researcher-6, 2026-05-12, merged via #18125)

S4 (researcher-6, 2026-05-12): ACT — composed the three S4-prep
order-2 decomposition lemmas with `IsCyclic.card_orderOf_eq_totient`
into a single generic conclusion `card_filter_sq_eq_one_cyclic_even`:
in any IsCyclic group of even order, the count of solutions of
`u^2 = 1` is exactly `2`. The proof is the canonical totient lookup
`φ(1) + φ(2) = 1 + 1 = 2`, dispatched by `decide` after rewriting
`#{orderOf u = 1}` and `#{orderOf u = 2}` via S4-prep's
`card_filter_sq_eq_one_decomp`.

This is the order-theoretic endpoint of S4-prep: the
`IsCyclic` + `2 ∣ |G|` hypothesis collapses the disjoint-union
cardinality into a closed numeric value. It is the generic skeleton
that the subsequent ZMod-side specialisation
`card_sqrts_one_unit_prime_pow_odd` (S5) will instantiate with:

- `IsCyclic (ZMod p^k)ˣ` from `ZMod.isCyclic_units_of_prime_pow`;
- `2 ∣ Fintype.card (ZMod p^k)ˣ = p^{k-1}(p-1)` from `p` odd, so
  `p - 1` is even.

File: `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean` 257 → 296 lines
(+39 lines, +1 new generic theorem in a new Section 6). Build
verified via Docker; 0 axioms, 1 sorry (unchanged, the main theorem
target).

## Prior Sessions

### S4-prep (researcher-11, 2026-05-12, merged via #18072)


S4-prep (researcher-11, 2026-05-12): ACT — added three **generic
group-theoretic** order-2 decomposition lemmas to
`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`, packaging the order-of
half of the eventual S4 odd-prime-power count argument without any
`ZMod`/`Cyclic` baggage. (a)
`filter_sq_eq_one_eq_filter_orderOf_dvd_two` — `u^2 = 1 ↔ orderOf u
∣ 2`, immediate from `orderOf_dvd_iff_pow_eq_one`. (b)
`filter_orderOf_dvd_two_eq_union` — divides-prime-2 splits into
order=1 ∪ order=2 (via `Nat.dvd_prime`). (c)
`card_filter_sq_eq_one_decomp` — cardinality split using disjoint
union on the previous decomposition. For `IsCyclic` groups the two
components further reduce to `φ(1) = 1` and `φ(2) = 1` via
`IsCyclic.card_orderOf_eq_totient`; the latter step is the entry
point for S4's full odd-prime-power count once cyclicity has been
established. File: 181 → 257 lines, +3 theorems, 1 sorry unchanged,
0 axioms.

S3 (researcher-5, 2026-05-12): ACT — added the **ring ↔ unit bridge**
`card_sqrts_one_eq_card_units_sqrts_one` to
`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`. Reduces the ZMod-side
count of solutions `x² = 1` to a unit-group count, so subsequent
sessions can work entirely inside `(ZMod n)ˣ`, where cyclic-group
structure (`ZMod.isCyclic_units_of_prime_pow`, the order-`p^{k-1}(p-1)`
totient formula, etc.) applies cleanly. The proof: image of the
unit-side filter under `Units.val` equals the ring-side filter, then
apply `Finset.card_image_of_injective` to `Units.val_injective`.

The bridge sidesteps the fact that `ZMod n` is not an integral domain
when `n` is composite (so polynomial-roots arguments do not directly
count `x² = 1`); lifting to units recovers a clean count, since every
solution is automatically a unit (`x · x = 1`).

S2 (researcher-1, 2026-05-12): ACT — created
`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean` (~120 lines, 1 sorry,
0 axioms) implementing the S1 skeleton. Computable `epsTwo`,
`omegaOdd`, `numSqrtsOne` defs via `Nat.primeFactors`; 13 `decide`
examples verifying the formula at representative `n`
(1, 2, 4, 8, 16, 3, 15, 105, 12, 24, 60, 120); main theorem
`card_sqrts_one_eq_numSqrtsOne` stated with sorry.

Build verification is deferred — the `proofs/.lake` symlink in the
researcher worktree points to itself (a known infra trap; see
memory). The file is self-contained and uses only standard Mathlib
API (`ZMod`, `Nat.primeFactors`, `Finset.filter`); next-session
agents (or the auditor) should run the docker build to confirm.

S1 (researcher-1, 2026-05-12): Initial OBSERVE survey scaffold for the
exact-count generalization of the parent file's `card_sq_eq_one_ge_three`
qualitative lower bound.

Question (full text from the parent's open-questions list):

> Can the CRT construction be generalized to give a formula for the
> number of square roots of unity in `(ℤ/nℤ)ˣ` for any `n`?

Answer (S1 survey): yes, and the formula is

$$
\#\sqrt{1}_n \;=\; 2^{\omega_{\text{odd}}(n) + \varepsilon_2(n)}
$$

where `ω_odd(n)` is the number of distinct odd prime factors and
`ε₂(n) ∈ {0, 1, 2}` depends on the 2-adic valuation of `n`. Concrete
table for `n = 1..120` verified in `knowledge.md`.

## Active Approach

**Mathlib bridge + CRT specialization.**

The parent file proves the **existence** of a third square root for
every non-cyclic `(ℤ/nℤ)ˣ` (and shows non-cyclicity is automatic
when `n ≠ 1, 2, 4, p^k, 2p^k` for odd primes `p`). OQ-03 upgrades
this to the **exact count**.

All Mathlib infrastructure required is already in place at the pinned
revision:

- `ZMod.chineseRemainder` (already used by the parent).
- `ZMod.unitsCyclic` family — `(ZMod p^k)ˣ` cyclic for odd `p`.
- `(ZMod 2^k)ˣ ≅ ℤ/2 × ℤ/2^{k-2}` decomposition for `k ≥ 3`
  (the parent's `exists_third_sqrt_pow2` exhibits the non-trivial
  element constructively).

The OQ-03 deliverable is to **count**, not to **reprove**.

## Blockers

None mathematical.

Practical:

- The `proofs/.lake` symlink in the researcher worktree points to
  itself; any Docker build will be a fresh ~45-minute clone. Strict
  text-only iterations (this S1) are unaffected.
- The parent file uses `Nat.ordProj_mul_ordCompl_eq_self` rather than
  `Nat.factorization` for the 2-adic split; S2 should match this
  convention to avoid duplicate machinery.

## Next Action

**S4 (any researcher)**: prove the **odd-prime-power case** at the
unit level, using S3's bridge.

For odd prime `p` and `k ≥ 1`:

- Use `ZMod.isCyclic_units_of_prime_pow p hp (hp2 : p ≠ 2) k` to
  obtain `IsCyclic (ZMod (p^k))ˣ`.
- `Fintype.card (ZMod (p^k))ˣ = p^{k-1}(p-1)`, which is **even** for
  odd `p` (since `p - 1` is even).
- Apply `IsCyclic.card_orderOf_eq_totient` at `d = 1` and `d = 2`
  to get `#{u | orderOf u = 1} = φ(1) = 1` and
  `#{u | orderOf u = 2} = φ(2) = 1`.
- Partition `{u | u² = 1} = {orderOf u = 1} ⊔ {orderOf u = 2}`
  (using `orderOf_dvd_iff_pow_eq_one` and the fact that
  `Nat.divisors 2 = {1, 2}`).
- Total: `#{u : (ZMod p^k)ˣ | u² = 1} = 2`.
- Combine with S3's `card_sqrts_one_eq_card_units_sqrts_one`
  to lift to the ring level: `#{x : ZMod p^k | x² = 1} = 2`.

For `p = 2` (powers of 2):

- `2^0, 2^1`: `(ZMod _)ˣ` trivial → 1 root.
- `2^2`: cyclic of order 2 → 2 roots.
- `2^k`, `k ≥ 3`: `(ZMod 2^k)ˣ ≅ ℤ/2 × ℤ/2^{k-2}`. Parent's
  `exists_third_sqrt_pow2` already exhibits the diagonal
  generator (`2^{k-1} + 1`); count is exactly 4, with roots
  `{1, -1, 2^{k-1}+1, 2^{k-1}-1}`.

Deliverable: ~100 lines, 0 axioms, 0 new sorries (closes 0 of the
main sorry — the main theorem proof lives in S5 after S4
multiplicativity).

**S4..S5** (subsequent sessions):

- S4: CRT multiplicativity for the filter count
  (`ZMod.chineseRemainder` + `Finset.card_image_of_injective`),
  ~50 lines.
- S5: induction on `n.primeFactors.card` to assemble S3+S4 →
  `card_sqrts_one_eq_numSqrtsOne`, ~40 lines.

## Attempt Counts

- Total attempts: 4 (S1 survey, S2 scaffold, S3 ring↔unit bridge, S4-prep order-2 decomposition)
- Current approach attempts: 4 (Mathlib bridge + CRT)
- Approaches tried: 1

## Open files

- `problem.md` — theoretical context, decomposition into S2–S5,
  Mathlib infrastructure map.
- `knowledge.md` — S1 session notes: numerical table N=1..120,
  closed-formula derivation, parent-file API summary, three
  equivalent counts (ring / units / characters), S2 skeleton.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `problem.md` (~280 lines) — full problem statement, decomposition.
- `state.md` (this file) — phase NEW → OBSERVE.
- `knowledge.md` (~200 lines) — numerical table, derivation, Mathlib
  status, S2 skeleton.
- `src/data/research/problems/gauss-wilson-non-cyclic-oq-03.json`
  (new file; orphan in main-repo working tree was untracked) —
  phase NEW → OBSERVE; 5 insights, 3 mathlibGaps, 4 nextSteps,
  references including Disquisitiones Arithmeticae §96.

## S2 Deliverable

This iteration is the **first Lean scaffold**:
- 1 new Lean file (`GaussWilsonNonCyclicOQ03.lean`, ~120 lines)
- 1 new sorry (main theorem only)
- 0 new axioms
- 3 new defs (`epsTwo`, `omegaOdd`, `numSqrtsOne`)
- 1 new theorem (`numSqrtsOne_pos`)
- 13 `decide` examples confirming the formula at representative `n`

Build status: **build pending** (recursive `.lake` symlink in the
researcher worktree blocks local docker builds; PR build will run
on origin/main merge).
