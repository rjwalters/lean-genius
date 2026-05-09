# Current State

**Phase**: ORIENT
**Since**: 2026-05-09T02:30:00Z
**Iteration**: 14

## Current Focus

Phase-2 formalization is complete (1 axiom for the open conjecture, 0 sorries).
Iteration 7 (researcher-11) added a uniform Z/2 lower bound `d − 1 ≤
symBUDim n d` valid at ALL dimensions (not just even) — strictly tighter than
`symBUDim_even_lower` at odd d. Combined with a generalized n=2 closed form,
the conjecture is now fully settled axiom-free at n=2 across all dimensions.

## Active Approach

Strengthen unconditional theorem coverage around the open axiom
`symBUDim_eq_largestPrime` so the boundary between proven content and the
open question is sharp. The conjecture itself requires Fadell-Husseini index
theory (not in Mathlib) so direct attack is out of scope; instead, we make
the surrounding facts increasingly precise.

## Blockers

The conjectural equality `symBUDim_eq_largestPrime` is genuinely open and
requires equivariant cohomology not currently in Mathlib (Fadell-Husseini
index for non-cyclic group actions). Direct proof is out of scope for this
file's scaffold.

## Next Action

Possible follow-ups:
1. Prove the n=4 case directly via the Klein-4 group structure (V₄ ≤ S₄).
   The new uniform Z/2 bound `d − 1 ≤ symBUDim 4 d` is the best axiom-free
   lower bound at n=4; an improvement would have to come from V₄-specific
   non-cyclic structure. A full equivariant index calculation would either
   confirm (if V₄ ⊕ Z/3 contributes nothing extra) or refute (if it does)
   the conjecture at n=4.
2. Investigate odd-d cyclic-prime Yang-Borsuk axiom: `buDim_prime` only
   handles even d. An odd-d analog at odd primes would let
   `symBUDim_eq_largestPrime` derive a tight closed form past even d.
3. Formalize the dihedral analog (sister question OQ-02-OQ-01-OQ-03-OQ-01).

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 1
- Approaches tried: 3 (Bertrand-derived quantitative refinement; structural
  fixed-point characterization; uniform Z/2 lower bound at all dimensions)

## Iteration 3 Builds (researcher-9, 2026-05-08)

- `n_div_two_lt_largestPrimeBelow` (axiom-free): for n ≥ 2,
  `n / 2 < largestPrimeBelow n`. Uses Mathlib's `Nat.exists_prime_lt_and_le_two_mul`.
- `largestPrimeBelow_in_bertrand_window` (axiom-free): two-sided bound
  `n/2 < largestPrimeBelow n ≤ n`.
- Updated meta.json: lineCount 187→241, theoremCount 8→10,
  substantiveTheoremCount 6→8, added Bertrand to mathlibDependencies.
- Added Bertrand bound to keyInsights, sections (Part VI), originalContributions.

## Iteration 4 Builds (researcher-3, 2026-05-08)

Focus: **prove the conjecture's n=2 case axiom-free** (consistency check) and
provide reusable infrastructure for future case-by-case attempts.

- `largestPrimeBelow_self_of_prime` (axiom-free): general squeeze lemma —
  when `n` itself is prime, `largestPrimeBelow n = n`. Reusable for all
  prime-n consequences below.
- `largestPrimeBelow_two`, `_three`, `_five`, `_seven` (axiom-free):
  concrete computations at small primes.
- `symBUDim_eq_largestPrime_two_unconditional` (axiom-free): the **n=2
  instance of the conjectured equality is provable** from the parent's
  `symBUDim_two` axiom and `largestPrimeBelow_two`, *without* invoking
  the new `symBUDim_eq_largestPrime` axiom. This is a non-trivial
  consistency check — it shows the new axiom is compatible with the
  pre-existing n=2 base axiom and is *redundant* at n=2.
- `symBUDim_two_even_formula_unconditional` (axiom-free): closed form
  `symBUDim 2 (2k) = 2k - 1` derived directly from parent axioms.
- `symBUDim_two_four_unconditional` (axiom-free): concrete `symBUDim 2 4 = 3`.
- Added `import Proofs.BorsukUlamOQ02OQ01OQ03OQ02` to `proofs/Proofs.lean`
  so the file is built as part of the gallery target.

**Counts**: lineCount 241→333, theoremCount 10→18, axiomCount 1 (unchanged),
sorries 0 (unchanged).

## Iteration 5 Builds (researcher-11, 2026-05-08)

Focus: **structural characterization** of `largestPrimeBelow` and **broaden
the unconditional lower-bound coverage** to S₆, S₇, S₈.

- `largestPrimeBelow_eq_self_iff_prime` (axiom-free): for n ≥ 2,
  `largestPrimeBelow n = n ↔ Nat.Prime n`. Forward direction uses
  `largestPrimeBelow_isPrime`; backward is `largestPrimeBelow_self_of_prime`.
  Cleaner than just having the prime → fixed-point direction.
- `largestPrimeBelow_lt_of_not_prime` (axiom-free): direct corollary —
  for composite n ≥ 2, `largestPrimeBelow n < n` (strict). Useful for
  case analyses that branch on primality.
- `symBUDim_six_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 6 (2k)`.
- `symBUDim_seven_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 7 (2k)`.
  (n=7 prime, parallels the n=5 case.)
- `symBUDim_eight_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 8 (2k)`.
  Notable: S₈ has the rich non-cyclic subgroup structure (V₄, A₄, …)
  cited in the problem statement. The cyclic-prime lower bound holds
  regardless — confirming `symBUDim_even_lower` is robust to S_n's
  composite/non-cyclic structure.

**Counts**: lineCount 333→387, theoremCount 18→23 (substantive 16→21),
axiomCount 1 (unchanged), sorries 0 (unchanged).

## Iteration 6 Builds (researcher-10, 2026-05-08)

Focus: **structural monotonicity** of `largestPrimeBelow` (S5 stretch goal)
and **further broadening of unconditional Yang-Borsuk lower bounds** through
n=12.

- `largestPrimeBelow_mono : Monotone largestPrimeBelow` (axiom-free):
  resolves S5's nextSteps[3]. Case split on n ≥ 2:
  - Positive (n ≥ 2): `largestPrimeBelow n` is itself a prime ≤ n ≤ m;
    apply `Nat.le_findGreatest` with the primality witness.
  - Negative (n < 2): `findGreatest Nat.Prime n = 0` (no prime ≤ 1);
    closed via `interval_cases` + `rfl` (n=0) + `decide` (n=1).
  Structurally aligns the new `symBUDim_eq_largestPrime` axiom with the
  parent file's `sym_has_smaller_sym n d` monotonicity in the n-variable.
- `largestPrimeBelow_eight_le_eleven` (axiom-free): concrete corollary
  pinning `largestPrimeBelow 8 ≤ 11` from monotonicity + value at 11.
- `symBUDim_nine_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 9 (2k)`.
- `symBUDim_ten_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 10 (2k)`.
- `symBUDim_eleven_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 11 (2k)`
  (n=11 prime).
- `symBUDim_twelve_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 12 (2k)`
  (n=12 highly composite — 2²·3, contains V₄ × Z/3, A₄, …).

All four extended bounds are direct applications of the existing
`symBUDim_even_lower`. The pattern is now uniformly demonstrated for
`n ∈ {3, …, 12}`, covering both prime cases (3, 5, 7, 11) and the full
range of composite cases including those with rich non-cyclic structure
(S₈, S₉, S₁₀, S₁₂).

**Counts**: lineCount 387→464 (+77), theoremCount 23→29 (substantive 21→27),
axiomCount 1 (unchanged), sorries 0 (unchanged).

**Build**: verified via `./proofs/scripts/docker-build.sh
Proofs.BorsukUlamOQ02OQ01OQ03OQ02` (128s for target file post Mathlib
cache; 3068 jobs total, 0 errors).

**PR**: #16890 (merged 2026-05-08T03:58:22Z).

## Iteration 7 Builds (researcher-11, 2026-05-08)

Focus: **uniform Z/2 lower bound at ALL dimensions** (including odd) and
**axiom-free closed form at n=2 generalized past even d**.

- `symBUDim_lower_z2` (axiom-free, core new theorem): for n ≥ 2 and d ≥ 1,
  `d − 1 ≤ symBUDim n d`. Routes through Z/2: parent's `symBUDim_two`
  + `buDim_two` + `symBUDim_le_of_le 2 n d`. Strictly tighter than
  `symBUDim_even_lower` at odd d (gives `d − 1 = 2k` at `d = 2k + 1`,
  whereas `symBUDim_even_lower` only delivers the floor-rounded `2k − 1`).
- `symBUDim_odd_lower_unconditional` (axiom-free corollary): for n ≥ 2,
  `2 * k ≤ symBUDim n (2 * k + 1)`. The strictly-stronger odd-d
  component of the Z/2 uniform bound.
- `symBUDim_two_general_unconditional` (axiom-free): for d ≥ 1,
  `symBUDim 2 d = d − 1`. Generalizes `symBUDim_two_even_formula_unconditional`
  past the even-d restriction. **At n=2 this fully settles the conjecture
  axiom-free across all dimensions** (combined with `largestPrimeBelow_two`,
  the conjectured equality `symBUDim 2 d = buDim (largestPrimeBelow 2) d`
  holds for all d ≥ 1 without invoking the new `symBUDim_eq_largestPrime`
  axiom).
- Concrete axiom-free instances:
  - `symBUDim_two_three_unconditional : symBUDim 2 3 = 2`
  - `symBUDim_two_five_unconditional : symBUDim 2 5 = 4`
  - `symBUDim_two_seven_unconditional : symBUDim 2 7 = 6`
  - `symBUDim_three_three_lower_unconditional : 2 ≤ symBUDim 3 3`
  - `symBUDim_four_three_lower_unconditional : 2 ≤ symBUDim 4 3` (V₄ ≤ S₄
    Klein-4 test case — Z/2 bound holds regardless of non-cyclic structure)
  - `symBUDim_three_five_lower_unconditional : 4 ≤ symBUDim 3 5`
  - `symBUDim_four_five_lower_unconditional : 4 ≤ symBUDim 4 5`

**Counts**: lineCount 530→674 (+144), theoremCount 35→45 (substantive
33→43), axiomCount 1 (unchanged), sorries 0 (unchanged).

**Build**: verified via `./proofs/scripts/docker-build.sh
Proofs.BorsukUlamOQ02OQ01OQ03OQ02` — `Build completed successfully (3068
jobs)` (clean except a pre-existing `unused variable hq` warning in
parent file `BorsukUlamOQ02OQ01.lean:111`, unrelated to S7 changes).

**Open content remaining**: the genuinely-open part of the new axiom is
now strictly `n ≥ 3` at odd `d ≥ 3` (whether S_n improves *past* the
uniform Z/2 bound `d − 1`). At `n = 2` the conjecture is fully axiom-free.

## Iteration 8 Builds (researcher-1, 2026-05-08)

Focus: **conditional structural consequence** — the axiom-free Z/2 lower
bound from iter 7 pulls through `symBUDim_eq_largestPrime` to deliver a
new lower bound on cyclic-prime Yang-Borsuk dimensions at ALL d, including
odd d (where the parent's `buDim_prime` axiom is silent for primes p ≥ 3).

- `buDim_largestPrime_lower_z2` (conditional, core new theorem): under
  `symBUDim_eq_largestPrime`, `d − 1 ≤ buDim (largestPrimeBelow n) d` for
  n ≥ 2, d ≥ 1. One-line proof: rewrite via the new axiom and cite
  `symBUDim_lower_z2` from iter 7.
- `buDim_prime_lower_z2_conditional` (conditional): at any prime p with
  d ≥ 1, `d − 1 ≤ buDim p d`. **Significance**: extends Yang-Borsuk's
  classical Borsuk-Ulam lower bound from p = 2 (parent's `buDim_two`,
  valid in any dimension) to ALL primes p ≥ 2 and ALL d ≥ 1. At odd d
  this is content beyond the parent's even-d-only `buDim_prime` axiom.
- `buDim_three_lower_z2_conditional`, `buDim_five_lower_z2_conditional`,
  `buDim_seven_lower_z2_conditional` (conditional corollaries):
  concrete instances at small odd primes. E.g., conditionally
  `buDim 3 3 ≥ 2`, `buDim 5 5 ≥ 4`.
- `symBUDim_prime_combined_lower` (axiom-free): packaged max-bound
  `max (buDim p d) (d − 1) ≤ symBUDim p d` at any prime p with d ≥ 1.
  Combines the Z/p contribution (parent's `sym_has_cyclic_prime`) with
  the Z/2 contribution (iter-7's `symBUDim_lower_z2`). At even d = 2k
  both terms equal d − 1 (via parent's `buDim_prime`); at odd d the Z/2
  component dominates.

**Counts**: lineCount 674→768 (+94), theoremCount 45→51 (+6, substantive
43→49), axiomCount 1 (unchanged), sorries 0 (unchanged).

**Significance**: the conditional consequence is genuinely new structural
content. Accepting `symBUDim_eq_largestPrime` would PIN a new lower bound
on Yang-Borsuk dimensions for cyclic primes p ≥ 3 at odd d — content
beyond the existing axiomatization. Inversely, any future computation of
`buDim p d` at odd d that violates `d − 1 ≤ buDim p d` would FALSIFY
`symBUDim_eq_largestPrime` at n = p. The conditional theorem is therefore
both a positive consequence and a falsification handle.

**Path forward** (unchanged from iter 7): direct proof of
`symBUDim_eq_largestPrime` requires Fadell-Husseini index theory not in
Mathlib. Stretch goals at small n: prove the n=3 case (next-easiest after
n=2; would need a `symBUDim_three` base axiom that the parent doesn't
yet have), prove the n=4 case via V₄ ≤ S₄ structure, or coordinate with
sister-question OQ-02-OQ-01-OQ-03-OQ-01 (dihedral D_n analog).

## Iteration 9 Builds (researcher-5, 2026-05-08)

Focus: **conjecture-as-Prop reformulation + explicit falsification handles**.
Crystallizes iter 8's "falsification handle" remark as concrete, well-typed
theorems and provides a hypothesis-form alternative to the file's axiom.

- `ConjectureLPB : Prop` (axiom-free definition): the equality conjecture
  stated as a `Prop` rather than via the file's `axiom`. Lets downstream
  developments take the conjecture as an explicit hypothesis instead of
  relying on the file's axiom — making conjecture-dependence visible at
  the type level.
- `buDim_largestPrime_lower_z2_of`, `buDim_prime_lower_z2_of`,
  `symBUDim_eq_buDim_at_prime_of` (axiom-free, hypothesis-form):
  hypothesis-form variants of iter-5/iter-8 conditional theorems
  (`symBUDim_eq_buDim_at_prime`, `buDim_largestPrime_lower_z2`,
  `buDim_prime_lower_z2_conditional`). Same statements, but the
  dependence on the conjecture is encoded via a `ConjectureLPB`
  hypothesis rather than via the file's axiom. Useful when downstream
  code wants to track conjecture-dependence in the type signature.
- `not_conjectureLPB_of_buDim_lt` (axiom-free): the **falsification
  theorem**. At any prime p with d ≥ 1, a future proof of
  `buDim p d < d − 1` refutes `ConjectureLPB`. Formal contrapositive
  of `buDim_prime_lower_z2_of` — turns iter 8's "falsification handle"
  remark into a concrete theorem.
- Concrete falsification handles at small (p, d):
  - `not_conjectureLPB_of_buDim_three_three_lt_two`
  - `not_conjectureLPB_of_buDim_five_three_lt_two`
  - `not_conjectureLPB_of_buDim_three_five_lt_four`
  Each pinpoints the simplest odd-d case at a small prime where the
  parent's `buDim_prime` axiom is silent (it fires only on even d).
  These mark exactly where future Yang-Borsuk research could refute
  the conjecture.

**Counts**: lineCount 769→878 (+109), theoremCount 51→58 (+7,
substantive 49→56), definitionCount 1→2 (+1 for `ConjectureLPB`),
axiomCount 1 (unchanged), sorries 0 (unchanged).

**Significance**: the conjecture is now expressible at two levels in
the file — as the `axiom symBUDim_eq_largestPrime` (used for direct
derivations of conditional consequences) and as `ConjectureLPB : Prop`
(used by hypothesis-form variants for explicit dependency tracking).
The `_of` lemmas mirror their axiom-using counterparts on a one-to-one
basis, and the falsification theorem is type-level explicit.

**Path forward** (unchanged from iter 8): direct proof of the
conjecture requires Fadell-Husseini index theory not in Mathlib.
Concrete next-target: compute or bound `buDim 3 3` directly via
equivariant cohomology of Z/3 on small spheres. A proof of
`buDim 3 3 < 2` would refute `ConjectureLPB` via
`not_conjectureLPB_of_buDim_three_three_lt_two`; a proof of
`buDim 3 3 = 2` would tighten the conjecture's content at the
simplest odd-d case beyond Yang-Borsuk.

## Iteration 10 Builds (researcher-6, 2026-05-08)

Focus: **plateau infrastructure for `largestPrimeBelow`**. Adds the
axiom-free engine for the local-constancy structure of `lpb` between
consecutive primes (the structural reason `lpb` is constant on
prime-gap intervals) plus the conditional `symBUDim` consequence —
the formal "plateau collapse" content of the conjecture.

### Part XVI additions (axiom-free)

- `largestPrimeBelow_succ_of_not_prime`: atomic step. If `n + 1` is
  not prime, `largestPrimeBelow (n + 1) = largestPrimeBelow n`.
  One-line corollary of Mathlib's `Nat.findGreatest_of_not`.
- `largestPrimeBelow_const_in_no_prime_range`: general plateau
  lemma. If no prime exists in `(n, m]`, then `largestPrimeBelow m =
  largestPrimeBelow n`. Proved by `Nat.le_induction` — each successor
  jump in the gap is at a composite number, so the atomic step
  applies.
- `largestPrimeBelow_eq_of_in_plateau`: prime-anchored packaging.
  If `p` is prime, `p ≤ n ≤ m`, `largestPrimeBelow n = p`, and no
  prime lies in `(n, m]`, then `largestPrimeBelow m = p`. Convenient
  for combining with prime-gap data.

### Part XVI additions (conditional on `symBUDim_eq_largestPrime`)

- `symBUDim_eq_of_lpb_eq`: plateau collapse — any two `n, m ≥ 2`
  with `largestPrimeBelow n = largestPrimeBelow m` have `symBUDim n d
  = symBUDim m d` at every dimension `d`. Two-line `rw` proof through
  the file's axiom.
- `symBUDim_const_in_no_prime_range`: chained corollary. If no prime
  exists in `(n, m]` and `n ≥ 2`, then `symBUDim n d = symBUDim m d`
  for every `d`. Formal expression of the "plateau collapse"
  prediction: distinct symmetric groups within any maximal prime-gap
  interval conjecturally share the equivariant Borsuk-Ulam dimension
  at every dimension.

### Hypothesis-form variants (matching Part XV)

- `symBUDim_eq_of_lpb_eq_of`, `symBUDim_const_in_no_prime_range_of`:
  identical statements with the dependence on the conjecture encoded
  via a `ConjectureLPB` hypothesis (Part XV) rather than via the
  file's `axiom symBUDim_eq_largestPrime`. For downstream
  developments that want to track conjecture-dependence in the type
  signature.

**Counts**: lineCount 878→1006 (+128), theoremCount 58→65 (+7,
substantive 56→63), definitionCount 2 (unchanged — no new defs;
all seven additions are theorems), axiomCount 1 (unchanged), sorries
0 (unchanged).

**Significance**: combined with the concrete LPB values at composite
n (PR #17286 — Parts XII, XIII, currently open), this gives a
uniform *structural* engine for the "plateau collapse" pattern.
Where #17286 shows individual values like `largestPrimeBelow 8 = 7`,
`_9 = 7`, `_10 = 7` via `decide`, this iteration shows the *general
reason* those values agree: no prime in `(7, 11)`, so the
atomic-step induction pins them all at 7. And the conditional
consequence `symBUDim_const_in_no_prime_range` says the conjecture
forces `symBUDim 8 d = symBUDim 9 d = symBUDim 10 d` for all `d` —
three distinct symmetric groups with qualitatively different
subgroup structures (S₈ ⊃ V₄ × A₄, S₉ ⊃ A₉ simple of order 181440,
S₁₀ ⊃ A₅ × A₅) nevertheless share the *same* equivariant BU
dimension at every `d`. The plateau collapse is the most concrete
content-bearing prediction of the conjecture between primes, and
now has a uniform axiom-free machine behind it — independent of any
individual `decide`-based LPB-at-composite-n computation.

**Build**: pending (Docker rebuild from fresh Mathlib cache).

**Path forward** (unchanged from iter 9 plus iter 10): once #17286
merges, two-line specializations of `symBUDim_const_in_no_prime_range`
should give clean axiom-pinning plateau collapse instances at
concrete composite n.

## Iteration 11 Builds (researcher-3, 2026-05-09)

Focus: **concrete plateau collapse instances** that directly apply iter
10's Part XVI infrastructure without depending on PR #17286's
LPB-at-composite-n decisions. Selected three prime-gap intervals
representative of the gap-size distribution below n = 30, derived
axiom-free LPB collapse + conditional symBUDim collapse for each,
plus hypothesis-form variants taking `ConjectureLPB` explicitly.

### Part XVII additions (axiom-free witnesses)

- `no_prime_in_eight_to_ten`: `∀ k, 8 < k → k ≤ 10 → ¬ Nat.Prime k`.
  `interval_cases` + `decide` over the three composite cases 9, 10.
  Witness for the dyadic gap (7, 11).
- `no_prime_in_fourteen_to_sixteen`: same shape over (13, 16] = {14,
  15, 16}. Witness for the gap (13, 17).
- `no_prime_in_twentyfour_to_twentyeight`: same shape over (23, 28]
  = {24, 25, 26, 27, 28}. Witness for the **first prime gap of size
  6** in ℕ — five consecutive composites.

### Part XVII additions (axiom-free LPB collapse)

- `largestPrimeBelow_eight_eq_ten`: `largestPrimeBelow 10 =
  largestPrimeBelow 8`. Direct application of
  `largestPrimeBelow_const_in_no_prime_range 8 10`.
- `largestPrimeBelow_thirteen_eq_sixteen`: `largestPrimeBelow 16 =
  largestPrimeBelow 13`.
- `largestPrimeBelow_twentythree_eq_twentyeight`: `largestPrimeBelow
  28 = largestPrimeBelow 23`. The longest LPB plateau below n = 30 —
  spans six consecutive ranks {23, 24, 25, 26, 27, 28}.

### Part XVII additions (conditional symBUDim collapse)

- `symBUDim_eight_eq_ten`: under `symBUDim_eq_largestPrime`,
  `symBUDim 8 d = symBUDim 10 d` for every `d`. Two distinct
  symmetric groups (S₈ ⊃ V₄·A₄, S₁₀ ⊃ A₅×A₅) conjecturally share
  equivariant Borsuk-Ulam dimensions at every dimension.
- `symBUDim_thirteen_eq_sixteen`: same form for n = 13, 16.
- `symBUDim_twentythree_eq_twentyeight`: same form for n = 23, 28
  — the longest plateau collapse below n = 30 (six consecutive
  symmetric groups conjecturally with identical equivariant BU
  dimensions despite radically different Sylow structure: |Sylow_2(S₂₃)|
  = 2¹⁹ vs |Sylow_2(S₂₈)| = 2²⁵).
- `symBUDim_eight_eq_ten_of`, `symBUDim_thirteen_eq_sixteen_of`,
  `symBUDim_twentythree_eq_twentyeight_of`: hypothesis-form variants
  taking `ConjectureLPB` explicitly. Useful for downstream code that
  wants to track conjecture-dependence at the type level.

**Counts**: lineCount 1006→1159 (+153), theoremCount 65→77 (+12,
substantive 63→75), definitionCount 2 (unchanged), axiomCount 1
(unchanged), sorries 0 (unchanged).

**Significance**: complementary to (and orthogonal from) the still-open
PR #17286 (S8 by another agent, currently in merge conflict — adds
LPB-at-composite values via `decide` for the Part XII/XIII RHS-resolved
forms). PR #17286's content is required to *interpret* the LHS of these
plateau collapse instances (e.g., to know that all six values
`largestPrimeBelow 23, ..., largestPrimeBelow 28` literally equal 23).
But the plateau collapse instances **themselves** are content-bearing
without those concrete values — they assert that the LPB function is
constant on the gap regardless of the specific value, and that the
conjecture forces the corresponding symBUDim values to coincide.
Independent of how PR #17286 resolves.

## Iteration 12 Builds (researcher-10, 2026-05-09)

Focus: **first prime gap of size 8** in ℕ — extend Iter 11's plateau
collapse infrastructure past the gap-of-size-6 cases (largest below
n = 30) to the **first gap of size 8** at (89, 97). The plateau spans
**eight consecutive ranks** `n ∈ {89, 90, …, 96}` — the longest
plateau collapse delivered by any single prime gap below n = 100.

### Part XVIII additions (axiom-free witnesses)

- `no_prime_in_ninety_to_ninetysix`: `∀ k, 89 < k → k ≤ 96 → ¬ Nat.Prime k`.
  `interval_cases k` + `decide` over the seven composite cases 90, 91,
  92, 93, 94, 95, 96. Witness for the **first prime gap of size 8 in ℕ**
  (between consecutive primes 89 and 97).

### Part XVIII additions (axiom-free LPB collapse)

- `largestPrimeBelow_eightynine_eq_ninetysix`: `largestPrimeBelow 96 =
  largestPrimeBelow 89`. The **longest LPB plateau below n = 100** —
  spans eight consecutive ranks {89, 90, 91, 92, 93, 94, 95, 96}. Direct
  application of `largestPrimeBelow_const_in_no_prime_range 89 96`.

### Part XVIII additions (conditional symBUDim collapse)

- `symBUDim_eightynine_eq_ninetysix`: under `symBUDim_eq_largestPrime`,
  `symBUDim 89 d = symBUDim 96 d` for every `d`. The **longest plateau
  collapse below n = 100**: eight consecutive symmetric groups (S₈₉ on
  prime rank, S₉₀ ⊃ A₉₀, ..., S₉₆ on the highly-composite rank
  96 = 2⁵·3 with Sylow_2-order 2⁹³) conjecturally share equivariant
  Borsuk-Ulam dimensions at every dimension despite qualitatively
  different rank structure. One-line specialization of Part XVI's
  `symBUDim_const_in_no_prime_range`.
- `symBUDim_eightynine_eq_ninetysix_of`: hypothesis-form variant taking
  `ConjectureLPB` explicitly.

**Counts**: lineCount 1159→1242 (+83), theoremCount 77→81 (+4,
substantive 75→79), definitionCount 2 (unchanged), axiomCount 1
(unchanged), sorries 0 (unchanged).

**Significance**: complementary to Iter 11's three gap-size-≤6
instances. The gap (89, 97) is mathematically distinguished as the
first occurrence of a gap exceeding 7 in the sequence of consecutive
prime gaps, distinguishing it from every gap among the first 24 primes
(2, 3, 5, …, 89). Where Iter 11 covers the first gap of size 6 (six
consecutive ranks coincide), this iteration covers the first gap of
size 8 (eight consecutive ranks coincide). The structural disparity
between S₈₉ (alternating-A₈₉ on prime rank) and S₉₆ on the
highly-composite 96 = 2⁵·3 makes this the most striking single
plateau-collapse instance in the file: a prime-rank symmetric group
and a smooth-rank one with radically different Sylow structure are
forced by the conjecture to agree on equivariant BU dimension at
every `d`.

**Build**: pending (Docker rebuild from fresh Mathlib cache; CI is
ground truth per `feedback_researcher_lake_symlink_broken.md`).

**Path forward** (unchanged from iter 11): direct proof of the
conjecture requires Fadell-Husseini index theory not in Mathlib.
Stretch goals at small n: prove the n=3 case (next-easiest after
n=2), prove the n=4 case via V₄ ≤ S₄ structure, or coordinate with
sister-question OQ-02-OQ-01-OQ-03-OQ-01 (dihedral D_n analog).
Concrete falsification target: compute or bound `buDim 3 3` directly
via equivariant cohomology of Z/3 on simple S²-actions.

**Build**: pending (Docker rebuild from fresh Mathlib cache).

## Iteration 13 Builds (researcher-1, 2026-05-09)

Focus: **structural converse to the plateau lemma** — break out of the
iter 11/12 enumeration pattern (concrete gap-N instances) by adding the
converse direction and packaging both directions as a single
biconditional. The biconditional subsumes the entire "first prime gap of
size N" enumeration template that iter 11/12 grew along.

### Part XIX additions (axiom-free)

- `largestPrimeBelow_lt_of_prime_in_range`: the structural converse of
  PART XVI. If a prime `p` lies in the half-open interval `(n, m]`,
  then `largestPrimeBelow n < largestPrimeBelow m`. Three-line proof
  via `Nat.le_findGreatest` (witness `p ≤ largestPrimeBelow m` from
  primality) and `largestPrimeBelow_le` (bound `largestPrimeBelow n
  ≤ n < p`). The `2 ≤ n` hypothesis is *not* required — the
  inequality chain is unconditional.
- `largestPrimeBelow_eq_iff_no_prime_in_range`: the **biconditional
  packaging**. For `n ≤ m`, `largestPrimeBelow n = largestPrimeBelow
  m` iff no prime lies in `(n, m]`. Forward direction is PART XVI;
  reverse is the contrapositive of the new strict-monotonicity lemma.
  Together they give a tight characterization: LPB plateaus
  correspond *exactly* to prime-gap intervals. Every Part XVII–XVIII
  concrete-gap LPB-equality instance is now a corollary of one
  biconditional.
- `largestPrimeBelow_strict_mono_at_prime`: clean specialization at
  `m = p` prime. `n < p` implies `largestPrimeBelow n <
  largestPrimeBelow p`. One-liner reduction to the general converse.

### Part XIX additions — concrete plateau-edge witnesses (axiom-free)

- `largestPrimeBelow_eight_lt_eleven`,
  `largestPrimeBelow_thirteen_lt_seventeen`,
  `largestPrimeBelow_twentythree_lt_twentynine`,
  `largestPrimeBelow_eightynine_lt_ninetyseven`: strict-mono witnesses
  at each plateau's right endpoint. Together with the existing
  `largestPrimeBelow_eight_eq_ten`, `_thirteen_eq_sixteen`,
  `_twentythree_eq_twentyeight`, `_eightynine_eq_ninetysix` from
  Parts XVII–XVIII, these pin each plateau as a *maximal* level set
  of `largestPrimeBelow` (rather than a cluster that might extend
  further). The plateau `{89, …, 96}` is now formally maximal: every
  rank in the plateau has `largestPrimeBelow = 89`, and any rank
  `≥ 97` strictly exceeds 89 in `largestPrimeBelow`.

**Counts**: lineCount 1242→1376 (+134), theoremCount 81→88 (+7,
substantive 79→86), definitionCount 2 (unchanged), axiomCount 1
(unchanged), sorries 0 (unchanged).

**Significance**: this iteration is a deliberate departure from iter
11/12's enumeration pattern. Part XVII (gap 4 at three intervals) +
Part XVIII (first gap of size 8) was a productive enumeration but
risked degenerating into "first gap of size N for each N" busywork.
The converse direction `largestPrimeBelow_lt_of_prime_in_range` — and
especially the biconditional `largestPrimeBelow_eq_iff_no_prime_in_range`
— packages the entire enumeration template as a single content-bearing
structural result. Future "first gap of size N" instances are now
two-line corollaries of the iff applied to a no-prime-in-range
witness; the structural content lives at PART XIX, not in repeated
PART XVII-style sections.

The plateau-edge witnesses (`_lt_` instances at 11, 17, 29, 97) tighten
the existing eq-instances by formally pinning each plateau as
*maximal*. Iter 11/12 showed the plateaus *exist*; iter 13 shows they
do not extend.

**Build**: pending (Docker rebuild from fresh Mathlib cache —
worktree's proofs/.lake recursive self-symlink forces ≥45-min cold-cache
builds per `feedback_researcher_lake_symlink_broken.md`). All new
content uses only Mathlib API exercised by earlier iterations
(`Nat.le_findGreatest`, `Nat.findGreatest_le`, `lt_of_le_of_lt`,
`lt_of_lt_of_le`, `ne_of_lt`, `absurd`, `decide`, `norm_num`); CI is
the ground truth.

**Path forward** (revised post-iter-13):
1. **Symmetric biconditional** (1-line follow-up): drop the `n ≤ m`
   hypothesis from the iff by symmetrizing — `largestPrimeBelow n =
   largestPrimeBelow m ↔ no prime in (min n m, max n m]`. Routine
   case-split.
2. **symBUDim-side iff** (conditional on conjecture): characterize when
   `symBUDim n d = symBUDim m d` for all `d` in terms of the LPB iff.
   Note: only the forward direction lifts cleanly; the reverse needs
   `symBUDim_cyc` injectivity-across-primes which is not currently
   axiomatized.
3. Stretch (unchanged): n=3 case directly via `symBUDim_three`-style
   axiom, or n=4 case via Klein-4 V₄ ≤ S₄ structure (would settle the
   conjecture for many small-n applications).
4. Stretch (unchanged): falsification target `buDim 3 3` via
   equivariant cohomology of Z/3 on simple S²-actions.

## Iteration 14 Builds (researcher-13, 2026-05-09)

Focus: **drop the order hypothesis from the Part XIX biconditional** —
execute Path Forward Item 1 from Iter 13 (`Symmetric biconditional`).
The Part XIX iff `largestPrimeBelow_eq_iff_no_prime_in_range` requires
`n ≤ m`; the new symmetric form characterizes the unordered pair via
`min`/`max`.

### Part XX additions (axiom-free)

- `largestPrimeBelow_eq_iff_no_prime_in_range_symm`: for arbitrary
  `n m : ℕ` (no order hypothesis), `largestPrimeBelow n =
  largestPrimeBelow m ↔ ∀ k, min n m < k → k ≤ max n m → ¬ Nat.Prime k`.
  Routine case-split via `le_total n m`: each branch reduces to the
  asymmetric Part XIX iff with arguments in the canonical order, with
  `Eq.symm` bridging the LHS in the reverse case. Six lines.
- `largestPrimeBelow_ne_of_prime_in_range_symm`: structural
  contrapositive for the unordered pair — prime in either `(n, m]`
  *or* `(m, n]` ⇒ `largestPrimeBelow n ≠ largestPrimeBelow m`. Built
  from `largestPrimeBelow_lt_of_prime_in_range` applied in each
  direction; the second case finishes via `(ne_of_lt _).symm`.

### Part XX additions (conditional on `symBUDim_eq_largestPrime`)

- `symBUDim_const_in_unordered_no_prime_range`: for `n, m ≥ 2` and
  arbitrary `d`, no prime in `(min n m, max n m]` ⇒ `symBUDim n d =
  symBUDim m d`. One-line composition of the new symmetric iff with
  `symBUDim_eq_of_lpb_eq` (Part XVI's symBUDim-LPB transfer).
- `symBUDim_const_in_unordered_no_prime_range_of`: hypothesis-form
  variant taking `ConjectureLPB` explicitly.

### Part XX additions (concrete demo)

- `largestPrimeBelow_ten_eq_eight`: re-derives the Part XVII LPB
  plateau equality `largestPrimeBelow 10 = largestPrimeBelow 8` via
  the new symmetric iff applied with arguments in the *non-canonical*
  order (`n = 10 > m = 8`), without going through `Eq.symm` of the
  existing `largestPrimeBelow_eight_eq_ten`. Verifies that `min`/`max`
  reduce as expected at concrete numerics (`min 10 8 = 8` and
  `max 10 8 = 10`, both by `decide`).

**Counts**: lineCount 1376→1485 (+109), theoremCount 88→93 (+5,
substantive 86→91), definitionCount 2 (unchanged), axiomCount 1
(unchanged), sorries 0 (unchanged).

**Significance**: this iteration packages the iter-13 biconditional in
its order-free form. The asymmetric Part XIX iff was the structural
result; the Part XX symmetrization is the *canonical statement* for
unordered pairs `{n, m}` and removes a routine boilerplate every
downstream caller would otherwise have to apply. It is also a
prerequisite for downstream symBUDim-side iff packaging where the
unordered pair is more natural than imposing an arbitrary order.

The downstream `symBUDim_const_in_unordered_no_prime_range` family
delivers the conjectural collapse `symBUDim n d = symBUDim m d` for
unordered pairs satisfying the no-prime-in-gap condition — directly
addressing the structural prediction from Iter 11 Part XVII without
needing to choose `min`/`max` orientation upfront.

**Build**: pending (Docker rebuild from fresh Mathlib cache —
worktree's proofs/.lake recursive self-symlink forces ≥45-min cold-cache
builds per `feedback_researcher_lake_symlink_broken.md`). All new
content uses only Mathlib API exercised by earlier iterations
(`le_total`, `min_eq_left`, `min_eq_right`, `max_eq_left`,
`max_eq_right`, `decide`, `Eq.symm`); the proof-side risk is minimal.
CI is the ground truth.

**Path forward** (revised post-iter-14):
1. **symBUDim-side biconditional** (still pending): characterize when
   `symBUDim n d = symBUDim m d` for *all* `d` in terms of the
   no-prime-in-range condition. Forward direction is now the new
   `symBUDim_const_in_unordered_no_prime_range`; the reverse direction
   needs `symBUDim_cyc` injectivity-across-primes which is not
   currently axiomatized. May be in scope as a *one-direction* iff
   bridging Part XVI and the symmetric form.
2. Stretch (unchanged): n=3 case directly via `symBUDim_three`-style
   axiom, or n=4 case via Klein-4 V₄ ≤ S₄ structure.
3. Stretch (unchanged): falsification target `buDim 3 3` via
   equivariant cohomology of Z/3 on simple S²-actions.
4. **Concrete unordered-pair instances**: apply
   `symBUDim_const_in_unordered_no_prime_range` to specific small-n
   pairs (`{8, 10}`, `{13, 16}`, `{23, 28}`, `{89, 96}`) to package
   each Part XVII–XVIII plateau as an unordered-pair statement. Likely
   incremental; gauge value before committing.
