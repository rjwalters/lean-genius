# Current State

**Phase**: SURVEY (obstruction scoped)
**Since**: 2026-06-26T19:00:00Z
**Iteration**: 4

## Current Focus

Iteration 4 (researcher-4, 2026-06-26): scoped the tractability of the
two remaining main-file sorries. **Conclusion: both are research-grade
and blocked on missing Mathlib infrastructure — not a single-iteration
target.** See "Iteration 4 Findings" below. No Lean changes made; the
verified entry was deliberately left untouched rather than padded with
speculative scaffolding sorries.

## Iteration 4 Findings (researcher-4, 2026-06-26)

Verified current ground truth across the three files:

- `Erdos1168Problem.lean` (255 L): **2 real sorries**
  (`base_case_under_gch`, `stepping_up`), 0 axioms, 14 thm / 9 def.
  (A `grep sorry` reports 4 — two are `(sorry)` mentions inside the
  Part V summary comment, not code.)
- `Erdos1168OQ01.lean` (169 L): **0 sorries, 0 axioms** — the verified
  ZFC pcf lower bound ℵ_{ω+1} ≤ ℵ_ω^{ℵ₀} ≤ 2^{ℵ_ω}. This is the
  achievable, shipped half.
- `Erdos1168Aristotle.lean` (68 L): **0 sorries** (the 8 routine
  cardinal-arithmetic helpers were already discharged in iteration 3;
  the lone `grep` hit is the docstring template line).

**Key obstruction (the reason this is not a single-iteration win):**
A full-tree search of the bundled Mathlib
(`proofs/.lake/packages/mathlib`) for partition-relation / Ramsey /
Sierpiński / Erdős–Rado infrastructure on infinite cardinals returns
**nothing**. Mathlib has *no* `κ → (α)²_c` notation, no negative
partition relations, no Sierpiński coloring, no Erdős–Rado theorem.
Therefore:

- `base_case_under_gch` (under GCH, ℵ_{n+1} ↛ (ℵ_{n+1}, n+3)²) must be
  built from scratch: the Sierpiński/Erdős–Rado coloring of pairs of
  2^{ℵ_n}=ℵ_{n+1} via a second (lexicographic) order, plus the counting
  argument bounding homogeneous sets. Multi-session formalization.
- `stepping_up` (Galvin–Hajnal cofinality-ω diagonalization assembling
  the bad ℵ₀-coloring of ℵ_{ω+1} from per-level bad 2-colorings) needs
  a concrete decomposition of ℵ_{ω+1} along the ℵ_n-filtration and the
  divergence-index coloring. Also multi-session.

Neither is reachable by Aristotle (the MCP proof-search agent is for
routine Mathlib-backed lemmas, not research-grade set-theory
constructions). Adding partial/speculative sorries for these into the
otherwise-verified parent file would *degrade* the entry, so it was
left as-is.

**Recommended next attack (for a dedicated multi-session effort):**
start the Sierpiński base case as a *separate* companion file
(`Erdos1168SierpinskiAristotle.lean` or similar) so the verified parent
is never put at risk; first formalize the abstract lemma "if a set
carries two well-orders of types κ and κ⁺ then the agreement-coloring
has no homogeneous set of size κ⁺", which is the GCH-free combinatorial
kernel of `base_case_under_gch`.

## (Iteration 3 record below)

## Earlier Focus (iteration 3)

Discharged the **8 routine cardinal-arithmetic sorries** in the
Aristotle helper file `Proofs/Erdos1168Aristotle.lean` (Mathlib
monotonicity, ℵ₀ bounds, cofinality of successor alephs).

## Active Approach

Direct proof via standard Mathlib API:
- `Cardinal.aleph_lt_aleph` / `Cardinal.aleph_le_aleph` for monotonicity
- `Cardinal.aleph0_le_aleph` for the universal infinitude bound
- `Cardinal.nat_lt_aleph0` for the finite-vs-aleph₀ comparison
- `Cardinal.isRegular_aleph_succ` (or equivalent) for the cofinality
  identity at successor alephs
- `Order.succ_eq_add_one` for the ω+1 vs Order.succ ω bridge

## Blockers

None for the helper file. The 2 main-file sorries (`base_case_under_gch`,
`stepping_up`) remain — they require the deep Erdős–Hajnal partition-tree
argument and Galvin–Hajnal cofinality-ω stepping-up theorem, both
research-grade results.

## Next Action

Session 4: After the helper sorries are clean, attack the main-file
sorries. `base_case_under_gch` follows from the standard Erdős–Hajnal
ω-tree partition: for each α < ℵ_{n+1}, choose an injection
α → ℵ_{n+1} via cardinal-equipotence (GCH), build the bad coloring
via the partition-tree structure. `stepping_up` follows the
Galvin–Hajnal pattern: a bad coloring at every aleph_n lifts to a
bad coloring at aleph_{ω+1} via cofinality-ω diagonalization.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 2 (axiom-elimination, ACT)

## Iteration 3 Builds (researcher-10, 2026-05-08)

Focus: clean up the **routine** half of the formalization stack —
the 8 cardinal-arithmetic sorries that the proof search agent could
likely close, but which are simple enough to prove by direct API
lookup.

- `aleph_omega_infinite : ℵ₀ ≤ Cardinal.aleph omega0` —
  direct from `Cardinal.aleph0_le_aleph`.
- `aleph_omega_succ_uncountable : ℵ₀ < Cardinal.aleph (omega0 + 1)` —
  via `aleph_zero` and strict monotonicity from `0 < omega0 + 1`.
- `omega_plus_one_is_succ : omega0 + 1 = Order.succ omega0` —
  `(Order.succ_eq_add_one omega0).symm`.
- `aleph_mono : α ≤ β → ℵ_α ≤ ℵ_β` —
  `Cardinal.aleph_le_aleph.mpr`.
- `aleph0_le_aleph (α) : ℵ₀ ≤ ℵ_α` —
  direct from `Cardinal.aleph0_le_aleph`.
- `three_le_aleph0 : (3 : Cardinal) ≤ ℵ₀` —
  `(Cardinal.nat_lt_aleph0 3).le`.
- `aleph0_le_aleph_nat_succ (n) : ℵ₀ ≤ ℵ_{n+1}` —
  same as `aleph0_le_aleph (n+1)`.
- `cof_aleph_succ : (ℵ_{succ α}).ord.cof = ℵ_{succ α}` —
  `(Cardinal.isRegular_aleph_succ α).cof_eq` (regular cardinal API).

**Counts**: lineCount 66 → ~66, theoremCount 10 (unchanged), sorries
8 → 0, axiomCount 0 (unchanged).

**Build**: verified via `./proofs/scripts/docker-build.sh
Proofs.Erdos1168Aristotle`.

## Iteration 2 Builds (earlier session, 2026-05-07)

Eliminated both axioms in `Erdos1168Problem.lean`:
- `erdos_1168` was an `axiom` claiming the open conjecture; now a
  `def : Prop` (not asserted true).
- `erdos_1168_under_gch` was an `axiom`; now a `theorem` with GCH
  hypothesis (no axiom required for the conditional result).

Result: axiomCount 2 → 0; 2 main-file sorries remain
(base_case_under_gch, stepping_up).

## Iteration 1 Builds (earliest session)

- Initial formalization: defined `partitionRelation`, `IsHomogeneous`,
  `targets`, `aleph_omega`, `aleph_omega_succ`.
- Proved: `empty_homogeneous`, `singleton_homogeneous`,
  `IsHomogeneous.subset`, `partitionRelation.mono_targets`.
- Set up the framework for `gch_implies_conjecture`.
