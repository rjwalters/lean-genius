# Research State: erdos-117-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T17:33:20-07:00
**Iteration**: 3

## Status (researcher-1, 2026-07-22, session 3) — FIRST JUMP: h(n) ≥ 3 FOR ALL n ≥ 3

New file `Erdos117WIP01Three.lean` (10 thm, 0 ax, 0 sorry, docker-verified, 8581 jobs;
`#print axioms = [propext, Classical.choice, Quot.sound]` — the `decide` route, NOT
`native_decide`, so no `Lean.ofReduceBool`). The ladder jumps past 2 at n=3.

- `eq_top_or_eq_top_of_cover` — **no group is a union of two proper subgroups** (classical:
  `x ∉ H`, `y ∉ K` force `xy ∉ H ∪ K`). No counting/finiteness/Lagrange — kills budget 2
  in complete generality (stronger than the order-count plan sketched last session).
- `comm_of_two_abelian_cover` — two abelian subgroups cover ⟹ the group is abelian.
- `quaternionGroup_hasNCommutingProperty_three` — **Q₈ = `QuaternionGroup 2` has the
  3-commuting property**, by kernel `decide` over all 2⁸ subsets (`maxRecDepth 8192`,
  `maxHeartbeats 1600000`). Math: a 4-subset meets the center or pigeonholes two elements
  onto one axis ⟨i⟩/⟨j⟩/⟨k⟩. With `quaternionGroup_not_comm` (`i·j ≠ j·i`, also `decide`):
  the n=2 collapse is **sharp** (`hasNCommutingProperty_three_not_comm`).
- `not_coversWithAbelian_two` / `_one` — for n ≥ 3, budgets 2 and 1 never cover. Witness
  `ULift Q₈` transported via `MulEquiv.ulift.symm` + `hasNCommutingProperty_mono`
  (universe gotcha handled; commutation pulled back through `congrArg ULift.down`).
- `three_le_abelianCoverNumber` — **h(n) ≥ 3 for all n ≥ 3**, conditional exactly on
  well-definedness (`∃ k, CoversWithAbelian k n` = Pyber's unformalized upper bound);
  via `Nat.sInf_mem` + `coversWithAbelian_upward`.
- `abelianCoverNumber_two_lt_three` — **h(2) < h(3)**: the ladder's first strict jump
  past 1. Known shape now `0, 1, 1, ≥3, …`.
- `abelianCoverNumber_three_eq_zero_or_three_le` — unconditional dichotomy: `h(3) = 0`
  (sInf ∅ fallback) ∨ `h(3) ≥ 3`; in no case is `h(3) ∈ {1, 2}`.

**v4.31 note**: `push_neg` deprecated → use `push Not`.

**Where this stops (likely SATURATED for elementary work)**: `h(3) ≤ 3` (hence = 3) needs
a *uniform* 3-cover for every 3-commuting group — classification-strength, blocked. Pyber's
exponential bounds remain deep. The elementary ladder is now complete: exact values h(0),
h(1), h(2), sharpness of the collapse, monotonicity, closure, and the first lower bound
beyond abelian covers. Next rungs would need either h(4)-witnesses with larger cliques
(same pattern, diminishing insight) or genuine Pyber machinery.

## Status (researcher-1, 2026-07-22, session 2) — COLLAPSE AT n=2, h(2)=1

New file `Erdos117WIP01Two.lean` (5 thm, 0 ax, 0 sorry, docker-verified). The second exact
value of the ladder: **h(2) = 1**, via the first collapse of the property hierarchy.

- `exists_three_pairwise_noncommuting` — the crux: any non-commuting pair `a, b` spawns the
  3-element pairwise non-commuting set `{a, b, a*b}` (a 3-clique in the non-commuting graph;
  `a` vs `a*b` commute iff `ab=ba` by left cancellation, `b` vs `a*b` by right cancellation;
  distinctness forced: `a = a*b ⟹ b = 1` central).
- `hasNCommutingProperty_two_iff` — the 2-commuting property ("every 3-subset has a commuting
  pair") is *exactly* commutativity.
- `hasNCommutingProperty_two_iff_one` — n=2 and n=1 properties coincide (reverse of the
  definitional monotonicity is the mathematical content).
- `abelianCoverNumber_two` — **h(2) = 1** (same inline-witness `sInf` pattern as h(1)=1,
  universe gotcha applies).
- `abelianCoverNumber_one_eq_two` — the ladder is flat across the collapse: h(0)=0, h(1)=h(2)=1.

**Where the collapse stops (next session's target)**: Q₈ is non-abelian with the 3-commuting
property (clique number of its non-commuting graph is 3 — a clique takes at most one of each
`{±i}, {±j}, {±k}`), and no 2 abelian subgroups cover Q₈ (abelian subgroups have order ≤ 4,
`4+4−|{±1} ⊆ shared| ≤ 6 < 8`). So **h(3) ≥ 3** — first genuinely non-abelian rung. Mathlib
has `QuaternionGroup`. h(3) ≤ 3 would need a classification — likely blocked.

## Status (researcher-1, 2026-07-22) — MONOTONICITY of the covering number h(n)

New file `Erdos117WIP01Mono.lean` (1 def, 3 thm, 0 ax, 0 sorry, docker-VERIFIED, 8578 jobs;
`#print axioms = [propext, Classical.choice, Quot.sound]`). Adds the elementary structural
monotonicity of `h(n) = abelianCoverNumber n` in `n`, building on `Erdos117WIP01.lean`'s
base values (`h(0)=0`, `h(1)=1`) and closure theory.

- `CoversWithAbelian k n` — names the membership condition of `abelianCoverNumber`'s defining
  set (`k` abelian subgroups cover every finite group with the `n`-commuting property).
- `abelianCoverNumber_eq_sInf` — `h(n) = sInf {k | CoversWithAbelian k n}` (`rfl`).
- `coversWithAbelian_of_le` — the crux: for `n ≤ m`, an `m`-cover is an `n`-cover (the
  `n`-property *implies* the `m`-property via the parent's `hasNCommutingProperty_mono`).
- `abelianCoverNumber_mono` — `n ≤ m` + a finite `m`-cover exists (`∃ k, CoversWithAbelian k m`)
  ⟹ `h(n) ≤ h(m)`. The nonemptiness hypothesis is honest: unconditional monotonicity fails
  under the `Nat.sInf ∅ = 0` convention when `h(m)` is ill-defined (Pyber's upper bound /
  well-definedness is unformalized). Via `Nat.sInf_mem` + `Nat.sInf_le` on the set inclusion.

**★GOTCHA (universe)**: `abelianCoverNumber` and `CoversWithAbelian` are universe-polymorphic
in the group universe (bodies quantify `∀ (G : Type*)`); the value depends on `u`. Every
occurrence must be pinned to a single explicit `universe u` with `.{u}` annotations, else
Lean assigns independent universes → `abelianCoverNumber.{u_1}` vs `.{u_3}` /
`@h G` application-type mismatches. Also: `/- -/` (not `/-- -/`) before a `universe` command.

**STILL OPEN / out of scope**: Pyber's exponential bounds `c₁ⁿ < h(n) < c₂ⁿ` and the OPEN
exact growth base stay unformalized; `h(n)` well-definedness for general `n` = the Pyber upper
bound (nonemptiness of the `sInf` argument), NOT elementary.

## Current Focus
Elementary axiom-free scaffolding of the def-only parent stub (base values, closure, and now
monotonicity of `h`). Deep Pyber bounds remain out of reach.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.

## Status (researcher-1, 2026-07-23) — h(3) = 3 EXACT, unconditional

New file `Erdos117WIP01Exact.lean` (0 ax, 0 sorry, docker-VERIFIED). The Three.lean
header's "classification-strength" assessment of `h(3) ≤ 3` was wrong — the uniform
3-cover is elementary:
- `no_four_clique` — the 3-commuting property forbids 4 pairwise non-commuting
  elements (distinctness free: non-commuting ⟹ distinct).
- `centralizer_abelian_of_three` — the crux: u,v ∈ C(a) non-commuting ⟹ 5-way case
  split on b vs {u, v, uv} each yields an explicit forbidden 4-set
  ({au,av,b,a(uv)} / {au,b,v,uv} / mirror / {b,u,v,a(uv)} / {b,u,v,uv}).
- `exists_three_abelian_cover` — G = C(a) ∪ C(b) ∪ C(ab) with all three abelian
  (finiteness unused; works for every group).
- `coversWithAbelian_three_three`, `coversWithAbelian_three_nonempty` — h(3)
  WELL-DEFINED (discharges every `hne` hypothesis in Three.lean).
- **`abelianCoverNumber_three : h(3) = 3`** — first nontrivial exact ladder value;
  `abelianCoverNumber_two_lt_three_unconditional`; `abelianCoverNumber_le_three_of_le`.

Ladder now EXACTLY `0, 1, 1, 3, …` (all unconditional).

## Next Action (updated 2026-07-23)
Candidate next rung: h(4) ≥ 4 via S₃ (ω(S₃) = 4, minimal abelian cover 4 — needs
`not_coversWithAbelian_three` by showing no 3 abelian subgroups cover S₃, likely
`decide`-able on Equiv.Perm (Fin 3) subgroups or by the transposition argument).
h(4) well-definedness (uniform bound at ω ≤ 4) does NOT follow from this session's
trick — the centralizer-abelianness argument is specific to ω = 3; treat h(4) ≤ C
as blocked pending a materially new mechanism. Pyber bounds remain DEEP/out of scope.

## Status (researcher-1, 2026-07-23, session 2) — h(4) ≥ 4 rung (S₃), conditional

`Erdos117WIP01Four.lean` (0 ax, 0 sorry, kernel decide only): budget 3 fails for
every n ≥ 4 — S₃ has the 4-commuting property sharply (not the 3-property), and a
generic transposition/3-cycle pigeonhole defeats any abelian 3-cover. Hence
h(n) ≥ 4 for n ≥ 4 (conditional on well-definedness), h(3) < h(4) conditional,
h(4) ∈ {0} ∪ [4,∞) unconditional. Ladder: 0, 1, 1, 3 (exact), ≥4, …

Elementary rungs n ≤ 4 now EXHAUSTED except h(4) well-definedness/upper bound,
which is a registered blocked route (the ω = 3 centralizer mechanism does not
extend; reopen: Neumann-type |G:Z| ≤ f(n) formalized or materially new mechanism).
Next elementary candidate if ever needed: h(5) lower rung would need a 5-clique
witness group with abelian-cover analysis (e.g. D₅ or S₄ subsets) — NOT session-
sized without new tooling; do not chase. Pyber bounds remain the open core.
