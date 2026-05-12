# sperner-simplicial-instance-oq-05 — State Log

## Session 1 — S1 OBSERVE (2026-05-12, researcher-11)

**Phase**: NEW → S1 OBSERVE complete

**Claim**: `research/claims/sperner-simplicial-instance-oq-05.json`
(researcher-11, expires 2026-05-12T17:46:39Z).

**Worktree branch**: `research/sperner-simplicial-instance-oq-05-s1-observe`,
based on `origin/main` at commit `6457155f73e` (S9 ACT angle-trisection).

### What was done

- Read the parent `proofs/Proofs/SpernerSimplicialInstance.lean` (994 LOC,
  28 thms, 0 sorries, 0 axioms, verified). Identified the bridge
  architecture: `Triangulation V n` → `toCellComplex` → `CellComplex` →
  `CellComplex.sperner` (`SpernerMathlib4.lean:714`).
- Read `proofs/Proofs/SpernerMathlib4.lean` (732 LOC) for the abstract
  framework. Confirmed `IsPanchromatic`, `IsDoor` are `Decidable`
  (lines 452, 459). `door_count_parity` (line 386) is the algorithmic
  heart of Scarf's pivot.
- Identified the **explicit OQ-stated bottleneck**: line 367,
  `noncomputable def AbstractSimplicialData.findOppositeIdx`, which
  uses `Classical.choose` on a decidable existential. This is also
  what the OQ-05 notes call out as the gating issue.
- Identified the **secondary site**: `Proofs/BrouwerFixedPointOQ04OQ04.lean:244`,
  `axiom scarf_approx_fixed_point` — the eventual replacement target
  for a verified Scarf algorithm.
- Surveyed neighbouring slugs (`sperner-ndim`, `sperner-freudenthal*`)
  to avoid duplicating existence-theorem work; OQ-05 is orthogonal
  (computability, not higher-dim existence).
- Wrote three candidate formal targets in `problem.md`:
  - (C1) brute-force enumeration via `Finset.filter` + correctness proof
    against the parity theorem;
  - (C2) the literal Scarf door-chain walk;
  - (C3) refactor `findOppositeIdx` from `Classical.choose` to
    `Finset.filter … .min'`.
- Wrote `knowledge.md` with the full Mathlib + gallery API survey,
  per-target LOC estimates, and Mathlib PR opportunities.

### Files produced

- `research/sperner-simplicial-instance-oq-05/problem.md` (this dir)
- `research/sperner-simplicial-instance-oq-05/knowledge.md`
- `research/sperner-simplicial-instance-oq-05/state.md` (this file)
- updated `src/data/research/problems/sperner-simplicial-instance-oq-05.json`
  with `knowledge.insights`, `builtItems`, `mathlibGaps`, `nextSteps`,
  iteration → 1, phase → "S1 OBSERVE complete", focus and nextAction
  updated.

**No Lean files edited.** S1 is observation/scaffolding only; the parent
verified file is untouched.

### Tractability assessment

| Target | Effort | Risk |
| --- | --- | --- |
| (C1) brute-force | LOW (~50 LOC, 1 session) | trivial correctness pitfall; ships a `#eval`-able demo |
| (C2-1d) Scarf walk on intervalTriangulation | MEDIUM (~120 LOC, 1 session) | termination measure needs care; no `findOppositeIdx` blocker |
| (C2-gen) Scarf walk on general Triangulation | HIGH (~250 LOC, 2-3 sessions) | requires (C3) for `AbstractSimplicialData` users |
| (C3) findOppositeIdx → computable | MEDIUM (~80 LOC, 1 session) | clean refactor of a verified 0-sorry parent; build-cost risk only |

### Next action

S2 should commit to **(C1) brute-force + correctness** as the highest
ROI ship. Concretely, S2 creates
`proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` with:

1. `def findPanchromaticBrute (T : Triangulation V n) (c : V → Fin (n+1))
   : Option T.Cell` (a one-liner `Finset.filter |>.toList.head?`);
2. `theorem findPanchromaticBrute_eq_some_iff` — characterisation;
3. `theorem findPanchromaticBrute_isSome_of_boundary_odd` — totality
   under the parity hypothesis, by `Triangulation.sperner`;
4. `#eval`-able demo on `intervalTriangulation 3 (by norm_num)` with an
   explicit Sperner coloring.

S3 (later) can pursue **(C3)** if a downstream session wants to attack
(C2-gen). The two are independent: (C1) ships value immediately even if
(C3) never lands.

### Race / coordination notes

- `gh pr list -R rjwalters/lean-genius --state open --search "sperner-simplicial-instance"`
  returned 0 results on 2026-05-12T16:11Z. Slug is **uncontested** as of
  S1 start.
- `gh pr list ... --search "sperner-ndim"` and
  `... --search "sperner-freudenthal"` return active session work — but
  those slugs are working on higher-dimensional *existence*, not
  computability, so race risk on this slug is low.
- Per `MEMORY.md` fresh-slug saturation note: this is a Seeker-added
  slug (added at 2026-05-12T14:13:22Z, ~2h before claim), no PR yet.
  Above the 30-min saturation window but well below the level of
  established slugs. S1 OBSERVE is the natural first PR.

### Blockers

None. (C1) is unblocked and ships in one session. (C3) is unblocked
modulo build re-verification. (C2-gen) is blocked on (C3).
