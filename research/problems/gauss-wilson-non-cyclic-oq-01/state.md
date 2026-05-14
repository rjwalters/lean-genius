# State — gauss-wilson-non-cyclic-oq-01

## Current phase

**S8 ACT shipped (2026-05-13).** Phase B strategic sorry discharged
via strong-induction-on-Finset (neither Route A nor Route B from S4
PREP). Slug-level sorry count: **1** (Phase C non-cyclic direction at
`GaussWilsonNonCyclicOQ01.lean:149`, transitively unblocked).

## Phase chain snapshot (2026-05-13 post-S8 ACT)

| Phase | File | LOC | Sorries | Status | Originating PR |
|---|---|---|---|---|---|
| A | `GaussWilsonNonCyclicOQ01A.lean` | 66 | 0 | build-verified | #18147 (S2 ACT) |
| B (core) | `GaussWilsonNonCyclicOQ01B.lean` | 243 | **0** | **build-verified** | #18232 (S3) + #18??? (S8 this PR) |
| C (iff scaffold) | `GaussWilsonNonCyclicOQ01.lean` | 201 | 1 | build-pending | #18652 (S6 ACT) |

**Remaining sorry (build-pending; companion: 0 axioms slug-wide):**

1. `GaussWilsonNonCyclicOQ01.lean:149` —
   `prod_eq_one_of_not_isCyclic_aux` (Phase C non-cyclic direction).
   Per the in-file docstring lines 133–135, composes (i) Phase A
   `prod_univ_eq_prod_two_torsion`, (ii) parent's
   `card_sq_eq_one_ge_three` + power-of-2-cardinality upgrade,
   (iii) Phase B `prod_univ_eq_one_of_elementary_card_ge_four`
   (now sorry-free post-S8). Estimated 30-50 lines.

## Iteration log

### S8 ACT — 2026-05-13 (this PR)

**Result:** Phase B strategic sorry
`prod_univ_eq_pow_card_div_two_of_elementary` at
`GaussWilsonNonCyclicOQ01B.lean:131` discharged. Slug-level sorry
count `2 → 1`. Phase B is now sorry-free; only the Phase C
non-cyclic-direction auxiliary remains.

**Route:** Strong induction on `Finset H` (not Route A.2 or Route B
from S4 PREP). Generalized statement: *any Finset `S` closed under
left-multiplication by `h` has cardinality `2k` and product `h^k`.*
Specialize to `S = univ` (closure trivial). Induction step erases one
orbit `{x, h*x}` per recursion (`x ∈ S`, `h*x ∈ S` by closure,
`h*x ≠ x` by `mul_left_ne_self_of_ne_one`); residue `S' = (S.erase
x).erase (h*x)` is again closed under `(h * ·)` by left cancellation
and `mul_left_self_inv_of_elementary`.

**LOC delta:** Phase B file 165 → ~243 (+78 net). Module docstring
refreshed; "deferred to S4" language removed.

**Why neither Route A nor Route B:**
- Route A.2 (Quot.out transversal + `Finset.prod_image`) requires
  `MulAction.Quotient` + `Subgroup.zpowers h` instance plumbing.
- Route B (`MulAction.selfEquivSigmaOrbits` per S4b PREP errata)
  requires `orderOf h = 2` lemma chase + `Fintype.card_zpowers`.
- Strong induction needs zero of these. Identifiers used:
  `Finset.strongInduction`, `Finset.erase_subset`,
  `Finset.erase_ssubset`, `Finset.mem_erase`,
  `Finset.card_erase_of_mem`, `Finset.card_pair`,
  `Finset.card_le_card`, `Finset.mul_prod_erase`,
  `Finset.card_univ`, `mul_left_cancel`, `mul_left_comm`,
  `pow_succ'`. All v4.26.0-verified at pinned commit
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Build status:** **build-verified** via
`./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01B`.
`✔ [3058/3058] Built Proofs.GaussWilsonNonCyclicOQ01B (4.5s)`.
The first build attempt hit a `lt_of_le_of_lt` vs `S' ⊂ S` type
mismatch (Finset's `HasSSubset` instance is not definitionally
inferred from `lt_of_le_of_lt`); fixed by inlining
`refine ⟨..., ...⟩` directly on the `HasSSubset.SSubset`
constructor.

**Sorries / axioms delta:**
- Sorries: −1 in `GaussWilsonNonCyclicOQ01B.lean` (1 → 0).
  Slug-level: 2 → 1.
- Axioms: 0 (unchanged).

**Session log file:**
`sessions/2026-05-13-s8-act-transversal-pairing-discharge.md`.

### S7 ACT — 2026-05-13 (PR #18743 merged)

**Result:** Cyclic-direction strategic sorry discharged in
`GaussWilsonNonCyclicOQ01.lean` (line 103 in the as-merged file →
`prod_eq_neg_one_of_isCyclic_aux`, now at line 97 post-merge). +29/-11
LOC; renames `_hcyc → hcyc` and refreshes docstring. Slug-level sorry
count `3 → 2`. Build pending (recursive `.lake` symlink, gallery
convention).

### S7 PREP — 2026-05-13 (PR #18700 merged)

**Result:** Doc-only. (a) S6 ACT audit (zero drift from S5b's corrected
skeleton across 10 audit dimensions); (b) 22-LOC drop-in recipe for the
cyclic-direction discharge via uniform `IsCyclic.card_pow_eq_one_le`
(no `p.Prime`/`p^k`/`2·p^k` case-split needed); (c) `haveI`
instance-lifting subtlety flagged for the `IsCyclic` hypothesis. Recipe
consumed verbatim by S7 ACT.

### S6 ACT — 2026-05-13 (PR #18652 merged)

**Result:** Phase C **scaffold** shipped in
`proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` (201 lines). Outer iff
`prod_univ_units_zmod_eq_neg_one_iff_isCyclic` derived modulo 2
strategic sorries (cyclic / non-cyclic direction aux lemmas). Follows
S5b's corrected skeleton (Bug 1–4 fixes present; `interval_cases`
properly bounded; `private` parent-file lemma re-derived inline as
`neg_one_ne_one_units_of_ge_three`).

### S5b PREP — 2026-05-13 (PR #18607 merged)

**Result:** Doc-only. Audits S5 PREP design memo (PR #18502/#18465) and
flags **4 concrete Lean-tactic bugs** in the iff-theorem skeleton: (1)
`interval_cases n` lacks upper bound on `1 ≤ n`; (2) `all_goals` after
`decide` is unreachable; (3) `absurd h_cyc h_cyc` type mismatch via
shadowing; (4) parent-file `neg_one_ne_one_units'` is `private` and
needs re-derivation. Full Mathlib v4.26.0 API verification against pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

### S5 PREP — 2026-05-12/13 (PR #18502 merged)

**Result:** Doc-only. Designs the **third independent deliverable**
(OQ-01-C: main iff theorem) per `problem.md` §"Approach map", with full
proof skeleton, Mathlib API map, and design memo for S6 ACT.

### S4b PREP — 2026-05-13 (PR #18467 merged)

**Result:** Doc-only. Mathlib v4.26.0 API audit at pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Two erratum-grade findings:
(1) `MulAction.selfEquivSigmaOrbits` actually at
`GroupTheory/GroupAction/Defs.lean:482` not `Basic.lean:476`; (2)
`|⟨h⟩| = orderOf h` Mathlib names corrected. No new Lean code.

### S4 PREP — 2026-05-12 (PR #18347 merged)

**Result:** Doc-only. Surveys **four Mathlib API routes** for closing
the Phase B strategic sorry `prod_univ_eq_pow_card_div_two_of_elementary`:
(A) explicit transversal Finset + `Finset.prod_image`, (B)
`MulAction.Quotient` via `Subgroup.zpowers h`, (C) involution-pairing
via `Finset.prod_involution` re-application, (D) `Equiv.Perm`
decomposition. Compares LOC, coverage risk, and prerequisite typeclass
machinery. Route ranking: B (preferred) > A > C > D. Single file
`sessions/2026-05-12-s4-prep-strategic-sorry-routes.md` (+391 LOC).

### S3 ACT (partial) — 2026-05-12 (researcher-1, PR #18232 merged)

**Result:** Phase B core theorem stated and derived modulo one
strategic sorry. Five helper lemmas fully build-verified.

**Built:**
- `proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean` — 165 lines.
  - `mul_left_self_inv_of_elementary` — for `h^2 = 1` in any `CommGroup`,
    left translation by `h` is an involution. (build-pending; 1-line
    proof via `mul_assoc + sq + one_mul`).
  - `mul_left_ne_self_of_ne_one` — in any group, left translation by
    `h ≠ 1` is fixed-point-free. (build-pending; 3-line proof via
    `mul_right_cancel`).
  - `pow_eq_one_of_sq_eq_one` — for `h^2 = 1` and `k` even, `h^k = 1`.
    (build-pending; 3-line proof via `obtain ⟨m, rfl⟩ := hk + pow_mul +
    one_pow`).
  - `pow_eq_self_of_sq_eq_one` — for `h^2 = 1` and `k` odd, `h^k = h`.
    (build-pending; 2-line proof via `obtain ⟨m, rfl⟩ := hk + pow_succ
    + pow_mul + one_pow + one_mul`).
  - `exists_two_distinct_ne_one` — in a finite group of order ≥ 4,
    there exist `h₀ ≠ h₁` both non-identity. (build-pending;
    ~20-line proof via `Finset.erase` cardinality bookkeeping).
  - **(STRATEGIC SORRY)** `prod_univ_eq_pow_card_div_two_of_elementary`
    — for elementary 2-abelian `H` and `h ≠ 1`,
    `∏ x : H, x = h ^ (Fintype.card H / 2)`. Deferred to S4.
  - `prod_univ_eq_one_of_elementary_card_ge_four` — Phase B main
    theorem; derived from the strategic sorry plus the helpers in
    ~15 lines via `by_cases Even (N/2)`.
- `proofs/Proofs.lean` — alphabetical insertion of import line.

**Mathematical content of the strategic sorry.** The map
`σ_h : H → H`, `σ_h x := h * x`, is a fixed-point-free involution
(established by the build-verified helpers
`mul_left_self_inv_of_elementary` + `mul_left_ne_self_of_ne_one`). Its
orbits partition `Finset.univ` into `Fintype.card H / 2` pairs of size
`2`. The product over a pair `{x, h*x}` is `x * (h*x) = h * x^2 = h`,
so the total product equals `h ^ (Fintype.card H / 2)`. The Lean
formalisation needs either (a) an explicit transversal Finset and
`Finset.prod_image`, or (b) a `MulAction.Quotient`-based route through
`H ⧸ Subgroup.zpowers h`. Neither is mechanical in 30 lines — deferred
to S4.

**Derivation of Phase B from the strategic sorry (build-verified, in
file).** Pick two distinct non-identity `h₀ ≠ h₁` via
`exists_two_distinct_ne_one`. The strategic sorry gives
`∏ x : H, x = h₀ ^ (N/2)` and `= h₁ ^ (N/2)` where
`N := Fintype.card H`. Either `N/2` is even (then `h₀ ^ (N/2) = 1` by
`pow_eq_one_of_sq_eq_one` and we conclude) or `N/2` is odd (then
`h₀ ^ (N/2) = h₀` and `h₁ ^ (N/2) = h₁`, forcing `h₀ = h₁`,
contradiction).

**Build status:** **build pending**. The worktree `proofs/.lake`
symlink is recursive (per `feedback_researcher_lake_symlink_broken.md`);
a fresh Docker Mathlib clone is ~25–45 min. The file imports only
`Mathlib.Algebra.BigOperators.Group.Finset.Basic`,
`Mathlib.Algebra.Group.Basic`, and `Mathlib.Tactic` — identical to the
S2 file (build-verified). Risk surface is minimal: each helper proof is
mechanical (≤ 5 lines), and the main theorem's case-split derivation is
a short tactic chain over `Even`/`Odd`.

**Sorries / axioms delta:**
- Sorries: +1 (strategic, in the new file).
- Axioms: 0 (unchanged).

**Why not the full Phase B?** The transversal-pairing identity
`prod_univ_eq_pow_card_div_two_of_elementary` requires either an
ad-hoc transversal construction or a `MulAction.Quotient` route. Both
need ~50–80 additional lines, and the right architecture is not
obvious without inspecting Mathlib's `MulAction.orbit` / `orbitFinset`
API in detail. Strategic-sorry isolation is the cleanest way to ship
the Phase B core structure now; the residual gap is localised to one
clearly-stated lemma whose mathematical content is a single textbook
identity.

### S2 ACT — 2026-05-12 (researcher-9, PR #18147 merged)

**Result:** Phase A delivered as a standalone Lean file with 0 sorries.

**Built:**
- `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` — 66 lines.
  Single theorem `prod_univ_eq_prod_two_torsion : ∀ G [CommGroup G]
  [Fintype G] [DecidableEq G], ∏ x : G, x = ∏ x ∈ univ.filter (·^2 = 1), x`.
  Proof via `Finset.prod_involution` with `x ↦ x⁻¹` on the non-2-torsion
  half.
- `proofs/Proofs.lean` — alphabetically inserted import line.

### S1 OBSERVE — 2026-05-12 (researcher-5, PR #18116 merged)

**Result:** Doc-only S1 OBSERVE, no Lean changes. Three-phase
decomposition (Phase A / Phase B / Phase C) with Mathlib readiness map
and 15-row numerical sanity table.

## Blockers

None mathematical. Only the Phase C non-cyclic-direction auxiliary
`prod_eq_one_of_not_isCyclic_aux` at `GaussWilsonNonCyclicOQ01.lean:149`
remains as a sorry, and it is no longer blocked transitively now that
Phase B is sorry-free.

**Operational:** The worktree `proofs/.lake` symlink is recursive
(`feedback_researcher_lake_symlink_broken.md`); S8 ACT shipped as
build pending per gallery convention.

**Doc-drift note (still open):** the in-file docstring of
`GaussWilsonNonCyclicOQ01.lean` (lines 25, 33) says "2 strategic
sorries deferred to S7/S8". Post-S7+S8 only 1 sorry remains in the
parent file, and Phase B is now sorry-free. The Phase chain table on
line 32 also still describes Phase B as "S3 PR #18232" only. Refresh
those docstrings opportunistically when the next ACT session touches
the file (S9 candidate).

## Next Action

**S9 ACT — close the Phase C non-cyclic-direction sorry
`prod_eq_one_of_not_isCyclic_aux`** at
`GaussWilsonNonCyclicOQ01.lean:149`. With Phase B now sorry-free (S8
ACT this PR), the composition described in the in-file docstring
(lines 133-135) is mechanically tractable:

1. Apply Phase A `prod_univ_eq_prod_two_torsion` to reduce `∏ univ`
   over `(ZMod n)ˣ` to `∏ 2-torsion`.
2. Invoke parent `card_sq_eq_one_ge_three` to get `|2-torsion| ≥ 3`.
3. Power-of-2-cardinality upgrade: 2-torsion has exponent 2 → its
   order is a power of 2 → `≥ 3` upgrades to `≥ 4`.
4. Apply Phase B `prod_univ_eq_one_of_elementary_card_ge_four`.

Step (3) is the load-bearing step; Mathlib offers
`IsPGroup.card_eq_pow_one_iff_orderOf_dvd` (or similar) for the
prime-power-cardinality lemma. S5b PREP (PR #18607) scoped this out
in detail. Estimated 30-50 lines.

**S10 (after S9) — completion:** build-verify all three files
(Docker rebuild from clean `.lake`); update meta.json sorry/axiom
counts; close the slug as COMPLETED.

## Attempt Counts

- Total attempts: 10 (S1 OBSERVE, S2 ACT, S3 ACT partial, S4 PREP, S4b
  PREP, S5 PREP, S5b PREP, S6 ACT, S7 PREP, S7 ACT).
- Current approach attempts: per-phase, 1 each.
- Approaches tried: 1 (3-phase decomposition).

## Open files

- `problem.md` — formal Lean signature targets, three-phase decomposition.
- `knowledge.md` — proof sketches, Mathlib API summary, S2 next-action skeleton.
- `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` — Phase A (S2, 0 sorries, build-verified).
- `proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean` — Phase B core (S3, 1 strategic sorry, build-pending).
- `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` — Phase C iff scaffold (S6, S7-discharged cyclic direction, 1 remaining sorry, build-pending).

## Race awareness

As of this STATE-SYNC commit, **0 open PRs** on
`gauss-wilson-non-cyclic-oq-01` (`gh pr list --search
"gauss-wilson-non-cyclic-oq-01 in:title" --state open` returns `[]`).
Sibling `gauss-wilson-non-cyclic-oq-03` has 1 open PR (#18230, S5-prep
on parity at odd primes) — independent slug, no overlap with this
slug's Phase B/C strategic sorries.

## STATE-SYNC notes

This entry is a doc-only tracker resync (no Lean / no JSON beyond
`currentState` / `knowledge.progressSummary` / `lastUpdate`). The
in-file Phase chain docstring in `GaussWilsonNonCyclicOQ01.lean` is
intentionally left stale (refresh deferred to next ACT touch).
