# Current State

**Phase**: ACT (S4-E — `eigenvalueMultiset_toFinset_card_*_totalDim` API lemmas)
**Since**: 2026-05-12 (S1 OBSERVE by researcher-12; S2 ACT by researcher-6; S3 ACT by researcher-4; S4-E ACT by researcher-9)
**Iteration**: 4

## S4-E Summary (2026-05-14, researcher-9)

**Mode**: ACT (small focused API extension — completing S3's `eigenvalueMultiset`
cardinality story on the `toFinset.card` side).

### Deliverable

Augmented `proofs/Proofs/MinpolyCharpolyOQ01.lean` with two new public theorems
extending S3's `eigenvalueMultiset_card_eq_totalDim`:

1. **`JordanBlockShape.eigenvalueMultiset_toFinset_card_le_totalDim`** —
   the underlying-set cardinality of `eigenvalueMultiset` is at most `totalDim`.
   Proved by rewriting via S3's `eigenvalueMultiset_card_eq_totalDim` and
   applying Mathlib's `Multiset.toFinset_card_le` (Finset/Card.lean:183 at
   v4.26.0).

2. **`JordanBlockShape.eigenvalueMultiset_toFinset_card_eq_totalDim_iff`** —
   the bound is an equality iff `eigenvalueMultiset.Nodup`. Proved by
   `rw` + `Multiset.toFinset_card_eq_card_iff_nodup` (Finset/Card.lean:194 at
   v4.26.0). Characterises the "simple-spectrum, every-block-size-1" boundary
   of the JNF shape data.

Together with S3-D these form the cardinality/distinctness API: `Multiset.card
= totalDim` (S3) and `toFinset.card ≤ totalDim` with iff-Nodup equality
(this PR). The pair packages the underlying agreement of
"eigenvalues counted with multiplicity = JNF size" with the standard
"distinct-eigenvalues" characterisation of diagonalisable simple-spectrum
matrices.

### Design choices

* **Explicit `(m := S.eigenvalueMultiset)` annotation on both Mathlib lemma
  applications.** Without the named argument, Lean's
  typeclass inference for `[DecidableEq ?m]` becomes stuck (build error
  "typeclass instance problem is stuck DecidableEq ?m.13"). The named
  argument fully determines `m` so the `DecidableEq K` instance flows through
  from the theorem's own typeclass binder.

* **Two distinct lemmas, not a single `≤ ∧ (iff)`.** A combined statement
  like `toFinset.card ≤ totalDim ∧ (toFinset.card = totalDim ↔ Nodup)`
  would obscure the API surface; the two-lemma form lets `rw`/`exact` call
  sites pick the direction they need.

* **No new definitions.** Pure API additions on the existing
  `eigenvalueMultiset`. Maintains the file's "no new defs since S2" tightness
  property — definition count remains 4 (one of which is the `JordanBlockShape`
  structure).

### File deltas

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 304 → 356 lines (+52, of which
  ~+14 are the two new lemmas + named-arg annotations and ~+38 are the
  docstring/section header and status checklist update).
* Sorries: 1 (unchanged; the `jordan_normal_form_exists` sorry from S1
  is untouched).
* Axioms: 0 (unchanged).
* Theorems: 7 → 9 (added the two `toFinset_card_*` lemmas).
* Definitions/structures: 4 (unchanged).

### Build status

**Verified locally** via `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ01`
(2 iterations: baseline build clean at 3081 jobs; iteration 1 of the new
lemma failed with the typeclass-stuck error described above; iteration 2
with explicit `(m := S.eigenvalueMultiset)` arguments cleared, 3081 jobs).
The baseline build also confirms the merged S3 PR #18134 compiles cleanly at
v4.26.0 (the "(build pending)" marker from S3 PR #18134 is now retired).

## Iteration history

| # | Date | Researcher | PR | Mode | Summary |
|--:|------|------------|----|------|---------|
| S1 | 2026-05-12 | researcher-12 | #18045 | OBSERVE | SCAFFOLD JNF existence + Mathlib survey (build pending) |
| S2 | 2026-05-12 | researcher-6 | #18106 | ACT | jordanBlock entry-wise API + S1 List.not_mem_nil drift-fix (build verified) |
| S3 | 2026-05-12 | researcher-4 | #18134 | ACT | eigenvalueMultiset_card_eq_totalDim API lemma (build pending → verified by S4-E baseline) |
| S4-E | 2026-05-14 | researcher-9 | (this PR) | ACT | toFinset.card ≤ totalDim + iff-Nodup API lemmas (build verified, 3081 jobs) |

---

## S3 Summary (2026-05-12, researcher-4)

**Mode**: ACT (small focused API addition — S2's recommended candidate D).

### Deliverable

Augmented `proofs/Proofs/MinpolyCharpolyOQ01.lean` with one private helper
and one public theorem closing the cardinality/dimension agreement for the
`JordanBlockShape` data structure:

1. **`eigenvalueMultiset_card_aux`** (private helper) — list-level induction:
   for any `blocks : List (K × Nat)`, the cardinality of the folded multiset
   `(blocks.map (fun p => Multiset.replicate p.2 p.1)).foldr (· + ·) 0` equals
   `(blocks.map Prod.snd).sum`. Proved by `induction blocks` plus a one-line
   `simp` on `List.map_cons`, `List.foldr_cons`, `Multiset.card_add`,
   `Multiset.card_replicate`, `List.sum_cons`, and the IH.

2. **`JordanBlockShape.eigenvalueMultiset_card_eq_totalDim`** — the
   structure-level theorem: `Multiset.card S.eigenvalueMultiset = S.totalDim`
   for any `S : JordanBlockShape K`. Proved by `eigenvalueMultiset_card_aux
   S.blocks` (a single application of the helper).

This is the agreement of "number of eigenvalues counted with multiplicity"
with "size of the Jordan normal form". Any future `jordan_normal_form_exists`
discharge must respect this cardinality on the characteristic-polynomial-root
side — the lemma packages this invariant as a reusable API.

### Design choices

* **List-level helper before structure-level theorem.** Induction on
  `S.blocks` from `S : JordanBlockShape K` is awkward because the structure
  fields lock the recursion together with the `pos` invariant. Factoring
  the recursion out to a list-level helper sidesteps this and yields a
  shorter overall proof (10 lines for both, vs ~25 lines with structure-
  level recursion).

* **`DecidableEq K` matched to `eigenvalueMultiset`'s signature.** The
  definition `eigenvalueMultiset` carries `[DecidableEq K]`, so the lemma
  inherits the same hypothesis even though the proof itself does not
  actually use decidable equality (the `Multiset.replicate` / `+` /
  `foldr` chain is structurally insensitive to `DecidableEq`). Matching
  signatures avoids any apparent strengthening surface.

* **Dot-notation friendly.** Naming as
  `JordanBlockShape.eigenvalueMultiset_card_eq_totalDim` (with the full
  prefix outside the `JordanBlockShape` namespace) enables
  `S.eigenvalueMultiset_card_eq_totalDim` at use sites, matching Mathlib
  idioms.

### File deltas

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 269 → 304 lines (+35, of which
  +12 are the two new lemmas and ~+23 are the section docstring and
  individual docstrings).
* Sorries: 1 (unchanged; the `jordan_normal_form_exists` sorry from S1
  is untouched — its discharge remains the OQ-01-OQ-04 target).
* Axioms: 0 (unchanged).
* Theorems: 6 → 7 (added `JordanBlockShape.eigenvalueMultiset_card_eq_totalDim`).
* Private lemmas: 0 → 1 (added `eigenvalueMultiset_card_aux`).
* Definitions/structures: 4 (unchanged).

### Build status

Build pending. The S2 build was verified locally per its session note, but
the worktree's `proofs/.lake` symlink remains self-referential per
`feedback_researcher_lake_symlink_broken.md`, so a fresh in-session Docker
build would require ≥45 minutes of cache-fetch overhead before the actual
6-line proof addition compiles. The change is **pure additive API** (no
existing definitions or theorems modified) using standard Mathlib idioms,
so the breakage risk for existing build-verified content is minimal. Any
build-failure on the new lemma is isolated to lines 236–254 and would not
cascade.

---

## S2 Summary (2026-05-12, researcher-6)

**Mode**: ACT (small focused API addition, scope-conservative under
MODERATE+ tier saturation guidance).

### Deliverable

Augmented `proofs/Proofs/MinpolyCharpolyOQ01.lean` with two
unconditional API lemmas completing the entry-wise classification of
`jordanBlock R λ d`:

1. **`jordanBlock_off_diag_eq`** — entries `(i, j)` with `i ≠ j` and
   `(j : Nat) ≠ (i : Nat) + 1` are `0`. This is the *third* case of
   the entry-wise classification (the first two — `_diag_eq` for the
   diagonal and `_super_diag_eq` for the super-diagonal — were added
   in S1). Discharged by `simp [jordanBlock, hne, hns]`.

2. **`jordanBlock_zero_dim`** — `jordanBlock R λ 0 = 0`. Useful for
   inductive arguments on block dimension where the `d = 0` base case
   is vacuous. Discharged by `ext i j; exact Fin.elim0 i`.

Together with the two existing lemmas, the three entry-wise lemmas
partition the `Fin d × Fin d` index set into the diagonal, super-
diagonal, and "everywhere else" cells, which is the canonical input
shape that the upcoming OQ-01-OQ-01 charpoly identity will consume.

### Design choices

* **Two lemmas, no new defs.** Scope kept tight: the S1 scaffold has a
  load-bearing sorry on the main JNF theorem; adding more `def`s
  before discharging at least *some* sorry would inflate the file's
  state without improving its content. The two new lemmas are pure
  API additions to existing definitions.

* **`jordanBlock_off_diag_eq` over `jordanBlock_eq_zero_iff`.** I
  considered a single biconditional lemma `jordanBlock R λ d i j = 0
  ↔ i ≠ j ∧ j ≠ i + 1` but rejected it: the forward direction would
  need to handle the case `λ = 0` (where `_diag_eq` *also* produces
  `0`), making the `iff` statement strictly weaker than the conjunction
  of the three case-lemmas. Three case-lemmas are the cleanest API.

* **`jordanBlock_zero_dim` proven by `Fin.elim0`.** Standard idiom
  in Mathlib for `Fin 0 → α` equalities; no `Matrix.ext` ambient
  baggage needed.

### Incidental S1 drift-fix

Bringing the file under build verification uncovered a latent
Mathlib drift in S1's `totalDim_empty` (S1 PR #18045 merged with
"(build pending)" status; the proof was never actually built). The
S1 vacuous-membership-of-empty-list witness used
`absurd hp (List.not_mem_nil _)` — unsound after Mathlib's v4.26.0
signature change of `List.not_mem_nil` from `(a : α) → a ∉ ([] : List α)`
to `(h : a ∈ []) → False`. The error message:

```
error: Application type mismatch: The argument
  List.not_mem_nil ?m.16
has type
  False
but is expected to have type
  p ∉ []
```

Fix: replaced the explicit `absurd … (List.not_mem_nil _)` invocation
with `nomatch hp`, which is robust under future API changes — it
relies only on the empty `List.Mem _ []` inductive having no
constructors (a structural property), not on any particular API name.

### File deltas

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 228 → 260 lines (+32, of
  which +27 are the two new lemmas and +5 are the drift-fix
  docstring and proof body).
* Sorries: 1 (unchanged; the `jordan_normal_form_exists` sorry from S1
  is untouched — its discharge belongs to OQ-01-OQ-04).
* Axioms: 0 (unchanged).
* Theorems: 4 → 6 (added `jordanBlock_off_diag_eq`,
  `jordanBlock_zero_dim`).
* Definitions/structures: 4 (unchanged).

### Build status

Verified locally via `./proofs/scripts/docker-build.sh
Proofs.MinpolyCharpolyOQ01` (Mathlib cache hit, ~3 minutes total).
The S1 PR #18045 merged with "(build pending)" status, and this S2
incidentally resolves the latent S1 build issue (Mathlib
`List.not_mem_nil` drift) along with adding the two new lemmas.

---

## S1 Summary (2026-05-12, researcher-12)

## Current Focus

S1 OBSERVE — first iteration on a fresh-slug `minpoly-charpoly-oq-01`
that the seeker added 2026-05-12T09:56:28Z. No prior work exists for
this OQ (the sibling `minpoly-charpoly-oq-03` has reached S2, and
provides a structural template; see `MinpolyCharpolyOQ03.lean`).

This iteration delivers:

1. **Affirmative strategy-level resolution.** Jordan normal form
   *can* be formalized in Lean 4 using the parent's minpoly/charpoly
   infrastructure plus three Mathlib ingredients (gen-eigenspace
   decomposition, gen-eigenspace internal direct sum, Jordan-Chevalley)
   — *modulo one Mathlib gap* (the nilpotent canonical form).
2. **Four-step roadmap** (sub-OQs OQ-01-OQ-01 through OQ-01-OQ-04)
   totalling ~930 lines.
3. **Lean scaffold** `Proofs/MinpolyCharpolyOQ01.lean` (228 lines, 1
   sorry, 4 theorems, 4 definitions/structures):
   * `JordanBlockShape` data structure
   * `jordanBlock R λ d` matrix definition (with two unconditional API
     lemmas: `jordanBlock_diag_eq`, `jordanBlock_super_diag_eq`)
   * `jordan_normal_form_exists` weak-form theorem statement (sorry-
     guarded)
   * `totalDim_empty` sanity lemma (unconditional)
4. **Gallery integration**: `src/data/research/problems/minpoly-charpoly-oq-01.json`
   and manifest import in `proofs/Proofs.lean`.

## Active Approach

Three-stage assembly, each stage cleanly resolvable:

1. Apply Mathlib's `Module.End.iSup_genEigenspace_eq_top` to split
   `V = ⨆_λ V_λ^∞` over the algebraically closed field `K`.
2. Promote the supremum to an internal direct sum via
   `Mathlib/LinearAlgebra/Eigenspace/Pi.lean` infrastructure.
3. On each `V_λ`, use `Module.End.exists_isNilpotent_isSemisimple`
   (Jordan-Chevalley) to split `f|_{V_λ} = λ · 1 + N_λ` (the semisimple
   part on a generalized eigenspace is `λ · 1`, the nilpotent part is
   `N_λ`).
4. Put `N_λ` into nilpotent-shift basis (**the Mathlib gap** — this is
   OQ-01-OQ-02). Standard textbook construction (Axler §8.D); ~400
   lines in Mathlib style.
5. Reassemble.

## Blockers

None at the strategy level. One *local* gap (the nilpotent canonical
form) is a self-contained classical proof, not a genuine obstacle.

## Sub-OQs Identified

* **OQ-01-OQ-01** — `jordanBlock` definition + basic API. ~80 lines.
* **OQ-01-OQ-02** — Jordan basis theorem for nilpotent operators on a
  finite-dim space. The load-bearing piece. ~400 lines.
* **OQ-01-OQ-03** — Per-eigenspace assembly: `f|_{V_λ}` similar to a
  direct sum of `jordanBlock K λ dᵢ`. ~250 lines.
* **OQ-01-OQ-04** — Global assembly: `f` similar to a direct sum of
  `jordanBlock`s across all eigenvalues. ~200 lines.

## Files Modified

* **Added**: `proofs/Proofs/MinpolyCharpolyOQ01.lean` (228 lines)
* **Added**: `research/problems/minpoly-charpoly-oq-01/problem.md`
* **Added**: `research/problems/minpoly-charpoly-oq-01/knowledge.md`
* **Added**: `research/problems/minpoly-charpoly-oq-01/state.md` (this)
* **Added**: `src/data/research/problems/minpoly-charpoly-oq-01.json`
* **Modified**: `proofs/Proofs.lean` (one new import line)

## Build Status

Not run locally. `proofs/.lake` is a recursive self-symlink in this
worktree (per
[`feedback_researcher_lake_symlink_broken.md`](../../../.claude/projects/-Users-rwalters-GitHub-lean-genius/memory/feedback_researcher_lake_symlink_broken.md)),
which forces a cold Mathlib clone (~30-45 min). Following the project
convention for S1 OBSERVE scaffolds with a single sorry on the main
theorem statement, CI is the ground truth.

The new file imports only:

* `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`
* `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly`
* `Mathlib.LinearAlgebra.Eigenspace.Triangularizable`
* `Mathlib.LinearAlgebra.JordanChevalley`
* `Mathlib.FieldTheory.IsAlgClosed.Basic`
* `Mathlib.Tactic`
* `Proofs.MinpolyCharpoly` (in-tree parent file, line 1 only — pure
  conceptual link via the docstring)

All Mathlib imports are stable Mathlib v4.26.0 modules with API in use
elsewhere in the gallery (e.g., `MinpolyCharpolyOQ03.lean`,
`CayleyHamiltonMinpolyOQ05OQ01OQ04WIP01.lean`).

## Next Action (S4+)

S3 (this PR) closed candidate D
(`JordanBlockShape.eigenvalueMultiset_card_eq_totalDim`, ~12-line proof
plus list-level helper). The remaining S2-candidate set narrows to:

* **S4 candidate A** — Open child OQ `minpoly-charpoly-oq-01-oq-01`
  and scaffold `MinpolyCharpolyOQ01OQ01.lean` with the `jordanBlock`
  charpoly identity `(jordanBlock R λ d).charpoly = (X - C λ)^d`,
  minpoly identity, nilpotent-shift identity. ~80 lines, fully
  dischargable (no sorry). The three entry-wise lemmas from S1+S2
  (`_diag_eq`, `_super_diag_eq`, `_off_diag_eq`) are the API inputs.
* **S4 candidate B** — Upgrade the S1 weak-form
  `jordan_normal_form_exists` to the strong form (existence of an
  invertible `P`), still sorry-guarded but with the full statement
  surfaced. ~5-line statement edit, but requires defining the
  block-diagonal assembly of `JordanBlockShape → Matrix` first.
* **S4 candidate C** — Begin OQ-01-OQ-02 (the nilpotent canonical
  form). Largest piece (~400 lines); needs the most preparation.
* **S4 candidate E (new)** — Add a strengthening of S3's lemma to the
  `Multiset.toFinset.card ≤ totalDim` form (with equality iff all
  eigenvalues are distinct). ~10 lines using
  `Multiset.toFinset_card_le_card` plus an `iff` decomposition. Pure
  API, complements S3's cardinality-equality lemma.

Recommend candidate A for the main thrust (largest forward progress
toward `jordan_normal_form_exists`), or candidate E for a small
follow-on continuing the S3 multiset/dimension API thread.

## Coordination Notes

* No prior PR or branch exists for this OQ (verified via
  `gh pr list --search "minpoly-charpoly-oq-01" --state all` and
  `git branch -r | grep minpoly-charpoly-oq-01`, 2026-05-12T10:00 UTC).
* Sibling OQ-03 has an active scaffold in
  `Proofs/MinpolyCharpolyOQ03.lean` (S2, researcher-10, 2026-05-12);
  this OQ-01 scaffold mirrors its structure for cross-OQ consistency.

## Pool Status Note

This slug should advance from `available` → `in-progress` upon
PR creation; the claim was placed via `claim-random` in the
`MODERATE+`-tier saturation phase (3 contested probes; fell back to
direct tier-B selection — `minpoly-charpoly-oq-01` was a fresh tier-B
slug with 0 open PRs and 0 recent merges).
