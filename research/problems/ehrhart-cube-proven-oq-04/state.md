# Current State

**Phase**: VERIFIED (S9 ACT mechanic fix PR #19101 merged 2026-05-15T22:59:15Z; Docker build clean, 7743 jobs; S12 STATE-SYNC absorbed state.md + meta.json; S13 STATE-SYNC absorbed research-JSON drift; S14 STATE-SYNC absorbs candidate-pool drift)
**Since**: 2026-05-15T22:59:15Z (S9 ACT mechanic fix merge — first clean Docker baseline)
**Iteration**: 14
**Researcher**: researcher-1 (S14 STATE-SYNC — candidate-pool catchup)

## Current Focus

S14 STATE-SYNC (this PR — researcher-1 2026-05-30):
Doc-only catchup PR closing the candidate-pool drift left by S13.
The `.lean/state/candidate-pool.json` entry for
`ehrhart-cube-proven-oq-04` still showed `status: "available"` /
`notes: "AVAILABLE"` two weeks after the slug verified at S9 ACT
(PR #19101, 2026-05-15) — because the pool is auto-generated from
`research/db/knowledge.db` (gitignored) and the DB regeneration had
not absorbed the verified status. S13 STATE-SYNC (researcher-12)
closed the tracked `src/data/research/problems/ehrhart-cube-proven-oq-04.json`
drift but deliberately left the gitignored pool untouched.

S14 closes the pool drift by invoking
`./scripts/research/claim-problem.sh update ehrhart-cube-proven-oq-04 completed`,
which sets `.candidates[].status = "completed"` in the local pool
file and drops a completion signal under `.loom/signals/completions/`.
Both side effects are gitignored / outside the tracked tree; the
**tracked** S14 deliverables in this PR are three doc-only edits:

- `research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-30-s14-state-sync-pool-catchup.md` (new)
- `research/problems/ehrhart-cube-proven-oq-04/state.md` (this head + Current Focus rewrite)
- `src/data/research/problems/ehrhart-cube-proven-oq-04.json` (7 field updates: phase unchanged; iteration 13→14; focus + nextAction rewrite; attemptCounts.total 13→14; lastUpdate 2026-05-15→2026-05-30)

Underlying Lean source unchanged. Docker build at Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) remains clean,
7743 jobs, ~10s warm-cache (verified by PR #19101 commit
`be08fef58bb`); 0 sorries, 0 axioms, 0 structure-encoded assumptions.

Re-verified at S14 write time (worktree, base `8ae064a390d`):
- `wc -l proofs/Proofs/EhrhartCubeProvenOQ04.lean` → **775**
- `grep -c "^axiom " …` → **0**
- `grep -c "^[[:space:]]*sorry" …` → **0** (2 `sorry` matches are in comments at L15 and L66)
- `grep -cE "^theorem |^lemma " …` → **30**

All four metrics match research-JSON (`lineCount: 775`, `axiomCount: 0`,
`sorryCount: 0`, `theoremCount: 30`) and meta.json (`status: verified`,
`badge: verified`, `lineCount: 775`, `theoremCount: 30`). Build inheritance
from origin/main is unconditional.

See `sessions/2026-05-30-s14-state-sync-pool-catchup.md` for the
per-field drift table, audit walkthrough, and conflict-free
guarantee. This PR is doc-only: touches exactly three tracked files.
No Lean source edits, no `meta.json` edits, no sibling-session
edits, no parent-file edits.

## Prior STATE-SYNC: S13 (research-JSON catchup PR, 2026-05-15)

S13 STATE-SYNC (researcher-12 2026-05-15):
Doc-only catchup PR closing the 12-item drift in
`src/data/research/problems/ehrhart-cube-proven-oq-04.json` left by
S12 STATE-SYNC PR #19334. The S12 STATE-SYNC was scoped to
`state.md` + `meta.json` + new session memo only (per its §10
"Conflict-free guarantees" manifest); the research-JSON file was
deliberately excluded and remained at its S7 (2026-05-13) snapshot
showing `phase: SCAFFOLDED`, `currentState.phase: PROVED`,
`iteration: 7`, `lastUpdate: 2026-05-13T23:00:00Z`,
`leanFiles[1].lineCount: 772`, and S4/S5/S6-stale `nextSteps`.

S13 STATE-SYNC corrects this drift in one doc-only PR:
- top-level `phase`: SCAFFOLDED → VERIFIED
- `currentState.phase`: PROVED → VERIFIED
- `currentState.since`: 2026-05-13 → 2026-05-15T22:59:15Z
- `currentState.iteration`: 7 → 13
- `currentState.focus`: rewritten to S13 narrative
- `currentState.nextAction`: rewritten to S14/S15 plan
- `currentState.attemptCounts.total`: 7 → 13
- `currentState.attemptCounts.approachesTried`: 0 → 2 (S8 inventory + S9 ACT mechanic fix)
- `knowledge.progressSummary`: S7 (build pending) → S12 (BUILD-VERIFIED, Mathlib v4.26.0)
- `knowledge.builtItems`: +7 entries (S8 BUILD-VERIFY, S9 PREP, S10 PREP, S11 PREP, S9 ACT, S12 STATE-SYNC, S13 STATE-SYNC)
- `knowledge.insights`: +3 entries (latent-defect interpretation, zero-drift cascade pedagogy, v4.26.0 no-op rewrite trap)
- `knowledge.nextSteps`: S5/S5/S6/S7+ stale items → S14/S15/S16/S17 forward plan
- `lastUpdate`: 2026-05-13T23:00:00Z → 2026-05-15T23:30:00Z
- `leanFiles[1].lineCount`: 772 → 775 (matches `wc -l proofs/Proofs/EhrhartCubeProvenOQ04.lean`)

Underlying Lean source unchanged. Docker build at Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) remains clean,
7743 jobs, ~10s warm-cache (verified by PR #19101 commit
`be08fef58bb`); 0 sorries, 0 axioms, 0 structure-encoded assumptions.

See `sessions/2026-05-15-s13-state-sync-research-json-catchup.md`
for the per-field drift table, audit walkthrough, and conflict-free
guarantee. This PR is doc-only: touches exactly the research-JSON
file + this state.md head + a new session memo. No Lean source
edits, no meta.json edits, no sibling-session edits.

## Prior STATE-SYNC: S12 (PR #19334)

S12 STATE-SYNC consumed the merged 5-PR cascade that resolved the
S8 7-error inventory:

| # | PR | Title | Merged |
|---|---|---|---|
| 1 | #19078 | S8 BUILD-VERIFY — 7-error inventory (doc-only) | 2026-05-15T23:26:37Z |
| 2 | #19220 | S9 PREP — mechanic kit (doc-only) | 2026-05-15T18:05:33Z |
| 3 | #19298 | S10 PREP — audit of S9 kit (doc-only) | 2026-05-15T18:00:47Z |
| 4 | #19303 | S11 PREP — ACT-readiness gate (doc-only) | 2026-05-15T19:00:33Z |
| 5 | #19101 | S9 ACT — mechanic 7-error parent repair (16 ins / 13 dels) | 2026-05-15T22:59:15Z |

Net result: `proofs/Proofs/EhrhartCubeProvenOQ04.lean` builds clean
at Mathlib v4.26.0 (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`),
7743 jobs in ~10s warm-cache. **0 sorries, 0 axioms, 0
structure-encoded assumptions** — meets CLAUDE.md `status: verified`
definition. The cascade's zero-drift property held: the S10 PREP
Option-variant recommendations `1A / 2B / 3A / 4A / 5A / 6 / 7`
landed verbatim through S11 PREP into PR #19101's per-site edits.

See `sessions/2026-05-15-s12-state-sync-build-verified.md` for the
full cascade timeline, drift-recheck table, and orthogonality
manifest. This PR is **doc-only**: updates state.md, meta.json, and
ships a new session note. No Lean source edits.

## Blockers (S8 BUILD-VERIFY INVENTORY — 7 errors)

Docker build command (from worktree CWD):
```
./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ04
```

Toolchain: `leanprover/lean4:v4.26.0`; Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. All 7 errors fired
during a single Lean process (Mathlib cache hit, no parent-file errors).

### Error 1 — `eulerian_zero_eq_one` termination (line 133:8)

```
fail to show termination for
  eulerian_zero_eq_one
with errors
failed to infer structural recursion
```

Definition site:

```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1
  | 0     => rfl
  | _ + 1 => eulerian_zero_eq_one _
```

v4.26.0 equation compiler is stricter on structural recursion through
the underlying `eulerianNumber` recursion. The `_+1` case recursive
call `eulerian_zero_eq_one _` doesn't reduce the argument under
`sizeOf`-WF (`eulerian_zero_eq_one (n+1) = eulerian_zero_eq_one n` is
syntactic but the compiler treats `n+1` and `_` as opaque after
match-binding).

**Surgical fix candidate** (~3-4 LOC):

```lean
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1 := by
  intro d
  induction d with
  | zero => rfl
  | succ n ih => exact ih
```

The induction tactic exposes the recursive call as `ih : eulerianNumber n 0 = 1`,
and `eulerianNumber (n+1) 0` reduces to `eulerianNumber n 0` by the
def's third arm, so `exact ih` closes by defeq.

### Error 2 — `eulerian_row_sum_factorial` `+ 0` gap (line 198:76)

After `rhs_extend` proves the sum-extension via
`Finset.sum_range_succ` + `eulerian_eq_zero_of_le`, an unsolved goal:

```
∑ k ∈ range d, (d + 1) * eulerianNumber d k = ∑ x ∈ range d, (d + 1) * eulerianNumber d x + 0
```

The `Nat.add_zero` in the `rw` chain at lines 199-202 fires but the
elaborator leaves a residual `+ 0` because `Finset.sum_range_succ`
peels off the last term (which is `0` after `eulerian_eq_zero_of_le`,
`Nat.mul_zero`, `Nat.add_zero`) — but a residual `+ 0` remains.

**Surgical fix candidate** (~1 LOC):

Append `; rfl` or `; ring` after the existing `rw` chain at line 202,
or replace `Nat.add_zero` with `Nat.add_zero, Eq.refl _`.

### Error 3 — `eulerian_palindrome` Unknown identifier `d` (line 368:27)

```lean
· -- k = d: A(d+1, d) = A(d+1, d - d) = A(d+1, 0)
  have hkd : k = d := by omega
  subst hkd
  -- After subst, the goal is A(d+1, d) = A(d+1, d - d)
  rw [Nat.sub_self d, hboundary, eulerian_zero_eq_one (d + 1)]
```

`subst hkd` substitutes the variable that was *introduced last*. With
`hkd : k = d`, `subst` eliminates `k` (the more recent variable) by
replacing it with `d` — so the identifier `k` is gone, but `d` should
remain. The error says `Unknown identifier d` — this means `subst`
eliminated `d` instead (i.e., direction was reversed).

**Surgical fix candidate** (~1 LOC):

Use `subst hkd.symm` to force the direction, or `obtain ⟨rfl⟩ := hkd`
which is unambiguous, or rephrase `hkd : d = k` with `omega` and then
`subst hkd`.

### Error 4 — `worpitzky_step` unsolved arithmetic (line 411:83)

```
⊢ k * m.choose (d + 1) + 1 * m.choose (d + 1) + (d - k) * m.choose (d + 1) + (d - k) * m.choose d =
  …
```

The calc step at line 411-412 applies `Nat.add_mul`:

```lean
_ = ((k + 1) + (d - k)) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
    rw [Nat.add_mul]
```

`Nat.add_mul : (a + b) * c = a*c + b*c` should reverse to combine
`(k+1) * c + (d-k) * c` into `((k+1) + (d-k)) * c`, but the goal
arrives with `k * c + 1 * c + (d-k) * c` (i.e., already distributed
`(k+1) * c = k*c + 1*c` by some earlier `simp`/`ring` normalization).
Pattern doesn't match because the LHS has THREE summands, not two.

**Surgical fix candidate** (~2 LOC):

Replace `rw [Nat.add_mul]` with `ring` (the goal is a pure semiring
equality after constant rearrangement). The previous proof worked when
Lean's normalization left `(k+1) * c` un-distributed; v4.26.0 may now
auto-distribute through `Nat.mul`-style normal form.

### Error 5 — `worpitzky_identity_cube` inductive step rewrite fail (line 478:20)

```
Tactic `rewrite` failed: Did not find an occurrence of the pattern
in the target expression
  eulerianNumber d k * (n + 1 + k).choose d * (n + 1) =
    eulerianNumber d k * ((k + 1) * (n + 1 + k).choose (d + 1) + (d - k) * (n + 2 + k).choose (d + 1))
```

The calc step at line 476-478 tries:

```lean
refine Finset.sum_congr rfl fun k hk => ?_
have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
rw [← worpitzky_step n d k hkd]; ring
```

`worpitzky_step n d k hkd : (k+1) * C(n+1+k, d+1) + (d-k) * C(n+2+k, d+1) = (n+1) * C(n+1+k, d)`.
Backward rewrite (`←`) requires matching `(n+1) * C(n+1+k, d)` on the
LHS, but the LHS is `eulerianNumber d k * (n+1+k).choose d * (n+1)`
— ordering doesn't match (factor `(n+1)` is on the RIGHT, not LEFT,
of the choose). v4.26.0 elaborator may have tightened pattern matching.

**Surgical fix candidate** (~1-2 LOC):

Pre-rewrite the LHS to put `(n+1)` on the left:
```lean
rw [show eulerianNumber d k * (n+1+k).choose d * (n+1)
      = eulerianNumber d k * ((n+1) * (n+1+k).choose d) from by ring,
    ← worpitzky_step n d k hkd]; ring
```

Or use `linear_combination worpitzky_step n d k hkd` to bypass the
explicit rewrite.

### Error 6 — `worpitzky_d2` redundant `pow_two` rewrite (line 584:17)

```
Tactic `rewrite` failed: Did not find an occurrence of the pattern in the current goal
case succ
e0 : eulerianNumber 2 0 = 1
e1 : eulerianNumber 2 1 = 1
m : ℕ
ih : (m + 1) * (m + 1) = (m + 1).choose 2 + (m + 2).choose 2
⊢ (m + 1 + 1) * (m + 1 + 1) = (m + 1 + 1).choose 2 + (m + 1 + 2).choose 2
```

`rw [pow_two, pow_two] at *` is the offender — the rewrite is applied
TWICE but only ONE `^2` exists per goal/hyp. After the first rewrite
all `_^2` become `_ * _`, and the second `pow_two` finds no pattern.

**Surgical fix candidate** (~1 LOC):

Replace `rw [pow_two, pow_two] at *` with `rw [pow_two] at *` (one
rewrite suffices). Note pre-v4.26.0 may have accepted no-op rewrites;
v4.26.0 errors on them.

### Error 7 — `cube_h_star_eulerian` `sum_ite_eq` direction (line 656:6)

```
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∑ x ∈ range d, if x = k then eulerianNumber d x else 0
in the target expression
  (∑ x ∈ range d, if k = x then eulerianNumber d x else 0) = eulerianNumber d k
```

`Finset.sum_ite_eq'` expects `if x = k then ... else 0` (`x` on the
LEFT). The goal has `if k = x then ... else 0` (`k` on the left,
flipped equality direction).

**Surgical fix candidate** (~1 LOC):

Two options:
1. Use the non-prime version: `Finset.sum_ite_eq (Finset.range d) k (fun j => eulerianNumber d j)` which expects `if k = x` form. Mathlib has both `sum_ite_eq` (`if k = x`) and `sum_ite_eq'` (`if x = k`).
2. Pre-rewrite with `simp only [eq_comm (a := k)]` to swap the equality direction, then keep `sum_ite_eq'`.

### Cumulative repair budget

7 surgical sites, ~10-15 LOC total edit. Pure surface fixes — no
mathematical content change. All errors are localized and independent
(no inter-error coupling). Mechanic should be able to land all seven
in one Docker iteration after triaging each independently.

## What's Built (cumulative S1–S7, BUILD-VERIFIED via PR #19101)

> Post-verification: all seven `[Error N]` markers below are
> retrospectively retired by the merged S9 ACT mechanic fix; the
> per-error inventory in §"Blockers" remains canonical surgical-fix
> reference for future toolchain regressions.

### Definitions (axiom-free, computable)
- `eulerianNumber : ℕ → ℕ → ℕ` — recurrence A(d+1, k+1) = (k+2) A(d, k+1) + (d-k) A(d, k).
- `cubeHStarPoly : ℕ → Polynomial ℕ` — Eulerian generating polynomial `∑ A(d, k) X^k`.

### Concrete value lemmas (all `rfl`)
- A(0..4, *) — 13 entries plus row-sum and palindrome sanity checks.

### Structural helpers (S3)
- `eulerian_zero_eq_one : ∀ d, A(d, 0) = 1`. [verified; PR #19101 Error 1 fix]
- `eulerian_eq_zero_of_le : ∀ d k, 0 < d → d ≤ k → A(d, k) = 0`.

### Recurrence helper (S5)
- `eulerianNumber_recurrence (d k : ℕ) :
    A(d+1, k+1) = (k+2)·A(d, k+1) + (d-k)·A(d, k)` — definitional `rfl`.

### Row-sum theorem (S3)
- `eulerian_row_sum_factorial : ∀ d, 0 < d → ∑ k ∈ range d, A(d, k) = d!`. [verified; PR #19101 Error 2 fix]

### Worpitzky step (S4)
- `worpitzky_step (n d k : ℕ) (hk : k ≤ d) :
    (k+1) * C(n+1+k, d+1) + (d-k) * C(n+2+k, d+1) = (n+1) * C(n+1+k, d)`. [verified; PR #19101 Error 4 fix]

### Worpitzky's identity (S4, main theorem)
- `worpitzky_identity_cube (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (n + 1)^d = ∑ k ∈ Finset.range d, A(d, k) * C(n + 1 + k, d)`. [verified; PR #19101 Error 5 fix]

### Palindromic symmetry (S5)
- `eulerian_palindrome (d k : ℕ) (hd : 0 < d) (hk : k < d) :
    A(d, k) = A(d, d - 1 - k)`. [verified; PR #19101 Error 3 fix]

### Coefficient extraction (S2)
- `cube_h_star_eulerian : ∀ d k, 0 < d → k < d → (cubeHStarPoly d).coeff k = A(d, k)`. [verified; PR #19101 Error 7 fix]
- `cube_lattice_count_eulerian : ∀ d n, 0 < d →
    |Fin d → Fin (n+1)| = ∑ A(d, k) C(n+1+k, d)`.

### Palindrome-reflected Worpitzky form (S6)
- `worpitzky_identity_cube_palindrome : ∀ d n, 0 < d →
    (n+1)^d = ∑ A(d, k) C(n+d-k, d)`.

### Polynomial-evaluation corollaries (S7)
- `cubeHStarPoly_eval_one : ∀ d, 0 < d → (cubeHStarPoly d).eval 1 = d.factorial`.
- `cubeHStarPoly_palindromic : ∀ d k, 0 < d → k < d →
    (cubeHStarPoly d).coeff k = (cubeHStarPoly d).coeff (d - 1 - k)`.

### Concrete cases (S4)
- `worpitzky_d2 (n : ℕ) : (n+1)^2 = C(n+1, 2) + C(n+2, 2)`. [verified; PR #19101 Error 6 fix]

## Next Action

**S14 (OPTIONAL — Mathlib upstream contribution)**:
The slug is now `verified`/`proved` from the gallery's perspective.
The Worpitzky identity (`worpitzky_identity_cube`) and the Eulerian
recurrence (`eulerianNumber`) are textbook combinatorial content
not currently in Mathlib (`Mathlib.Combinatorics.Enumerative.*`).
Upstreaming candidates: `Nat.eulerianNumber` (def + recurrence),
`Nat.eulerian_row_sum_factorial` (row-sum), and
`Nat.worpitzky_identity_cube` (main theorem). See S12 STATE-SYNC
session note (`sessions/2026-05-15-s12-state-sync-build-verified.md`)
§7 for the full contribution map.

S14 is **not required** for slug completion. If no S14 work is
undertaken, the slug terminates here with 30 theorems + 2 defs,
0 sorries, 0 axioms, Docker-verified at Mathlib v4.26.0.

**S15 (REGRESSION CHECK — prospective)**:
On any future Mathlib toolchain bump (v4.27.0 and beyond), re-run
`./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ04`
as a regression baseline before any new S## research lands. The
7-error v4.26.0 surface is canonical — should it recur, the S8
inventory in §"Blockers" below remains the surgical-fix reference.

**S16 (OPTIONAL — Polynomial-degree corollary)**:
Prove `cubeHStarPoly_natDegree (d : ℕ) (hd : 0 < d) :
(cubeHStarPoly d).natDegree = d - 1` via
`Polynomial.natDegree_eq_of_coeff_ne_zero_of_le` + the
leading-coefficient computation A(d, d-1) = A(d, 0) = 1 (from
`eulerian_zero_eq_one` + `eulerian_palindrome`). ~25-40 LOC; would
complete the three classical h*-vector invariants for the cube
(palindromic, sums to d!, degree d-1).

**S17 (HERMIT cross-gallery scan — optional)**:
The Mathlib v4.26.0 stricter no-op rewrite pattern (Error 6:
`rw [pow_two, pow_two] at *` where only one `^2` exists per goal)
may have latent failures across the gallery. Out of scope for this
slug; flagged for Hermit cross-gallery scan.

## Attempt Counts

- Total iterations: 13 (S1 SCAFFOLD, S2 STRUCTURAL, S3 ROW-SUM, S4 WORPITZKY, S5 PALINDROME, S6 PALINDROME-COROLLARY, S7 POLY-COROLLARIES, S8 BUILD-VERIFY, S9 PREP, S10 PREP, S11 PREP, S12 STATE-SYNC, S13 STATE-SYNC)
- S9 ACT (mechanic-scope, sibling PR #19101): 1 iteration (clean on first Docker build)
- Approaches tried: 2 (S8 docker baseline → 7-error inventory; S9 ACT mechanic surgical 7-site repair → clean build)

## Open Questions / Risks (post-verify, retrospective)

1. **All seven errors were surface-fixable** — confirmed by PR #19101's
   single-iteration clean Docker build (7743 jobs, ~10s). The
   "hidden eighth error" risk did not materialize. The pre-fix
   inventory's confidence rating ("≥ 0.6 conf for medium-confidence
   sites 2/4/5") was upheld by S11 PREP's goal-state walks
   upgrading those to ≥ 0.95 conf.

2. **Pre-v4.26.0 build status confirmed unknown / likely never-built**
   — the S1-S7 PRs (2026-05-12 to 2026-05-13) all shipped under
   "(build pending)" convention with the toolchain bump landing
   between then and S8 BUILD-VERIFY (2026-05-14). PR #19101's clean
   build at v4.26.0 retroactively confirms the seven errors were
   latent defects, not regressions — they would have surfaced on the
   first Docker build regardless of toolchain version, since the
   v4.26.0-specific changes (Error 4 `Nat.add_mul` distribution,
   Error 6 `pow_two` no-op) interact with proof-construction choices
   the original PRs made.

3. **Mathlib v4.26.0 stricter no-op rewrites pattern** — Error 6
   (`rw [pow_two, pow_two] at *`) is a Hermit-scope concern: same
   lemma repeated in `rw [_, _]` chains is now a silent failure
   across the gallery. Out of scope for this slug; flagged for a
   Hermit cross-gallery scan.

4. **`theoremCount` / `lineCount` audit drift** — meta.json's
   `theoremCount: 27` (now 30) and `lineCount: 677` (now 775)
   pre-date the S6/S7 corollaries and post-S1 LOC growth. The prior
   `fix(meta) #17850/#17868/#17878` audit chain (2026-05-12)
   didn't catch the drift because it used merged pre-build counts.
   S12 STATE-SYNC corrects this; future `fix(meta)` PRs should hit
   `wc -l` parity against the source.
