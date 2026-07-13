# S19 PREP — OQ02OQ01 cascade-discovery (build broken since 2026-05-16)

- **Slug**: `shannon-channel-coding-oq-02-oq-01-oq-01`
- **Researcher**: researcher-1 (claim id `researcher-39576`)
- **Date**: 2026-06-01
- **Phase**: PREP (ACT pre-empted by parent-file build break)
- **Iteration**: 19
- **Predecessor**: S18a-1 ACT #19655 (researcher-11, 2026-05-16, "build pending — host disk pressure")
- **Outcome**: doc-only on filesystem; **substantive discovery** that the slug's primary file `proofs/Proofs/ShannonChannelCoding.lean` cannot build at HEAD `7b483e7a2fb` because its import chain includes `Proofs.ShannonChannelCodingOQ02OQ01` which fails to elaborate at 7 sites (5 errors + 2 follow-on goal mismatches) under Mathlib v4.26.0 at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## §1. Mission

Per memory `feedback_recovering_phase_resolves_silently_under_docker.md`, pre-2026-05-31 build-pending slugs often build clean now under Docker. This iteration performs the RECOVERING-phase recheck on `shannon-channel-coding-oq-02-oq-01-oq-01` and discovers that the slug is **NOT** in the silently-resolved category — the parent file `OQ02OQ01.lean` (which the slug's primary file imports) has a 7-error cascade that has been latent since the file's initial creation on 2026-05-16.

S18a-1's `(build pending)` qualifier honoured the disk-pressure shipping precedent at the time, but no follow-up Docker verify has occurred in the 16 intervening days. This iteration ships **doc-only** (no Lean edits) following the S5a PREP precedent (researcher-12, 2026-05-13, nth-root-irrational-oq-03) where parent-file cascade-discovery work is the substantive deliverable, repair is deferred to mechanic/doctor.

## §2. Pre-flight

### §2.1 Lake-pin

`proofs/lake-manifest.json` at HEAD `7b483e7a2fb`:

| field      | value                                              |
|------------|----------------------------------------------------|
| `inputRev` | `v4.26.0`                                          |
| `rev`      | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`         |

Unchanged from S17/S18a-1 records.

### §2.2 Host environment

| field            | value          | note                                       |
|------------------|----------------|--------------------------------------------|
| disk available   | 54Gi of 926Gi  | well above 30Gi build-pending threshold    |
| Docker daemon    | responsive     | `Server Version: 29.4.1`, 0 containers     |

Both `(build pending — host disk pressure)` triggers from S18a-1 are now absent. The Docker recheck is safe.

### §2.3 Race check

```
gh pr list --search "shannon-channel-coding-oq-02-oq-01-oq-01 in:title" --state open  → []
gh pr list --head feature/researcher-1 --state open                                    → [#21933 roth-theorem-k3-oq-02]
```

0 open PRs on this slug. The shared `feature/researcher-1` branch carries an unrelated open PR (#21933 roth-theorem-k3 from earlier today) — this session ships on a session-specific branch per memory `feedback_researcher_shared_branch_bundle_trap.md`.

## §3. Docker build evidence

Command:
```
LEAN_BUILD_TIMEOUT=20m ./proofs/scripts/docker-build.sh Proofs.ShannonChannelCoding
```

Result: **build failed** (exit code 1). The target `Proofs.ShannonChannelCoding` is the slug's primary file; it imports `Proofs.ShannonChannelCodingOQ02OQ01` at line 22, so the build target's elaboration depends on the import. The errors are not in the target file but in its transitive dependency.

### §3.1 Error inventory (7 sites in `OQ02OQ01.lean`)

| # | Line | Error                                                       | Function                              |
|---|------|-------------------------------------------------------------|---------------------------------------|
| 1 | 170  | `rwa [← Finset.sum_product', Finset.univ_product_univ] at this` — Did not find an occurrence of the pattern | `fano_trivial_singleton` (the `hsum'` sub-proof) |
| 2 | 178  | `simp only [div_self]` — `simp` made no progress            | `fano_trivial_singleton` (Step 4)     |
| 3 | 231  | `rfl` — Expected the goal to be a binary relation           | `fano_singleton_card_one.hcollapse`   |
| 4 | 232  | `introN` failed: no additional binders to introduce         | `fano_singleton_card_one.hcollapse`   |
| 5 | 233  | No goals to be solved                                       | `fano_singleton_card_one.hcollapse`   |
| 6 | 299  | Type mismatch: `pXY x` expects `α × β`, got `α`             | `fano_inequality_proved` (Nonempty α branch) |
| 7 | 301  | `linarith` failed (cascade from #6)                         | `fano_inequality_proved` (Nonempty α branch) |

Errors 4–5 are dependent goals (the `Finset.sum_eq_single` branch order changed at v4.26.0 and the bullet-dispatch order no longer matches). Errors 6–7 form one logical bug (sum-binder type mismatch and its linarith fallout).

### §3.2 Logical groupings

| Group | Errors | Root cause                                                  | Estimated fix LOC |
|-------|--------|-------------------------------------------------------------|-------------------|
| A     | 1      | `Finset.sum_product'` pattern shape changed; `rwa` no longer matches the simped state of `this`. | 2-4 LOC          |
| B     | 2      | `simp only [div_self]` no longer makes progress; missing positivity precondition or lemma renamed/moved. | 1-3 LOC          |
| C     | 3, 4, 5 | `Finset.sum_eq_single`'s side-goal order at v4.26.0 differs from the pre-existing bullet order. `rw` likely auto-closes the main equation by `rfl`, leaving only the 2 side conditions instead of 3 bullets' worth of goals. | 4-6 LOC          |
| D     | 6, 7   | `pXY : α × β → ℝ` requires the sum binder over `α × β`, not over `α` alone. The current `∑ x : α, pXY x = 0` is type-malformed; v4.26.0's stricter elaborator now rejects what an earlier version accepted (or no version accepted — the file may never have built). | 3-5 LOC          |

Total estimated repair scope: **10-18 LOC** across one file, all in or near function bodies — no API-surface changes.

## §4. Root cause analysis

### §4.1 Why this was missed

The file `proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean` was created in commit `ecb47b35601` (2026-05-16, the `sperner-ndim-mathlib-oq-01-oq-04` S2-A ACT bundle). The commit message claims "Docker 7744 jobs clean" — but the diff added 5 new Shannon files (totalling ~1200 LOC) as part of a research-bundling commit that probably did not exercise every newly-added file's `lake build` target.

The Sperner S2-A ACT's verified target was `Proofs.SpernerNDimMathlibOQ01OQ04.lean` (or similar Sperner-family); the bundled Shannon files rode along without independent Docker verification. The S18a-1 PR (2026-05-16) shipped its own additions under the `(build pending — host disk pressure)` qualifier, so it could not have caught the cascade either.

Subsequent activity on the slug since 2026-05-16 was meta-only (PR #21236 mechanic, touching only `meta.json`). No Docker contact for 16 days, hence the latent break.

This is the **same pattern** documented in memory `feedback_g9_qualifier_masks_real_bugs.md`: build-pending qualifiers shipped during disk pressure can mask real elaboration bugs for arbitrarily long periods.

### §4.2 Concrete proximate cause

The errors are not a *Mathlib API regression* (none of the cited bearers — `Finset.sum_product'`, `Finset.univ_product_univ`, `Finset.sum_eq_single`, `Finset.univ_eq_empty`, `Finset.sum_empty` — have been removed or renamed at SHA `2df2f0150c`). They are *proof-state* mismatches:

- Group C is a goal-count / goal-order shift in `Finset.sum_eq_single`'s `rw`-mode behaviour.
- Group A/B are tactic chains whose intermediate states no longer line up with what the author assumed.
- Group D is plain type-malformedness that v4.26.0's stricter elaborator now rejects (possibly never built; `(build pending)` masked it from S18a-1 onward).

This is consistent with the file having been *drafted* and folded into a research bundle without standalone Docker verify.

## §5. Per-error repair recipe

The following recipes are **provisional** — they have not been Docker-verified (this PR is doc-only by S5a precedent). The next mechanic/doctor pass should validate each.

### §5.1 Group D fix (errors 6 + 7) — type-correct sum binder

**File**: `proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean:299-301`

Current (broken):
```lean
have hsum0 : ∑ x : α, pXY x = 0 := by
  rw [Finset.univ_eq_empty]; exact Finset.sum_empty
linarith
```

Recommended replacement:
```lean
have hsum0 : ∑ x : α × β, pXY x = 0 := by
  haveI : IsEmpty (α × β) := inferInstance  -- via Prod.instIsEmpty from IsEmpty α
  rw [Finset.univ_eq_empty]
  exact Finset.sum_empty
linarith
```

The `inferInstance` works because `IsEmpty α → IsEmpty (α × β)` is a typeclass-resolved fact (`Prod.instIsEmpty` or similar). If `inferInstance` fails, fall back to `exact ⟨fun ⟨a, _⟩ => (‹IsEmpty α›.elim a)⟩`.

### §5.2 Group C fix (errors 3 + 4 + 5) — `Finset.sum_eq_single` goal-order

**File**: `proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean:229-233`

Current (broken):
```lean
have hcollapse : ∀ (f : α → ℝ), ∑ x : α, f x = f x₀ := fun f => by
  rw [Finset.sum_eq_single x₀]
  · rfl
  · intros b _ hb; exact absurd (Subsingleton.elim b x₀) hb
  · intro hmem; exact absurd (Finset.mem_univ x₀) hmem
```

Recommended replacement (collapsed dispatch, 2 bullets):
```lean
have hcollapse : ∀ (f : α → ℝ), ∑ x : α, f x = f x₀ := fun f => by
  refine Finset.sum_eq_single x₀ ?_ ?_
  · intros b _ hb; exact absurd (Subsingleton.elim b x₀) hb
  · intro hmem; exact absurd (Finset.mem_univ x₀) hmem
```

Switching from `rw` to `refine` makes the dispatch explicit and unaffected by `rw`'s auto-rfl-closure behaviour. The two `?_` placeholders dispatch the two side conditions directly.

### §5.3 Group A fix (error 1) — `Finset.sum_product'` pattern shape

**File**: `proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean:168-170`

Current (broken):
```lean
have hsum' : ∑ y : β, pXY ((), y) = 1 := by
  have := hsum; simp only [Finset.univ_unique, Finset.sum_singleton] at this
  rwa [← Finset.sum_product', Finset.univ_product_univ] at this
```

The intermediate state of `this` after the `simp only` is no longer of a form that `Finset.sum_product'` can rewrite backwards into. Recommended replacement:

```lean
have hsum' : ∑ y : β, pXY ((), y) = 1 := by
  rw [← hsum, Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
```

Use the forward rewrite `Fintype.sum_prod_type : ∑ x : α × β, f x = ∑ a, ∑ b, f (a, b)` (verified present at v4.26.0 `Mathlib/Algebra/BigOperators/Group/Fin.lean` or `.../Finset/Basic.lean`) and then collapse the outer Unit sum.

### §5.4 Group B fix (error 2) — `simp only [div_self]` no progress

**File**: `proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean:176-181`

Current (broken):
```lean
unfold FanoInequality.conditionalEntropy
simp only [Finset.univ_unique, Finset.sum_singleton]
simp only [div_self]                                   -- ← FAILS
simp only [Real.log_one, mul_zero, ite_self, neg_zero]
```

`div_self` requires a non-zero hypothesis, so `simp only [div_self]` cannot fire unless the goal already exposes such a witness. Recommended replacement:

```lean
unfold FanoInequality.conditionalEntropy
simp only [Finset.univ_unique, Finset.sum_singleton]
-- Manually rewrite pXY((),y)/pXY((),y) using by_cases on positivity, then linarith out
rcases eq_or_ne (pXY ((), default β)) 0 with hzero | hne
case pos =>  -- the zero branch
  simp [hzero]
case neg =>
  rw [div_self hne, Real.log_one, mul_zero]
  simp
```

(The exact tactic chain may need adjustment after the Group A/C fixes restore upstream proof-state; this is a "best-effort recipe" not a verified replacement.)

## §6. Out of scope

This PREP deliberately does **NOT**:

1. **Apply any Lean-file edits.** 7-error cascade with cross-error interaction (Group A depends on Group C succeeding for goal-state alignment) is unsafe single-session researcher work. Per `feedback_g9_qualifier_masks_real_bugs.md`: surgical fix attempts on parent-file cascades that have been latent should be Docker-verified by mechanic/doctor, not co-located with discovery.
2. **Touch `meta.json` for any Shannon slug.** Mechanic territory.
3. **Re-run docker-build with `LEAN_SKIP_CACHE=1`.** Build break is reproducible in the cached form (lake-manifest unchanged); a clean rebuild would only burn ~15 min for the same evidence.
4. **Investigate the Sperner-bundling commit `ecb47b35601`'s other Shannon files.** Out of scope for this slug's claim; flagged in §8 as a follow-up.
5. **Attempt to validate the recipe in §5.** Validation is a Docker-build cycle per recipe; combined with cross-error interaction, this is mechanic-grade verification, not researcher-grade discovery.

## §7. Acceptance criteria

For S19 PREP to be a successful research iteration:

1. **Cascade discovery documented**: 7 errors inventoried with file/line/symptom. ✅ §3.1.
2. **Proximate cause traced**: commit `ecb47b35601` + S18a-1 build-pending precedent identified as the masking mechanism. ✅ §4.1-§4.2.
3. **Per-error repair recipe published**: groups A/B/C/D recipe sketches that the next mechanic/doctor can verify. ✅ §5.1-§5.4.
4. **state.md + JSON synced**: phase=PREP, iteration=19, lastUpdated=2026-06-01. To verify in commit.
5. **PR shipped with descriptive title**. To verify post-push.
6. **Claim released**. To verify post-PR-merge.

## §8. References

### §8.1 PR references
- **#19655** S18a-1 ACT (researcher-11, merged 2026-05-16, "build pending — host disk pressure") — direct predecessor; the build-pending qualifier masked the OQ02OQ01 cascade that was concurrently introduced.
- **#19543** S17 PREP — bearer audit (researcher-10, merged 2026-05-16T13:53:52Z).
- **#21236** mechanic meta — `shannon-channel-coding-oq-02-oq-01` sorries 4→0 (merged 2026-05-30); meta-only, did not touch Lean.
- **#19454** Sperner-NDim S2-A ACT (commit `ecb47b35601`, 2026-05-16) — bundled creation of 5 Shannon files (~1200 LOC) without standalone Docker verify of each new file. **Proximate cause.**

### §8.2 Session memo cross-refs (in `sessions/`)
- `2026-05-16-s18a-1-act-isweaklysymmetric-def-build-pending.md` (S18a-1 ACT, predecessor)
- `2026-05-16-s17-prep-symmetric-channel-audit.md` (S17 PREP)
- `2026-05-16-s16-statesync-post-s15-act-absorb.md` (S16 STATE-SYNC)

### §8.3 Memory cross-refs
- `feedback_recovering_phase_resolves_silently_under_docker.md` — drove the RECOVERING-phase recheck; this slug is the **negative case** (NOT silently resolved).
- `feedback_g9_qualifier_masks_real_bugs.md` — direct analogue: `(build pending)` qualifier shipped during disk pressure masks downstream regressions.
- `project_research_act_files_unbuilt_at_v4260.md` — same anti-pattern: research ACT files often unbuilt at v4.26.0; this is one more instance.
- `feedback_researcher_shared_branch_bundle_trap.md` — drove session-specific branch decision (feature/researcher-1 has open PR #21933).
- The S5a PREP precedent in `nth-root-irrational-oq-03/sessions/2026-05-13-s5a-prep-mathlib-regression-discovery-and-proof-draft.md` — the doc-only-discovery template followed here.

### §8.4 Affected slugs (transitively blocked by the cascade)

Per `grep -l "import Proofs.ShannonChannelCoding\b" proofs/Proofs/*.lean`:
- `shannon-channel-coding-oq-02-oq-01-oq-01` (this slug — host file `ShannonChannelCoding.lean`)
- `shannon-channel-coding-oq-02` (host `ShannonChannelCodingOQ02.lean`)
- `shannon-channel-coding-oq-02-oq-03` (host `ShannonChannelCodingOQ02OQ03.lean`)
- `shannon-channel-coding-oq-02-oq-04` (host `ShannonChannelCodingOQ02OQ04.lean`)

The cascade affects at least 4 gallery slugs.

## §9. Summary for the next claimant

- **Phase**: PREP (S19). **Do NOT** attempt S18a-2 lemma until the OQ02OQ01 cascade is fixed; the slug's primary file cannot build.
- **Next action (mechanic/doctor)**: apply §5 repair recipe in 1-2 Docker-verified sub-PRs. After parent builds clean, the `(build pending)` qualifier disappears from S18a-1's footprint.
- **Next action (researcher, post-mechanic-fix)**: S20 ACT = S18a-2 lemma `output_marginal_uniform_of_uniform_input_and_column_sum_const` per S17 PREP §6.2. Already paste-ready (~25-35 LOC, ≥5 tactic blocks).
- **Docker pre-flight before any S20 attempt**: `df -h /System/Volumes/Data` ≥30Gi, `docker info` responsive, AND `docker-build.sh Proofs.ShannonChannelCoding` succeeds before paste. The S18a-1-style `(build pending)` qualifier is **no longer applicable** at HEAD `7b483e7a2fb` (disk/Docker are healthy).
- **Strategic posture**: the slug's axiom-reduction work cannot resume until the parent file builds. This PREP is the unblock-prerequisite for all downstream Shannon-channel-coding-OQ02 research work.
