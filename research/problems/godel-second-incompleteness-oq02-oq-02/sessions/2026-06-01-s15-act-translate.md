# S15 ACT — translate function (GL → PA realization) — Docker 3062 jobs clean

- **Slug**: `godel-second-incompleteness-oq02-oq-02`
- **Researcher**: researcher-1 (claim id `researcher-70456`)
- **Date**: 2026-06-01
- **Phase**: ACT
- **Iteration**: 15 (advances S14 priority #1)
- **Predecessor**: S14 STATE-SYNC #20656 (researcher-1, merged 2026-05-25)
- **Outcome**: substantive — new companion file `GodelSecondIncompletenessOQ02Translate.lean` defines the realization function `translate : (PropAtom → Formula) → GLFormula → Formula` per S10 PREP #18678 §3.3, with 4 recursive cases + 5 `rfl`-discharged simp-equation theorems. **0 new axioms.** Docker-verified at HEAD: 3062 jobs, target built in 9.0s.

## §1. Mission

S14 STATE-SYNC §3 elevated "S10 translate ACT" to priority #1 on axiom-integrity grounds (0 new axioms vs S4 Löb ACT's +1). This iteration discharges that priority. The translate function is the **realization-function bridge** from GL syntax (`GLFormula`, S8 ACT #19146) to PA syntax (`GodelFirst.Formula`, parent + S2-α Companion #19037), parametrized by a propositional atom assignment `ρ : PropAtom → Formula`.

Per S10 PREP #18678 §3.3, this unblocks S7 ACT (arithmetical soundness of GL: the five-case induction `GL_proves φ → ∀ ρ, ⊢ translate ρ φ`).

## §2. Pre-flight

### §2.1 Lake-pin

`proofs/lake-manifest.json` at HEAD pins Mathlib `v4.26.0` → SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged from S14, 7 days ago).

### §2.2 Host environment

| field            | value          | note                                       |
|------------------|----------------|--------------------------------------------|
| disk available   | 54Gi of 926Gi  | well above 30Gi build threshold            |
| Docker daemon    | responsive     | `Server Version: 29.4.1`                   |

### §2.3 Race check

```
gh pr list --search "godel-second-incompleteness-oq02-oq-02 in:title" --state open  → []
gh pr list --search "GodelSecondIncompletenessOQ02Translate"           --state all  → []
```

0 open PRs on slug. 0 PRs on the target file name.

## §3. Design (paste-verbatim from S10 PREP #18678 §3.3)

### §3.1 Type signature

```lean
def translate (ρ : PropAtom → Formula) : GLFormula → Formula
```

`PropAtom := Nat` (from `GodelSecondGLSyntax.lean:46`), giving countably-many atoms suitable for Solovay's completeness construction (Boolos 1993, §3).

### §3.2 Four recursive cases

| GL constructor   | translate clause                                              | Discharged by   |
|------------------|---------------------------------------------------------------|-----------------|
| `.atom n`        | `ρ n`                                                         | base case (rfl) |
| `.falsum`        | `GodelSecond.falsum`                                          | base case (rfl) |
| `.impl φ ψ`      | `impl_formula (translate ρ φ) (translate ρ ψ)`                | S2-α Companion `impl_formula`, line 108 |
| `.box φ`         | `Prov (godelNum (translate ρ φ))`                             | First Provability D1, parent `:123` |

### §3.3 Simp-equation lemmas

Each of the 4 cases is exposed as a `@[simp] theorem translate_*` for downstream rewriting:

```lean
@[simp] theorem translate_atom   (ρ) (n : PropAtom) : translate ρ (.atom n) = ρ n := rfl
@[simp] theorem translate_falsum (ρ)                : translate ρ .falsum = GodelSecond.falsum := rfl
@[simp] theorem translate_impl   (ρ) (φ ψ)          : translate ρ (.impl φ ψ) = impl_formula (translate ρ φ) (translate ρ ψ) := rfl
@[simp] theorem translate_box    (ρ) (φ)            : translate ρ (.box φ) = Prov (godelNum (translate ρ φ)) := rfl
```

All discharged by `rfl` because the def is implemented by pattern-match.

### §3.4 Derived sanity theorem

```lean
@[simp] theorem translate_not (ρ) (φ : GLFormula) :
    translate ρ φ.not = impl_formula (translate ρ φ) GodelSecond.falsum := rfl
```

Sanity check that the simp normal form composes through `GLFormula.not = .impl _ .falsum` (defined at `GodelSecondGLSyntax.lean:63`). Also `rfl`.

## §4. Build

### §4.1 Command

```
LEAN_BUILD_TIMEOUT=20m ./proofs/scripts/docker-build.sh Proofs.GodelSecondIncompletenessOQ02Translate
```

### §4.2 Result

**Build completed successfully (3062 jobs).** Target `Proofs.GodelSecondIncompletenessOQ02Translate` built in 9.0s. Mathlib cache replay: 7727 files in ~150s + 21s unpack. Total wall-clock ~3 minutes (cache-dominated).

### §4.3 Pre-existing linter warnings (NOT introduced by S15)

```
warning: Proofs/GodelFirstIncompletenessOQ01.lean:193:24: unused variable `h`
warning: Proofs/GodelFirstIncompletenessOQ01.lean:260:35: unused variable `h`
```

These are in the First-Incompleteness file (transitive dependency), not in any S15-touched file. Out of S15 scope; flagged as a follow-up mechanic cleanup.

## §5. Axiom budget delta

| File | Before S15 | After S15 | Change |
|------|------------|-----------|--------|
| `GodelFirstIncompletenessOQ01.lean` | 5 | 5 | 0 |
| `GodelSecondIncompletenessOQ02.lean` | 1 | 1 | 0 |
| `GodelSecondIncompletenessOQ02Companion.lean` | 3 | 3 | 0 |
| `GodelSecondIncompletenessOQ02GLSyntax.lean` | 0 | 0 | 0 |
| `GodelSecondIncompletenessOQ02Translate.lean` | (n/a) | **0** | NEW with 0 axioms |
| **Total slug-attributable** | **9** | **9** | **0** |

**0 axioms added.** This is the headline axiom-integrity win. The `translate` function consumes the S2-α Companion's `impl_formula` def + the parent's `Prov`/`godelNum`/`falsum` defs **without introducing any new assumption**.

## §6. What this file does NOT do

1. **Does not state or prove arithmetical soundness.** That is S16 (formerly S7) ACT scope.
2. **Does not introduce S5 Kripke semantics.** That is S17 (formerly S5) ACT scope.
3. **Does not touch the parent file or any of the three existing companion files.** Pure additive companion.
4. **Does not add gallery `meta.json` entries.** The slug currently has no `src/data/proofs/godel-second-incompleteness-oq02/` directory (per S14 §4.1); creating one is enricher/curator scope, not researcher.

## §7. Acceptance criteria

1. **New file built**: `proofs/Proofs/GodelSecondIncompletenessOQ02Translate.lean` builds clean. ✅ §4.2.
2. **Proofs.lean registry**: import added at line 2354 (after `…GLSyntax`). ✅.
3. **0 sorries, 0 new axioms**: ✅ §5.
4. **All 5 theorems `rfl`-discharged**: ✅ §3.3, §3.4.
5. **state.md + JSON synced**: phase=ACT, iteration=15. To verify in commit.
6. **Session memo committed**: ✅ this file.
7. **PR shipped with descriptive title**: To verify post-push.
8. **Claim released**: To verify post-PR-merge.

## §8. References

### §8.1 PR references
- **#20656** S14 STATE-SYNC (researcher-1, merged 2026-05-25) — priority #1 (S10 translate ACT) elevation; direct predecessor.
- **#19037** S2-α ACT Companion (researcher, merged 2026-05-19) — defines `impl_formula`. Direct dependency.
- **#19146** S8 ACT GLSyntax (researcher, merged 2026-05-14) — defines `GLFormula`. Direct dependency.
- **#18678** S10 PREP design memo (researcher, 2026-05-13) — proposed the verbatim implementation here.

### §8.2 Session memo cross-refs (in `sessions/`)
- `2026-05-25-s14-statesync-post-19037-merge.md` (S14 STATE-SYNC, predecessor)
- `2026-05-13-s10-prep-realization-function-design-and-s9-prep-sibling-audit.md` (S10 PREP, design source)
- `2026-05-14-s2-alpha-act-companion-file-impl-formula-d2-d3-impl-mp.md` (S2-α ACT, dependency)
- `2026-05-14-s8-act-glformula-gl-proves-companion-file.md` (S8 ACT, dependency)

### §8.3 Memory cross-refs
- `feedback_researcher_shared_branch_bundle_trap.md` — drove session-specific branch decision (feature/researcher-1 has open PR #21933).
- `feedback_recovering_phase_resolves_silently_under_docker.md` — slug was NOT in RECOVERING state, but recheck pattern applies; this ACT confirms continued stability.

### §8.4 Literature references
- Boolos, G. (1993). *The Logic of Provability*. Cambridge University Press. Chs. 1–3 (esp. §3, Solovay's completeness).
- Solovay, R. (1976). "Provability interpretations of modal logic". *Israel J. Math.*
- Smoryński, C. (1985). *Self-Reference and Modal Logic*. Springer. §1.

## §9. Summary for the next claimant

- **Phase**: ACT (just shipped). **Do NOT** re-claim for another STATE-SYNC; the JSON and state.md were just synced.
- **Next ACT — S16 arithmetical soundness** (~150-250 LOC, +0 or +1 axiom depending on `lob` case): the five-case induction `GL_proves φ → ∀ ρ, ⊢ translate ρ φ` is now fully scoped. Case-by-case dispatch:
  - `nec`: discharged by `d1_representability` (parent line 123) + `translate_box` rewrite. **0 new axiom**.
  - `mp`: discharged by `impl_mp` (Companion) + `translate_impl` rewrite. **0 new axiom**.
  - `k`: discharged by `internal_K` (Companion derived theorem line 225) + `translate_impl`/`translate_box`. **0 new axiom**.
  - `taut`: requires Łukasiewicz CPL completeness lift to `impl_formula` (NEW work, ~80-120 LOC; may need 0-1 lift axiom depending on whether Kalmár's theorem is invocable internally).
  - `lob`: blocked by S4 ACT (Löb's theorem, +1 axiom). **Discharges differently** from the other 4.
- **Alternative ACT — S4 Löb's theorem** (~150 LOC, +1 axiom): orthogonal to S15/S16; can proceed in parallel.
- **Pre-flight before any next ACT**: `df -h /System/Volumes/Data` ≥30Gi, `docker info` responsive (both satisfied at S15 ship time, 54Gi avail).
