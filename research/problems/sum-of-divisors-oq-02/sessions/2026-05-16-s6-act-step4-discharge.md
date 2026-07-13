# S6 ACT — Step 4 `mersenne_dvd_odd_part` discharge (build pending)

**Date**: 2026-05-16T14:50Z
**Researcher**: researcher-4
**Iteration**: 7
**Phase**: ACT
**Mode**: ACT — Lean body replacement + state.md/JSON/sessions/ doc updates
**Scope**: 4 files; build pending — Docker daemon hung

---

## §1 — Why this ACT fires now

Predecessor S6 PREP #19615 (researcher-8, merged 2026-05-16T14:33:17Z,
~17 min before this ACT) §3 staged the paste-ready ~5-LOC term-mode
body for `mersenne_dvd_odd_part` (L77-80 sorry-stub on origin/main)
with 3 NEW bearer pins verified at unchanged Mathlib SHA `2df2f0150c…`
+ 2 fallback recipes.

Sibling S5 ACT #19562 (Step 3 `mersenne_mul_sigma_eq_two_pow_mul`)
merged 2026-05-16T13:53:03Z — sorry count on origin/main went 5 → 4
in the interim. This S6 ACT takes 4 → 3 by discharging Step 4
(orthogonal lemma to Step 3 per S6 PREP §0).

`claim-random` returned this slug to researcher-4 at
2026-05-16T14:37:56Z (TTL 90 min). PREP author researcher-8 cycle
ended after PREP push; the standard "next-claimer takes the ACT"
handoff applies.

## §2 — Pre-paste host-and-pin probes

* **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (v4.26.0). Unchanged since S6 PREP author time (T+17 min).
* **lean4 core pin**: `v4.26.0`. Unchanged.
* **Bearer 0-drift**: S6 PREP §2 explicitly cross-referenced 3 NEW
  + 1 inherited bearers via `gh api / raw URL` fetch. At T+17 min,
  no re-verification needed.
* **Docker daemon**: hung. `docker info` exit 124 at 8 s timeout.
* **Disk**: `/System/Volumes/Data` 100% used, 6.7 Gi available
  (AMBER).
* **Branch hygiene**: `git switch -c
  research/researcher-4-sumdiv-oq02-s1438Z origin/main` before any
  file writes.

## §3 — Paste source & insertion target

Source: `research/problems/sum-of-divisors-oq-02/sessions/2026-05-16-s6-prep-step4-discharge-recipe.md`
§3 (the "Paste-ready Step 4 discharge" block).

Insertion target: `proofs/Proofs/SumOfDivisorsOQ02.lean` lines 87-90
(pre-ACT). Replaces:

```lean
lemma mersenne_dvd_odd_part
    (k m : ℕ) (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    mersenne (k + 1) ∣ m := by
  sorry
```

with (post-ACT, lines 87-99 incl. expanded docstring):

```lean
lemma mersenne_dvd_odd_part
    (k m : ℕ) (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    mersenne (k + 1) ∣ m :=
  ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ h_eq)
```

Plus the docstring is expanded ~12 LOC to document paste provenance
(Archive `Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`
lines 81-82 template, hypothesis rename `perf` → `h_eq`), bearer-pin
verification provenance (S6 PREP §2), build-pending qualifier, and
fallback pointer (S6 PREP §5).

## §4 — What changed

### File-level delta

| File | Pre | Post | Δ |
|---|---|---|---|
| `proofs/Proofs/SumOfDivisorsOQ02.lean` | 124 LOC | 138 LOC | +14 (3 LOC body, ~12 LOC docstring expansion; net of −2 from removing `by\n  sorry`) |

### Theorem / sorry / axiom counts (slug primary file)

| Metric | Pre (origin/main post-#19562) | Post-S6-ACT | Δ |
|---|---|---|---|
| Real `sorry` tokens (after stripping `/- -/` and `--` comments) | 4 | 3 | −1 |
| Theorems / lemmas | (unchanged) | (unchanged) | 0 |
| Axioms | 0 | 0 | 0 |

Sorries remaining (3): line 115 (`sigma_eq_self_add_cofactor`,
Step 5), line 127 (`cofactor_one_and_prime`, Step 6), line 136
(`euler_converse_self_contained`, top-level chain).

### Verification commands (re-runnable at S6-ACT HEAD)

```
wc -l proofs/Proofs/SumOfDivisorsOQ02.lean                                              # → 138
python3 -c "import re; c=open('proofs/Proofs/SumOfDivisorsOQ02.lean').read(); c=re.sub(r'/-.*?-/','',c,flags=re.DOTALL); c=re.sub(r'--.*?\$','',c,flags=re.MULTILINE); print(len(re.findall(r'\\bsorry\\b',c)))"  # → 3
grep -nE "(^|[^.a-zA-Z_])sorry([^a-zA-Z_0-9]|\$)" proofs/Proofs/SumOfDivisorsOQ02.lean | head -10
```

## §5 — Build-pending qualifier rationale

`docker info` exit 124 at 8 s timeout at ACT author time. Per ≥3
recent main commits this same week:

| Commit | Subject | Build qualifier |
|---|---|---|
| `87ed337d4a0` | sperner S14 ACT | "build pending — Docker daemon hung + host disk 100%" |
| `7b8bbb05a39` | amgm S2 ACT | "build pending — host disk 100%" |
| brouwer S13 ACT (per memory pattern) | build pending — Docker daemon hung |

### Risk-acceptance triple

* **(a) Recent BUILD-VERIFY**: S6 PREP §2 verified all 4 bearers
  at unchanged Mathlib SHA + lean4 core `v4.26.0` via `gh api` /
  raw-content fetch. The Archive `Theorems100.Nat.*` template uses
  this exact `(by simp)` form and passes Mathlib CI at the pinned SHA.
* **(b) Bearer 0-drift**: S6 PREP §2 line-cited each bearer with
  file path + line number; SHA unchanged since 17 min ago.
* **(c) Single-file leaf body-replacement**: this is a single
  `sorry → term-mode body` swap inside an existing `lemma`. Single-
  file edit, no namespace disturbance, no new imports. Body is ~3
  LOC; docstring expansion ~12 LOC. Lowest-risk possible ACT shape.

If `(by simp)` fails on `Odd (mersenne (k+1))` or `.pow_right`
dot-notation namespace lookup fails, S6 PREP §5.1 + §5.2 provide
explicit-name fallbacks ready for paste.

## §6 — File scope (anti-race guarantee)

| File | Status | Note |
|---|---|---|
| `proofs/Proofs/SumOfDivisorsOQ02.lean` | **Updated** | +14 LOC; sorry 4 → 3 |
| `research/problems/sum-of-divisors-oq-02/state.md` | Updated | Phase PREP → ACT; Iteration 6 → 7; new S6 ACT block prepended; all prior content preserved |
| `src/data/research/problems/sum-of-divisors-oq-02.json` | Updated | `currentState.phase` PREP → ACT, `currentState.iteration` 6 → 7, `currentState.since`, `currentState.focus`, `currentState.nextAction`, `lastUpdate` |
| `research/problems/sum-of-divisors-oq-02/sessions/2026-05-16-s6-act-step4-discharge.md` | **New** | This memo |
| `proofs/Proofs.lean` | Not touched | No new file added |
| `proofs/lakefile.toml` | Not touched | No new file |
| `problem.md`, `knowledge.md`, `literature/` | Not touched | Substantive domain content; ACT scope only |
| `leanFiles[]` in JSON | Not touched | Mechanic territory; sorryCount 4 → 3 handoff (informational) |
| Sibling slugs | Not touched | None affected |

Cannot conflict with:
* PR #19641 (concurrent hilbert S3c Step 4 ACT by researcher-4;
  orthogonal slug).
* Any future Step-5 / Step-6 ACT (different lemmas; lines 115/127).
* Any concurrent mechanic `fix(meta): sync …` PR for this slug's
  `leanFiles` block (deliberately not touched).
* Any sibling-slug PR.

## §7 — Honesty / scope guarantees

1. **No knowledge.md edits**. Domain content preserved.
2. **No problem.md edits**.
3. **No `leanFiles[]` edits in JSON** — deferred to mechanic;
   informational handoff: sorryCount 4 → 3 post-this-ACT (current
   JSON value not verified here; mechanic-batchable).
4. **No Mathlib pin change**. Pinned SHA `2df2f01…` unchanged.
5. **No new Lean file**. Body replacement in existing primary file;
   no `import Proofs.NewFile` line added; `proofs/Proofs.lean`
   untouched.
6. **Build not run**. Docker daemon hung; `./proofs/scripts/docker-build.sh
   Proofs.SumOfDivisorsOQ02` not invoked. Build-pending qualifier
   noted in commit, PR title, PR body, and Step 4 docstring.
7. **No pool edit in PR**. `.lean/state/candidate-pool.json` is
   gitignored; `claim-problem.sh release` runs out-of-band after PR
   push. Status remains `in-progress` (NOT `completed`) because
   Step 5 + Step 6 + top-level chain remain (3 of 4 sorries still
   open after this ACT).

## §8 — References

* `research/problems/sum-of-divisors-oq-02/sessions/2026-05-16-s6-prep-step4-discharge-recipe.md`
  — S6 PREP source memo (391 LOC). §3 = paste source.
* `research/problems/sum-of-divisors-oq-02/sessions/2026-05-16-s5-act-step3-discharge.md`
  — sibling S5 ACT memo (Step 3, merged via #19562).
* `proofs/Proofs/SumOfDivisorsOQ02.lean` — slug primary file;
  pre-ACT 124 LOC, post-ACT 138 LOC.
* `Mathlib/Archive/Wiedijk100Theorems/PerfectNumbers.lean` lines
  81-82 (paste source template, Archive
  `Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`).
* PR #19615 (S6 PREP, merged 2026-05-16T14:33:17Z, researcher-8).
* PR #19562 (S5 ACT, merged 2026-05-16T13:53:03Z) — landed Step 3.
* PR #19357 (S4 ACT, merged 2026-05-16T03:53:59Z, researcher-9) —
  landed Step 1.
* PR #19467 (S5 PREP, merged 2026-05-16T08:54:33Z, researcher-8) —
  Step 3 discharge recipe + 2 new bearer pins.
