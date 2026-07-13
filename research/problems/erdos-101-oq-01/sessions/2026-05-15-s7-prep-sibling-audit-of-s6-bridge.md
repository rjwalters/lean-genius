# Session 7 PREP — Sibling-audit of S6 PREP (#19221) IsBigO/IsLittleO bridge plan

- **Date**: 2026-05-15
- **Session**: 7
- **Phase**: PREP (no ACT — slug remains BLOCKED pending #19097/#19099)
- **Researcher**: researcher-12
- **Status**: doc-only sibling-audit, conflict-free with #19097/#19099/#19221

## 1. TL;DR

Sibling-PREP audit of my own S6 PREP (PR #19221, 2026-05-14T19:26Z, MERGEABLE/CLEAN)
goal-state-simulates the queued S6 ACT three-artifact plan at the lake-pinned
Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and surfaces **3
substantive bugs + 1 phantom-name + 1 LOC-budget undercount** that the
implementer following S6 PREP's recipe would otherwise hit during Docker iter 1:

| # | Severity | Location in #19221 | Issue |
|---|----------|---------------------|-------|
| **A** | low (name) | §"Reusable proof skeleton" + recipe step 4(ii) | `Filter.eventually_atTop_iff` is **not a Mathlib name** at the pinned SHA. The actual lemma is `Filter.eventually_atTop` (no `_iff` suffix), `Mathlib/Order/Filter/AtTopBot/Basic.lean:72`. `gh api search/code "eventually_atTop_iff" repo:leanprover-community/mathlib4` returns **0 hits**. |
| **B** | substantive | §"Comparison to `Asymptotics.isLittleO_iff`" | The `<` vs `≤` direction analysis is **reversed**. S6 PREP says: "for the `→` direction, replace `ε` by `ε/2`; for the `←` direction, use the `c < ε` freedom." The truth is the opposite — see §3 below. Implementer following the recipe would write the wrong tactic body. |
| **C** | substantive | §"S6 ACT scope" artifact (i) + recipe step 4(i) | Artifact (i)'s signature `Asymptotics.IsBigO atTop (fun P : PlanarPointSet => ...) (fun P => ...)` is **type-incoherent**. `atTop : Filter α` requires `[Preorder α]` (and `[Nonempty α]`); `PlanarPointSet` is a plain `structure` (`Erdos101Problem.lean:25-27`) with NO `Preorder`/`LE`/`SemilatticeSup` instance. Lean would fail with "failed to synthesize Preorder PlanarPointSet" during elaboration. Fix: route through an aggregator `ℕ → ℝ`, which the slug's S2 Next-Action #1 already names. See §4. |
| **D** | minor | implicit in §"Comparison" | The slug's `IsLittleOh_n_squared g` strict-`<` form is **vacuously unsatisfiable at `n = 0`** (would require `g 0 < ε * 0 = 0`). Doesn't break definitional equivalence — the `∃ N` existential simply forces `N ≥ 1` — but the ← direction of the bridge needs `set N := max N₀ 1` to pick up the strict gap `(ε/2) * n^2 < ε * n^2 ⇔ n ≥ 1`. S6 PREP doesn't mention this. See §3. |
| **E** | LOC budget | §"S6 ACT scope" totals row | Original budget `~80 LOC`. Revised post-fix budget: **~105–125 LOC** (~25–45 over) due to artifact (i) needing the aggregator + finiteness scaffold (was ~25 LOC, now ~50–65 LOC). See §5. |

**Recommendation**: amend the queued S6 ACT recipe per §3–§5 below before Docker iter 1.
This audit is doc-only and adds **exactly one new sessions/ file**; touches no
state.md / knowledge.md / JSON / Lean.

## 2. Pre-claim probe (2026-05-15T05:30Z)

```
$ gh pr list -R rjwalters/lean-genius --state open \
    --search 'erdos-101 in:title' --json number,title,createdAt,mergeStateStatus
[
  {"number":19097, "createdAt":"2026-05-14T17:15:44Z", "mergeStateStatus":"CLEAN", ...},
  {"number":19221, "createdAt":"2026-05-14T19:26:13Z", "mergeStateStatus":"CLEAN", ...}
]
```

Two open PRs; both MERGEABLE/CLEAN; deployer stall continues. No Docker
processes touching `Erdos101OQ01.lean` in any sibling worktree
(`ps -ef | grep docker-build`). Sibling state.md mtimes all ≥24 h old
(newest: researcher-8 at May 14 06:28). Race-free.

## 3. Bug B + D: `<` vs `≤` direction analysis (the bridge core)

### 3.1 The two definitions side-by-side

**Slug** (`Erdos101OQ01.lean:68-69`):

```lean
def IsLittleOh_n_squared (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (f n : ℝ) < ε * (n : ℝ)^2
```

**Mathlib** (`Mathlib/Analysis/Asymptotics/Defs.lean:175`, pinned SHA):

```lean
theorem isLittleO_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖
```

For the bridge `IsLittleOh_n_squared g ↔ Asymptotics.IsLittleO atTop (↑g) (· ^ 2)`,
specialise `l := atTop : Filter ℕ`, `f := ((g · : ℕ → ℕ) : ℕ → ℝ)`, `g_target := fun n : ℕ => (n : ℝ)^2`.
Then `‖(g n : ℝ)‖ = (g n : ℝ)` (nonneg cast, via `RCLike.norm_natCast`
— `Mathlib/Analysis/RCLike/Basic.lean:625`) and `‖((n : ℝ)^2)‖ = (n : ℝ)^2`
(square is nonneg).

### 3.2 Goal-state walk: `→` direction (slug ⇒ Mathlib)

**Goal** after `intro hslug; rw [isLittleO_iff]; intro c hc_pos; rw [Filter.eventually_atTop]`:

```
hslug : ∀ ε > 0, ∃ N, ∀ n ≥ N, (g n : ℝ) < ε * (n : ℝ)^2
hc_pos : 0 < c
⊢ ∃ a, ∀ b ≥ a, ‖(g b : ℝ)‖ ≤ c * ‖((b : ℝ)^2)‖
```

**Tactic sketch** (no ε/2 trick needed):

```lean
obtain ⟨N, hN⟩ := hslug c hc_pos
refine ⟨N, fun b hbN => ?_⟩
have h_strict : (g b : ℝ) < c * (b : ℝ)^2 := hN b hbN
calc ‖(g b : ℝ)‖
    = (g b : ℝ)              := Real.norm_natCast _
  _ ≤ c * (b : ℝ)^2          := h_strict.le
  _ = c * ‖((b : ℝ)^2)‖      := by rw [Real.norm_of_nonneg (sq_nonneg _)]
```

The strict `<` collapses to `≤` via `.le`. **No `ε/2` specialization** —
S6 PREP's claim "for the `→` direction, replace `ε` by `ε/2`" is wrong.

### 3.3 Goal-state walk: `←` direction (Mathlib ⇒ slug)

**Goal** after `intro hmathlib; rw [isLittleO_iff] at hmathlib; intro ε hε`:

```
hmathlib : ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in atTop, ‖(g x : ℝ)‖ ≤ c * ‖((x : ℝ)^2)‖
hε : 0 < ε
⊢ ∃ N, ∀ n ≥ N, (g n : ℝ) < ε * (n : ℝ)^2
```

**Tactic sketch** (ε/2 trick + n≥1 lift):

```lean
have hε2 : 0 < ε / 2 := by positivity
have h_ev : ∀ᶠ x in atTop, ‖(g x : ℝ)‖ ≤ (ε / 2) * ‖((x : ℝ)^2)‖ := hmathlib hε2
rw [Filter.eventually_atTop] at h_ev
obtain ⟨N₀, hN₀⟩ := h_ev
refine ⟨max N₀ 1, fun n hn => ?_⟩       -- Bug-D mitigation: n ≥ 1
have h₁ : N₀ ≤ n := (le_max_left _ _).trans hn
have h₂ : 1 ≤ n := (le_max_right _ _).trans hn
have h_le : (g n : ℝ) ≤ (ε / 2) * (n : ℝ)^2 := by
  have := hN₀ n h₁
  rwa [Real.norm_natCast, Real.norm_of_nonneg (sq_nonneg _)] at this
have h_pos : (0 : ℝ) < (n : ℝ)^2 := by
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h₂
  positivity
have h_strict : (ε / 2) * (n : ℝ)^2 < ε * (n : ℝ)^2 := by
  have hε2_lt : ε / 2 < ε := by linarith
  exact mul_lt_mul_of_pos_right hε2_lt h_pos
linarith
```

The ε/2 trick **is** needed here — to leave room for the strict `<` —
together with the `max N₀ 1` lift to ensure `(n : ℝ)^2 > 0` (Bug D).
S6 PREP's "use the `c < ε` freedom" gloss skips both the ε/2 instantiation
and the n≥1 lift; an implementer following the recipe verbatim would loop
on `mul_lt_mul_of_pos_right` (no `0 < n^2` hypothesis in scope) before
realising they need the `max … 1`.

### 3.4 Direction-mapping correction (one-line amendment to S6 PREP)

The S6 PREP §"Comparison to `Asymptotics.isLittleO_iff`" sentence

> Bridging needs the standard trick: for the `→` direction, replace `ε` by `ε/2`; for the `←` direction, use the `c < ε` freedom.

should be replaced by

> Bridging is asymmetric: the `→` direction (slug ⇒ Mathlib) is direct
> via `le_of_lt` — take Mathlib's universal `c` as slug's `ε`. The `←`
> direction (Mathlib ⇒ slug) needs (i) instantiate Mathlib's universal `c`
> at `ε / 2`, (ii) `max N₀ 1` to ensure `(n : ℝ)^2 > 0`, (iii) finish via
> `mul_lt_mul_of_pos_right`.

## 4. Bug C: `Asymptotics.IsBigO atTop` on `PlanarPointSet` is type-incoherent

### 4.1 What S6 PREP prescribes

S6 PREP §"S6 ACT scope" artifact (i):

> `fourPointLineCount_isBigO_n_squared` (~25 LOC). Reformulate
> `fourPointLineCount_le_quadratic` (existing, line ~190 of the file)
> as `Asymptotics.IsBigO atTop (fun P : PlanarPointSet => (fourPointLineCount P : ℝ)) (fun P => (P.points.card : ℝ)^2)`
> modulo the discrete-input handling.

Recipe step 4(i): "uses `Asymptotics.IsBigO.of_norm_le` + the existing
`fourPointLineCount_le_quadratic`."

### 4.2 Why this fails to elaborate

`Asymptotics.IsBigO l f g` (`Defs.lean:93`) takes `l : Filter α` for
implicit `α`. The `atTop` notation expands to
`Filter.atTop : Filter α` requiring `[Preorder α]` (and effective use
needs `[Nonempty α]`) — see `Mathlib/Order/Filter/AtTopBot/Defs.lean`.

The slug's parent (`Erdos101Problem.lean:25-27`):

```lean
structure PlanarPointSet where
  points : Finset (ℝ × ℝ)
  size_pos : points.card > 0
```

is a plain structure. **Verification**:

```
$ grep -rn "PlanarPointSet" proofs/Proofs/ | grep -E "instance|extends"
proofs/Proofs/Erdos101Problem.lean:25:structure PlanarPointSet where
# (no instance/extends lines)
```

No `Preorder`/`LE`/`SemilatticeSup`/`OrderBot`/`OrderTop` instance is
declared anywhere in the project. Elaboration of artifact (i) would fail
at the `atTop` token with `failed to synthesize Preorder PlanarPointSet`
(canonical Lean error for missing typeclass inference at filter notation).

### 4.3 Why the existing `fourPointLineCount_le_quadratic` doesn't rescue artifact (i) directly

`fourPointLineCount_le_quadratic` (`Erdos101OQ01.lean:143-145`):

```lean
theorem fourPointLineCount_le_quadratic (P : PlanarPointSet)
    (hP : NoFiveCollinear P) :
    (fourPointLineCount P : ℝ) ≤ (P.points.card : ℝ)^2
```

is a **pointwise** statement (per `P`), not an asymptotic statement. It
has no "filter direction" to feed into `IsBigO.of_norm_le`'s
`∀ x, ‖f x‖ ≤ g x` premise (which IS pointwise but typed at the wrong α).

### 4.4 Two fixes

**Path A — aggregator routing (recommended, matches knowledge.md S2 NA #1)**:

Define an aggregator `ℕ → ℝ`:

```lean
noncomputable def maxFourPointLines (n : ℕ) : ℕ :=
  -- supremum of fourPointLineCount over no-five-collinear sets of size n;
  -- finite by `improved_upper_bound` (≤ n*(n-1)/12)
  if h : 0 < n then ⌊(n * (n - 1) / 12 : ℕ)⌋ else 0  -- pessimistic surrogate
```

Then state `IsBigO atTop` on `ℕ → ℝ`:

```lean
theorem maxFourPointLines_isBigO_n_squared :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => (maxFourPointLines n : ℝ))
      (fun n : ℕ => (n : ℝ)^2) := by
  apply Asymptotics.IsBigO.of_norm_le
  intro n
  -- combines ‖·‖ = id (nonneg) + algebraic bound n*(n-1)/12 ≤ n²
  ...
```

LOC: aggregator def ~10 LOC + `IsBigO` proof ~25 LOC = **~35 LOC** (for
the surrogate `n*(n-1)/12` upper bound; if instead defining true sup
over no-five-collinear sets, add ~15 LOC for the `Finset.sup'`/finite-set
argument, total ~50 LOC).

A separate per-`P` corollary can recover the original
`(fourPointLineCount P : ℝ) ≤ maxFourPointLines P.points.card`
relation (~10 LOC), giving total artifact (i) **~45–60 LOC**.

**Path B — restate without `IsBigO` (not recommended)**:

Drop artifact (i) entirely; restate only artifacts (ii) and (iii).
Loses the trivial-O(n²) statement in Mathlib idiom but ships smallest;
LOC delta: ~−25 LOC (artifact (i) absent). Recovery requires
later session.

### 4.5 Recommendation

**Path A**, with surrogate aggregator (n*(n-1)/12 upper-bound) for the
first iteration to avoid the `Finset.sup'`-over-uncountable-set argument
(`PlanarPointSet`'s underlying `Finset (ℝ × ℝ)` is not enumerable, so
`Finset.sup'` over the `setOf` is infinite). The surrogate gives the
correct asymptotic bound; the "true sup" version can replace it in a
later refinement pass without changing the `IsBigO` statement.

## 5. Revised LOC budget for S6 ACT

| Artifact | S6 PREP estimate | Revised (post-audit) | Delta | Reason |
|----------|------------------|---------------------|-------|--------|
| (i) `…isBigO_n_squared` (now via aggregator) | ~25 | **~45–60** | +20–35 | aggregator def + per-P corollary (Bug C) |
| (ii) `isLittleOh_n_squared_iff_isLittleO` | ~25 | **~30** | +5 | n=0 lift via `max … 1` (Bug D) + corrected ε/2 direction (Bug B; same LOC) + `Real.norm_natCast` invocations |
| (iii) `erdos_101_oq_01_isLittleO_form` | ~30 | **~30** | 0 | unchanged |
| **Total** | **~80** | **~105–125** | **+25–45** | |

Docker budget for S6 ACT: plan **2 iterations** (was likely 1 implied).

## 6. Bearer pin re-verification (delta vs S6 PREP table)

All bearers from S6 PREP §"Mathlib bearer audit" re-verified at SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | S6 PREP file:line | Re-verified file:line | Status |
|--------|-------------------|----------------------|--------|
| `Asymptotics.IsBigO` | `Defs.lean:93` | `Defs.lean:93` | ✓ |
| `Asymptotics.IsLittleO` | `Defs.lean:162` | `Defs.lean:162` | ✓ |
| `Asymptotics.isLittleO_iff` | `Defs.lean:175` | `Defs.lean:175` | ✓ |
| `Asymptotics.isBigO_iff` | `Defs.lean:104` | `Defs.lean:104` | ✓ |
| `Asymptotics.IsBigO.of_norm_le` | `Defs.lean:155` | `Defs.lean:155` | ✓ |
| `Filter.eventually_atTop_iff` | (no line) | **DOES NOT EXIST** | ❌ Bug A |
| `Filter.eventually_atTop` | (not pinned) | `AtTopBot/Basic.lean:72` | ✓ correct name |

Additional bearers needed for the corrected bridge (§3.2/§3.3):

| Bearer | file:line @ SHA | Used in |
|--------|-----------------|---------|
| `RCLike.norm_natCast` | `Mathlib/Analysis/RCLike/Basic.lean:625` | both directions, `‖(n : ℝ)‖ = n` |
| `Real.norm_of_nonneg` | `Mathlib/Analysis/Normed/Group/Real.lean` (auto) | `‖x‖ = x` for `x ≥ 0` |
| `mul_lt_mul_of_pos_right` | `Mathlib/Algebra/Order/…` (mathlib std) | ← direction strict-step |
| `sq_nonneg` | `Mathlib/Algebra/Order/Ring/Lemmas.lean` (mathlib std) | both directions |

Negative-bearer search confirms `Filter.eventually_atTop_iff` doesn't
exist at any SHA in mathlib4:

```
$ gh api 'search/code?q=%22eventually_atTop_iff%22+repo:leanprover-community/mathlib4'
{"total_count":0, ...}
```

## 7. What this S7 PREP does NOT do

- **No Lean edits.** `Erdos101OQ01.lean`, `Erdos101Problem.lean` unchanged.
- **No `state.md` / `knowledge.md` / JSON edits.** PR #19097 owns those;
  PR #19221 is doc-only sessions/ supplement; this PR ships exactly one
  more sessions/ file. Strict conflict-free guarantee with #19097/#19221/#19099.
- **No claim that the ACT is now mergeable.** The slug is BLOCKED until
  #19097 + #19099 land. This PREP only fixes S6 PREP's recipe so the
  post-merge S6 ACT compiles on Docker iter 1 instead of iter 2 or 3.
- **No claim about the open OQ-01 conjecture.** Artifact (iii)'s body
  remains a `sorry` (the $100 Erdős prize).

## 8. Conflict-free guarantee

Files this PR touches:

```
research/problems/erdos-101-oq-01/sessions/2026-05-15-s7-prep-sibling-audit-of-s6-bridge.md  (NEW)
```

Files PR #19097 (S5 OBSERVE) touches:

```
research/problems/erdos-101-oq-01/{state.md, knowledge.md}            (DISJOINT)
src/data/research/problems/erdos-101-oq-01.json                        (DISJOINT)
```

Files PR #19099 (mechanic) touches:

```
proofs/Proofs/Erdos101Problem.lean                                     (DISJOINT)
```

Files PR #19221 (S6 PREP, mine) touches:

```
research/problems/erdos-101-oq-01/sessions/2026-05-15-s6-prep-isbigo-bridge-bearer-audit.md (DIFFERENT FILENAME)
```

All paths disjoint by construction; no merge conflict possible.

## 9. Post-merge sequencing (replaces S6 PREP recipe step 4)

After #19097, #19099, AND #19221 merge, AND this S7 PREP merges:

1. `git fetch origin && git rebase origin/main` (worktree).
2. Verify parent file at expected line numbers post-#19099.
3. Add to `Erdos101OQ01.lean` (post line 470):
   - **(i')** `maxFourPointLines : ℕ → ℕ` (aggregator, ~10 LOC) +
     `maxFourPointLines_isBigO_n_squared : Asymptotics.IsBigO atTop …`
     (~25 LOC) + per-P corollary `fourPointLineCount_le_max …` (~10 LOC).
     **Total ~45 LOC.**
   - **(ii')** `isLittleOh_n_squared_iff_isLittleO` per §3.2/§3.3
     (~30 LOC including `max N₀ 1` lift and `Real.norm_natCast` lifts).
   - **(iii)** `erdos_101_oq_01_isLittleO_form` per S6 PREP (~30 LOC).
4. Imports: add explicit
   `import Mathlib.Analysis.Asymptotics.Defs` and
   `import Mathlib.Order.Filter.AtTopBot.Basic` to bypass any
   transitive-import fragility (the `Pow.Real → Pow.Complex → Complex.Log`
   chain leads to Asymptotics.Defs only via `Normed.Field.Basic`, which
   IS upstream — confirmed at SHA — but explicit imports are cheap
   insurance).
5. Docker-build the file as a baseline. **Plan 2 iterations** (likely
   needs at most one round of `Real.norm_natCast` vs `‖((g n : ℕ) : ℝ)‖`
   normalisation).
6. Update state.md / JSON / knowledge.md (now owned by post-merged #19097
   so safe to edit).
7. PR title: `research(erdos-101-oq-01): S6 ACT — IsBigO/IsLittleO bridge to Mathlib idiom (build verified)`.

## 10. Sequencing dependency map (updated)

```
   PR #19099 (mechanic, parent fix) ─┐
                                      ▼
   PR #19097 (S5 OBSERVE → BLOCKED) ──┐
                                       │
   PR #19221 (S6 PREP, bridge plan) ──┤
                                       │
   [this PR] (S7 PREP, audit of #19221)┤
                                       ▼
                       S6 ACT (post-all-PRs-merge):
                         ~105-125 LOC, 2 Docker iters,
                         3 artifacts via Path A aggregator
```

## 11. Cross-pattern composability

This audit composes with prior sibling-audit patterns:

- `_sibling_prep_audits_peer_prep_workaround_finds_sharper_cancellation_path` (LOC efficiency)
- `_sibling_prep_compile_simulates_peer_complete_dropin_body_finds_three_tactic_bugs` (drop-in tactic body)
- `_concrete_counterexample_falsifies_peer_prep_unsound_recommendation` (numerical)
- `_sibling_prep_validates_self_prep_via_hou_audit_plus_2x2_matrix_companion` (self-validates)

This S7 firing is closer to "_sibling_prep_compile_simulates_peer_complete_dropin_body_finds_three_tactic_bugs"
but with two distinguishing features: (a) audits **own prior PREP** (researcher-12 → researcher-12)
rather than peer; (b) the bug class includes a **type-coherence failure** (Bug C
on `Preorder PlanarPointSet`), not just tactic-elaboration nuances.

## 12. Sanity-check footer

- **State.md not edited** (PR #19097 owns it): ✓ confirmed
- **Knowledge.md not edited** (PR #19097 owns it): ✓ confirmed
- **JSON not edited** (PR #19097 owns it): ✓ confirmed
- **Lean files not edited** (PR #19099 owns parent; ACT defers): ✓ confirmed
- **`research/problems/erdos-101-oq-01/sessions/` is a NEW directory**: ✓ confirmed (didn't exist on main)
- **One file added**: `2026-05-15-s7-prep-sibling-audit-of-s6-bridge.md`
- **Conflict-free with PRs #19097, #19099, #19221**: ✓ disjoint paths
- **Pre-claim probe**: 2 open PRs on slug (no race), 0 sibling Docker
  processes touching `Erdos101OQ01.lean`, sibling state.md mtimes ≥24 h old.

---

## Appendix A — Why this audit catches type-coherence (Bug C) but a "bearer-existence" PREP wouldn't

S6 PREP correctly identifies `Asymptotics.IsBigO`, `IsLittleO`,
`isLittleO_iff`, `IsBigO.of_norm_le` as existing at SHA. All bearer-level
checks pass. But the **typeclass inference chain** triggered by the
`atTop` token at the application site (specialised α := PlanarPointSet)
fails. This is a class of bug invisible to:

- pin-verifying the bearer's existence (the lemma exists; it's
  applicable in principle);
- reading the bearer's signature (the signature is generic over `α`);
- checking the import graph (the imports are correct).

It only surfaces when the implementer either (a) attempts the application
in Docker and reads the elaboration error, or (b) walks the goal-state
post-`unfold IsBigO` and notices `Preorder α` showing up in the
typeclass binder slot.

This audit's contribution is goal-state simulation that catches (b)
before Docker iter 1.

## Appendix B — Why this audit catches `<` vs `≤` reversal (Bug B) but a "bearer-existence" PREP wouldn't

S6 PREP correctly notes "the slug uses strict `<`; Mathlib's
`isLittleO_iff` uses `≤`" and correctly identifies that bridging
"needs the standard trick" (i.e., ε/2 specialization). But **assigns
the trick to the wrong direction**. This is the kind of error that
appears when the PREP author writes the bridge plan from memory of
"there's an ε/2 trick for `<`/`≤` bridges" without instantiating the
two implications and walking the goal-state for each.

A goal-state simulation as in §3.2/§3.3 forces explicit accounting
for which side has the universal `c` vs the existential `ε`, which
side starts with `<` and ends with `≤`, and where the `ε/2`
substitution slots in.
