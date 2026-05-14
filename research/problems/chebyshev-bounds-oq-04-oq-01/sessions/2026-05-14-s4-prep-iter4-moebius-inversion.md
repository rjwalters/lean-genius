# S4 PREP — Iter 4 Möbius inversion: API pins + proof sketch

**Slug**: `chebyshev-bounds-oq-04-oq-01` (Elementary Proof of Full PNT from
Chebyshev Bounds — Selberg–Erdős 1949).
**Researcher**: researcher-8.
**Date**: 2026-05-14 ~22:30 UTC.
**Mode**: doc-only PREP (no Lean, no gallery JSON, no candidate-pool, no
`state.md`, no `meta.json` touch).
**Purpose**: De-risk the Iter 4 ACT (literal Möbius–log identity
`Λ₂(n) = Σ_{d∣n} μ(d) · log²(n/d)` for `n ≥ 1`) by pinning every Mathlib
API at the project's current Mathlib SHA, decomposing the proof into
verifiable sub-steps, and noting the explicit dependency on the OPEN
PR #19092 (Iter 3 ACT).

## §1 Pre-claim survey

### 1.1 PR landscape (slug-scoped)

`gh pr list -R rjwalters/lean-genius --search
"chebyshev-bounds-oq-04-oq-01 in:title" --state open` returns two OPEN
PRs as of session start (2026-05-14 ~22:30 UTC):

| PR | Title | Created | Updated | Mergeable | Notes |
|---|---|---|---|---|---|
| #17689 | `Iter 2 — prime values (build pending)` | 2026-05-12T00:12Z | 2026-05-12T22:13Z | CONFLICTING | Stale; superseded by merged PR #17690 (same scope, different branch). Already documented in S3 STATE-SYNC. |
| #19092 | `Iter 3 ACT — Selberg dual identity Σ_{d∣n} Λ₂(d) = (log n)² (build verified)` | 2026-05-14T16:22Z | 2026-05-14T16:22Z | MERGEABLE | researcher-9; +91/-14 on `ChebyshevBoundsOQ04OQ01.lean` (+ incidental parent fixes). Build verified Docker 7744 jobs. |

**Important framing**: PR #19092 (still OPEN at session start) is the
substantive Iter 3 ACT in the project's current PR queue. It does
**not** prove the literal `Λ₂(n) = Σ_{d∣n} μ(d) · log²(n/d)` form that
`state.md` 's "Next Action" names — it proves the *dual* form
`Σ_{d∣n} Λ₂(d) = (Real.log n)²` (call this the "Iter 3 dual identity"),
which is equivalent to the literal form via Möbius inversion. Its body
explicitly defers the literal Möbius–log identity to Iter 4.

This PREP is the Iter 4 plan that consumes PR #19092's
`sum_divisors_selbergLambda2_eq_log_sq` as its single non-trivial input
and runs `sum_eq_iff_sum_mul_moebius_eq` + an antidiagonal-to-divisors
bridge to reach the literal form.

### 1.2 Current main-target file state

`proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` at `origin/main` (HEAD
`2afb1b79c0a`, last touched by PR #17690 merge on 2026-05-12):

- 230 LOC, 12 theorems, 3 noncomputable defs, 0 sorries, 0 axioms.
- Iter 2 prime-value lemmas (`vonMangoldtConv_prime`,
  `selbergLambda2_prime`) present (lines 188–204).
- File has a Future Work section (lines 206–228) explicitly enumerating
  the Möbius–log identity as deliverable #1.

### 1.3 `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json`
staleness note (not corrected here; conflict-free with PR #19092)

The JSON's `leanFiles[3].lineCount` for `ChebyshevBoundsOQ04OQ01.lean`
is 206 (Iter 1 number) and `theoremCount` is 10 (also Iter 1). The file
is 230 LOC / 12 theorems on `main`. PR #19092 will further push to
~307 LOC / 15 theorems when merged. **This PREP deliberately does not
touch the JSON** because PR #19092 itself updates this exact JSON file
(`+28/-18 lines`); refreshing it here would create a 3-way merge
conflict on the LOC/theorem fields. Iter 4 ACT should refresh these
numbers post-#19092-merge.

## §2 Iter 3 dual identity recap (PR #19092 input to Iter 4)

PR #19092 proves (in `ChebyshevBoundsOQ04OQ01.lean` after merge):

```lean
theorem sum_divisors_selbergLambda2_eq_log_sq (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, selbergLambda2 d = (Real.log n) ^ 2 := by
  -- (PR #19092 proof: 3-step chain via vonMangoldt_sum + Λ ∗ Λ ∗ ζ = Λ ∗ log
  --  + Real.log_mul for divisor pairs; ≈25-LOC proof body)
  ...
```

The PR also lands two supporting bridges:

```lean
theorem vonMangoldtConv_eq_mul (n : ℕ) :
    vonMangoldtConv n =
      ((vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n : ℝ) := by
  -- bridge from local divisor-sum to Mathlib's ArithmeticFunction.mul form
  -- proof: Nat.map_div_right_divisors + Finset.sum_map + rfl  (≈1-LOC body)

theorem sum_divisors_vonMangoldtConv (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, vonMangoldtConv d
      = ∑ d ∈ n.divisors, vonMangoldt d * Real.log (n / d) := by
  -- (Λ ∗ Λ) ∗ ζ = Λ ∗ (Λ ∗ ζ) = Λ ∗ log  via vonMangoldt_mul_zeta + mul_assoc
```

(Quoting from PR #19092's body — full Lean text not inlined here to
keep this PREP conflict-free.)

## §3 Mathlib API pin verification (Mathlib v4.26.0, SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

All lemmas needed by Iter 4 ACT verified via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Lemma | File | Line | Note |
|---|---|---|---|
| `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` | `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean` | 240 | `[NonAssocRing R]`; gives the antidiagonal form of Möbius inversion. |
| `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq` | same file | 210 | `[AddCommGroup R]`; smul variant, used internally by the `_mul_` form's `rw` |
| `Nat.sum_divisorsAntidiagonal` (via `@[to_additive]` on `prod_divisorsAntidiagonal`) | `Mathlib/NumberTheory/Divisors.lean` | 543 | `∑ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∑ i ∈ n.divisors, f i (n / i)` |
| `Nat.map_div_right_divisors` | `Mathlib/NumberTheory/Divisors.lean` | 370 | Underlying `Finset.map` form (no `AddCommMonoid`); used by PR #19092 already. |
| `ArithmeticFunction.coe_mul_zeta_apply` | `Mathlib/NumberTheory/ArithmeticFunction/Zeta.lean` | 81 | Right-`ζ`-convolution unfold: `(f * ζ) n = ∑ d ∈ n.divisors, f d`. Used by PR #19092 for `(Λ*Λ)*ζ`. |
| `ArithmeticFunction.coe_zeta_mul_apply` | same file | 77 | Left form: `(ζ * f) n = ∑ d ∈ n.divisors, f (n/d)`. |
| `ArithmeticFunction.vonMangoldt_sum` | `Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean` | 102 | `∑ i ∈ n.divisors, Λ i = Real.log n`. Used by PR #19092 in chain. |
| `ArithmeticFunction.vonMangoldt_mul_zeta` | same | 119 | `Λ * ζ = log`. Used by PR #19092. |
| `ArithmeticFunction.vonMangoldt_apply_one` | same | 77 | `Λ 1 = 0`. Iter 1+2 lemma already in slug. |
| `ArithmeticFunction.vonMangoldt_apply_prime` | same | 89 | `Λ p = Real.log p` for prime `p`. Iter 2 dep. |
| `ArithmeticFunction.vonMangoldt_nonneg` | same | 80 | `0 ≤ Λ n`. Iter 1 dep. |
| `Nat.Prime.divisors` (dot-method form) | `Mathlib/NumberTheory/Divisors.lean` | 416 | `pp.divisors = {1, p}`; replaces v4.25 `Nat.divisors_prime` — incidental in PR #19092 (line 191 of slug Lean file). |

**Barrel deprecation note**: `Mathlib/NumberTheory/ArithmeticFunction.lean`
at the pinned SHA is a *deprecated re-export shim* (`deprecated_module
(since := "2025-12-01")`). Iter 4 ACT should `import Mathlib`
(consistent with current slug) and not refer to the deprecated barrel
path directly; `open ArithmeticFunction` continues to expose
`vonMangoldt`, `moebius`, `μ`, `ζ` correctly.

## §4 Iter 4 proof sketch

### 4.1 Target statement

```lean
/-- **Möbius–log identity (literal form)**: for `n ≥ 1`,
    `Λ₂(n) = Σ_{d ∣ n} μ(d) · log²(n/d)`.
    Equivalent to Iter 3's dual identity `Σ_{d ∣ n} Λ₂(d) = log²(n)` by
    Möbius inversion. -/
theorem selbergLambda2_eq_moebius_log_sq (n : ℕ) (hn : 0 < n) :
    selbergLambda2 n =
      ∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℝ) * (Real.log (n / d : ℕ)) ^ 2) := by
  ...
```

(Statement form intentionally uses `(n / d : ℕ)` cast to `ℝ`, matching
what comes out of `Nat.sum_divisorsAntidiagonal` after the inversion
rewrite. An optional Iter 4-bis variant with `(↑n / ↑d : ℝ)` inside the
log is straightforward to add via `Nat.cast_div_eq_of_dvd` once the
literal form is in place — see §6 "follow-up" note.)

### 4.2 Proof structure (estimated ≤ 25 LOC body)

The key step is bidirectional application of Möbius inversion. The
Mathlib lemma `sum_eq_iff_sum_mul_moebius_eq` takes an `iff` between

- **LHS hypothesis** (Iter 3 form, ranges over `divisors`):
  `∀ n > 0, ∑ i ∈ n.divisors, f i = g n`
- **RHS conclusion** (Iter 4 form, ranges over `divisorsAntidiagonal`):
  `∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n`

Setting `R := ℝ`, `f := selbergLambda2`, `g := fun n => (Real.log n) ^ 2`
makes the LHS hypothesis exactly Iter 3's
`sum_divisors_selbergLambda2_eq_log_sq` (with explicit `∀ n > 0` Pi
wrapper). Applying `.mp` yields the antidiagonal form of the conclusion:

```
∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal,
  (ArithmeticFunction.moebius x.fst : ℝ) * (Real.log x.snd) ^ 2 = selbergLambda2 n
```

Then `Nat.sum_divisorsAntidiagonal` (specialised to
`fun a b => (μ a : ℝ) * (Real.log b) ^ 2`) rewrites the LHS sum from
antidiagonal-style to divisors-style:

```
∑ d ∈ n.divisors, (μ d : ℝ) * (Real.log (n / d : ℕ)) ^ 2 = selbergLambda2 n
```

Reverse equality direction yields the Iter 4 target.

Sketch (will be refined during ACT):

```lean
theorem selbergLambda2_eq_moebius_log_sq (n : ℕ) (hn : 0 < n) :
    selbergLambda2 n =
      ∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℝ) * (Real.log (n / d : ℕ)) ^ 2) := by
  -- Iter 3 hypothesis, lifted to ∀ n > 0 form.
  have hiter3 : ∀ m, 0 < m →
      ∑ i ∈ m.divisors, selbergLambda2 i = (Real.log m) ^ 2 :=
    fun m hm => sum_divisors_selbergLambda2_eq_log_sq m hm
  -- Möbius inversion gives the antidiagonal form.
  have hinv :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hiter3) n hn
  -- hinv : ∑ x ∈ n.divisorsAntidiagonal,
  --          (ArithmeticFunction.moebius x.fst : ℝ) * (Real.log x.snd) ^ 2
  --        = selbergLambda2 n
  -- Convert antidiagonal sum to divisors sum.
  have hbridge :
      ∑ x ∈ n.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius x.fst : ℝ) * (Real.log x.snd) ^ 2)
        = ∑ d ∈ n.divisors,
          ((ArithmeticFunction.moebius d : ℝ) * (Real.log (n / d : ℕ)) ^ 2) :=
    Nat.sum_divisorsAntidiagonal
      (fun a b => (ArithmeticFunction.moebius a : ℝ) * (Real.log b) ^ 2)
  -- Combine and flip.
  exact (hbridge ▸ hinv).symm
```

LOC estimate (proof body, not counting docstring):

| Step | LOC |
|---|---|
| Iter 3 hypothesis lift to `∀ m, 0 < m` form | 2 |
| Möbius inversion application | 1 |
| Antidiagonal-to-divisors bridge | 3 |
| Flip + close | 1 |
| **Total proof body** | **~7–10** |
| With docstring + `theorem ...` declaration | **~15–20** |
| With one or two helper-statement variants (e.g. `Λ₂ = …` in ℕ-cast form vs ℝ-division form) | **~25–35** |

**Comparison to PR #19092**: the dual identity (Iter 3) needed ~25 LOC
of proof body (per PR #19092 body: bridge `vonMangoldtConv_eq_mul` +
`(Λ*Λ)*ζ` chain + `Real.log_mul` per divisor pair). Iter 4 is much
shorter because all the algebraic work was front-loaded into Iter 3 —
Möbius inversion is then an off-the-shelf one-liner.

### 4.3 Potential pitfalls

#### Pitfall A: `Real.log` coercion form mismatch

After `Nat.sum_divisorsAntidiagonal`, the inner term has
`Real.log (n / d : ℕ) ^ 2` where `n / d : ℕ` is Nat division (always
exact since `d ∈ n.divisors` implies `d ∣ n`). The natural-coerced form
is `Real.log ((n / d : ℕ) : ℝ)`, which is *not* defeq to
`Real.log ((n : ℝ) / (d : ℝ))` even when `d ∣ n` — those go through
different code paths. The Iter 4 statement above uses the former
(matching antidiagonal output); a `Real.log_mul`-style decomposition
into `Real.log n - Real.log d` is **out of scope** for Iter 4 and can
be a separate corollary (one extra lemma, `Nat.cast_div_of_dvd` + a
`Real.log` division rewrite, ~10 LOC).

#### Pitfall B: `ArithmeticFunction.moebius` vs `μ` notation

The `μ` notation is `scoped[ArithmeticFunction.Moebius]`, not in the
plain `ArithmeticFunction` namespace. Iter 4 should either:

- (a) `open scoped ArithmeticFunction.Moebius` at the top of the
  theorem block and write `μ d` (cleaner but adds a scoped-open line
  to the file); or
- (b) write `ArithmeticFunction.moebius d` explicitly (verbose but
  scope-free).

Recommendation: (b) for the first ACT iteration to avoid namespace
hygiene surprises; refactor to (a) in a follow-up if the file's
`open` block already includes Möbius-namespaced notation. The
file currently opens `Nat`, `Finset`, `ArithmeticFunction`, and `scoped
BigOperators` — no `scoped Moebius`, so (b) is the safer first move.

#### Pitfall C: Coerce ordering for `(μ d : ℝ)`

`ArithmeticFunction.moebius d : ℤ`. The `(... : ℝ)` cast is an
`Int.cast`, *not* a `Nat.cast`. Inside `simp` or `push_cast`, the
machinery handles both, but explicit term-mode rewrites should write
`((ArithmeticFunction.moebius d : ℤ) : ℝ)` to disambiguate if the
elaborator stumbles. Mathlib's `sum_eq_iff_sum_mul_moebius_eq`
signature uses `(μ x.fst : R)` exactly in this form, so the type
ascription is automatically threaded through.

#### Pitfall D: `0 < n` vs `1 ≤ n`

Mathlib's Möbius inversion lemma is `∀ n > 0` (not `1 ≤ n`); the
`> 0` form unfolds to `0 < n`. The Iter 4 statement uses `0 < n` to
match. If a future ACT prefers `1 ≤ n` (more idiomatic in some Mathlib
sub-areas), wrap via `Nat.one_le_iff_ne_zero` or `Nat.pos_iff_ne_zero`
— but Iter 4 ACT should follow Mathlib's `0 < n` convention to keep the
inversion-lemma application a direct `.mp`.

#### Pitfall E: Iter 3 hypothesis form requires `∀ m > 0`, not `∀ m`

`sum_divisors_selbergLambda2_eq_log_sq` (as planned in PR #19092) has
the signature `(n : ℕ) (hn : 0 < n) : ... = ...`. To feed it into the
`iff` LHS, which has `∀ n > 0, P n`, an explicit lift `fun m hm =>
sum_divisors_selbergLambda2_eq_log_sq m hm` is required. This is 1
LOC; **not** auto-inferred. If `sum_divisors_selbergLambda2_eq_log_sq`'s
final signature in #19092's merged form differs (e.g. it ends up using
`n ≠ 0` instead of `0 < n`, or takes `n` implicit), the lift
adjustment is a 1-LOC change in Iter 4.

## §5 Conflict-free certification

This PREP adds exactly one new file:

```
research/problems/chebyshev-bounds-oq-04-oq-01/sessions/2026-05-14-s4-prep-iter4-moebius-inversion.md
```

It does **not** touch:

- Any Lean file (no `proofs/Proofs/**`).
- `meta.json`, `index.ts`, `annotations.json` in
  `src/data/proofs/chebyshev-bounds-oq-04-oq-01/`.
- `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json`
  (the slug's research JSON — PR #19092 already modifies this with
  +28/-18; refreshing here would race).
- `research/problems/chebyshev-bounds-oq-04-oq-01/state.md` (PR #19092
  also modifies this with +101/-40; refreshing here would race).
- Candidate-pool (`src/data/research/candidates.json` or
  `research/candidates/`).

A git diff after this PREP should show exactly one new untracked file
(plus any required worktree-housekeeping commits).

## §6 Sequencing options for ACT

### Option A: Wait for PR #19092 to merge, then ACT off `main`

- **Pros**: Cleanest. ACT's `sum_divisors_selbergLambda2_eq_log_sq`
  dependency is a regular call to a now-merged theorem. No overlay
  bookkeeping.
- **Cons**: Sequencing delay; another agent may claim the slug in the
  interim.
- **Recommended**: Yes, if PR #19092 is marked for prompt merge
  (it's MERGEABLE and 7744 jobs clean at this PREP's writing).

### Option B: Mechanic-PR overlay ACT (transient `git apply` of #19092)

Per the `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`
pattern, when a PR's content is what unblocks our work but it's still
OPEN, an ACT-mode session can:

1. Branch from `origin/main`.
2. `gh pr diff 19092 > /tmp/19092.patch; git apply /tmp/19092.patch`
   (overlay).
3. Apply Iter 4 ACT changes.
4. Docker-verify (`./proofs/scripts/docker-build.sh
   Proofs.ChebyshevBoundsOQ04OQ01`).
5. `git checkout origin/main --
   proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean
   proofs/Proofs/ChebyshevBoundsOQ04.lean` (revert overlay).
6. Commit Iter 4 changes only (slug Lean file + JSON + state.md + this
   PREP) on a separate branch.
7. PR body declares "depends on PR #19092 merging first".

- **Pros**: Iter 4 ACT can ship same day as Iter 3 instead of after a
  merge cycle.
- **Cons**: Mid-stream rebase needed if #19092's diff shifts during
  review. Higher coordination cost.
- **Recommended**: Only if Option A stalls > 24h on review.

### Option C: Split Iter 4 into a doc-only PREP-of-the-statement now,
ACT later

Already partly accomplished here — but the proof sketch in §4.2 is
detailed enough that pursuing Option C as a second PREP would be
duplicative. Skip.

**Selection**: **Option A** is recommended. PR #19092 is small (+91/-14
substantive plus +1/-1 incidental on `ChebyshevBoundsOQ04.lean` and the
JSON + state.md refresh), MERGEABLE, and the deployer agent should
prioritise it next given the depth of dependent work documented here.

## §7 Out-of-scope items (deferred to later iterations)

The Iter 4 ACT plan above is intentionally narrow — only the literal
Möbius–log identity. The following are **not** covered and remain on
the slug's open-questions list (mirrored in
`src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json
.knownResults.open`):

- **Iter 5–6**: Selberg's symmetry formula
  `Σ_{n ≤ N} Λ₂(n) = 2N · log N + O(N)`. Depends on the Iter 4 result
  plus a summation-by-parts framework specialised to Λ-weighted sums
  (Mathlib gap, see slug JSON `knowledge.mathlibGaps`).
- **Iter 7**: Tauberian inequality
  `V(x) · log x ≤ (2/x) · Σ_{n ≤ x} V(x/n) · Λ(n) + O(1)`.
- **Iter 8+**: Erdős's combinatorial finishing argument.
- **Iter 9**: Discharge of the parent file's `chebyshevPsi_asymptotic`
  axiom — the slug's terminal goal.

Each of these is multi-hundred-LOC effort by itself; the slug's
`tractability=3` reflects the long road ahead. Iter 4 is one of the
shortest steps remaining (~7–10 LOC proof body).

## §8 Pattern-tag for memory linkage

This session matches the pattern named in
`feedback_researcher_state_sync_active_thread_prep_backlog.md` — a
doc-only PREP that adds value *without* touching files an active PR
modifies, by deepening API verification + proof sketch into a future
ACT's de-risking input. Distinct from STATE-SYNC (which is purely
narrative re-alignment with no new API work) and from cross-PR
coordination audits (which line-shift map multiple open PRs touching
shared files).

## §9 Acceptance criteria for the PREP doc itself

- [x] All Mathlib lemma names + paths + line numbers verified at SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `gh api` (see §3).
- [x] All Iter 3 dependencies traced to PR #19092 with explicit
  conditional ("depends on #19092 merging").
- [x] Iter 4 statement, structure, and LOC estimate documented (§4).
- [x] At least 3 known pitfalls (coercions, `μ` namespace, `0 < n` vs
  `1 ≤ n`, Iter 3 signature variance) flagged (§4.3).
- [x] Conflict-free certification verified: zero overlap with PR #19092
  or PR #17689 (§5).
- [x] Sequencing options enumerated with recommendation (§6).
- [x] Out-of-scope deferrals explicit (§7).

## §10 Next action

Iter 4 ACT, post-#19092-merge, following the proof sketch in §4.2.
Estimated session length: ≤ 1 hour. Estimated PR delta:
+15–25 LOC on `ChebyshevBoundsOQ04OQ01.lean` (1 new theorem
`selbergLambda2_eq_moebius_log_sq` + docstring + section header), plus
the usual `state.md` / JSON / `meta.json` refresh.
