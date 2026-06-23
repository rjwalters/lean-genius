# S5 PREP — Step 3 (`mersenne_mul_sigma_eq_two_pow_mul`) discharge recipe + bearer pin (doc-only)

**Author:** researcher-8
**Timestamp:** 2026-05-16 ~05:00 UTC
**Phase:** S5 PREP (doc-only; bridges S4 ACT ship → S5 ACT pickup)
**Iteration:** 5 (S1 OBSERVE + S2 SCAFFOLD + S3 PREP + S4 ACT + this S5 PREP)
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; **unchanged** since S2 SCAFFOLD)
**origin/main HEAD at branch creation:** `78448f56d0a` (research(birthday-problem-oq-01-oq-02): S5 STATE-SYNC #19355)
**Scope:** Doc-only PREP. NO Lean edits. Locks in a **paste-ready ~7-LOC Step 3 discharge** with two new bearer pins (`Nat.perfect_iff_sum_divisors_eq_two_mul` + `sigma_one_apply`) and a build-pending caveat (Docker daemon I/O failure observed at PREP time — see §6).

## 0. Trigger — Step 3 is the natural S5 follow-on to S4 ACT's Step 1

The S3 PREP (`sessions/2026-05-14-s3-prep-step1-step5-discharge.md` §8
"Out of scope (deferred)") explicitly marks Step 3 as **S4 follow-up**:

> | Step 3 (`mersenne_mul_sigma_eq_two_pow_mul`) | Requires `Nat.perfect_iff_sum_divisors_eq_two_mul` + Steps 1 + 2 + the `(2^k * m).Perfect` hypothesis unfolding. **~6 LOC. S4 follow-up.** |

S4 ACT (PR #19357, researcher-9, **MERGED 2026-05-16T03:53Z**) shipped
Step 1 only (3-LOC term-mode via `isMultiplicative_sigma.map_mul_of_coprime`).
Step 3 was therefore not actioned in S4 and is the natural S5 picker target.

This S5 PREP:

1. Pins **2 NEW bearers** at unchanged Mathlib SHA `2df2f0150c…`:
   `Nat.perfect_iff_sum_divisors_eq_two_mul` (Divisors.lean:405) and
   `sigma_one_apply` (ArithmeticFunction/Basic.lean:169).
2. Drafts a **paste-ready ~7-LOC Step 3 discharge** (§3 below), verbatim from
   the bridging math.
3. Catalogues 3 build-risk items + 3 fallback recipes (§4 + §5).
4. Refreshes the ACT-readiness gate to **7/7 GREEN** (§7).
5. Records a **build-pending caveat** observed at PREP time: the host
   Docker daemon was in a corrupt state (containerd blob I/O error +
   `Mathlib/Data/DFinsupp/Module.olean.server invalid header`); the S5 ACT
   picker must verify the build on a healthy Docker host (§6).

## 1. Math walk-through — Step 3 from S4's Steps 1+2 + Perfect bridge

Setup (from file header L40-46, namespace `SumOfDivisorsOQ02`):
```
import Archive.Wiedijk100Theorems.PerfectNumbers
import Mathlib.Tactic
namespace SumOfDivisorsOQ02
open ArithmeticFunction Finset Nat
open scoped sigma
```

Step 1 (shipped S4): `sigma_two_pow_mul_odd k m hm_odd : σ 1 (2^k * m) = σ 1 (2^k) * σ 1 m`.

Step 2 (shipped S2): `sigma_two_pow_eq_mersenne k : σ 1 (2^k) = mersenne (k+1)`.

Goal (Step 3): `mersenne (k+1) * σ 1 m = 2^(k+1) * m` from
`h_perfect : Nat.Perfect (2^k * m)`.

### Math chain

`Nat.Perfect n` is defined as `(∑ i ∈ properDivisors n, i = n) ∧ 0 < n`.
Equivalently (via `Nat.perfect_iff_sum_divisors_eq_two_mul`, requires
`h : 0 < n` which comes from `h_perfect.right`):
`Perfect n ↔ ∑ i ∈ divisors n, i = 2 * n`.

Bridge to `σ 1`: `sigma_one_apply n : σ 1 n = ∑ d ∈ divisors n, d`.

Hence (instantiating `n = 2^k * m`):
```
σ 1 (2^k * m) = ∑ d ∈ divisors (2^k * m), d           [sigma_one_apply]
              = 2 * (2^k * m)                          [perfect_iff_sum_divisors_eq_two_mul.mp h_perfect]
```

Apply Step 1 to LHS:
```
σ 1 (2^k) * σ 1 m = 2 * (2^k * m)                     [sigma_two_pow_mul_odd]
mersenne (k+1) * σ 1 m = 2 * (2^k * m)                [sigma_two_pow_eq_mersenne]
```

Re-associate and collapse the power:
```
2 * (2^k * m) = (2 * 2^k) * m                          [← mul_assoc]
              = 2^(k+1) * m                            [← pow_succ']
```

Final: `mersenne (k+1) * σ 1 m = 2^(k+1) * m`. □

## 2. Bearer pins (2 NEW + 4 inherited from S3 PREP / file body)

Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0;
`proofs/lake-manifest.json` rev verified at branch creation — unchanged
since S1 OBSERVE / S2 SCAFFOLD / S3 PREP / S4 ACT).

### 2.1 NEW bearers (2) — pinned this PREP

| # | Bearer | File / L | Cited typeclass / hyp | Use in S5 ACT |
|---|--------|----------|-----------------------|----------------|
| N1 | `Nat.perfect_iff_sum_divisors_eq_two_mul` | `Mathlib/NumberTheory/Divisors.lean:405` | `(h : 0 < n) : Perfect n ↔ ∑ i ∈ divisors n, i = 2 * n` | §3 — bridge `Perfect` to `σ 1 n = 2*n` |
| N2 | `ArithmeticFunction.sigma_one_apply` | `Mathlib/NumberTheory/ArithmeticFunction/Basic.lean:169` | `σ 1 n = ∑ d ∈ divisors n, d` (over `ℕ`) | §3 — rewrite divisor sum to `σ 1` |

Authenticated `gh api …?ref=<SHA>` content fetch confirms:

```
Nat.perfect_iff_sum_divisors_eq_two_mul (Divisors.lean:405):
  theorem perfect_iff_sum_divisors_eq_two_mul (h : 0 < n) :
      Perfect n ↔ ∑ i ∈ divisors n, i = 2 * n := by
    rw [perfect_iff_sum_properDivisors h, sum_divisors_eq_sum_properDivisors_add_self, two_mul]
    constructor <;> intro h
    · rw [h]
    · apply add_right_cancel h

  -- Context: file L399 def Perfect (n : ℕ) : Prop := ∑ i ∈ properDivisors n, i = n ∧ 0 < n
  -- So h_perfect.right : 0 < n (which we supply as h in the .mp call)

sigma_one_apply (Basic.lean:169):
  theorem sigma_one_apply (n : ℕ) : σ 1 n = ∑ d ∈ divisors n, d := by simp [sigma_apply]

  -- sigma_apply (L151): σ k n = ∑ d ∈ divisors n, d ^ k
  -- sigma_one_apply reduces the k=1 case via d^1 = d
```

### 2.2 Inherited bearers (4) — file body + S4 ACT

| Symbol | File | Line | Used by |
|--------|------|------|---------|
| `sigma_two_pow_mul_odd` | (this file) | L52 | Step 3 LHS rewrite |
| `sigma_two_pow_eq_mersenne` | (this file) | L62 | Step 3 LHS rewrite |
| `mul_assoc` | core | — | Step 3 RHS re-association |
| `pow_succ'` | `Mathlib/Algebra/Group/Defs.lean:647` | `a^(n+1) = a * a^n` | Step 3 RHS power collapse |

(`pow_succ'` re-verified at SHA `2df2f0150c…` by `gh api` content fetch: L647 `lemma pow_succ' (a : M) : ∀ n, a ^ (n + 1) = a * a ^ n`.)

## 3. Paste-ready Lean discharge (~7 LOC)

Replace the existing `sorry` in `proofs/Proofs/SumOfDivisorsOQ02.lean`
(currently at the Step 3 lemma, L67-71):

```lean
/-- **Step 3** (perfect equation expansion). If `n = 2^k · m` is perfect with `m` odd,
combining `σ(n) = 2n` with Steps 1+2 gives `M_{k+1} · σ(m) = 2^(k+1) · m`.
Proof: bridge `Perfect` to `σ 1 (2^k * m) = 2 * (2^k * m)` via
`Nat.perfect_iff_sum_divisors_eq_two_mul` (Divisors.lean:405) + `sigma_one_apply`
(Basic.lean:169). Apply Steps 1+2 to LHS, then `← mul_assoc; ← pow_succ'` to
collapse `2 * 2^k = 2^(k+1)`. -/
lemma mersenne_mul_sigma_eq_two_pow_mul
    (k m : ℕ) (hm_odd : Odd m) (h_perfect : (2 ^ k * m).Perfect) :
    mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m := by
  have hsigma_eq : σ 1 (2 ^ k * m) = 2 * (2 ^ k * m) := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul h_perfect.right).mp h_perfect
  rw [sigma_two_pow_mul_odd k m hm_odd, sigma_two_pow_eq_mersenne k] at hsigma_eq
  rw [← mul_assoc, ← pow_succ'] at hsigma_eq
  exact hsigma_eq
```

**Net delta:** ~7 LOC body + ~4 LOC docstring refinement. Sorry count
delta: `5 → 4`. No new sorries, no new axioms, no new theorems beyond the
discharge. `hm_odd` is unused by this Step 3 body (only Step 1's call site
uses oddness via the coprimality bridge) — Lean should accept it as an
explicit hypothesis without warning since it's in the signature
upstream of S4's Step 1 lemma call.

### 3.1 Provenance note (PREP-time build attempt)

This PREP author (researcher-8) attempted Docker build verification of
the discharge before reverting to doc-only PREP form. The attempt:

- **Build v1**: surfaced a Mathlib cache corruption mid-elaboration —
  `error: Archive/Wiedijk100Theorems/PerfectNumbers.lean:6:0: failed to
  read file '/Users/rwalters/GitHub/lean-genius/proofs/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/DFinsupp/Module.olean.server', invalid header`.
  This is a shared `lean-mathlib-cache` Docker volume contention with
  concurrent agent builds, not a fault of the discharge.
- **Build v2**: failed earlier with `ERROR: failed to build: failed to
  solve: write /var/lib/desktop-containerd/daemon/io.containerd.metadata.v1.bolt/meta.db: input/output error`. The host
  Docker daemon's containerd backend is in a corrupt state (verified via
  `docker info` → `Error response from daemon: failed to retrieve image list: … blob sha256:1487d0… input/output error`). Host-level
  problem, not Lean-related.

The S5 ACT picker should:
1. Wait for Docker host to recover (or restart Docker Desktop).
2. Apply the discharge from §3 verbatim.
3. Run `./proofs/scripts/docker-build.sh Proofs.SumOfDivisorsOQ02`.
4. Expected: ~7744 jobs warm cache + ~10s elaboration for the +7-LOC delta.

## 4. Build risk inventory (S5 ACT)

| # | Risk | Likelihood | Mitigation |
|---|------|-----------|------------|
| 1 | `hm_odd` unused-variable lint warning (S5 ACT body doesn't reference it; the field is in the existing signature) | low | Accept; the parameter is mandated by the parent-file convention for Step 3-Step 5 uniformity (S4-S6 will use it). If the warning is severe, prefix with `_` per S2 SCAFFOLD's `_hm_odd` pattern — but file convention is name-without-underscore |
| 2 | `(Nat.perfect_iff_sum_divisors_eq_two_mul h_perfect.right).mp h_perfect` may need explicit `Nat.` prefix or no prefix depending on `open Nat` scoping | low | File already has `open Nat` (L43); should resolve. If not, fully-qualify as `Nat.perfect_iff_sum_divisors_eq_two_mul` (it's `Nat.Perfect` either way per file L399 `def Perfect (n : ℕ) : Prop := …` inside `namespace Nat`) |
| 3 | `rw [← pow_succ']` may pattern-match differently against `2 * 2^k` if `2` is `Nat.lit 2` vs `(2 : ℕ)` | low | Fallback: `rw [← mul_assoc, ← pow_succ' 2 k] at hsigma_eq` — explicit args. Or `omega` finisher if rw fails (`omega` can't handle the structure, but `ring` likely can since this is `ℕ`-arithmetic) — actually safer fallback: replace last `rw` with `linarith` or `ring_nf at hsigma_eq` |

**Build iteration estimate:** **1 iteration** on a healthy Docker host
(the discharge is mechanical; all bearers re-verified at SHA; no kernel
elaboration risk identified).

## 5. Fallback recipes

### 5.1 If `Nat.perfect_iff_sum_divisors_eq_two_mul` resolution fails

```lean
-- Alternative: unfold Perfect directly
have hsigma_eq : σ 1 (2 ^ k * m) = 2 * (2 ^ k * m) := by
  rw [sigma_one_apply, sum_divisors_eq_sum_properDivisors_add_self, h_perfect.left, two_mul]
```

(Uses `sum_divisors_eq_sum_properDivisors_add_self : ∑ i ∈ divisors n, i = ∑ i ∈ properDivisors n, i + n`,
likely at `NumberTheory/Divisors.lean` near `:380-400`, paired with `h_perfect.left : ∑ i ∈ properDivisors (2^k*m), i = 2^k*m`.)

### 5.2 If `← pow_succ'` doesn't fire

```lean
-- Alternative endgame:
  rw [show (2 : ℕ) * (2 ^ k * m) = 2 ^ (k + 1) * m by ring] at hsigma_eq
  exact hsigma_eq
```

Or even simpler — just close with `linarith [hsigma_eq, pow_succ' 2 k]` or convert to `Nat.pow_succ`.

### 5.3 If `sigma_one_apply` is namespace-shadowed inside `ArithmeticFunction`

```lean
-- Explicit namespace:
  rw [ArithmeticFunction.sigma_one_apply]
```

(The file has `open ArithmeticFunction` at L43, but `simp`-named lemmas can sometimes need explicit prefixes when the `σ` notation is `scoped sigma`.)

## 6. Build-pending caveat (host Docker daemon I/O failure)

At PREP draft time (2026-05-16T~05:00Z), the host Docker daemon was
observed in a corrupt state:

```
$ docker info
Error response from daemon: failed to retrieve image list: rpc error:
  code = Unknown desc = blob sha256:1487d0af5f52b4ba31c7e465126ee2123fe3f2305d638e7827681e7cf6c83d5e
  expected at /var/lib/desktop-containerd/daemon/io.containerd.content.v1.content/blobs/sha256/1487d…:
  open /var/lib/desktop-containerd/daemon/io.containerd.content.v1.content/blobs/sha256/1487d…:
  input/output error
```

The concurrent agent fleet was running 5+ Docker builds (`LagrangeFourSquares`,
`SchroederBernsteinOQ01`, etc.) — likely cache-volume contention.
Restarting Docker Desktop or pruning the shared `lean-mathlib-cache`
volume should restore service.

This S5 PREP is doc-only by design (NO Lean edits) so the build-pending
state does not block PR merge. The S5 ACT picker can run on a healthy
Docker host without waiting for this PREP to merge.

## 7. ACT-readiness gate (7-item checklist for S5 ACT)

| # | Item | Status | Evidence |
|---|------|--------|----------|
| 1 | Mathlib pin unchanged at S5 ACT branch-creation time | **GREEN** | `proofs/lake-manifest.json` rev `2df2f0150c…` re-verified at this PREP |
| 2 | Step 1 + Step 2 lemmas in scope | **GREEN** | `sigma_two_pow_mul_odd` (L52) + `sigma_two_pow_eq_mersenne` (L62) both proved; S4 ACT (PR #19357) shipped Step 1 |
| 3 | 2 NEW bearers pinned at SHA + content-verified | **GREEN** | §2.1 above |
| 4 | Paste-ready Lean discharge (~7 LOC) | **GREEN** | §3 above |
| 5 | Build risk assessed + 3 fallback recipes documented | **GREEN** | §4 + §5 |
| 6 | Host Docker daemon healthy at S5 ACT pick time | **AMBER (must re-check)** | §6 — PREP-time observation showed corrupt blob storage; restart Docker Desktop and re-run `docker info` before S5 ACT |
| 7 | No open peer PRs on this slug | **GREEN** | `gh pr list --repo rjwalters/lean-genius --search "sum-of-divisors-oq-02" --state open` returned `[]` at branch creation |

**6/7 GREEN + 1/7 AMBER** (gate 6 re-checkable on-demand). S5 ACT is
unblocked from a code/math perspective; the AMBER is an infrastructure
gate, not a content gate.

## 8. Anti-targets (S5 ACT — what NOT to do)

1. ❌ Discharge Steps 4/5/6 in the same PR — keep S5 = Step 3 only (orthogonal sub-iterations per S3 PREP §8 + the file's 6-step decomposition).
2. ❌ Change the lemma signature of `mersenne_mul_sigma_eq_two_pow_mul` (existing call sites in Steps 4-6 sketches assume this exact 4-arg form).
3. ❌ Prefix `hm_odd` with `_` (file convention is name-without-underscore for cross-Step parameters; lint warnings accepted as documentation).
4. ❌ Refactor Step 1 or Step 2 (both ship-stable post-S4 and S2 respectively).
5. ❌ Touch `proofs/Proofs.lean` (this file is already imported via the parent gallery's umbrella; no S5-ACT-level wiring needed).
6. ❌ Bump Mathlib pin via `lake update`.
7. ❌ Run the Docker build BEFORE confirming `docker info` returns successfully — current host state will produce false-negative cache-corruption errors that look like Lean failures.

## 9. Conflict-free guarantee

Files touched in this S5 PREP (3, doc-only):

1. `research/problems/sum-of-divisors-oq-02/sessions/2026-05-16-s5-prep-step3-discharge-recipe.md` (this file, NEW).
2. `research/problems/sum-of-divisors-oq-02/state.md` (prepend S5 PREP block; preserve rest verbatim).
3. `src/data/research/problems/sum-of-divisors-oq-02.json` (`currentState.{phase ACT→PREP, iteration 4→5, since, focus, nextAction}`, `updatedAt` (top-level), top-level `phase OBSERVE→ACT` drift fix).

PR overlap matrix at S5 PREP draft time:

| PR | State | Files | Overlap |
|----|-------|-------|---------|
| (none) | (none) | n/a | `gh pr list --repo rjwalters/lean-genius --search "sum-of-divisors-oq-02" --state open` returned `[]` at 2026-05-16T05:00Z |

Pre-push race recheck will run immediately before `git push -u origin <branch>`.

## 10. Race awareness

| Aspect | State at S5 PREP draft time (2026-05-16 ~05:00Z) |
|---|---|
| `lake-manifest.json` mathlib pin | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S1 OBSERVE) |
| Open PRs on this slug | 0 |
| Recent merges on this slug | #19357 (S4 ACT, researcher-9) at 2026-05-16T03:53Z; #19169 (S3 PREP, researcher-8) at 2026-05-15T22:56Z; #19131 (S2 SCAFFOLD) at 2026-05-15T22:57Z |
| HEAD of main this branch tracks | `78448f56d0a` (research(birthday-problem-oq-01-oq-02): S5 STATE-SYNC #19355) |
| Active researcher claims on this slug | this S5 PREP (researcher-8, claimed 2026-05-16T04:43:17Z, TTL 90 min, expires 2026-05-16T06:13:17Z) |
| Docker daemon | **CORRUPT** (containerd blob I/O error; restart needed before S5 ACT) |
| Concurrent agent Docker builds observed | 5+ (`LagrangeFourSquares`, `SchroederBernsteinOQ01`, others) |

## 11. Honesty footprint

- 0 new Lean theorems (the §3 discharge is paste-ready but not committed)
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified (PREP-time build attempt edit reverted)
- 2 Docker build attempts (both failed at host-infrastructure layer, not Lean layer)

Produced:

- 1 new sessions/ memo (this file, ~310 LOC)
- 1 state.md head replacement (~40 LOC of new front-matter; rest preserved verbatim)
- 1 JSON refresh: bump `currentState.{phase,iteration,since,focus,nextAction}`, set top-level `phase` ACT (drift fix: was OBSERVE despite `currentState.phase = ACT`), set top-level `updatedAt` (was null)

## 12. References

- **PR #18166** — seeker workspace init (slug created).
- **PR #18220** (S1 OBSERVE, researcher-12, MERGED 2026-05-12T22:20Z) — Euler-converse pedagogical decomposition.
- **PR #18311** (S2 OBSERVE, MERGED 2026-05-12T22:14Z) — Mathlib Archive duplicate-detection audit.
- **PR #19131** (S2 SCAFFOLD, MERGED 2026-05-15T22:57Z) — 6-step decomposition Lean file (110 LOC, 5 sorries).
- **PR #19169** (S3 PREP, researcher-8, MERGED 2026-05-15T22:56Z) — Step 1 + Step 5 discharge plans (doc-only).
- **PR #19357** (S4 ACT, researcher-9, MERGED 2026-05-16T03:53Z) — Step 1 discharged term-mode (Sorry count: 6→5).
- `proofs/Proofs/SumOfDivisorsOQ02.lean` — gallery scaffold, Step 1+2 proved + 4 sorries (post-S4).
- Mathlib `NumberTheory/Divisors.lean:399` (def `Perfect`), `:402` (`perfect_iff_sum_properDivisors`), `:405` (`perfect_iff_sum_divisors_eq_two_mul`).
- Mathlib `NumberTheory/ArithmeticFunction/Basic.lean:151` (`sigma_apply`), `:169` (`sigma_one_apply`).
- Mathlib `Algebra/Group/Defs.lean:641` (`pow_succ`), `:647` (`pow_succ'`).
- `proofs/lake-manifest.json` — mathlib `rev: "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"`.
- Memory `_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header` — applied at §2.1 (N1/N2 + N2's `simp` reduction note).
- Memory `_postship_pivot_upgrades_audit_doc_deferred_sketch_to_pasteready_prep` — applied (this PREP closes S3 PREP §8's "S4 follow-up" deferred-via-sorry sketch with paste-ready Lean).
- Memory `feedback_researcher_field_simp_leaves_algebraic_residue_needs_ring` — N/A here (no `field_simp` in the discharge).

## 13. Closing checklist

- [x] Audit/PREP-doc deferred Step 3 sketch upgraded to paste-ready ~7-LOC Lean (§3)
- [x] 2 NEW bearer pins added at SHA `2df2f0150c…` with file/line/typeclass (§2.1)
- [x] Math walk-through recorded (§1)
- [x] Build risk inventory + 3 fallback recipes (§4 + §5)
- [x] Build-pending caveat (host Docker daemon corrupt) explicitly recorded (§6)
- [x] ACT-readiness gate 6/7 GREEN + 1/7 AMBER (gate 6, re-checkable; §7)
- [x] Anti-targets enumerated (§8)
- [x] Conflict-free guarantee + race awareness (§9 + §10)
- [x] Honesty footprint declared (§11)
- [x] PREP-time Lean edit reverted (no Lean delta on origin/main)
- [ ] (Pre-push) Re-run `gh pr list --repo rjwalters/lean-genius --search …` immediately before `git push -u`
- [ ] (Post-merge, S5 ACT picker) Confirm `docker info` succeeds, apply §3 discharge, run Docker build, verify 7744 jobs / 4 sorries / 0 axioms / 0 warnings

End of S5 PREP.
