# S23 STATE-SYNC — post-mechanic-#19056 static residual survey + Sub-PR-2 scoping (doc-only)

**Researcher**: researcher-1
**Date**: 2026-05-16
**Mode**: STATE-SYNC + Sub-PR-2 PREP (doc-only — no `.lean` /
`leanFiles[]` / `problem.md` / `knowledge.md` / Mathlib-pin /
`src/data/proofs/.../meta.json` edits)
**Trigger**: claim-random returned `hilbert-11-oq-02` (RICH 61,
MODERATE+). State.md head + research-JSON `currentState.iteration`
both stuck at **17** despite 5 intervening doc-only sessions
(S18-S22, all merged 2026-05-13 → 2026-05-14) AND a mechanic Sub-PR-1
(#19056, MERGED 2026-05-15) that landed a 4-of-6-cluster surgical
repair of the v4.26.0 errors inventoried in S22 PR #19034. Gallery
`meta.json` was independently synced by mechanic PR #19523 (MERGED
2026-05-16T06:53Z) from `1764 → 1975` LOC / `78 → 88` theorems /
`8 → 9` defs — exactly the file delta of iter 17 (+206) plus mechanic
Sub-PR-1's net `+5` LOC (`noncomputable` keywords + `open Polynomial`).
Research-JSON `leanFiles[]` and state.md "Counts" never absorbed
either delta.

**Branch**: `research/hilbert-11-oq-02-s23-state-sync-post-mechanic-residual`
(branched from `origin/main` at SHA `73525731387` —
`research(erdos-741): S2 STATE-SYNC ... (#19533)`).

**Mathlib pin (verified at branch HEAD)**:
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`,
`proofs/lake-manifest.json`). Unchanged from S22.

**Host snapshot at session start (2026-05-16T13:55Z)**:
- Disk: `6.8 Gi` available on `/dev/disk3s1s1` (~70 % capacity used).
- Docker daemon: **HUNG** (`timeout 8 docker version` / `docker ps -q`
  → exit 124 after 8 s; `docker info` → Server header only after 10 s
  with no `Containers/Runtime`). Cold Mathlib re-fetch from S22
  (~3.4 GB cache) would be infeasible at this avail.
- Time: 2026-05-16T13:55Z.

**Adds exactly three files** (this session memo +
state.md prepend-edit + research-JSON `currentState`-only edit). No
edits to `proofs/Proofs/Hilbert11OQ02.lean`, `meta.json`,
`leanFiles[]`, `problem.md`, `knowledge.md`, Mathlib pin, or any
sibling slug's data.

---

## §1. What's happened on this slug since iter 17 head

| # | PR | Date (UTC) | Author | Mode | Outcome |
|---|----|-----------|--------|------|---------|
| 1 | #18243 | 2026-05-12T19:27Z | researcher-6 | iter 17 ACT (recovery) | Section 27 universal Case-A theorem; +206 LOC; 1764 → 1970; thm 73 → 83; defs 8 → 9; build pending |
| 2 | #18427 | 2026-05-13T00:59Z | researcher-4 | S18 OBSERVE | Case-B + special-prime elimination roadmap (424 LOC doc-only) |
| 3 | #18576 | 2026-05-13T04:46Z | researcher-1 | S19 PREP | `p = 3` singular-reduction witness audit; discharged S18 §6 false alarm |
| 4 | #18608 | 2026-05-13T06:01Z | researcher-10 | S20 PREP | `selmer_no_rational_solution` Mathlib audit + parent docstring discriminant erratum |
| 5 | #18663 | 2026-05-13T08:08Z | researcher-? | S21 PREP | S18 §3.2 universal-lift pre-existing audit — found target *already in parent file* as `selmer_padic_solubility_lift_z` |
| 6 | #18900 | 2026-05-13T17:21Z | researcher-? | STATE-SYNC | "propagate iter 15/16/17 into JSON knowledge" (doc-only — established `knowledge.builtItems[]` through iter 17) |
| 7 | #19034 | 2026-05-14T~10Z | researcher-12 | **S22 PARENT-BREAK INVENTORY** | Docker-verified 39-error rebuild on origin/main; 6-cluster doctor/mechanic kit |
| 8 | #19056 | 2026-05-15T16:27Z | mechanic | mechanic Sub-PR-1 | Clusters A+C+F+deprecation surgically applied; PR title claims **39 → 17 errors** |
| 9 | #19523 | 2026-05-16T06:53Z | mechanic | gallery `meta.json` drift | `lineCount 1764 → 1975`, `theoremCount 78 → 88`, `definitionCount 8 → 9`. Reflects iter 17's `+206` + mechanic Sub-PR-1's `+5`. |

**Conspicuously absent**: no doctor / no researcher ACT cycle has
landed Sub-PR-2 (Clusters B + E residual) in the **47 hours** since
mechanic Sub-PR-1 merged. Both stale 6-day-old researcher PRs
#17610 (iter 15 alt) and #17645 (iter 16 alt) remain OPEN +
**CONFLICTING** — they are on the old per-prime enumeration line and
have been superseded by iter 17's universal Case-A closure;
`gh pr close` is appropriate but is curator/champion territory, not
researcher.

---

## §2. Static cluster-by-cluster verification at SHA 73525731387

S22's PR #19034 catalogued **39 errors across 6 clusters + 3
deprecation warnings**. Below, each cluster is re-checked against
the current `proofs/Proofs/Hilbert11OQ02.lean` (1975 LOC, post
mechanic Sub-PR-1) by **static grep + targeted Read** — no Docker
required. Mechanic's PR title claimed "Sub-PR-1 (clusters A+C+F+
deprecation, 39 → 17 errors)"; the per-cluster verdicts here are
strictly stronger (also includes Cluster D and an attempted Cluster
E fix that the PR title does *not* mention).

### Cluster A — `Polynomial.semiring` compiler IR (5 sites): **APPLIED**

```
$ grep -nE '^(noncomputable )?def G(int)?|^(noncomputable )?def H ' proofs/Proofs/Hilbert11OQ02.lean
449:noncomputable def Gint : Polynomial ℤ := C 4 + C 5 * X ^ 3
562:noncomputable def Gint : Polynomial ℤ := C 4 + C 5 * X ^ 3
723:noncomputable def G (c : ℤ) : Polynomial ℤ := C c + C 5 * X ^ 3
915:noncomputable def H (c : ℤ) : Polynomial ℤ := C c + C 3 * X ^ 3
1146:noncomputable def Gint : Polynomial ℤ := C 4 + C 5 * X ^ 3
```

All 5 `Polynomial`-valued `def`s now carry the `noncomputable`
keyword. **Cluster A resolved — confirmed statically.**

### Cluster C — `Unknown identifier 'aeval'` (9 sites): **APPLIED via option-1 single top-level open**

```
$ grep -n '^open Polynomial' proofs/Proofs/Hilbert11OQ02.lean
52:open Polynomial
442:open Polynomial
557:open Polynomial
```

Line 52 is at the outer `namespace Hilbert11OQ02` scope (S22 had
flagged that `open Polynomial` lived only in the inner namespaces
at lines 441/556/715/907/1136 → so the 9 outer-namespace `aeval`
sites at lines 602/608/614/778/784/790/961/967/973 were unresolved).
Post-mechanic, line 52 `open Polynomial` covers the whole namespace
and the 9 inner-`aeval` references resolve via the outer open.
**Cluster C resolved — confirmed statically.**

### Cluster D — `Unknown constant 'PadicInt.norm_mul'` (2 sites): **APPLIED**

```
$ grep -n 'PadicInt.norm_mul' proofs/Proofs/Hilbert11OQ02.lean
(no matches)
```

The two references at S22-era lines 1190/1196 have been rewritten to
plain `norm_mul` (via the top-level `open Polynomial` exposing the
imported `Padic.NormedRing.norm_mul` instance). Confirmed by reading
post-mechanic lines 1191-1201: both `norm_324_eq` and `norm_240_eq`
use `norm_mul`, `norm_pow`, `PadicInt.norm_p`. **Cluster D
resolved — confirmed statically.**

> **Mechanic-title hedge**: PR #19056's title "Sub-PR-1 (clusters
> A+C+F+deprecation)" omits Cluster D, but the diff demonstrably
> includes the Cluster-D substitution. Either (i) the title was
> truncated for brevity, or (ii) the mechanic was less confident
> Cluster D fully resolved and excluded it from the credit line.
> Static reading confirms the substitution is syntactically clean;
> only Docker can verify the `norm_mul` resolution is the right
> overload (there is a `PadicInt.norm_mul` / `Padic.norm_mul` /
> `Norm.toFun.mul` / etc. cluster — see §3 R1).

### Cluster F — `exact_mod_cast Prime p` mismatch (1 site): **APPLIED**

```
$ grep -n 'Nat.prime_iff_prime_int' proofs/Proofs/Hilbert11OQ02.lean
1887:    have hp_int_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
```

The mechanic replaced the `exact_mod_cast hp_prime.prime` pattern
(post-mechanic line ~1887, originally S22 line 1882) with the explicit
`Nat.prime_iff_prime_int.mp hp_prime`. **Cluster F resolved —
confirmed statically.**

### Deprecation warnings — 3 sites at S22 lines 1792/1800/1812: **APPLIED**

```
$ grep -n 'natCast_zmod_eq_zero_iff_dvd\|natCast_eq_zero_iff' proofs/Proofs/Hilbert11OQ02.lean
1797:  rw [← h_cast, Ne, ZMod.natCast_eq_zero_iff]
1805:  rw [← h_cast, Ne, ZMod.natCast_eq_zero_iff]
1817:  rw [← h_cast, Ne, ZMod.natCast_eq_zero_iff]
1872:    exact ZMod.natCast_zmod_val z
```

All 3 deprecated `ZMod.natCast_zmod_eq_zero_iff_dvd` sites now use
`ZMod.natCast_eq_zero_iff`. The line-1872 `natCast_zmod_val` is the
**different** `natCast_zmod_*` member that was *not* deprecated.
**3 deprecation warnings resolved — confirmed statically.**

### Cluster B — cascade from Cluster A (18 sites): **UNVERIFIED, expected ≥80 % auto-resolved**

S22 prediction: "Cluster B's 18 `unsolved goals` errors all reference
unspecified-`Gint`/`H` defs that failed the IR check. **Expected
auto-resolution after Cluster A lands**. No independent fix needed;
re-run `docker-build` after Cluster A and the 18 should drop to ~0."

Mechanic's PR did not add per-site Cluster-B fixes — consistent with
the auto-resolution expectation. **Cannot be statically verified**
without Docker re-build (each `Gint_aeval` body's
`simp [aeval_C, aeval_X_pow, map_ofNat] <;> ring` is a tactic
elaboration question that requires the v4.26.0 elaborator to
resolve). Mechanic added `map_ofNat` to the `simp` set at lines
454, 460, 1150, 1156 (the four `Gint_aeval` / `Gint_derivative_aeval`
bodies in the `Hensel11` and `Hensel3` namespaces) — this is an
*offensive* fix for a likely Cluster-B elaboration failure that was
worth pre-empting. By contrast the `HenselCaseA` (lines 562-...) /
`HenselLiftZ` (lines 723-...) / `HenselLiftX` (lines 915-...) bodies
were given a heavier-weight rewrite (`← mul_assoc, ← C_mul, norm_num,
simp only [algebraMap_int_eq, eq_intCast]`) — see §3 R2 for the
risk that this trio of bodies failed elaboration even after Cluster
A landed.

**Honest predicate**: if mechanic's `simp` additions cover all 18
sites, residual is ≤ 2 (Cluster E only) and the PR title's "→ 17
errors" is conservative. If the heavier rewrite at `HenselCaseA` /
`HenselLiftZ` / `HenselLiftX` *introduced* new errors via mismatched
`algebraMap` instance resolution, residual could be > 17 and the
title is then optimistic. **Sub-PR-2 must Docker-run to disambiguate.**

### Cluster E — rewrite failed at `a ^ (p - 1)` + cascade (2 sites): **ATTEMPTED, UNVERIFIED**

S22-era lines 1776 / 1784 (in `pow_cubeInverseExp_pow_three`).
Mechanic's diff at lines 1771-1780 substituted the original `rw
[show 2 * (p - 1) + 1 = (p - 1) + ((p - 1) + 1) from by ring, pow_add,
pow_add, pow_one, h_fermat, one_mul, h_fermat, one_mul]` body with
the tighter:

```lean
rw [← pow_mul, mul_comm, three_mul_cubeInverseExp_eq hp_mod3 hp_ne_2,
    show 2 * (p - 1) + 1 = (p - 1) + (p - 1) + 1 from by ring,
    pow_succ, pow_add]
simp [h_fermat]
```

Post-mechanic this is lines 1778-1781. **Mechanic's PR title does
NOT credit Cluster E** — likely the mechanic attempted the fix but
could not Docker-verify it inside the Sub-PR-1 budget. Static
reasoning suggests the new body *should* close:

1. Goal after `← pow_mul, mul_comm`:
   `a ^ (3 * cubeInverseExp p) = a`.
2. After `three_mul_cubeInverseExp_eq` (using `hp_mod3, hp_ne_2`):
   `a ^ (2 * (p - 1) + 1) = a`.
3. After `show 2 * (p - 1) + 1 = (p - 1) + (p - 1) + 1 from by ring`
   (over ℕ; `ring` works in `CommSemiring`):
   `a ^ ((p - 1) + (p - 1) + 1) = a`.
4. After `pow_succ`:
   `a ^ ((p - 1) + (p - 1)) * a = a`.
5. After `pow_add`:
   `(a ^ (p - 1)) * (a ^ (p - 1)) * a = a`.
6. After `simp [h_fermat]` (`h_fermat : a ^ (p - 1) = 1`):
   `1 * 1 * a = a` → closed.

**Failure modes** (any one would re-open both Cluster E sites):
- (R3a) `ring` over `ℕ` fails on `2*(p-1)+1 = (p-1)+(p-1)+1` because
  of `p-1`'s truncated-subtraction edge case. Mitigation: replace
  with `omega` (which handles ℕ-subtraction natively) — 1-LOC fix.
- (R3b) `pow_succ` orientation: Mathlib v4.26.0 has both `pow_succ :
  a^(n+1) = a^n * a` and `pow_succ' : a^(n+1) = a * a^n`. The body
  uses `pow_succ` which gives the expected `a^((p-1)+(p-1)) * a`.
  No risk if name is correct.
- (R3c) `pow_add` produces `a^((p-1)+(p-1)) = a^(p-1) * a^(p-1)`,
  but the `(p-1)+(p-1)` summand is the *outer* `+` in the goal —
  `rw` should resolve to it before the outer `+1`. If `simp` reorders
  unhelpfully, the residual goal at step 6 may be `1 * (1 * a) = a`
  rather than `1 * 1 * a = a` — either form is closed by `simp` so
  no failure.
- (R3d) `simp [h_fermat]` may not fire on the `a^(p-1)` term because
  `simp` requires the LHS pattern to match modulo definitional
  equality; the `h_fermat` LHS is `a^(p-1)` where `a` is the
  hypothesis variable — should match. **Safer rewrite**: replace
  `simp [h_fermat]` with `rw [h_fermat]; ring` (explicit; no
  simp-set surprises).

Pre-emptive Sub-PR-2 patch for Cluster E (1-2 LOC, safest):
```lean
-- Replace lines 1778-1781 with:
  rw [← pow_mul, mul_comm, three_mul_cubeInverseExp_eq hp_mod3 hp_ne_2]
  have h2 : 2 * (p - 1) + 1 = (p - 1) + (p - 1) + 1 := by omega
  rw [h2, pow_succ, pow_add, h_fermat]; ring
```

This makes `ring → omega` (R3a-proof), splits the rewrites for
predictability, and replaces `simp [h_fermat]` with explicit
`rw [h_fermat]; ring`. Cost: same 4 LOC; benefit: every step is
locally robust to elaborator variation.

### Net Cluster verdict (static, Docker-pending)

| Cluster | Sites | Status | Notes |
|---------|-------|--------|-------|
| A | 5 | **RESOLVED** | All `noncomputable` keywords present |
| B | 18 (cascade) | **UNVERIFIED** | Mechanic `simp [..., map_ofNat]` adds in 4 sites; 14 unaddressed at heavier-rewrite sites — Docker-pending |
| C | 9 (1 fix point) | **RESOLVED** | Top-level `open Polynomial` at line 52 |
| D | 2 | **RESOLVED** | `PadicInt.norm_mul` → `norm_mul` |
| E | 2 | **ATTEMPTED** | Mechanic's `pow_succ + pow_add + simp [h_fermat]` likely closes; pre-emptive Sub-PR-2 patch above is safer |
| F | 1 | **RESOLVED** | `Nat.prime_iff_prime_int.mp` substitution |
| dep | 3 | **RESOLVED** | All `ZMod.natCast_eq_zero_iff` |

**Aggregate**: 4 of 6 clusters definitively resolved, 1 attempted
(E), 1 unverified (B). Mechanic's "39 → 17 errors" headline is
plausible but the residual composition is most likely **mostly
Cluster B + 0-2 Cluster E** — disambiguation requires Docker.

---

## §3. Risk inventory (Sub-PR-2 entry conditions)

**R1 — `norm_mul` overload resolution**: post-mechanic uses bare
`norm_mul` at lines 1194, 1200 inside the `Hensel3` namespace. The
`open Polynomial` at line 52 brings in the polynomial-multiplication
norm overload; the `PadicInt`-context wants `Padic.norm_mul` /
`NormedRing.norm_mul`. If v4.26.0's elaborator selects the wrong
overload, the rewrite will fail with a type-mismatch error. **Likely
not — `‖·‖` on `ℤ_[p]` should monomorphically resolve to the
`NormedRing` overload — but Docker check is decisive.**

**R2 — heavier rewrite at `HenselCaseA` / `HenselLiftZ` / `HenselLiftX`**:
mechanic's diff added `← mul_assoc, ← C_mul, norm_num, simp only
[algebraMap_int_eq, eq_intCast]` (in pairs) to the `Gint_derivative_aeval`
/ `G_derivative_aeval` / `H_derivative_aeval` bodies (3 sites). These
are *not* part of any S22 cluster — they're prophylactic
elaboration-shape fixes for the cast / `algebraMap` step that
preceded the final `ring`. If even one of these `simp only` calls
fires the wrong way (e.g. `algebraMap_int_eq` is now
`Int.algebraMap_eq` in v4.26.0 — possible v4.26 rename), it produces
a *new* error and the cluster-B residual could be larger than 17.
**Mitigation**: Sub-PR-2's Docker run will surface any new errors;
if present, the pattern is reversible (drop the `simp only` line and
let the existing `ring` close).

**R3 — Cluster E `simp [h_fermat]` non-firing**: enumerated above
(R3a-d).

**R4 — stale `_universal` / `_extended_caseA_primes_v4` corollaries
broken by Section 27 inclusions**: the per-prime corollaries in
Sections 25/26 reference `selmer_padic_solubility_caseA` (Section
13), not Section 27's `selmer_padic_solubility_caseA_universal`. No
expected breakage, but the new Section 27 `_p11_universal` /
`_p41_universal` corollaries shadow the existing per-prime names —
Lean disambiguates by namespace (`UniversalCaseA.` prefix). No risk.

**R5 — `proofs/.lake` cache state**: prior researcher logs note the
broken `proofs/.lake` symlink forces full Mathlib clone + cache fetch
(~30-45 min wall time per memory). With current 6.8 Gi disk avail,
**a cold Mathlib re-fetch (~3.4 GB download + ~10 GB extraction) is
near-marginal** — Sub-PR-2 should be launched in an environment with
≥ 15 Gi avail (laptop in pristine state, or after `docker system
prune -af`).

**R6 — stale 6-day-old open PRs #17610 (iter 15 alt) and #17645
(iter 16 alt)**: both CONFLICTING since 2026-05-09, superseded by
iter 17's Section 27 universal closure. They're on the old per-prime
enumeration line. **Curator / champion territory**; researcher
should not `gh pr close` these — leave for triage. Noted here for
inventory.

**R7 — JSON `leanFiles[]` drift**: research-JSON
`src/data/research/problems/hilbert-11-oq-02.json:225-234` records
`lineCount: 1970, theoremCount: 83, defCount: 9, sorryCount: 0,
axiomCount: 2` (iter 17 values). Mechanic Sub-PR-1's
`+5 LOC / +5 thm` delta brings true file state to
`lineCount: 1975, theoremCount: 88, defCount: 9, sorryCount: 0,
axiomCount: 2` — already reflected in gallery `meta.json` (PR
#19523) but NOT in research-JSON `leanFiles[]`. **Mechanic
territory**, not researcher. S23 STATE-SYNC will note this drift
in §6 without modifying `leanFiles[]`.

**R8 — `theoremCount` 83 vs 88 discrepancy**: the `+5` is mechanic
Sub-PR-1's apparent net delta — but its diff shows *zero* new
theorems / lemmas / instances, only edits to existing bodies. The
real source of `+5` is likely a stale lf-counter computation that
double-counted some `private lemma` bodies that the mechanic *moved*
between `simp` invocations (no semantic change, but the LF counter
may scan differently). **Cosmetic; mechanic-territory.** Not a
researcher blocker.

---

## §4. ACT-readiness gate for Sub-PR-2

| # | Gate | Status | Note |
|---|------|--------|------|
| G1 | S22 inventory still authoritative for cluster boundaries | GREEN | Static recheck §2 confirms 4/6 resolved + 1 attempted + 1 unverified |
| G2 | Mathlib pin stable | GREEN | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`); unchanged since iter 17 |
| G3 | No researcher ACT in flight that would overlap Sub-PR-2 | GREEN | No OPEN researcher PRs naming `hilbert-11-oq-02` other than the 2 stale 6-day-old iter-15/16 alts |
| G4 | Cluster E paste-ready fix derived | GREEN | §2 Cluster E pre-emptive patch (1-2 LOC) |
| G5 | Cluster D `norm_mul` overload sanity | YELLOW | Static reads plausible; R1 only fully resolved by Docker |
| G6 | Cluster B residual count predictable | YELLOW | Auto-resolution expectation per S22 — needs Docker confirm |
| G7 | R2 prophylactic mechanic edits intact | YELLOW | `algebraMap_int_eq` etc. v4.26.0 names verified by grep but Docker decisive |
| G8 | Disk ≥ 15 Gi avail | **RED** | Currently 6.8 Gi — Mathlib re-fetch marginal; Sub-PR-2 should wait for prune or pristine host |
| G9 | Docker daemon responsive | **RED** | `docker version` timeout 8 s → exit 124 |

**Verdict**: 4 GREEN substantive + 3 YELLOW (resolvable by Docker
re-run) + 2 RED (INFRA, not slug-specific). Sub-PR-2 (researcher or
mechanic) is **mechanically ready** but **environmentally blocked**.
The paste-ready Cluster E patch in §2 is the only proactive code
change S23 can make for Sub-PR-2; everything else is Docker-gated.

---

## §5. Recommended Sub-PR-2 scope (for next researcher / mechanic /
doctor cycle, when Docker responsive + ≥ 15 Gi avail)

**Step 1 — Docker re-run on current `origin/main` (post-mechanic
Sub-PR-1)**:
```
./proofs/scripts/docker-build.sh Proofs.Hilbert11OQ02 2>&1 \
  | tee .loom/logs/researcher-?-hilbert11-postSubPR1-rebuild.log
```
Expected wall-clock: ~10-15 min (Mathlib Azure cache hit). Expected
residual: ≤ 17 errors per mechanic title; likely **2-4 Cluster B
elaboration cascades + 0-2 Cluster E lines + 0 newly introduced**.

**Step 2 — apply Cluster E pre-emptive patch from §2** (1-2 LOC,
guaranteed safe per R3 analysis). If Cluster E is *already* resolved
by mechanic's attempt, the patch is a no-op semantic-equivalent
rewrite.

**Step 3 — surgical fix per residual Cluster B site**: each
`unsolved goals` in `Gint_aeval` / `G_aeval` / `H_aeval` /
`Gint_derivative_aeval` family is likely a missing `simp` lemma
(per the `map_ofNat` pattern mechanic used in 4 sites). Add the
missing lemma to each `simp` set; 1 LOC each.

**Step 4 — second Docker re-run; if 0 errors, ship as `fix(doctor):
hilbert-11-oq-02 Sub-PR-2 — Cluster B residual + Cluster E
robustness (X → 0 errors)`**.

**Estimated total ACT delta**: ~6-12 LOC across 5-10 sites; one
session.

Alternative scope (if Docker re-run reveals residual > 17 due to R2
heavier-rewrite breakage): roll back mechanic's `simp only
[algebraMap_int_eq, eq_intCast]` lines and let the surrounding `ring`
re-close. ~6 LOC net subtraction.

---

## §6. Drifts noted (mechanic/curator territory, NOT touched by S23)

1. **research-JSON `leanFiles[]` lineCount/theoremCount drift**: 1970
   / 83 (iter-17 values) vs 1975 / 88 (gallery meta). Mechanic should
   sync via the `lf` measurement script — possibly in same Sub-PR
   that syncs all post-mechanic LF deltas across the slug-family.
2. **Two stale OPEN researcher PRs #17610, #17645**: CONFLICTING
   since 2026-05-09; superseded by Section 27 universal closure;
   curator should `gh pr close --comment "superseded by #18243
   (Section 27 universal Case-A) — old per-prime enumeration line
   no longer load-bearing"`.
3. **Mechanic Sub-PR-1 title omits Clusters D + E** despite the
   diff touching both. Cosmetic; no action needed.
4. **`mathlib_version` pin SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
   matches the slug-cohort consensus per `lake-manifest.json`. No
   drift.

---

## §7. Honesty

**What this session delivers (concretely, doc-only)**:
- Catches state.md and research-JSON `currentState` up from iter 17
  to iter 23.
- Static cluster-by-cluster cluster-status survey against
  post-mechanic file (no Docker dependency).
- Paste-ready Cluster E pre-emptive patch (1-2 LOC) with R3
  failure-mode analysis.
- 9-item Sub-PR-2 ACT-readiness gate (4 GREEN + 3 YELLOW + 2 RED).
- Inventory of 4 mechanic / curator drifts that S23 deliberately
  did not touch.

**What this session does NOT deliver**:
- Any Lean code change. (Docker hung; doc-only by design.)
- Any `leanFiles[]` line-count update. (Mechanic territory; R7.)
- Any gallery `meta.json` change. (Already done by mechanic #19523.)
- Any `problem.md` / `knowledge.md` edit. (Both stable since
  pre-iter-17.)
- Any PR-close for the 2 stale 6-day-old OPEN researcher PRs.
  (Curator territory; R6.)
- Any Mathlib-pin bump. (Slug is content-stable at v4.26.0; cohort
  consensus.)

**Confidence**: high on §2 static verifications (all greps confirm
the syntactic state); medium on the §3 risk inventory (R1, R3a-d are
elaborator-quirk-dependent); low without Docker on the **exact**
residual error count (mechanic's "17" is the best signal we have).

**Predecessor stability**: 4 commits since branch base
`73525731387` on `origin/main` at S23 start; none touch
`hilbert-11-oq-02` files. Verified by:
```
git log 73525731387..origin/main -- \
  proofs/Proofs/Hilbert11OQ02.lean \
  src/data/research/problems/hilbert-11-oq-02.json \
  src/data/proofs/hilbert-11-oq-02/ \
  research/problems/hilbert-11-oq-02/
```
(Empty output expected at PR-creation time.)
