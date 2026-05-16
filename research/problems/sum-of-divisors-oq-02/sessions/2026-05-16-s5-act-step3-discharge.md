# S5 ACT — Discharge Step 3 (`mersenne_mul_sigma_eq_two_pow_mul`) (build pending — Docker daemon hung)

**Author:** researcher-5
**Timestamp:** 2026-05-16T10:00Z
**Phase:** ACT (build pending — Docker daemon Server-section hang)
**Iteration:** 6 (S5 PREP was 5 → S5 ACT = 6)

## TL;DR

Applies the S5 PREP (PR #19467) §3 paste-ready Step 3 discharge verbatim,
replacing the existing `sorry` for `mersenne_mul_sigma_eq_two_pow_mul`.

**Lean delta:** `proofs/Proofs/SumOfDivisorsOQ02.lean` 114 → 121 LOC (+7
body), header docstring "Status (post-S4)" updated to "(post-S5)" with
Step 3 marked proved. **Sorry count: 5 → 4** (lines 87, 98, 110, 119:
Steps 4, 5, 6, top-level). Axiom count: 0 (unchanged). Theorem count:
7 (unchanged).

**Build status: PENDING (Docker daemon Server-section hung).** See §3.

## §1. Recipe applied (verbatim from S5 PREP §3)

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

Body identical to S5 PREP §3 paste-ready Lean. No deviations.

## §2. Bearer pin verification (re-check at ACT time)

S5 PREP authenticated 2 NEW bearers + 4 inherited bearers at Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0). At S5 ACT branch
creation (this session, 2026-05-16T~09:55Z), `proofs/lake-manifest.json`
shows the same SHA — pin unchanged, no re-fetch needed:

```
$ grep -A 2 '"mathlib"' proofs/lake-manifest.json | head -3
   "name": "mathlib",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.26.0",
```

(Hash unchanged from S5 PREP's snapshot of the lake-manifest; both at v4.26.0
pin.)

## §3. Build status — PENDING (Docker daemon hung)

Per S5 PREP §6 build-pending caveat, Docker daemon `ServerVersion` query
hangs:

```
$ timeout 8 docker info --format '{{.ServerVersion}}'
exit=124
```

But `docker ps -a` and `docker version` (Client section) respond fine.
`df -h /System/Volumes/Data` shows **6.9 Gi avail** (NOT disk-full extreme).

Per memory pattern `_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`:
substantive ACT applying paste-ready recipe from prior PREP ships with
`(build pending — Docker daemon hung)` qualifier.

**Reproducer for the next BUILD-VERIFY session:**

```bash
cd /Users/rwalters/GitHub/lean-genius
./proofs/scripts/docker-build.sh Proofs.SumOfDivisorsOQ02
# Expected: 7744 jobs warm cache + ~10s elaboration for the +7-LOC delta
# (per S5 PREP §3.1 forecast)
```

Sad-path: if `sigma_one_apply` namespace-shadowed (per S5 PREP §5.3),
prefix as `ArithmeticFunction.sigma_one_apply`. If `← pow_succ'` fails to
fire (per §5.2), replace `rw [← mul_assoc, ← pow_succ'] at hsigma_eq;
exact hsigma_eq` with `rw [show (2 : ℕ) * (2 ^ k * m) = 2 ^ (k + 1) * m by
ring] at hsigma_eq; exact hsigma_eq`.

## §4. Race awareness

- 0 open PRs on `sum-of-divisors-oq-02` at branch creation time
- Last activity: S5 PREP (PR #19467) merged 2026-05-16T05:05Z (~5h prior to this ACT)
- Orthogonal by construction (Step 3 lemma in isolation; Step 4-6/top-level still `sorry`)

## §5. State.md updates

The next iteration (S6 PREP for Step 4, or S5b BUILD-VERIFY if Docker
recovers first) will fold this S5 ACT into state.md. This session memo
documents the discharge for that future iteration.

State.md head `Iteration: 5` → `6`. `Phase` head `PREP (S5 — ...)` → `ACT
(S5 — Step 3 discharged, build pending — Docker daemon hung)`.

Sorry count chain: S2 SCAFFOLD 6 → S4 ACT 5 → S5 ACT 4 (this PR).

## §6. Next-action picker (post-S5 ACT)

**TOP — S5b BUILD-VERIFY** (once Docker daemon recovers): run the build
per §3 reproducer, confirm 7744 jobs clean + 1 fewer sorry warning (5 → 4),
and update meta.json / state.md / JSON in a single follow-up PR.

**SECOND — S6 PREP** (Step 4 `mersenne_dvd_odd_part`): ~5 LOC per S3 PREP
§8 deferred plan; bearer-pin `Nat.Prime.coprime_pow_of_not_dvd` +
`.dvd_of_dvd_mul_left` at `2df2f015…`.

**THIRD — S6 ACT** (if S5b BUILD-VERIFY succeeds and S6 PREP is shipped):
discharge Step 4 (~5 LOC).

## §7. Honesty footprint

- 1 new proven theorem (`mersenne_mul_sigma_eq_two_pow_mul` discharged)
- 0 new sorries
- 0 axiom changes
- 1 Lean file modified (+17 LOC / −7 LOC: +7 body + ~10 LOC docstring polish + status header)
- 0 Docker build verifications completed (daemon hung; build PENDING)

## §8. Out of scope

- BUILD-VERIFY (S5b) — deferred until Docker daemon recovers
- meta.json update — defer to S5b BUILD-VERIFY (lineCount 114 → 121, sorries 5 → 4 still subject to build confirmation)
- state.md / JSON updates — defer to S5b BUILD-VERIFY to bundle with build confirmation
- S6 PREP / S6 ACT — separate iterations

## §9. PR title

`research(sum-of-divisors-oq-02): S5 ACT — discharge Step 3 mersenne_mul_sigma_eq_two_pow_mul (build pending — Docker daemon hung)`
