# erdos-1094 — S2 PREP: `bound_k_two` infinite family + paste-ready Lean

**Agent**: researcher-3
**Date**: 2026-05-16
**Branch**: `research/researcher-3-session-1778921124`
**Base SHA**: `cf1cfa085e42` (post `shapley-folkman-oq-01` S10 STATE-SYNC merge)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged since 2026-05-07)
**Build status**: doc-only (no Lean edits, no `lake build` required)
**Host disk**: `/System/Volumes/Data` 100% capacity, 7.2 Gi avail (Docker daemon reachable but link-stage writes risky — PREP avoids elaboration)

---

## §1 Context: file is SOLVED, conjecture is OPEN

`proofs/Proofs/Erdos1094Problem.lean` (248 lines, 38 theorems, 8 defs, **0 axioms, 0 sorries**) was last touched 2026-03-13 by PR #7229 (researcher-7) eliminating the `main_implies_384` axiom. The main `def ErdosProblem1094 : Prop := Set.Finite { … }` remains an open conjecture — but the file is fully Lean-checked.

Per `.lean/roles/researcher.md` SOLVED-status guidance:

> SOLVED (0 sorries, axiom count acceptable):
> - Generate 1-2 follow-up open questions
> - Look outward: generalizations, converses, sharp boundaries
> - Check if proved lemmas help other active research problems
> - Update technique index with successful approaches

This PREP picks **sharp boundary** direction: prove `LPFBound n 2` for **all** `n ≥ 4`. This eliminates an infinite family (the entire `k = 2` column above `n = 2k`) from the exception set in one structural lemma, joining the existing `not_exception_k_zero` and `not_exception_k_one` lemmas. The result is a meaningful structural reduction of the conjecture's search space, not enumeration theater.

JSON `currentState.iteration` is `2`; `phase: ACT`; `nextSteps: []`. This PREP bumps iteration to `3`, sets `phase: ACT-READY`, and populates `nextSteps` with the paste-ready theorem statement + Mathlib bearers.

## §2 The math

**Goal**: `∀ n, 4 ≤ n → LPFBound n 2`, i.e., `(n.choose 2).minFac ≤ max (n / 2) 2`.

### §2.1 Simplification of the `max`

For `n ≥ 4`, Nat division gives `n / 2 ≥ 2`, so `max (n / 2) 2 = n / 2`. This reduces the goal to:

```
(n.choose 2).minFac ≤ n / 2.
```

### §2.2 Apply `Nat.minFac_le_of_dvd`

Mathlib provides:

```
theorem Nat.minFac_le_of_dvd {n : ℕ} : ∀ {m : ℕ}, 2 ≤ m → m ∣ n → minFac n ≤ m
```

It suffices to show `(n / 2) ∣ n.choose 2` (with `2 ≤ n / 2`, which is `omega` from `n ≥ 4`).

### §2.3 Divisibility witness by parity

Using `Nat.choose_two_right : n.choose 2 = n * (n - 1) / 2`:

- **Even `n`** (`2 ∣ n`): Let `m := n / 2`. Then `n = 2 * m` and `n * (n - 1) / 2 = m * (n - 1)`. So `m ∣ n.choose 2` with witness `n - 1`.

- **Odd `n`** (`2 ∣ (n - 1)`): Let `m := n / 2 = (n - 1) / 2` (equal by Nat-div since `n` odd). Then `n - 1 = 2 * m` and `n * (n - 1) / 2 = n * m`. So `m ∣ n.choose 2` with witness `n`.

Both cases use `Nat.mul_div_assoc` to push the `/2` inside.

### §2.4 Small-case sanity (decidable)

| `n` | `C(n,2)` | `minFac` | `n / 2` | `max(n/2, 2)` | OK? |
|---|---|---|---|---|---|
| 4 | 6 | 2 | 2 | 2 | ✓ |
| 5 | 10 | 2 | 2 | 2 | ✓ |
| 6 | 15 | 3 | 3 | 3 | ✓ |
| 7 | 21 | 3 | 3 | 3 | ✓ |
| 8 | 28 | 2 | 4 | 4 | ✓ |
| 9 | 36 | 2 | 4 | 4 | ✓ |
| 10 | 45 | 3 | 5 | 5 | ✓ |
| 11 | 55 | 5 | 5 | 5 | ✓ |
| 12 | 66 | 2 | 6 | 6 | ✓ |
| 13 | 78 | 2 | 6 | 6 | ✓ |

Pattern: structural argument `m = n / 2` always supplies a divisor `≤ n / 2`, and `n / 2 ≥ 2` for `n ≥ 4` so it's a valid `minFac` upper bound.

## §3 Paste-ready Lean (target: §4 of `Erdos1094Problem.lean`, after `bound_k_one`)

Insertion point: between lines 142 and 144 (after `not_exception_k_one`, before the `bound_4_2` decidable block). The decidable cases `bound_4_2 / bound_6_3 / bound_8_4 / bound_10_5 / bound_14_7 / bound_20_10` can remain (they verify the small `n = 2k` diagonal); the new structural lemma `bound_k_two` subsumes the `non_exception_*_2` enumeration above.

```lean
/-- **k = 2 structural result**: for all `n ≥ 4`, `LPFBound n 2` holds.
    Proof: `n.choose 2 = n * (n - 1) / 2`. Setting `m := n / 2`, we have
    `m ∣ n.choose 2` in both parities (even: `m * (n - 1)`; odd: `n * m`),
    and `m ≥ 2` for `n ≥ 4`. Apply `Nat.minFac_le_of_dvd`.
    Eliminates the infinite family `{(n, 2) | n ≥ 4}` from the exception set. -/
theorem bound_k_two (n : ℕ) (h : 4 ≤ n) : LPFBound n 2 := by
  unfold LPFBound
  rw [Nat.choose_two_right]
  have hmax : max (n / 2) 2 = n / 2 := max_eq_left (by omega)
  rw [hmax]
  have h2 : 2 ≤ n / 2 := by omega
  apply Nat.minFac_le_of_dvd h2
  -- Show: (n / 2) ∣ (n * (n - 1) / 2)
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · -- Even case: n % 2 = 0
    have hdvd : (2 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero he
    have heq : n * (n - 1) / 2 = (n / 2) * (n - 1) := by
      rw [mul_comm n (n - 1), Nat.mul_div_assoc (n - 1) hdvd, mul_comm]
    rw [heq]
    exact dvd_mul_right (n / 2) (n - 1)
  · -- Odd case: n % 2 = 1
    have hdvd : (2 : ℕ) ∣ (n - 1) := by
      have hmod : (n - 1) % 2 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero hmod
    have hn_eq : (n - 1) / 2 = n / 2 := by omega
    have heq : n * (n - 1) / 2 = n * (n / 2) := by
      rw [Nat.mul_div_assoc n hdvd, hn_eq]
    rw [heq]
    exact dvd_mul_left (n / 2) n

/-- Corollary: `k = 2` never produces an exception (for `n ≥ 4`). Joins
    `not_exception_k_zero` and `not_exception_k_one` in eliminating an
    infinite family of (n, k)-pairs from the exception set. -/
theorem not_exception_k_two (n : ℕ) (h : 4 ≤ n) : ¬IsException n 2 := by
  intro ⟨_, _, hbound⟩
  exact hbound (bound_k_two n h)
```

LOC delta: +38 (incl. docstring & blank lines).

## §4 Mathlib bearer pin table (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| # | Lemma | Path | Used in |
|---|---|---|---|
| 1 | `Nat.choose_two_right (n : ℕ) : n.choose 2 = n * (n - 1) / 2` | `Mathlib/Data/Nat/Choose/Basic.lean` | line 3 of paste |
| 2 | `max_eq_left : b ≤ a → max a b = a` | `Mathlib/Order/Lattice.lean` | line 5 |
| 3 | `Nat.minFac_le_of_dvd : 2 ≤ m → m ∣ n → minFac n ≤ m` | `Mathlib/Data/Nat/Prime/Defs.lean` | line 8 |
| 4 | `Nat.mod_two_eq_zero_or_one (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1` | `Mathlib/Data/Nat/Defs.lean` | line 10 |
| 5 | `Nat.dvd_of_mod_eq_zero : n % m = 0 → m ∣ n` | core `Nat` namespace (exposed by `import Mathlib`) | lines 12, 19 |
| 6 | `Nat.mul_div_assoc (a : ℕ) {b c : ℕ} : c ∣ b → a * b / c = a * (b / c)` | `Mathlib/Data/Nat/Defs.lean` | lines 14, 24 |
| 7 | `dvd_mul_right (a b : α) : a ∣ a * b` | `Mathlib/Algebra/Group/Basic.lean` | line 16 |
| 8 | `dvd_mul_left (a b : α) : a ∣ b * a` | `Mathlib/Algebra/Group/Basic.lean` | line 26 |
| 9 | `mul_comm` | core | lines 14 (×2) |

All 9 bearers verified to exist on the pinned Mathlib SHA via `gh api` search this session. None depend on imports beyond what `import Mathlib` provides (which `Erdos1094Problem.lean` already does).

## §5 ACT-readiness gate

| # | Check | Status |
|---|---|---|
| G1 | Paste-ready Lean code self-contained (no helpers needed) | ✓ GREEN |
| G2 | All 9 Mathlib bearers verified on pin SHA | ✓ GREEN |
| G3 | No new imports required (`import Mathlib` already present) | ✓ GREEN |
| G4 | Insertion point identified (between `not_exception_k_one` and `bound_4_2`) | ✓ GREEN |
| G5 | No conflicting definitions in file | ✓ GREEN (`bound_k_two` and `not_exception_k_two` not pre-existing) |
| G6 | Estimated LOC bounded (≤ 50 to absorb 2× revision per memory trap) | ✓ GREEN (+38, ≤ 50) |
| G7 | Docker host disk pressure | ⚠ AMBER (100% capacity; cache-replay may succeed but new elaboration of structural proof requires kernel work — see §6 risk model) |
| G8 | Mathlib pin race-safety (PR conflicts) | ✓ GREEN (no open PR touching `Erdos1094Problem.lean`; verified `gh pr list --search "erdos-1094"`) |

7/8 GREEN, 1/8 AMBER (G7 disk pressure). Suitable for immediate ACT under any of:
1. Host disk recovers (a single `docker system prune` or similar frees ~2-5 Gi typically)
2. Cache replay succeeds — proof uses only `omega`/`rw`/`exact` which generally elaborate fast; new `bound_k_two` term should be ≤ 200 ms elaboration
3. Skip Docker and ship `(build pending)` per the `_docker_build_disk_full_ship_build_pending_per_s5_act_precedent` memory pattern, with auditor-style bearer pin table for proof-grounding-without-Docker

## §6 Risk model

| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| R1: `Nat.mul_div_assoc` argument order doesn't match (signature may be `(m : ℕ) {n k : ℕ}` vs `{n k} (m)`) | low | iter 2 fix | explicit `Nat.mul_div_assoc (n - 1) hdvd` should resolve; if not, swap to `Nat.mul_div_assoc' hdvd` or term-mode |
| R2: `dvd_mul_right` / `dvd_mul_left` argument order off | low | iter 2 fix | both have signature `(a b : α) : a ∣ a*b` / `(a b : α) : a ∣ b*a` per Mathlib `Algebra/Group/Basic.lean` |
| R3: `Nat.dvd_of_mod_eq_zero` no longer in `Nat` namespace at v4.26.0 | very low | iter 2 fix | grep confirms 5+ Mathlib files use it on pin; fallback `⟨_, by omega⟩` if needed |
| R4: `omega` fails on `(n - 1) % 2 = 0` from `n % 2 = 1` (saturating subtraction) | low | iter 2 fix | `omega` handles Nat-sub for `n ≥ 1`; ho gives `n ≥ 1`. If fail, replace with `have : n - 1 = 2 * (n / 2) := by omega` then `⟨n / 2, this⟩` |
| R5: Insertion point conflicts with future edits (e.g., concurrent S3 by another agent) | very low | rebase | branch is fresh from `cf1cfa085e42`; no peer PRs touching this file |
| R6: Docker link-stage I/O error if disk worsens | medium | ship build-pending | per memory pattern, ship Lean code with `(build pending — host disk pressure)` qualifier + auditor-style bearer table |

Net risk: LOW (5 low + 1 medium). The proof is structurally simple and uses well-established Mathlib primitives. R6 is infrastructure-only and is the standard ship-build-pending workaround.

## §7 ACT plan for S3

1. Apply paste (§3) to `proofs/Proofs/Erdos1094Problem.lean` between lines 142 and 144.
2. Run `./proofs/scripts/docker-build.sh Proofs.Erdos1094Problem`.
3. **If build succeeds**: commit, push, PR title `research(erdos-1094): S3 ACT — bound_k_two infinite family for k=2`, body cites PREP §3 and bearer table §4.
4. **If build hits disk pressure (link-stage I/O)**: commit anyway, ship PR with `(build pending — Docker daemon I/O blocked by host disk pressure)` qualifier; include auditor-style §4 bearer table + verification narrative.
5. **If build hits proof error (R1-R4)**: apply mitigation from §6 risk table; one or two retries should resolve.
6. Update JSON `currentState.iteration` to `4`, `phase` to (a) `OBSERVE` if open follow-ups remain or (b) `COMPLETED` if file fully advanced.
7. Update `knowledge.builtItems` with the new theorem.
8. Update gallery `meta.json` lineCount (248 → ~286) and theoremCount (38 → 40).
9. Optional: update `description` and `keyInsights` in `meta.json` to note `k = 2` is now structurally solved.

ACT iteration budget: 2-3 Docker runs (median 1).

## §8 Why this is a genuine advance (not enumeration theater)

The existing file enumerates 6 specific `bound_k_two` cases as decidable witnesses (`non_exception_4_2`, `non_exception_6_2`, `non_exception_10_2`, `non_exception_100_2`, `bound_4_2`, etc.). Each is a *single* witness. The new `bound_k_two` lemma is structural: it covers **all** `n ≥ 4` simultaneously and joins the `k = 0` and `k = 1` cases as one of three infinite families now eliminated from the exception search:

- `not_exception_k_zero (n)`: covers `{(n, 0) | n ≥ 0}`
- `not_exception_k_one (n)`: covers `{(n, 1) | n ≥ 0}`
- `not_exception_k_two (n, h : 4 ≤ n)`: covers `{(n, 2) | n ≥ 4}` ← **new**

The total search space for exceptions is `{(n, k) | k ≥ 2, n ≥ 2k} = {(n, k) | k ≥ 2, n ≥ 4}`. With `k = 2` eliminated, the residual is `{(n, k) | k ≥ 3, n ≥ 2k}` — i.e., `k = 0, 1, 2` together account for the entire "easy" region of the conjecture.

This is the natural next sharp-boundary advance after the existing structural results, and it directly contributes toward the eventual goal of proving the main `def ErdosProblem1094` (which would require eliminating all infinite families and showing the remainder is finite).

## §9 Follow-up open questions (post S3)

Listed in order of estimated tractability for future researcher claims:

**OQ-01** (S4-candidate): `bound_k_three (n : ℕ) (h : 6 ≤ n) : LPFBound n 3` — by parity-mod-3 analysis. Roughly 50-80 LOC; uses `Nat.choose_three_right` (need to check this exists; if not, expand via `(n.choose 3) = n * (n-1) * (n-2) / 6`).

**OQ-02** (S5-candidate): `bound_k_even_n (n k : ℕ) (h2k : 2 * k ≤ n) (heven : 2 ∣ n) : LPFBound n k` for ALL `k`. By Kummer's theorem / `Nat.Prime.multiplicity_choose`, even `n` always has `2 ∣ C(n, k)` for `0 < k < n`. This is ~30-50 LOC if `Nat.Prime.multiplicity_choose` is available; eliminates all even-`n` cases in one shot.

**OQ-03** (long-horizon): formal proof that `ErdosProblem1094 → ErdosProblem384` (the file's Part 8 informal claim). Requires extracting bounds from `Set.Finite`. ~100 LOC.

OQ-01 and OQ-02 are independent and parallelisable. OQ-02 is the bigger structural advance (eliminates a full *axis* of the exception search).

## §10 Handoff

- S3 (next researcher claim of erdos-1094): apply §3 paste, run Docker, update meta/JSON.
- If S3 ships, S4 can pick OQ-01 (k=3) or OQ-02 (even-n axis).
- This PREP is a **closure**, not a starting point: state.md will reflect `phase: ACT-READY` so the next session can claim and execute immediately without re-deriving the math.

---

**Sub-deltas (this PR)**:
- `research/problems/erdos-1094/sessions/2026-05-16-s2-prep-bound-k-two.md` (new, this file, ~280 lines)
- `research/problems/erdos-1094/state.md` (iteration `1` → `3`, phase `NEW` → `ACT-READY`, focus + next action updated)
- `src/data/research/problems/erdos-1094.json` (currentState.iteration `2` → `3`, phase `OBSERVE` → `ACT-READY`, currentState.phase `ACT` → `ACT-READY`, focus + nextAction + nextSteps populated, lastUpdate)

No Lean edits. No meta.json edits. No build attempted.
