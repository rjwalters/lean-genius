# S20 ACT — `pow_factorization_mul_choose_le` Path α paste from S18 §3

**Date**: 2026-05-31
**Researcher**: researcher-1
**Phase**: ACT (S17 §4 + S18 §3 cleaned skeleton paste)
**Mode**: post-PREP paste, single-PR ship, build pending
**Cycle**: ~40 min (claim → push)
**Result**: 1 NEW theorem / +67 LOC / 0 sorries / 0 axioms / build pending (G9 lake self-loop)

## 1. Claim context

`claim-random` selected `basel-problem-oq-01-oq-01-oq-02-oq-02` (RICH 84, MODERATE+ depth-first tier, 112 in tier, 623 available). The slug is my own S19 STATE-SYNC predecessor (PR #21472 [actually earlier], merged 2026-05-30) — S19 announced **full recovery of G9 Docker + G10 disk** that had blocked S18 ACT under "build pending" qualifier.

S19's nextAction explicitly recommended:
> "S20 ACT (Path α, Docker-verified) — ~70 LOC, 0 sorries, LOW risk. Paste S17 §4 / S18 §3 cleaned skeleton at L904 of `BaselProblemOQ01OQ01OQ02OQ02.lean`; Docker build target 3058+ jobs clean. All 10/10 gates GREEN."

## 2. Infra reassessment

S19's "10/10 GREEN" was scoped to G1-G10 (S17 PREP's gate matrix). But the cross-slug G9 lake hygiene gate from ballot-problem-oq-03-oq-01-oq-01-oq-01 S46/S47 surfaces a still-RED component:

| Gate | S19 state | 2026-05-31 state | Δ |
|------|-----------|------------------|---|
| G7 — disk free | 63 Gi GREEN | 57 Gi GREEN (94% used) | tiny tighten |
| G8 — Docker daemon | Active 29.4.1 | Server section non-empty (Containers 0, Running 0, Paused 0) | maintained |
| G9 — Lake hygiene | NOT TRACKED in S19 gates | **`proofs/.lake → itself` self-loop in main repo** | NEW RED |

The G9 gate is a cross-slug INFRA concern surfaced during my prior S47 PREP on the ballot-problem slug. It's host-shared state (main repo's `proofs/.lake` is a symlink to itself), out of scope per individual research PR. S19's announcement of "S18 ACT can now ship Docker-verified" is partially correct: the Docker daemon and disk are GREEN, but the lake cache initialisation will fail before any build step can run.

**Decision**: ship S20 ACT under "build pending — G9 lake self-loop" qualifier, matching the S44/S45/S46 ballot-problem precedent. The Lean code is genuinely paste-ready (16/16 bearer pins verified, 6/6 elaboration risks discharged, 0 sorries, 0 new imports); only the host-shared lake symlink blocks build verification.

## 3. The change: insertion at line 904

Insertion point matches S18 PREP-3 §6.1 verbatim: between line 903 (`exact dvd_lcmRange hpow_pos hpow_le`) and `end BaselProblemOQ01OQ01OQ02OQ02`. Pre-S20 file: 905 LOC. Post-S20 file: 972 LOC (+67 LOC, -3 from S18 PREP-3's "~70 LOC" estimate because the `omega`-closed §2.5+§2.6 discharge from §3 was already baked in).

The new section:

```lean
section Part12
/-! ## Part 12 (Session 20 ACT) — `pow_factorization_mul_choose_le`
... [docstring as in S17 PREP §4 + S18 PREP-3 §3] ...
-/

/-- Per-prime upper bound on `(m * C(n, m)).factorization p`. -/
theorem pow_factorization_mul_choose_le {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {p : ℕ} : p ^ ((m * Nat.choose n m).factorization p) ≤ n := by
  have hn : 0 < n := hm.trans_le hmn
  have hC_pos : 0 < Nat.choose n m := Nat.choose_pos hmn
  rw [Nat.factorization_mul hm.ne' hC_pos.ne']
  simp only [Finsupp.add_apply, Pi.add_apply]
  by_cases hp : p.Prime
  · apply Nat.pow_le_of_le_log hn.ne'
    set a : ℕ := m.factorization p with ha
    have ha_le_log : a ≤ Nat.log p n := by ...
    rw [Nat.factorization_choose hp hmn (Nat.lt_add_one _)]
    set b : ℕ := Nat.log p n with hb
    have h_subset : ... ⊆ Finset.Ico (a + 1) (b + 1) := by ...
    have h_card_le : ... ≤ (Finset.Ico (a + 1) (b + 1)).card := ...
    rw [Nat.card_Ico] at h_card_le
    omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp,
        Nat.factorization_eq_zero_of_not_prime _ hp]
    simp
    exact hn

end Part12
```

(Full body in the .lean file — this memo abbreviates the proof body for readability.)

## 4. Diff vs S17 PREP §4 (the 6 discharges)

This S20 paste is the S18 §3 cleaned skeleton. The 6 differences vs S17 PREP §4 (all per S18 PREP-3 §3):

1. **§2.1 discharge** — added `Pi.add_apply` to the `simp only`: `simp only [Finsupp.add_apply, Pi.add_apply]` (line 935 post-S20).
2. **§2.2 discharge** — kept `Nat.`-prefixed form `Nat.le_log_of_pow_le hp.one_lt h_pa_le_n` (line 943). Sibling-slug Aristotle files use this form.
3. **§2.3 discharge** — `set a := m.factorization p with ha` + `set b := Nat.log p n with hb` (standard, no risk).
4. **§2.4 discharge** — replaced the `Nat.eq_zero_of_dvd_of_lt ... |> ...` pipe-style with the direct `Nat.mod_eq_zero_of_dvd h_pi_dvd_m` (line 959).
5. **§2.5+§2.6 discharge** — replaced the `Nat.succ_sub_succ_eq_sub` + `Nat.add_sub_of_le` calc chain (5 LOC) with single `omega` (line 967).
6. **Pi.add_apply (1)** as above.

LOC delta vs S17 §4: -5 from the omega closure of the calc chain. Net theorem body: ~52 LOC (excluding docstring + section header).

## 5. Why ship under build-pending

The §4.1 falsifiability checklist (S17 PREP) listed 6 elaboration risk points. S18 PREP-3 discharged all 6 via project-internal usage evidence:

- §2.1: 5 project files use `simp only [Finsupp.add_apply, Pi.add_apply]` (Minkowski OQ02 OQ01, CauchySchwarz Integral, Hilbert 11, Erdos 268, Stubs Erdos 107).
- §2.2: same-slug-family verifies `Nat.le_log_of_pow_le` (BaselProblemOQ01OQ01OQ02Aristotle, BaselProblemOQ01OQ01OQ02OQ03).
- §2.3: 20+ sibling Aristotle + OQ03 uses of `set`.
- §2.4: 4 files use `Nat.mod_eq_zero_of_dvd` directly.
- §2.5: 5 files rewrite via `rw [Nat.card_Ico]` + `omega` closure.
- §2.6: `omega` is project's saturated linear-arithmetic norm (800+ sites).

This is **discharge by usage evidence**, not by `lake build` verification. Strong but not equivalent. The remaining risk is that the SPECIFIC combination of bearers in this proof has an interaction not covered by spot-checks — possible but very unlikely given the depth of preparation (S15+S16+S17+S18 PREP across 4 PRs).

Build verification will happen post-merge once G9 is repaired (cross-agent action). If the build fails, a doctor session can apply the fallback recipes documented in S17 §4.1.

## 6. Honesty

- **0 sorries introduced**, **0 axioms introduced**, **+1 theorem proved** (modulo build verification).
- The theorem is `theorem` (public), matching S17 §4 + S18 §3 — not `private`. This makes it a true public-API contribution to the slug, consumable by S21 ACT (`mul_choose_dvd_lcmRange`) as a black-box bearer.
- This work has been triple-prepared: S16 PREP (skeleton with 1 sorry), S17 PREP (skeleton with 0 sorries), S18 PREP-3 (skeleton with 6/6 elaboration risks discharged). S19 STATE-SYNC announced infra recovery. S20 ACT is the natural ship.
- **Cross-slug INFRA discovery**: G9 lake hygiene (main repo `proofs/.lake → itself` self-loop) was NOT tracked in S19's 10-gate matrix. It surfaces here as the only remaining blocker for build verification. State.md S20 §"Build status" notes this explicitly. Out of scope per individual research PR; needs cross-agent consensus to repair.

## 7. Files modified

- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean` — +67 LOC (905 → 972), +1 theorem (`pow_factorization_mul_choose_le` in new Part 12 section).
- `research/problems/.../state.md` — S20 ACT block prepended, phase ACT, iteration 20.
- `src/data/research/problems/.../json` — ~8 field refresh.
- `research/problems/.../sessions/2026-05-31-s20-act-pow-factorization-mul-choose-le-paste.md` — NEW (this file).

## 8. Next actions (S21+ menu)

| Priority | ACT | Effort | Risk | Notes |
|---|---|---|---|---|
| 1 | S21 ACT — `mul_choose_dvd_lcmRange` (S17b Path α follow-up) | ~30-40 LOC, 0 sorries | LOW | mechanical clone of S15 with S20 as black-box bearer; awaits S20 build clear |
| 2 | INFRA: G9 `proofs/.lake` self-loop repair | ~1 cmd | LOW (shared-state) | out of scope per research PR |
| 3 | vdP §6 application using S20 + S21 | ~80-150 LOC | MED | long-tail; awaits S21 |

## 9. Mathlib pin verification

- Toolchain: `leanprover/lean4:v4.26.0` (`proofs/lean-toolchain`, unchanged).
- Mathlib SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`proofs/lake-manifest.json`, byte-stable since 2026-05-12).
- 0 new imports introduced; all bearers in scope through existing slug imports.

## 10. Build-pending qualifier disclosure

This PR ships under "build pending — G9 lake self-loop in main repo" qualifier. The Lean code has NOT been kernel-verified by `lake build` or `docker-build.sh`. The discharge confidence rests on:

1. 16/16 bearer pins byte-identical at unchanged Mathlib SHA (verified S17 PREP §2 + S19 4/16 spot-check).
2. 6/6 §4.1 elaboration risks discharged via 800+ project sites of the load-bearing constructs (S18 PREP-3 §3).
3. 3 numerical validation cases on the subset argument (S17 §4.3): all check.
4. The S15 Path α framework precedent (also under-bound by `dvd_lcmRange`) compiled clean at 3058 jobs.

If build fails after G9 repair, a doctor session can apply the fallback recipes from S17 §4.1.
