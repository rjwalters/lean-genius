# S31 ACT — Peel-off recipe paste + state.md head drift fix

**Author**: researcher-1
**Date**: 2026-06-09T22:47:00Z
**Claim**: `abel-ruffini-galois-extensions-oq-07` (RICH 86), claimed 22:11:34Z, expires 00:11:34Z (window: 2h)
**Pivot**: started as STATE-SYNC, pivoted to ACT after baseline Docker re-verify finished in 210s (within budget)

## §1 Trigger and pivot rationale

`claim-problem.sh claim-random` returned this slug at 22:11:34Z. Predecessor on the slug was my own S30 BUILD-FIX (PR #20904, merged 2026-05-28T23:30:00Z = T+12 days idle). Pre-flight survey revealed:

- state.md head STALE at iter 29 BUILD-BLOCKER (S29 STATE-SYNC by researcher-10, 2026-05-16T18:57Z) — the S30 BUILD-FIX commit updated JSON but did not propagate to state.md head
- JSON CURRENT at iter 30 BUILD-FIXED with three S31+ ACT candidates outlined (S26 peel-off recipe, meta.json sync, hard residue character-theory)
- meta.json IN SYNC (sorries: 0, axiomCount: 1, lineCount: 1894, theoremCount: 38)
- INFRA all-GREEN (Docker 29.5.3 vs S29 hung, disk 85 Gi vs S29 RED 3.3 Gi, .lake worktree symlink correctly redirects to main-repo cache)
- Mathlib pin `2df2f0150c…` byte-stable 24+ days

Initial plan was STATE-SYNC (doc-only) given the 1h24min claim-window concern. But a baseline Docker re-verify of S30 BUILD-FIX completed in **210s (3074 jobs, 0 errors)**, well under budget — so the plan pivoted to **ACT** within the same window: paste the S26 §3.2/§3.3 peel-off recipe verbatim, no dispatch update yet.

## §2 14-day arrears inventory (state.md head)

| Section | S29 era (2026-05-16) | S30 actual (2026-05-28) | S31 (this ship) |
|---|---|---|---|
| Phase | BUILD-BLOCKER | BUILD-FIXED | ACT |
| Iteration | 29 | 30 | 31 |
| Last Updated | 2026-05-16T18:57Z | (state.md not updated by S30) | 2026-06-09T22:47Z |
| Docker state | hung (empty Server:) | 29.4.1 | 29.5.3 |
| Disk | 3.3 Gi RED | 66 Gi | 85 Gi |
| .lake symlink | RED B3 | "removed" (per S30 narrative) | re-classified as correct worktree-redirect (not self-circular) |

S30 BUILD-FIX did the heavy lifting (clearing the 18 elaboration errors); S31 absorbs the state.md head arrears and re-classifies the .lake symlink (the S26-S29 narrative incorrectly called it "circular self-symlink" — actually it correctly redirects worktree → main-repo cache; the path strings appear identical only because the worktree path component differs).

## §3 INFRA spot-check (S31 author-time, 2026-06-09T22:47Z)

```
$ docker info --format '{{.ServerVersion}}'
29.5.3                             # GREEN (S29 was empty)

$ df -h /System/Volumes/Data
... 85 Gi avail / 91% used         # GREEN (vs S29's 3.3 Gi RED, +81.7 Gi)

$ readlink proofs/.lake
/Users/rwalters/GitHub/lean-genius/proofs/.lake
                                   # worktree → main repo cache (correct)
```

## §4 S26 §3.2/§3.3 paste (verbatim)

Inserted after L361 in `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` (immediately following the existing `burnside_p_squared_q_p_gt_q` which is the `a=2` instance of the new theorem).

### §4.1 `burnside_p_pow_a_q_q_lt_p` (45 LOC)

Generalizes `burnside_p_squared_q_p_gt_q` from `(a := 2)` to `(a := a)` with `1 ≤ a` hypothesis. Line-for-line copy of the existing proof body — only the type signature and the final `burnside_pq_with_normal_pSylow` invocation change. Discharges `|G| = p^a · q` whenever `q < p`.

For `a = 1` this would reduce to the squarefree case (already covered axiom-free by `burnside_pq_pq_case`). For `a = 2` this is `burnside_p_squared_q_p_gt_q` (subsumed by this theorem for the `q < p` direction). For `a ≥ 3` this is genuinely new content peeling shapes off the axiom whenever `q < p`.

### §4.2 `burnside_p_q_pow_b_p_lt_q` (12 LOC wrapper)

```lean
theorem burnside_p_q_pow_b_p_lt_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] {b : ℕ}
    (hb : 1 ≤ b) (hpq : p < q)
    (hcard : Nat.card G = p * q ^ b) :
    IsSolvable G := by
  have hcard' : Nat.card G = q ^ b * p := by rw [hcard]; ring
  exact burnside_p_pow_a_q_q_lt_p (p := q) (q := p) (a := b) hb hpq hcard'
```

Mirror of `burnside_p_pow_a_q_q_lt_p` with primes swapped. Discharges `|G| = p · q^b` whenever `p < q`.

## §5 Docker verification

### §5.1 Baseline (S30 re-verify)

```
$ timeout 1500 ./proofs/scripts/docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ07
... (210s wall-clock)
⚠ [3074/3074] Built Proofs.AbelRuffiniGaloisExtensionsOQ07 (18s)
warning: Proofs/AbelRuffiniGaloisExtensionsOQ07.lean:293:17: unused variable `hp`
Note: This linter can be disabled with `set_option linter.unusedVariables false`
... [#print signature output for 17 theorems]
Build completed successfully (3074 jobs).
=== Build succeeded ===
```

**Outcome**: GREEN. 3074 jobs, 0 errors, 1 pre-existing unused-variable warning (line 293, predates S30). Confirms S30 BUILD-FIX still holds 12 days later at the same Mathlib pin.

### §5.2 S31 paste verify

```
$ timeout 1500 ./proofs/scripts/docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ07
... (150s wall-clock, warm cache)
[3074/3074] Built Proofs.AbelRuffiniGaloisExtensionsOQ07
... [#print signature for new theorems + 17 existing]
Build completed successfully (3074 jobs).
=== Build succeeded ===
```

**Outcome**: GREEN. 3074 jobs, 0 errors, same 1 pre-existing warning. New theorems elaborate cleanly. No Mathlib API drift surfaced — the S26 spec written 14 days before BUILD-FIX still compiles verbatim because the proof structure mirrors `burnside_p_squared_q_p_gt_q` which is itself GREEN at S30.

## §6 S32 dispatch-wiring picker matrix

| Option | LOC | Build risk | Mathematical value | Recommendation |
|---|---|---|---|---|
| (a) Insert `b=1 ∧ q<p` and `a=1 ∧ p<q` branches in `burnside_pq` dispatch (no axiom-hypothesis tightening) | ~15-20 | Low (additive `by_cases`) | Realizes the S31 paste — actually shrinks what the axiom carries | **Recommended** for S32 first step |
| (b) Same as (a) + tighten axiom hypothesis from `4 ≤ a + b` to explicit shape disjunction | ~30-40 | Moderate (changes axiom signature; dispatch must thread the new hypothesis) | Honest accounting — axiom signature reflects what's actually needed | S32+ once (a) is in |
| (c) Implement S26 §3.4 hard direction `(a ≥ 3, p < q, b = 1)` via new helper `sylow_count_eq_one_of_lt_prime_pow_n` | ~80 | High (new helper + new theorem + dispatch) | Genuinely new content (closes the `(a≥3, p<q)` residue strip) | S32+ once (a)/(b) are in |
| (d) Character-theory route for `(a ≥ 2 ∧ b ≥ 2)` residue (Burnside 1904) | ~500-2000 | Very high | The genuine open content | Long-horizon |

## §7 Honesty calibration

- S31 paste is real Lean content (57 LOC of new theorem bodies + 10 LOC of docstrings), Docker-verified GREEN.
- But the axiom-count is **unchanged at 1**. The two new theorems sit available but UNUSED by `burnside_pq` dispatch — the axiom still carries the full `4 ≤ a + b` shape.
- So S31 does NOT yet narrow the axiom's responsibility. That happens at S32 when the dispatch branches wire in.
- Framing this as "axiom narrowing" would be over-claiming. Framing this as "scaffold paste preparing S32 dispatch wiring" is honest.
- Two Docker builds (210s baseline + 150s paste verify) consumed within 1h24min window — both well under the 60min/job soft cap.

## §8 Memory citations

- Pattern: post-build-fix STATE-SYNC → pivot to ACT when baseline re-verify completes in budget (general pattern, no specific memory file)
- Pattern: peel-off recipe paste from session memo (S26 §3.2/§3.3 was the spec; S31 is the paste; S32 is the dispatch wiring) — multi-session decomposition standard for RICH problems with large LOC budgets

## §9 PR

Branch: `feature/researcher-1`
Files changed:
- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` (+67 LOC, +2 theorems)
- `src/data/proofs/abel-ruffini-galois-extensions-oq-07/meta.json` (lineCount 1894→1961, theoremCount 38→40)
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json` (phase BUILD-FIXED→ACT, iter 30→31, focus/nextAction/progressSummary prepend, lastUpdate)
- `research/problems/abel-ruffini-galois-extensions-oq-07/state.md` (head replacement: BUILD-BLOCKER→ACT, iter 29→31; S31 entry prepend; S29→S1 tail preserved verbatim)
- `research/problems/abel-ruffini-galois-extensions-oq-07/session-31-act-peeloff-paste.md` (NEW — this file)

Label: `research`. No `loom:review-requested` (per CLAUDE.md, deployer merges math PRs directly).
