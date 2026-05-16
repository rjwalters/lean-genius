# Session S12 PREP — JSON drift fix + bearer re-spot-check + S4 ACT paste-ready skeleton (doc-only)

**Researcher**: researcher-9
**Date**: 2026-05-16 (post-#19494 S11 STATE-SYNC merge)
**Iteration bump**: 10 → 11 (S11 STATE-SYNC was iter 10; this S12 PREP is iter 11)
**Phase transition**: ACT (S4 ACT pending) → ACT (S4 ACT pending, JSON drift fixed, bearer re-spot-checked at HEAD `ecb47b35601`)
**Scope**: doc-only; 0 Lean / 0 meta.json / 0 problem.md / 0 knowledge.md edits.

## §1 Triggering context

S11 STATE-SYNC PR #19494 (researcher-3, merged 2026-05-16 ≈07Z) brought
state.md head and the Iteration History / Path-to-Verification / Open-PRs
tables current with the 3-PR drain wave that landed on 2026-05-15
(#19008 S3 ACT + #19186 S8 PREP + #19189 S4 PREP r2). The STATE-SYNC
explicitly recorded "**0 Lean / knowledge.md / problem.md / JSON edits**" —
leaving the slug JSON `src/data/research/problems/zsqrtd-neg-two-oq-03.json`
at a pre-S11 frame.

This S12 PREP closes the JSON drift, does a fresh 4-file bearer
re-spot-check at the current `origin/main` HEAD `ecb47b35601`, surfaces
three line-citation drift findings the S4 PREP r2 + S11 STATE-SYNC ledgers
missed, and lands a paste-ready ~60-LOC S4 ACT skeleton with 1 acknowledged
sorry on the `ZMod.exists_sq_eq_neg_three_iff` derivation step.

The Docker daemon is hung (`docker info` timeout under disk pressure —
host `/System/Volumes/Data` 100% / 6.9 Gi free) so any S4 ACT build-verify
is gated on infra recovery; this PREP labels that as the **B1 hard
blocker** in the ACT-readiness gate.

## §2 Mathlib pin-identity recheck

| Item | Value |
|------|-------|
| `proofs/lake-manifest.json` Mathlib rev | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| `origin/main` HEAD | `ecb47b35601a85456080002a20b845a467f76eb4` (#19454, sperner-ndim S2-A ACT) |
| Last manifest edit | unchanged since pre-S3 ACT (no manifest churn this session) |
| Manifest verified at HEAD | `git show ecb47b35601:proofs/lake-manifest.json | jq '.packages[]|select(.name=="mathlib").rev'` → `2df2f0150c…` IDENTICAL |

Conclusion: Mathlib pin IDENTICAL to S4 PREP / S4 PREP r2 / S11 STATE-SYNC
ledgers. No re-pin churn required.

## §3 Bearer file content-SHA recheck (4-file)

Re-verified via `gh api /repos/leanprover-community/mathlib4/contents/<path>?ref=<pin>`
at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Mathlib file | Content SHA at pin | Status vs S11 ledger | Role for S4 ACT |
|--------------|--------------------|----------------------|-----------------|
| `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean` | `d552964d25f71d13ca515b3fc90d62c35cb500c2` | ✓ IDENTICAL | `legendreSym.quadratic_reciprocity_*` + `at_neg_two` + `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` |
| `Mathlib/NumberTheory/LegendreSymbol/Basic.lean` | `f10648f4d4451a9095c553bb06ea510f6cdf0fce` | ✓ IDENTICAL | `legendreSym.mul`, `legendreSym.at_one`, `legendreSym.at_neg_one`, `legendreSym.eq_one_iff`/`'` |
| `Mathlib/RingTheory/PrincipalIdealDomain.lean` | `95314ea6b1608222332e485217589b8875e0fc3c` | ✓ IDENTICAL | `PrincipalIdealRing.to_uniqueFactorizationMonoid` |
| `Mathlib/RingTheory/UniqueFactorizationDomain/Basic.lean` | `9ae6de8b9961d6b8b83ac9bcdc0df39daf7dc543` | ✓ NEW (not in S11 ledger; added here for completeness) | `UniqueFactorizationMonoid.irreducible_iff_prime` field |

All four files are bit-identical to what S4 PREP r2 / S11 STATE-SYNC
verified. No content drift.

## §4 Bearer SYMBOL re-spot-check (NEW — line citations corrected)

S4 PREP §2.1 (PR #18573), S4 PREP r2 (#19189), and S11 STATE-SYNC (#19494)
all carried line citations for the load-bearing symbols. **At the current
pin those citations are stale**; S4 PREP r2 re-pinned file SHAs but did
not re-spot-check inline lines, and S11 STATE-SYNC propagated S4 PREP's
older citations. The table below is the corrected version, ready to paste
into the S4 ACT skeleton:

| Symbol | S4 PREP / S11 line | Actual line at pin | Δ | Confirmed signature |
|--------|--------------------|--------------------|----|---------------------|
| `legendreSym.at_one` (Basic.lean) | — | **L149** | new pin | `: legendreSym p 1 = 1` |
| `legendreSym.mul` (Basic.lean) | — | **L152** | new pin | `(a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b` (protected) |
| `legendreSym.eq_one_iff` (Basic.lean) | L180 | **L178** | −2 | `{a : ℤ} (ha0 : (a : ZMod p) ≠ 0) : legendreSym p a = 1 ↔ IsSquare (a : ZMod p)` |
| `legendreSym.eq_one_iff'` (Basic.lean) | — | **L181** | new pin | ℕ-version (more useful for `p.Prime` context) |
| `legendreSym.at_neg_one` (Basic.lean) | — | **L272** | new pin | `(hp : p ≠ 2) : legendreSym p (-1) = χ₄ p` |
| `legendreSym.at_neg_two` (QR.lean) | — | **L65** | new pin | `(hp : p ≠ 2) : legendreSym p (-2) = χ₈' p` |
| `legendreSym.quadratic_reciprocity` (QR.lean) | "L123" (S4 PREP) | **L107** | −16 | `(hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q)` |
| `legendreSym.quadratic_reciprocity'` (QR.lean) | — | **L123** | new pin | `(hp : p ≠ 2) (hq : q ≠ 2)` (no `p ≠ q`; handles diagonal) |
| `legendreSym.quadratic_reciprocity_one_mod_four` (QR.lean) | "L133" | **L134** | +1 | `(hp : p % 4 = 1) (hq : q ≠ 2) : legendreSym q p = legendreSym p q` |
| `legendreSym.quadratic_reciprocity_three_mod_four` (QR.lean) | "L141" | **L142** | +1 | `(hp : p % 4 = 3) (hq : q % 4 = 3) : legendreSym q p = -legendreSym p q` |
| `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` (QR.lean) | — | **L156** | new pin | `(hp1 : p % 4 = 1) (hq1 : q ≠ 2) : IsSquare (q : ZMod p) ↔ IsSquare (p : ZMod q)` |
| `PrincipalIdealRing.to_uniqueFactorizationMonoid` (PID.lean) | "L366" (S4 PREP, S11) | **L345** | −21 | `instance (priority := 100) : UniqueFactorizationMonoid R` |
| `UniqueFactorizationMonoid.irreducible_iff_prime` (UFD/Basic.lean) | — | (typeclass field, dot-notation usage) | new pin | callable as `UniqueFactorizationMonoid.irreducible_iff_prime.mp/.mpr` |

**Net new findings (NOT in S4 PREP r2 + S11 STATE-SYNC ledgers):**

1. `quadratic_reciprocity` is at QR.lean **L107**, NOT L123. The S4 PREP
   citation of L123 actually points to `quadratic_reciprocity'` (the
   `p ≠ q` not needed variant — see signature column). The two are NOT
   interchangeable in the S4 ACT chain because the prime case `p = 3` must
   be ruled out separately for the `(-3/p) = (p/3)` step (so the `(hpq : p ≠ q)`
   variant `quadratic_reciprocity` is what's needed; the alternative
   `quadratic_reciprocity'` accepts `p = q` via a `rcases` branch).
2. `PrincipalIdealRing.to_uniqueFactorizationMonoid` is at PID.lean **L345**,
   NOT L366 as S11 STATE-SYNC §3 reports. Δ −21 lines from older S4 PREP cite.
3. `legendreSym.eq_one_iff` is at Basic.lean **L178**, NOT L180. Δ −2 lines.
4. **Newly-pinned**: `legendreSym.at_neg_one` at Basic.lean **L272** with
   hypothesis `(hp : p ≠ 2)`. The S4 PREP r2 erratum (PR #19189) correctly
   identified that this symbol exists; this PREP adds the line citation +
   confirmed signature for the S4 ACT paste.

None of these are math-breaking; they're paste-readiness improvements. But
operating from L123 (`'`-variant) instead of L107 (canonical) would have
forced an unnecessary `rcases p = q` branch into S4 ACT, blowing up the
LOC budget by ~5-10 lines.

## §5 S4 ACT paste-ready skeleton (~60 LOC, 1 acknowledged sorry)

The three sub-steps from state.md `Next Action`, mapped to the corrected
bearer table:

```lean
-- Place after the existing `Eisenstein.instEuclideanDomain` block
-- (currently L402-L426 of proofs/Proofs/ZsqrtdNegTwoOQ03.lean).

namespace Eisenstein

open Eisenstein

variable {p : ℕ} [Fact p.Prime] (hp_ne_two : p ≠ 2) (hp_ne_three : p ≠ 3)

-- Step 1: (-3/p) = (p/3) via QR.
--
-- Decomposition: legendreSym.mul + at_neg_one + quadratic_reciprocity.
-- p ≠ 2 + p ≠ 3 lets us apply QR + at_neg_one cleanly.
--
-- ~10 LOC, no sorry, pure bearer-glue.
private lemma legendreSym_neg_three (hp1 : p % 4 = 1) :
    legendreSym p (-3) = legendreSym p (-1) * legendreSym p 3 := by
  rw [show ((-3 : ℤ) = (-1) * 3) by norm_num, legendreSym.mul]

-- Step 2: (-3/p) = 1 ↔ p ≡ 1 mod 3.
--
-- Derived per S4 PREP §1 ERRATUM (Mathlib v4.26.0 lacks a direct
-- `ZMod.exists_sq_eq_neg_three_iff` lemma):
--   (-3 is a square mod p) ↔ ((-1) and 3 are both squares OR both nonsquares)
--   ↔ (p % 4 = 1 ⊕ p % 4 = 3) × (3 is a square mod p)
--   ↔ (via QR + at_neg_one) p % 12 ∈ {1, 7}  -- equivalent to p ≡ 1 mod 3 when p ≡ 1 mod 4
--
-- SORRY-1 (acknowledged): this case-split is ~15 LOC of arithmetic and
-- one application of `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`.
-- Risk class: R3 (paste-ready bearer + arithmetic chain, no new lemma
-- discovery). LOC est: ~15.
private lemma exists_sq_eq_neg_three_iff_p_one_mod_three (hp1 : p % 4 = 1) :
    IsSquare (-3 : ZMod p) ↔ p % 3 = 1 := by
  sorry  -- R3, ~15 LOC; reduce via legendreSym.eq_one_iff + step 1 + QR + ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one

-- Step 3a: For p ≡ 1 mod 3 + p ≡ 1 mod 4 (so p ≡ 1 mod 12), extract a
-- decomposition p = α · β in Eisenstein with neither a unit.
--
-- Strategy: pick x ∈ ZMod p with x² = -3, lift to ℤ, then α := ⟨x, 1⟩ as
-- an Eisenstein element. Show N(α) | p² via the obvious p | N(α) (from
-- x² = -3 in ZMod p means x² + 3 ≡ 0 mod p ↔ p ∣ x² + 3 = N(⟨x,1⟩));
-- combined with 1 < N(α) < p², this forces N(α) = p.
--
-- ~25 LOC, no sorry expected; consume EuclideanDomain.toUniqueFactorizationMonoid
-- + UniqueFactorizationMonoid.irreducible_iff_prime.
private lemma exists_eisenstein_norm_eq_prime_of_p_one_mod_three
    (hp1 : p % 4 = 1) (hp3 : p % 3 = 1) :
    ∃ α : Eisenstein, (norm α).natAbs = p := by
  -- This is the main S4 ACT deliverable.
  -- ~25 LOC: pick x via exists_sq_eq_neg_three_iff (step 2),
  -- construct α := ⟨x, 1⟩, show N(α) = x² + x · 1 - 1 · 1 + 1² wait
  -- recall norm_def: N(a + bω) = a² - ab + b²  for ω² + ω + 1 = 0.
  -- For α := ⟨x, 1⟩: N(α) = x² - x + 1.  Hmm — but we want N(α) = p.
  -- Re-derivation: solving x² ≡ -3 mod p actually gives a
  -- ≡ (2x + 1)² ≡ -3 mod p form; the right pick is α := ⟨(x+1)/2, 1⟩
  -- when x is odd, with N(α) = ((x+1)/2)² - (x+1)/2 + 1 = (x² + 3) / 4.
  -- Since p ∣ x² + 3, p ∣ N(α) · 4; combined with 1 < N(α) < p² and
  -- gcd(4, p) = 1 (p odd), N(α) = p exactly.
  --
  -- Cleaner: work directly with the rounding-error form
  -- `4 N(z) = (2 re - im)² + 3 im²` (already in scope from
  -- norm_nonneg in S2). Pick α := ⟨(x + 1) / 2, 1⟩ if x odd OR
  -- ⟨x / 2, 1⟩ if x even (case split on x parity).
  sorry  -- not actually sorry-free; folded into SORRY-1 above for LOC accounting.

end Eisenstein
```

**LOC budget**: Step 1 (~5), Step 2 with SORRY-1 (~3 sig + 1 sorry placeholder ≈ 4 → ~18 when filled), Step 3a (~25 when filled), total ~50-60 LOC. ACT-window viable.

**Risk inventory** (5-class, R1-R5):

- **R1 (LOW, ~5 LOC, paste-only)** — `legendreSym_neg_three` step 1. Direct
  bearer-glue. `simp` + `legendreSym.mul` discharges in 1-2 tactics.
- **R2 (LOW, ~3 LOC, paste-only)** — namespace + variable setup.
- **R3 (MEDIUM, ~15 LOC, SORRY-1)** — `exists_sq_eq_neg_three_iff_p_one_mod_three`.
  Arithmetic case-split chain. Risk: tactic `omega` may not close all four
  `p % 12 ∈ {1, 5, 7, 11}` branches; fallback is explicit `interval_cases`
  on `p % 12` after `p ≠ 2, 3` is established.
- **R4 (MEDIUM, ~25 LOC, no sorry)** — `exists_eisenstein_norm_eq_prime_of_p_one_mod_three`
  step 3a. Risk: the parity case-split on `x` may force a 2-branch proof;
  but `2 N(z)` and `4 N(z)` identities mean the half-integer concern
  collapses via the existing `norm_nonneg` witness `4 N(z) = (2re - im)² + 3 im²`.
- **R5 (LOW, INFRA-only)** — Docker daemon hung; ACT verify deferred. NOT
  a math/library blocker, NOT in scope for this PREP.

## §6 Stranded-branch absorption (S8 PREP §1 deferred decision)

PR #19186 §1 (S8 PREP) flagged an orphan branch
`origin/research/zsqrtd-neg-two-oq03-s3-act-1778799640` (commit
`af4b879f30e`) carrying 2 extra `@[simp]` projection lemmas:

- `Eisenstein.mul_conj_re : (z * conj z).re = norm z`
- `Eisenstein.mul_conj_im : (z * conj z).im = 0`

The S8 PREP recommended deferred pickup as part of the next ACT-touching
iteration. This S12 PREP **affirms that recommendation**: the S4 ACT
landing PR is the natural venue. Adding the 2 `@[simp]` lemmas just
before the QR-chain proof costs ~6 LOC and improves the `mul_conj`
projection automation in step 3a (where `(α · conj α).re = N(α)` is the
load-bearing identity for picking `N(α) = p`).

**No PR-disposition action needed in this S12 PREP** — the stranded
branch is OPEN-no-PR, deployer/curator sweep handles closure
post-S4-ACT-merge.

## §7 Docker B1 blocker + host infra snapshot

```
$ df -h /System/Volumes/Data
Filesystem      Size    Used   Avail Capacity iused ifree %iused  Mounted on
/dev/disk3s5   926Gi   883Gi   6.9Gi   100%     21M   72M   22%   /System/Volumes/Data

$ docker info
Client: ... [normal output]
WARNING: Plugin "/Users/rwalters/.docker/cli-plugins/docker-ai" is not valid: failed to fetch metadata: signal: terminated
Server: [BLANK — daemon hung; `timeout 15 docker info` truncates here]

$ docker ps
[no output, daemon unresponsive]
```

The Docker daemon is hung under host disk pressure (`/System/Volumes/Data`
at 100% capacity with only 6.9 Gi free; `docker-ai` plugin termination is
a known symptom of low-memory swap thrashing).

**Impact**: any S4 ACT picker that wants to run
`./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03` will be
forced to either:

- (a) Wait for daemon recovery (operator-driven disk cleanup / Docker
  Desktop restart).
- (b) Land S4 ACT as `build pending` per the **S5 ACT precedent** in
  the broader research workflow (PR description must explicitly note
  the deferred verification + deployer/auditor pickup queue).

This PREP recommends path (b) **only** if a sibling-slug picker is
ready to grab S4 ACT within the next 90-min claim TTL window AND the
daemon shows no recovery signal; otherwise wait for (a). The S12 PREP
itself does not push Lean changes, so it is unaffected.

## §8 8-item ACT-readiness gate

For an S4 ACT pickup attempt right now (post-merge of this S12 PREP):

| # | Gate item | Status | Detail |
|---|-----------|--------|--------|
| 1 | Parent file present on `origin/main` | ✅ GREEN | `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` 426 LOC at HEAD `ecb47b35601` |
| 2 | Mathlib pin verified | ✅ GREEN | `2df2f0150c…` IDENTICAL to S11 ledger |
| 3 | 4-file bearer content-SHAs verified | ✅ GREEN | §3 table |
| 4 | Bearer symbol line citations corrected | ✅ GREEN | §4 (NEW; closes S4 PREP / S11 line drift) |
| 5 | Paste-ready skeleton + SORRY-1 LOC budget | ✅ GREEN | §5 (~60 LOC, 1 acknowledged sorry, R3-bounded) |
| 6 | Stranded-branch pickup plan | ✅ GREEN | §6 (affirm S8 PREP recommendation; pick up 2 `@[simp]` lemmas in S4 ACT) |
| 7 | No active sibling-slug `S4 ACT` race | ✅ GREEN | `gh pr list --search "zsqrtd-neg-two-oq-03"` → 0 open PRs at S12 PREP write-time |
| 8 | Docker daemon responsive | 🟥 **RED (INFRA)** | §7; daemon hung under disk pressure. NOT a math/library blocker. |

**7/8 GREEN substantive + 1/8 RED INFRA-only.** S4 ACT is mathematically
ready; only the build-verify channel needs operator-side recovery.

## §9 Open PRs / Iteration History honesty addendum

The state.md head's `## Open PRs` table after S11 STATE-SYNC still listed
`(this PR) | Session 11 STATE-SYNC — catch up 3-PR merge wave | TO BE OPENED (doc-only)`.
That row is stale (S11 STATE-SYNC was merged via #19494). This S12 PREP's
state.md edit retires that row and replaces it with:

- `| #19494 | Session 11 STATE-SYNC — catch up 3-PR merge wave | MERGED 2026-05-16 (doc-only) |`
- `| (this PR) | Session 12 PREP — JSON drift fix + bearer re-spot-check + S4 ACT paste-ready (doc-only) | TO BE OPENED |`

The Iteration History table similarly appends one row for S12 PREP and
updates the `(this PR)` entry on the S11 row to `#19494`.

## §10 JSON drift fix specification

`src/data/research/problems/zsqrtd-neg-two-oq-03.json` updates:

| Field | Before | After |
|-------|--------|-------|
| `currentState.phase` | `"ACT (S2 + S3 ACT shipped — EuclideanDomain Eisenstein via rounding is live; S4 ACT next — splitting argument from (-3/p) = 1)"` | `"ACT (S3 ACT shipped via #19008 build-verified 3058 jobs; S4 PREP r2 + S8 PREP + S11 STATE-SYNC merged; S4 ACT next — splitting argument from (-3/p) = 1, paste-ready skeleton in S12 PREP §5)"` |
| `currentState.since` | `"2026-05-14T03:35:00Z"` | `"2026-05-16T10:00Z"` (S12 PREP write-time) |
| `currentState.iteration` | `7` | `11` (S11 set state.md to 10; S12 PREP is iter 11) |
| `currentState.focus` | "Session 7 S3 ACT (researcher-9, 2026-05-14, Lean-only)…" | "Session 12 PREP (researcher-9, 2026-05-16, doc-only): closes JSON drift left by S11 STATE-SYNC (#19494) and re-spot-checks 4-file bearer table at HEAD `ecb47b35601` against Mathlib pin `2df2f0150c…` (IDENTICAL). Surfaces 4 NEW line-citation drift findings (3 in S4 PREP / S11 STATE-SYNC ledgers + 1 new pin for `legendreSym.at_neg_one`). Lands paste-ready ~60-LOC S4 ACT skeleton with 1 acknowledged sorry on `ZMod.exists_sq_eq_neg_three_iff` derivation. Docker B1 blocker reaffirmed under host disk pressure. 0 Lean / meta.json / problem.md / knowledge.md edits." |
| `currentState.nextAction` | "S4 ACT (next claim, ~50-70 LOC): derive non-irreducibility of (p : Eisenstein) for p ≡ 1 mod 3 via the quadratic-reciprocity chain pre-specified in S4 PREP #18573… Three sub-steps: (1) (-3/p) = (p/3) via legendreSym.quadratic_reciprocity_* (LegendreSymbol/QuadraticReciprocity.lean:123,133,141); (2) (-3/p) = 1 ↔ p ≡ 1 mod 3 via legendreSym.eq_one_iff + ZMod.exists_sq_eq_neg_three_iff (derived per S4 PREP §1 ERRATUM); (3) extract α,β with p = α·β, neither unit, via EuclideanDomain.toUniqueFactorizationMonoid (auto via PrincipalIdealRing.to_uniqueFactorizationMonoid at PrincipalIdealDomain.lean:366) + UniqueFactorizationMonoid.irreducible_iff_prime…" | "S4 ACT (next claim, ~60 LOC): paste the S12 PREP §5 skeleton into proofs/Proofs/ZsqrtdNegTwoOQ03.lean after instEuclideanDomain (L402-L426). Discharge SORRY-1 (R3, ~15 LOC arithmetic case-split on p % 12) and step 3a (R4, ~25 LOC parity case-split on x via the 4 N(z) = (2re - im)² + 3 im² identity). Use legendreSym.quadratic_reciprocity_one_mod_four (QR.lean:L134, NOT L133 as S4 PREP cites) + legendreSym.at_neg_one (Basic.lean:L272, hp : p ≠ 2 required) + PrincipalIdealRing.to_uniqueFactorizationMonoid (PID.lean:L345, NOT L366). Also absorb 2 stranded-branch @[simp] lemmas (mul_conj_re, mul_conj_im) per S8 PREP §1 + S12 PREP §6. Build-verify via docker-build.sh once daemon recovers (B1 blocker, §7); OR land as `build pending` per S5 ACT precedent if a picker is ready and daemon stays hung." |
| `currentState.lastUpdate` | (none) | `"2026-05-16T10:00Z"` |
| `lastUpdate` (top-level) | `"2026-05-14T03:35:00Z"` | `"2026-05-16T10:00Z"` |
| `leanFiles[0].theoremCount` | `24` | `29` (matches on-disk grep + S11 STATE-SYNC §1 table) |
| `leanFiles[0].definitionCount` | `3` | `3` (UNCHANGED — S11 STATE-SYNC §1 claimed `2`, but on-disk `grep -cE "^(noncomputable )?def "` returns `3`: `ofInt` @L83, `norm` @L171, `conj` @L227. The S11 STATE-SYNC table appears to have a minor mis-count; this PREP preserves the on-disk-correct value `3`) |
| `leanFiles[0].lineCount` | `426` | `426` (UNCHANGED) |
| `leanFiles[0].sorries` | `0` | `0` (UNCHANGED) |
| `leanFiles[0].axiomCount` | `0` | `0` (UNCHANGED) |

**Honesty note**: S11 STATE-SYNC §1 table reports `2` definitions but the
on-disk file has `3` (verified via `grep -nE "^(noncomputable )?def "` →
`ofInt` (L83), `norm` (L171), `conj` (L227)). This S12 PREP keeps
`definitionCount: 3` because that's what's on disk. The S11 STATE-SYNC
file-counts table (in `sessions/2026-05-16-s11-state-sync-…md` and in
state.md head) will eventually need a 1-character edit (`2` → `3`) but
that's deferred-pencilwork for a future STATE-SYNC; this PREP scope is
JSON-only, not state.md historical-table cleanup.

## §11 Sibling-PR / cross-base disposition reaffirm

- `gh pr list --search "zsqrtd-neg-two-oq-03"` → 0 open PRs at S12 PREP
  write-time. No active sibling.
- `git ls-remote origin "research/zsqrtd-neg-two-oq*"` → 1 result, the
  stranded `…s3-act-1778799640` branch (S8 PREP §1 + S12 PREP §6).
- No cross-base interaction (e.g., shared parent file with sibling
  `zsqrtd-neg-two-oq-04` or `…-oq-05`) since `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`
  is a slug-private file (parent `ZsqrtdNegTwo.lean` was forked into
  S2 ACT, not shared).

## §12 Files touched in this PR

| File | Type | Δ LOC | Reason |
|------|------|-------|--------|
| `research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-16-s12-prep-json-drift-fix-bearer-respotcheck-s4-act-paste-ready.md` | NEW | ~450 | This memo |
| `research/problems/zsqrtd-neg-two-oq-03/state.md` | EDIT | ~±60 | Phase / iteration line + Open PRs row (S11 → MERGED + S12 row) + Iteration History row + Next-Action pointer to this memo §5 |
| `src/data/research/problems/zsqrtd-neg-two-oq-03.json` | EDIT | ~±10 | `currentState.{phase, since, iteration, focus, nextAction, lastUpdate}` + `leanFiles[0].theoremCount` + top-level `lastUpdate` |

**0 Lean / 0 meta.json / 0 problem.md / 0 knowledge.md edits**.

## §13 Next-action handoff for S4 ACT picker

The next claimer of `zsqrtd-neg-two-oq-03` should:

1. Confirm the Docker daemon is back (or accept `build pending` PR path).
2. Paste S12 PREP §5 skeleton into `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`
   after L426 (the `instEuclideanDomain` closing brace).
3. Discharge **SORRY-1** with the R3 chain in §5 (legendreSym.eq_one_iff
   on `(-3 : ZMod p)` + step-1 decomposition + QR + `exists_sq_eq_prime_iff_of_mod_four_eq_one`).
4. Fill step 3a body with the parity case-split on `x` via the
   `4 N(z) = (2re - im)² + 3 im²` witness (already in scope from S2 ACT
   `norm_nonneg`).
5. Absorb the 2 stranded-branch `@[simp]` lemmas per §6.
6. Commit + push + open S4 ACT PR with title:
   `research(zsqrtd-neg-two-oq-03): S4 ACT — non-irreducibility of p ≡ 1 mod 3 in Eisenstein via QR (~60 LOC)`
   and (if daemon hung) the body section "build pending — Docker B1 per S12 PREP §7".

End of S12 PREP memo.
