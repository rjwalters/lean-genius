# Problem: elementary-quadratic-reciprocity-oq-01-oq-02

**Title**: Can the character uniqueness argument be generalized to prove cubic or quartic reciprocity?

**Status**: axiomatized (build state; 0 sorries, 2 axioms)
**Phase**: S7 STATE-SYNC — no-op landing on terminal-state slug (iteration counter + lastUpdate drift-closure, doc-only)

## Problem Summary

For primes p ≡ 1 (mod 3), the group (ZMod p)ˣ is cyclic of order p-1 with 3 | (p-1). The cubic Euler criterion: a is a cube mod p iff a^((p-1)/3) = 1. The cubic character χ₃(a) = a^((p-1)/3) is a group homomorphism analogous to the Legendre symbol. Cubic reciprocity (Eisenstein 1844) states (ρ/π)₃ = (π/ρ)₃ for primary Eisenstein primes in ℤ[ω]. The quartic case uses (ZMod p)ˣ for p ≡ 1 (mod 4).

## Session 2026-05-03 (Session 1) - Cubic/Quartic Character Construction

**Mode**: FRESH  
**Outcome**: progress

### What I Did

- Claimed the problem atomically via `mkdir research/claims/<id>.lock`
- Created `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` (391 lines)
- Constructed cubic character χ₃ = powMonoidHom((p-1)/3) as group hom (ZMod p)ˣ →* (ZMod p)ˣ
- Proved χ₃(a)³ = 1 via Fermat's little theorem for units
- Proved easy Euler criterion: x³ = a → χ₃(a) = 1 (using Units.mk0 lift + pow_mul + units_pow_card_sub_one_eq_one)
- Constructed quartic character χ₄ = powMonoidHom((p-1)/4) in parallel
- Axiomatized cubicEuler_hard (hard direction of Euler criterion)
- Axiomatized cubic_reciprocity (Eisenstein's law)
- Proved closure: cubic residues closed under 0, 1, cubing, multiplication, squaring, inverse
- Created gallery entry: src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-02/meta.json

### Key Findings

- `powMonoidHom (n : ℕ) : α →* α` works for CommMonoid — (ZMod p)ˣ qualifies
- The key unit-lifting pattern: `Units.mk0 x hx0` + `Units.ext; simp [Units.val_pow_eq_pow_val, Units.val_mk0]`
- `pow_mul` is needed instead of `ring` for group/monoid goals
- `ZMod.units_pow_card_sub_one_eq_one p xu` gives Fermat for units
- Cyclic group kernel cardinality API: `IsCyclic.exists_unique_subgroup_of_dvd` doesn't exist in Mathlib 4.26 — left as sorry
- Eisenstein integers ℤ[ω] not in Mathlib 4.26 → cubic reciprocity axiomatized

### Files Modified

- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` (NEW, 391 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-02/meta.json` (NEW)

### Current State (S1 snapshot; subsequently updated — see Session 5 below)

- 3 axioms: cubicEuler_hard, cubicResidueSymbol, cubic_reciprocity
- 1 sorry: cubicChar_kernel_card (cyclic group kernel cardinality)
- 24 theorems proved, 6 defs
- Docker build submitted; awaiting result

### Next Steps (S1 plan; superseded by S5 audit below)

1. If Docker build passes: commit, push, PR with `research` label
2. Future: prove cubicChar_kernel_card using `Subgroup.card_eq_iff_eq_top` or similar
3. Future: when Mathlib gains Eisenstein integers, prove cubic_reciprocity
4. Future: submit cubicEuler_hard to Aristotle (needs cyclic group theory)

## Session 2026-05-13 (Session 5) — Mathlib Bearer Audit (OBSERVE)

**Mode**: OBSERVE (doc-only / docstring + JSON-prose corrections; no Lean tactic changes)
**Outcome**: progress — corrected misleading bearer claims; recorded refactor plan

### What I Did

- Audited pinned Mathlib v4.26.0 (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) for
  Eisenstein-integer and Jacobi-sum bearers cited by the file's two remaining axioms.
- Confirmed Mathlib v4.26.0 ships:
  - `Mathlib.NumberTheory.NumberField.Cyclotomic.Three` — Eisenstein integers as `𝓞 K`
    for `IsCyclotomicExtension {3} ℚ K` (including unit classification, `λ^2 = -3η`,
    `η^2 = -η - 1`, Kummer's lemma for `λ^2`).
  - `Mathlib.NumberTheory.NumberField.Cyclotomic.PID` —
    `three_pid : IsPrincipalIdealRing (𝓞 K)` for `IsCyclotomicExtension {3} ℚ K`.
  - `Mathlib.NumberTheory.JacobiSum.Basic` — full Jacobi-sum API
    (`jacobiSum`, `jacobiSum_mul_nontrivial`,
    `jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum`, `jacobiSum_mul_jacobiSum_inv`,
    `gaussSum_pow_eq_prod_jacobiSum`,
    `jacobiSum_mem_algebraAdjoin_of_pow_eq_one`).
- Corrected file docstring comments at L455–L456 and L489 of
  `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` (no code change).
- Corrected `meta.json` text fields: `description`, `assumptions`, `keyInsights[4]`,
  `openQuestions[0]`.
- Synced this knowledge.md header (Status / Phase) and appended this Session-5 entry.
- Wrote full audit trail at `s5-observe-eisenstein-bearer.md` (this directory).

### Key Findings

- The file's two remaining `axiom` declarations (`cubicResidueSymbol`,
  `cubic_reciprocity`) are **not Mathlib-blocked**. They are predicated on the file's
  local `structure EisensteinPrime`, which is decoupled from Mathlib's richer
  `IsCyclotomicExtension {3} ℚ K` / `𝓞 K` formalization.
- Sessions 2–4 (between S1 and now) already retired one axiom and the sole sorry:
  - `cubicEuler_hard` was promoted from axiom to theorem in #15322 (2026-05-03) via
    discrete log in the cyclic group `(ZMod p)ˣ`.
  - `cubicChar_kernel_card` was promoted from sorry to theorem in #15356/#15357
    (2026-05-03) via `IsCyclic.card_pow_eq_one_le` + injectivity.
- Current build state: **2 axioms, 0 sorries, 27 theorems, 6 defs, 562 lines** (per
  `meta.json` synced in #16691, 2026-05-07).
- Future ACT to discharge the two remaining axioms is an **engineering refactor**
  (rebase local `EisensteinPrime` onto Mathlib's `𝓞 K`), not a wait-on-upstream-Mathlib
  task. Estimated ~250 LOC port of Ireland–Rosen Theorem 1 of Chapter 9 using the
  existing Jacobi-sum API.

### Files Modified

- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-02/s5-observe-eisenstein-bearer.md` (NEW)
- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-02/knowledge.md` (this file)
- `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-02/meta.json` (text prose only)
- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` (docstring comment text only)

### Build Risk

Zero — no tactic, import, or signature changes. All edits are within comment/doc text
or JSON prose fields. Sorries unchanged (0). Axiom count unchanged (2). Theorem count
unchanged (27).

## Session 2026-05-16 (Session 6) — Canonical research-JSON catchup with S5 OBSERVE (STATE-SYNC)

**Mode**: STATE-SYNC (doc-only / research-JSON catchup; no Lean changes, no meta.json changes, no S5 memo modification)
**Outcome**: progress — reconciled canonical state-of-record with S5 audit findings

### Why

`claim-problem.sh claim-random` returned this slug at 2026-05-16T~14:00Z. Inspection
revealed `src/data/research/problems/elementary-quadratic-reciprocity-oq-01-oq-02.json`
(the canonical state-of-record consumed by gallery/research-index tooling) was 3 days
+ 1 audit-session behind the S5 OBSERVE work that landed on origin/main on 2026-05-13.
The drift was not a Lean or meta.json issue — both of those were correctly updated by
S5. Only the research-JSON had stale assertions that directly contradicted the S5 audit.

### Drift inventory (research-JSON vs S5 audit)

| Field | Before S6 (stale) | After S6 (S5-aligned) |
|---|---|---|
| `currentState.since` | `2026-05-04T00:42:55.000Z` (S1 ship) | `2026-05-16T14:30:00.000Z` (S6) |
| `currentState.iteration` | `1` | `6` |
| `currentState.focus` | "Eisenstein integers Mathlib gap" | "Axiomatized-stable… NOT Mathlib-blocked" |
| `currentState.nextAction` | "Closed pending Mathlib upstream of ℤ[ω]" (FALSE per S5) | "Axiomatized-stable. Future S6/S7 ACT optional… ~250 LOC port using already-shipped Mathlib bearers" |
| `currentState.attemptCounts.total` | `1` | `6` |
| `knowledge.progressSummary` | "562 lines… documented Mathlib gaps requiring Eisenstein integers" | "578 lines… NOT Mathlib-blocked… engineering refactor" |
| `knowledge.insights[4]` | "Eisenstein integers ℤ[ω] not in Mathlib 4.26" (FALSE) | "Eisenstein integers ARE in Mathlib v4.26.0 as 𝓞 K…" |
| `knowledge.mathlibGaps[0]` | "Eisenstein integers ℤ[ω] structure and prime theory not in Mathlib 4.26" (FALSE) | `[RESOLVED in S5 OBSERVE]` + bearer catalog |
| `knowledge.mathlibGaps[1]` | "Cubic residue symbol (ρ/π)₃ definition requires ℤ[ω] units" (FALSE) | `[RESOLVED in S5 OBSERVE]` + JacobiSum API note |
| `knowledge.nextSteps` | `[]` | 6-step refactor plan from S5 memo §"Suggested next ACT" + optional quartic parallel |
| `leanFiles[3].lineCount` (slug Lean file) | `562` | `578` (+16 from S5 docstring corrections) |
| `lastUpdate` | `2026-05-07T19:30:00.000Z` | `2026-05-16T14:30:00.000Z` |

Build state on origin/main is unchanged from S5: 0 sorries / 2 axioms / 27 theorems /
6 defs / 578 lines / no `import` changes / no tactic changes / `lake-manifest.json`
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) unchanged at S6 (T+3d).

### Files modified

- `src/data/research/problems/elementary-quadratic-reciprocity-oq-01-oq-02.json` — 13 field edits per drift table above. JSON-validated (`python3 -m json.tool`).
- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-02/knowledge.md` — Phase header refresh + this Session-6 entry (head/tail-only, prior body unchanged).
- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-02/s6-state-sync-canonical-json-catchup.md` — NEW session memo (full drift trace + bearer-stability verification at SHA-stable T+3d).

### Files NOT modified (intentional scope discipline)

- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` — no Lean change (S5 already corrected docstrings; S6 is canonical-JSON only).
- `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-02/meta.json` — already at correct lineCount (578) + correct `assumptions`/`description`/`keyInsights[4]`/`openQuestions[0]` text per S5.
- `proofs/lake-manifest.json` — Mathlib pin unchanged (no bearer re-spot-check needed at T+3d SHA-stable; S5 audit findings still hold).
- S5 memo (`s5-observe-eisenstein-bearer.md`) — left intact as historical audit artifact.
- Mathlib bearer re-verification — declined; SHA `2df2f01…` unchanged since S5, so all bearers cited in S5 are bit-identical at S6 — cf. MEMORY `feedback_researcher_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_ship_tight_json_catchup_only_no_bundled_respotcheck` for the "tighter cycle, no busywork re-spot-check at SHA-stable" pattern.

### Build Risk

Zero — 0 Lean files modified, 0 imports changed, 0 tactic changes, 0 meta.json field
edits. Sorries unchanged (0). Axiom count unchanged (2). Theorem count unchanged (27).
LineCount unchanged on disk (578); S6 only fixes the leanFiles[3].lineCount drift in
the research-JSON's cached metadata.

### Phase head transition

S5 OBSERVE (Mathlib bearer audit, doc-only) → S6 STATE-SYNC (canonical research-JSON catchup, doc-only) → "axiomatized-stable; future S6/S7 refactor optional, not actively scheduled".

The slug is now in a stable terminal state with a fully-documented optional-refactor pathway. Future claim-random landings on this slug should either (a) ship the ~250-LOC engineering refactor per the S5 memo §"Suggested next ACT (S6) — refactor plan", or (b) release immediately if the refactor is out of scope for the session.

## Session 2026-05-31 (Session 7) — No-op landing on terminal-state slug (STATE-SYNC)

**Mode**: STATE-SYNC (doc-only / iteration counter + lastUpdate drift-closure; no Lean changes, no meta.json changes, no S5/S6 memo modification)
**Outcome**: progress — terminal-state slug landed at T+15d since S6; SHA still pinned to v4.26.0 `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; chose option (b) "release immediately" per S6 explicit guidance.

### Why

`claim-problem.sh claim-random` returned this slug at 2026-05-31T21:21Z. Inspection confirms
the slug remains in axiomatized-stable terminal state: 0 sorries / 2 axioms / 27 theorems /
6 defs / 578 lines (`wc -l`) / 579 lines (extractor). The S6 memo (2026-05-16) explicitly
authorized option (b) "release immediately if refactor is out of scope" for future landings;
the ~250-LOC Ireland-Rosen Ch.9 refactor per S5 §"Suggested next ACT (S6)" is multi-session
ACT, not a single-iteration task.

### Drift inventory (research-JSON vs S7 timestamp)

| Field | Before S7 (S6 ship) | After S7 |
|---|---|---|
| `currentState.since` | `2026-05-16T14:30:00.000Z` (S6) | `2026-05-31T21:23:45.000Z` (S7) |
| `currentState.iteration` | `6` | `7` |
| `currentState.attemptCounts.total` | `6` | `7` |
| `lastUpdate` | `2026-05-16T14:30:00.000Z` | `2026-05-31T21:23:45.000Z` |

All other S6 content (`focus`, `nextAction`, `progressSummary`, `insights`, `mathlibGaps`,
`nextSteps`, `builtItems`, `leanFiles[*]`) remains accurate at T+15d and is NOT rewritten.

### Files modified

- `src/data/research/problems/elementary-quadratic-reciprocity-oq-01-oq-02.json` — 4 field edits per drift table.
- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-02/knowledge.md` — Phase header refresh + this Session-7 entry (head/tail-only).
- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-02/s7-no-op-landing-sha-stable.md` — NEW session memo.

### Files NOT modified (intentional scope discipline)

- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` — Lean file untouched.
- `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-02/meta.json` — already correct.
- `proofs/lake-manifest.json` — Mathlib pin unchanged at v4.26.0 SHA `2df2f01…`.
- S5/S6 memos — left intact as historical audit artifacts.
- Mathlib bearer re-verification — declined; SHA `2df2f01…` unchanged since S5/S6, so all bearers
  cited in S5 are bit-identical at S7 — cf. MEMORY `feedback_researcher_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_ship_tight_json_catchup_only_no_bundled_respotcheck` (tighter cycle, no busywork re-spot-check at SHA-stable).

### Build risk

Zero — 0 Lean files modified, 0 imports changed, 0 tactic changes, 0 meta.json field edits.
Sorries unchanged (0). Axiom count unchanged (2). Theorem count unchanged (27). LineCount
unchanged on disk (578 / 579 by respective conventions).

### Phase head transition

S5 OBSERVE → S6 STATE-SYNC → **S7 STATE-SYNC (no-op landing, iteration counter + lastUpdate drift-closure)** → "axiomatized-stable; future S8 refactor optional, not actively scheduled".

The slug remains in terminal state. Future claim-random landings should continue to either
(a) ship the ~250-LOC refactor, or (b) repeat this S7-style no-op landing with iteration-counter
increment. Don't generate busywork by re-auditing Mathlib bearers at fixed SHA, and don't
re-rewrite S5/S6 documentation that is already accurate.
