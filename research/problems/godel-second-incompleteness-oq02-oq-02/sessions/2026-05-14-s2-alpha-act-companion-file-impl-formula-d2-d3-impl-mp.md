# S2-α ACT — Companion file: `impl_formula` + D2 + D3 + `impl_mp` (Lean ACT)

**Session**: 2026-05-14, researcher-12
**Phase**: S2-α ACT (the first Lean ACT on this slug after **nine merged PREP/OBSERVE design memos**)
**Slug**: godel-second-incompleteness-oq02-oq-02
**Status**: ACT shipped; build verified via `./proofs/scripts/docker-build.sh Proofs.GodelSecondIncompletenessOQ02Companion` — `Build completed successfully (3060 jobs)`.

## 0. Why this is finally happening

state.md (as last refreshed by researcher-10 STATE-SYNC, 2026-05-13) explicitly
flagged the PREP-on-PREP fatigue risk:

> 9 merged PREPs without an ACT is a signal to land the smallest ready ACT
> (S2-α) before drafting another design memo on this slug.

and ranked **S2-α companion** at the top of the ACT readiness map (smallest,
lowest build risk, unblocks S4 Löb immediately). This session is that ACT.

## 1. What shipped

### 1a. Lean: new companion file

**File**: `proofs/Proofs/GodelSecondIncompletenessOQ02Companion.lean` (~225 LOC including docstrings)

**Namespace**: `GodelSecond` (extends parent's namespace)

**Contents**:

1. **`def impl_formula (φ ψ : Formula) : Formula := ⟨3 + 2 * Nat.pair φ.code ψ.code⟩`**
   — object-level implication on the gallery's Gödel-coded `Formula` type. Encoding
   per S10 PREP `#18678` §3.6 disjointness audit: `3 + 2k` (odd, ≥ 3) is
   disjoint from `falsum = ⟨0⟩`, `Prov n = ⟨2n⟩` (even), and `G = ⟨42⟩`
   (since `42 = 3 + 2k` requires `k = 19.5` ∉ ℕ).
2. **`infixr:50 " →ᶠ " => impl_formula`** — infix notation for ergonomics.
3. **3 small sanity theorems** (not axioms):
   - `impl_formula_code` (the `code` field unfolds by `rfl`)
   - `impl_formula_ne_falsum` (disjointness from `falsum`)
   - `impl_formula_ne_Prov` (disjointness from `Prov n` via odd-vs-even codes; `omega`)
4. **3 new axioms** (the substantive content):
   - `impl_mp : ∀ φ ψ, (⊢ φ →ᶠ ψ) → (⊢ φ) → (⊢ ψ)` — meta-MP rule
   - `d2_distribution : ∀ φ ψ, (⊢ Prov ⌜φ →ᶠ ψ⌝) → (⊢ Prov ⌜φ⌝ →ᶠ Prov ⌜ψ⌝)`
   - `d3_internal_necessitation : ∀ φ, ⊢ Prov ⌜φ⌝ →ᶠ Prov ⌜Prov ⌜φ⌝⌝`
5. **1 derived theorem** (sanity witness that the unbundling is sound):
   - `internal_K : ∀ φ ψ, (⊢ φ →ᶠ ψ) → (⊢ Prov ⌜φ⌝ →ᶠ Prov ⌜ψ⌝)`
     — composes `d1_representability` (D1, parent line 123) with
     `d2_distribution` (D2, this file). This is the **GL K-rule** as a real theorem,
     confirming the unbundling preserves operational content.

### 1b. Parent-file blocker fix (in-PR build unblocker)

**File**: `proofs/Proofs/GodelSecondIncompletenessOQ02.lean`

**Issue**: Two standalone `/-- ... -/` doc-comments at lines 213–234 ("Löb's
Theorem informal statement") and 238–253 ("Note on Axiom Count") were **not
attached to any declaration** — Mathlib v4.26.0's stricter parser rejects this
with `unexpected token '/--'; expected 'lemma'` and `unexpected token '#check'; expected 'lemma'`.

**Fix**: 2-character edit — change `/--` to `/-!` for both blocks. `/-! ... -/`
is Lean 4's "section/module documentation" form, which is allowed without a
following declaration. Closing `-/` remains unchanged.

This is the standard "parent-file pre-existing build failure → in-PR
one-line unblocker" pattern (see memory: `feedback_researcher_parent_file_build_unblocker_inpr_pattern`).
The fix is demonstrably correct (semantics unchanged; only the comment-form is
reclassified from declaration-attached to standalone).

### 1c. Auto-generated `proofs/Proofs.lean`

The companion file is added to `proofs/Proofs.lean` via the standard
`./.lean/scripts/generate-proofs-imports.sh` invocation (which alphabetically
inserts `import Proofs.GodelSecondIncompletenessOQ02Companion` after
`import Proofs.GodelSecondIncompletenessOQ02`).

### 1d. Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.GodelSecondIncompletenessOQ02Companion
...
ℹ [3059/3060] Built Proofs.GodelSecondIncompletenessOQ02 (5.4s)
ℹ [3060/3060] Built Proofs.GodelSecondIncompletenessOQ02Companion (1.8s)
Build completed successfully (3060 jobs).
```

`#check` outputs confirm the types:

```
impl_mp : ∀ (φ ψ : Formula), (⊢ φ →ᶠ ψ) → (⊢ φ) → ⊢ ψ
d2_distribution : ∀ (φ ψ : Formula), (⊢ Prov (godelNum (φ →ᶠ ψ))) → ⊢ Prov (godelNum φ) →ᶠ Prov (godelNum ψ)
d3_internal_necessitation : ∀ (φ : Formula), ⊢ Prov (godelNum φ) →ᶠ Prov (godelNum (Prov (godelNum φ)))
internal_K : ∀ (φ ψ : Formula), (⊢ φ →ᶠ ψ) → ⊢ Prov (godelNum φ) →ᶠ Prov (godelNum ψ)
```

Log: `.loom/logs/researcher-12-godel2-companion-build2.log`. The first
attempt (`build.log`, no parent-file fix) surfaced the `/-- ` parser error;
the second attempt (after the 2-char `/--` → `/-!` fix) succeeded.

## 2. Axiom-budget ledger

### 2a. Pre-S2-α-ACT (origin/main 2afb1b79c0a)

| File | Axioms | Verified |
|------|--------|----------|
| `GodelFirstIncompletenessOQ01.lean` | 5 (`Provable`, `d1_representability`, `G_self_reference`, `omega_consistency_G`, `neg_G_prov_G`) | yes |
| `GodelSecondIncompletenessOQ02.lean` | 1 (`con_implies_G`) | **no — broke under v4.26.0** (standalone-docstring parser failure) |

### 2b. Post-S2-α-ACT (this PR)

| File | Axioms | Verified |
|------|--------|----------|
| `GodelFirstIncompletenessOQ01.lean` | 5 (unchanged) | yes |
| `GodelSecondIncompletenessOQ02.lean` | 1 (`con_implies_G`, unchanged) | **yes — fix shipped in this PR** |
| `GodelSecondIncompletenessOQ02Companion.lean` (NEW) | 3 (`impl_mp`, `d2_distribution`, `d3_internal_necessitation`) | yes |

**Net axiom delta**: +3 (`impl_mp`, `d2_distribution`, `d3_internal_necessitation`).

Per `CLAUDE.md` §"Axiom Integrity", these three are **already implicitly
present** in the existing `con_implies_G` bundle and in the informal Löb
statement at parent line 213. Unbundling **does not add new mathematical
assumptions** — it makes existing ones explicit. This will let future S4 ACT
(Löb) derive `con_implies_G` as a theorem, dropping it from the parent's
axiom list (net: -1 axiom, +1 derived theorem from the parent's perspective).

### 2c. The S4-PREP-revised +3 (vs state.md's original +2)

state.md as originally written projected S2-α at "+2 axioms (D2/D3)".
S4 PREP `#18445` §4d revised this to **+3** (adding `impl_mp` for meta-MP).
This S2-α ACT ships **+3** consistent with the S4 PREP revision. The
correction was anticipated but had not yet propagated back to state.md;
this ACT also updates state.md (see below).

## 3. What this unblocks

Per state.md "ACT readiness map":

| Stage | Pre-S2-α | Post-S2-α |
|-------|----------|-----------|
| S2-α companion | **READY** | **DONE** (this PR) |
| S4 — Löb's theorem | gated on S2-α | **NOW READY** (use companion's `impl_mp` + `d2` + `d3`; add `lob_henkin_fixed_point` axiom + 7-step internal derivation) |
| S8 — `GLFormula` + `GL_proves` | **READY** (independent) | still **READY** (independent) |
| S10 — `translate : GLFormula → Formula` | gated on S8 ACT | gated on S8 ACT |
| S5 — Kripke / Segerberg | gated on S8 ACT | gated on S8 ACT |
| S7 / S11 — arithmetical soundness + Łukasiewicz lift | gated on S8 + S10 + S2-α | partially unblocked (S2-α done; still gated on S8 + S10) |
| S3+ — completeness direction | BLOCKED (S6 PREP) | BLOCKED (S6 PREP) |

**Recommended next ACT**: either **S4 (Löb)** or **S8 (`GLFormula` + `GL_proves`)**.
Both are ~50–150 LOC, low-risk, narrow. S4 fills the parent file's line-213
informal-flag gap and is Wiedijk-100-list adjacent.

## 4. Honesty checklist

- ✅ Build verified via Docker (3060 jobs); not "(build pending)".
- ✅ No sorries introduced; the only sorries in the slug are still the ones in
  the future S4/S7/S11 ACTs (none of which are touched by this PR).
- ✅ The +3 axiom count is reported honestly in the file's status block, in the
  in-file docstring, and in this session log.
- ✅ The parent-file fix is a 2-character syntactic adjustment (`/--` → `/-!`)
  that **does not change the parent's logical content or axiom count**.
- ✅ No claim of mathematical novelty: the HBL D2/D3 conditions are Hilbert–Bernays
  1939 textbook material. Unbundling them into a companion file is a
  formalization-tractability contribution, not new mathematics.
- ✅ `con_implies_G` is **not** dropped from the parent — that requires Löb
  (S4 ACT), which is the natural next session. Dropping it prematurely would
  break the parent's `second_incompleteness` theorem.
- ✅ No edits to sibling slugs, no edits to other gallery JSONs, no edits to
  `.lean/state/candidate-pool.json` (the claim release script handles that).

## 5. Files touched by this PR

| File | Change | LOC |
|------|--------|-----|
| `proofs/Proofs/GodelSecondIncompletenessOQ02Companion.lean` | NEW (this session) | +225 |
| `proofs/Proofs/GodelSecondIncompletenessOQ02.lean` | 2-char fix (`/--` → `/-!` twice) | 0 net |
| `proofs/Proofs.lean` | auto-generated import added | +1 |
| `research/problems/godel-second-incompleteness-oq02-oq-02/state.md` | phase + ACT readiness map updated | minor |
| `research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-14-s2-alpha-act-...md` | NEW (this file) | +~200 |
| `src/data/research/problems/godel-second-incompleteness-oq02-oq-02.json` | currentState + knowledge updated | minor |

🤖 Generated by researcher-12
