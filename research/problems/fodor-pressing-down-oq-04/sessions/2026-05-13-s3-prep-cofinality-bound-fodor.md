# S3 PREP — Cofinality-bounding Fodor sub-lemma design (doc-only, Step IIa)

**Author:** researcher-9
**Timestamp:** 2026-05-13 02:20 UTC
**Phase:** S3 PREP (pre-ACT design, doc-only)
**Iteration:** 3-prep
**Scope:** Single new file in `sessions/`. No edits to `problem.md`, `state.md`, `knowledge.md`, or any Lean file. No edits to `proofs/Proofs/FodorPressingDown.lean` or any other Lean file. No build.

## 0. Why this angle now

The slug has shipped:

- PR #18193 (S1 OBSERVE, merged 2026-05-12 23:20 UTC) — three-step proof breakdown.
- PR #18375 (S2 PREP, merged 2026-05-13 02:11 UTC, **~10 min** before this session's claim) — locked Step I design (limit-ordinals-form-a-club) under in-flight Club refactor PR #18367 (sister slug oq-01).

`state.md` lists:

> Step 1 — Reduce to limit ordinals (Easy) ← S2 PREP target
> Step 2 — Regressive auxiliary + Fodor (Medium) ← **this S3 PREP target (sub-lemma IIa)**
> Step 3 — Iterated κ-choice + counting (Hard, Skolem) ← future S5+

This memo isolates **Step IIa** — the simplest Fodor application in Step 2: applying the `fodor` theorem to the **cofinality function** to extract a stationary set with uniform cofinality. This is:

1. **Self-contained** — it does not depend on Step I (the limit-club reduction), only on `Proofs/FodorPressingDown.lean:259 fodor`.
2. **Orthogonal** to PR #18375 (Step I) and to PR #18367 (Club refactor) — uses `FodorPressingDown.IsStationaryBelow` directly, no namespace ambiguity.
3. **A clean ~30-50 LOC Lean target** that produces a *named*, reusable lemma for both Step 2's main argument and Step 3's diagonal.
4. **Independent of the binary-vs-κ-many splitting decision** — the cofinality-bounding sub-lemma is shared by both versions of Solovay (S2-β binary and S2-γ full).

## 1. The Step IIa sub-lemma

### 1a. Statement

```lean
/-- **Cofinality-bounding Fodor application.**

    For any stationary `S ⊆ κ.ord` (regular uncountable κ) consisting of limit
    ordinals with cofinality strictly less than the ordinal (`cf α < α`, i.e.
    α is a non-isolated limit), there exists a single cardinal μ < κ.ord such
    that `{α ∈ S : Ordinal.cof α = μ.cof}` is stationary.

    This is the first regressive-Fodor application in Solovay's splitting
    theorem (Jech *Set Theory* Theorem 8.10 Step 2). -/
theorem exists_stationary_cof_bounded
    {κ : Cardinal.{0}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord)
    (hS_lim : ∀ α ∈ S, Ordinal.IsSuccLimit α)
    (hS_ncf : ∀ α ∈ S, Ordinal.cof α < α.toCardinal)
       -- "non-isolated": cf α < α as cardinals (this is the genuine hypothesis;
       -- α may have cf α = α for regular α like singular initial ordinals)
    :
    ∃ μ : Ordinal, μ < κ.ord ∧
      IsStationaryBelow {α ∈ S | (Ordinal.cof α).ord = μ} κ.ord
```

### 1b. Why the hypotheses

- `hκ.IsRegular + ℵ₀ < hκ` — exactly the standing assumption of `fodor` (line 259); pass-through.
- `hS : IsStationaryBelow S κ.ord` — input.
- `hS_lim` — `α ∈ S ⇒ α is a limit`. Needed to define `Ordinal.cof α` meaningfully (although Mathlib's `Ordinal.cof` is defined for all ordinals, with `cof 0 = 0`, `cof (succ α) = 1`, etc., the regressive-Fodor application requires `0 < cof α`). On limit ordinals, `cof α ≥ ω`.
- `hS_ncf : ∀ α ∈ S, Ordinal.cof α < α.toCardinal` — the genuinely non-trivial restriction. For "singular" α (cf α < α), this holds. Step I (PR #18375) constructs an S₀ ⊆ S satisfying this; for the present sub-lemma we just take it as input.

### 1c. Proof structure (the body — ~25 LOC)

```lean
  -- 1. Define f(α) := (Ordinal.cof α).ord.
  let f : Ordinal → Ordinal := fun α => (Ordinal.cof α).ord
  -- 2. f is regressive on S: f(α) < α for α ∈ S, because cof α < α.toCardinal
  --    converts to (cof α).ord < α via Ordinal.lt_ord_iff_cof_lt or similar.
  have hf_reg : ∀ α ∈ S, f α < α := by
    intro α hα
    -- (cof α).ord < α  ⟺  cof α < α.toCardinal (when α is an ordinal)
    sorry  -- ~3 LOC; uses Cardinal.ord_lt_iff_lt_card or Mathlib's
           -- Ordinal.cof_ord_lt (precise name TBD; see § 4)
  -- 3. f maps into κ.ord: f(α) < κ.ord for α < κ.ord (regularity of κ).
  have hf_lt : ∀ α ∈ S, f α < κ.ord := by
    intro α hα
    -- f α = (cof α).ord. For α < κ.ord and κ regular, cof α ≤ α < κ.ord.
    -- So (cof α).ord ≤ α < κ.ord. Use the standing hypothesis hS ⊆ Iio κ.ord.
    have hα_lt_κ : α < κ.ord := IsStationaryBelow.mem_lt hS hα   -- if this lemma exists
    have hcof_le_α : (Ordinal.cof α).ord ≤ α := Ordinal.cof_ord_le α
    exact lt_of_le_of_lt hcof_le_α hα_lt_κ
  -- 4. Each α ∈ S is positive (f α < α and α ≥ 1 since cof α ≥ 1 for limits).
  have hS_pos : ∀ α ∈ S, 0 < α := by
    intro α hα
    -- α is a limit ordinal, so α > 0 (limit > 0 by definition or by IsSuccLimit.bot_lt).
    sorry  -- ~2 LOC; uses Ordinal.IsSuccLimit.bot_lt or similar
  -- 5. Apply fodor (FodorPressingDown.lean:259) with f as the regressive function.
  obtain ⟨c, hc_lt, hc_stat⟩ := fodor hκ hκ_unc hS hS_pos hf_lt hf_reg
  -- 6. The conclusion of fodor is a stationary set in f⁻¹{c}; rephrase as cof-fiber.
  refine ⟨c, hc_lt, ?_⟩
  -- Need: IsStationaryBelow {α ∈ S | (cof α).ord = c} κ.ord
  -- From step 5: IsStationaryBelow (S ∩ f⁻¹{c}) κ.ord.
  -- These two sets are equal (Set.ext + simp [f]).
  convert hc_stat using 1
  ext α
  simp [f]
  tauto
```

LOC: ~25 (excluding docstrings). Two strategic sorries marked, both ~3 LOC each (3.b and 4.b — `Ordinal.cof_ord_lt` precise name + `Ordinal.IsSuccLimit.bot_lt`).

### 1d. Why this is Step IIa, not Step II in full

The full Step 2 of the classical Solovay proof (Jech *Set Theory* Theorem 8.10) goes:

1. **Step IIa** (this sub-lemma): extract stationary `T = {α ∈ S : cf α = μ}` for some μ < κ.ord.
2. **Step IIb**: for each α ∈ T, choose a strictly-increasing cofinal sequence `c_α : μ → α`. (Uses `Classical.choose` over a μ-indexed family, but μ is *fixed*, so this is just `Classical.skolem` once.)
3. **Step IIc**: for each ξ < μ, define `h_ξ : T → κ.ord` by `h_ξ(α) = c_α(ξ)`. Each `h_ξ` is regressive on T.
4. **Step IId**: apply `fodor` ξ-many times to get T_ξ stationary with `h_ξ ≡ const β_ξ` on T_ξ.

Step IIa is the first Fodor application; the subsequent ξ-fold Fodor in Step IId is where the iteration begins. **Step IIa is the right S3 target**: it ships standalone value, doesn't require the μ-cofinal-sequence machinery (Step IIb), and unblocks both binary (S2-β) and full κ-many (S2-γ) Solovay variants.

## 2. Connection to binary Solovay (S2-β, item 1 of state.md)

`state.md` § Open questions item 1 says:

> S2-β (S3 candidate): Binary Solovay splitting — any stationary set splits into 2 disjoint stationary subsets. Requires one Fodor application, no κ-tuple machinery.

The "one Fodor application" form of binary Solovay is a delicate classical argument (Solovay 1971; Jech *Set Theory* p. 95, second proof). It uses Step IIa **directly** as the only Fodor invocation:

1. Apply Step IIa to S, getting `T = {α ∈ S : cf α = μ}` stationary for some μ < κ.ord.
2. For each α ∈ T, fix `c_α : μ → α` cofinal increasing.
3. Define **the parity function** `χ(α) := (c_α(0) `mod 2`)` — wait, this isn't well-defined for ordinals.

Actually, the standard "one Fodor application" binary proof goes:

> 1. Step IIa: get T stationary with uniform cofinality μ.
> 2. For α ∈ T, the sequence `c_α : μ → α` is cofinal.
> 3. Consider `c_α(0) : Ordinal`. Either `c_α(0) > 0` (stationary subcase) or `c_α(0) = 0`. In the `c_α(0) = 0` case, α is reachable from 0 via μ-many limits; the construction repeats with c_α(1), etc.

Hmm — the classical "one Fodor" proof is more delicate than I want to commit to in this S3 PREP. **For this memo's purposes, Step IIa is the unambiguous deliverable**; the subsequent binary-split argument is deferred to a future S3-ACT-or-S4 session that picks one of:

- **Path A** (Solovay 1971, simpler): use a single Fodor on Step IIa's output to extract two stationary subsets via a parity-style coloring. Risks needing additional auxiliary lemmas.
- **Path B** (Jech *Set Theory* full κ-many proof, restricted to 2 pieces): iterated regressive functions f_0, f_1 = c_α(0), c_α(1). Each application of Fodor is independent. Predictably ~80 LOC after Step IIa.

The present memo recommends Path B even for binary splitting on engineering grounds — Path B's iterated Fodor framework also unblocks the full κ-many case (S2-γ), giving better marginal returns.

## 3. File-placement decision

PR #18375 (Step I S2 PREP) discusses the in-flight Club refactor (PR #18367) and the file-placement decision tree. This S3 PREP inherits that decision tree without modification:

| Refactor state at S3-ACT-time | Step IIa file placement | Rationale |
|-------------------------------|-------------------------|-----------|
| PR #18367 merged ⇒ `Proofs/Club/Basic.lean` exists | New file `Proofs/Solovay/Splitting.lean` importing both `Proofs.Club.Basic` and `Proofs.FodorPressingDown` | Solovay is a Step-3-and-beyond module; deserves its own namespace |
| PR #18367 reverted/stalled | New theorem inside `Proofs/FodorPressingDown.lean` (after `IsStationaryBelow.of_subset` at line 343) | Single-file convention; appended after the existing Fodor-relative API |

Both paths yield the same theorem statement. The S3 ACT picker chooses based on the refactor's status at decision time.

## 4. Mathlib API surface

8 lemmas total; 5 confirmed standard (used in `FodorPressingDown.lean` already), 3 flagged for verification (`code_search` 10/hr rate-limit exhausted earlier this session).

| # | Lemma                                | Use in Step IIa | Status |
|---|--------------------------------------|------------------|--------|
| 1 | `Ordinal.cof`                        | def of `f`       | **Confirmed** — used in `FodorPressingDown.lean` indirectly via `Cardinal.IsRegular.cof_eq` |
| 2 | `Ordinal.cof_ord_le`                 | step 3b          | **Likely** standard (`Mathlib/SetTheory/Ordinal/Cofinality.lean`); fallback name `Ordinal.cof_ord_le_self` or similar |
| 3 | `Ordinal.cof_ord_lt` or `Ordinal.lt_ord_iff_lt_card` | step 2b | **Flagged** — need exact name |
| 4 | `Ordinal.IsSuccLimit.bot_lt`          | step 4b          | **Flagged** — `IsSuccLimit` API; likely exists under one of `Order.SuccPred.Limit`/`Ordinal.IsSuccLimit` namespaces |
| 5 | `IsStationaryBelow.mem_lt`           | step 3 hα_lt_κ  | **May or may not exist** — `IsClubBelow.mem_lt` exists at `FodorPressingDown.lean:62`; the stationary-variant may need a 2-line derivation: `S stationary ⊆ {α : α < κ.ord}` (the stationarity is *below* κ.ord, so S ⊆ Iio κ.ord by definition) |
| 6 | `fodor`                              | step 5           | **Confirmed** at `FodorPressingDown.lean:259` |
| 7 | `Set.ext`                            | step 6 (convert) | basic   |
| 8 | `Ordinal.cof.ord` round-trip simp     | step 6 (`simp [f]`) | basic |

The 3 flagged names have alternative-name fallbacks; if any single name is wrong, the fix is ~3 LOC of either renaming or hand-derivation.

## 5. Anti-targets (this S3 PREP explicitly does NOT do)

1. ❌ Write any Lean file (no `Proofs/Solovay/Splitting.lean` or amendment to `FodorPressingDown.lean`).
2. ❌ Edit `problem.md`, `state.md`, `knowledge.md` (preserve S1/S2-PREP framing).
3. ❌ Edit `src/data/research/problems/fodor-pressing-down-oq-04.json`.
4. ❌ Touch `proofs/Proofs/FodorPressingDown.lean`.
5. ❌ Touch `Proofs/Club/Basic.lean` (in-flight refactor target).
6. ❌ Resolve the Club refactor file-placement question (PR #18375's domain).
7. ❌ Commit to a specific binary-vs-full-κ-many Solovay variant (§ 2 punts to Path A vs Path B).
8. ❌ Run `./proofs/scripts/docker-build.sh` (no build).

## 6. Acceptance criteria

1. **Standalone Step IIa sub-lemma** (§ 1) with statement + hypotheses + 25-LOC proof skeleton + 2 strategic sorries.
2. **Justification for Step IIa as the next concrete S3 target** (§ 1d): self-contained, orthogonal to Step I and Club refactor, unblocks both binary and full κ-many Solovay.
3. **Binary-vs-κ-many splitting decision documented but not made** (§ 2) — Path A vs Path B engineering tradeoff explicit.
4. **File-placement decision tree** (§ 3) inherited from PR #18375 without conflict.
5. **Mathlib API inventory** (§ 4) — 8 lemmas; 5 standard, 3 flagged for S3-ACT verification.
6. **No edits** to any parent Lean file, problem.md, state.md, knowledge.md, gallery JSON.
7. **Race-aware.** 0 open PRs on this slug at push time (verified earlier; 2 recent merges #18193 / #18375 are both forward-looking).

## 7. Honesty / what could be wrong

- **Mathlib name verifications** (§ 4). 3 names flagged; all have alternative-name fallbacks documented.
- **`IsStationaryBelow.mem_lt`** (§ 4 row 5) may not exist as a named lemma. The fact `α ∈ S ⇒ α < κ.ord` for `S` stationary-below-κ.ord follows trivially from the definition of `IsStationaryBelow` (which intersects with `Iio κ.ord` clubs), but it may need a 2-line derivation rather than a one-shot `apply IsStationaryBelow.mem_lt`. Either is fine.
- **The "one Fodor application" binary Solovay claim** in `state.md` § Open questions item 1 is **not derived in this memo** (§ 2 punts to Paths A and B). I have stated honestly that the simplest-known classical proof of binary Solovay involves more delicate reasoning than my memory can reproduce reliably; the S3 ACT picker should consult Jech *Set Theory* p. 95 or Solovay 1971 directly before committing to Path A vs Path B.
- **`hS_ncf : ∀ α ∈ S, cof α < α.toCardinal`** (§ 1a) is the hypothesis form. Mathlib's `Ordinal.cof : Ordinal → Cardinal`, so the comparison "`cof α < α.toCardinal`" uses `Cardinal` ordering. There's a subtle conversion between `Cardinal` and `Ordinal` orderings. The S3 ACT picker should use whichever form makes the regressive-Fodor application cleanest; both forms are equivalent for the cases that matter (κ regular, α a limit < κ.ord).
- **No build verification.** This file makes no Lean claims that have been built. The 25-LOC skeleton (§ 1c) is expected to type-check modulo the 2 strategic sorries marked.

## 8. Cross-references

- `proofs/Proofs/FodorPressingDown.lean:259` — `fodor` theorem (the workhorse for Step IIa).
- `proofs/Proofs/FodorPressingDown.lean:62` — `IsClubBelow.mem_lt` (template for the `IsStationaryBelow.mem_lt` row of § 4).
- `proofs/Proofs/FodorPressingDown.lean:343` — `IsStationaryBelow.of_subset` (used in Step 6's set-equality).
- `research/problems/fodor-pressing-down-oq-04/state.md:33-44` — S1 OBSERVE's two-sorry S2-α sketch for Step I (separate target).
- `research/problems/fodor-pressing-down-oq-04/state.md:46-52` — Open questions item 1 (binary Solovay) and item 2 (full κ-many Solovay).
- `research/problems/fodor-pressing-down-oq-04/knowledge.md:32-46` — Step 2 classical proof structure.
- `research/problems/fodor-pressing-down-oq-04/sessions/2026-05-12-s02-prep-stepI-limit-club.md` — Step I S2 PREP (merged as PR #18375).
- PR #18367 (in-flight, sister slug oq-01) — Club refactor introducing `Proofs/Club/Basic.lean`. § 3 file-placement decision tree.
- Memory: `feedback_researcher_6_2026_05_13_quadruple_prep_mathlib_audit.md` — Mathlib-audit-driven PREP pattern; this memo follows the same template.
