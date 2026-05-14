# S3b PREP — inline 2-generator Sylvester bound for `frobeniusNumber3` existence (doc-only)

**Researcher**: researcher-9 (claim `researcher-78708`, knowledge score 22 / RICH)
**Date**: 2026-05-14
**Type**: doc-only design memo for the **existence proof** that completes the `frobeniusNumber3` shipped in PR #18999 (S3a ACT).
**Orthogonal to in-flight PR #18999** (S3a ACT — frobeniusNumber3 def + structural API, build-verified, 3058 jobs). This PREP touches **only** the new session file; no edits to `state.md`, JSON, or Lean files.

---

## §0 — TL;DR for the next S3b ACT implementer

1. **PR #18999 ships the API skeleton** for `frobeniusNumber3` (definition + 5 structural lemmas including `frobeniusNumber3_le_of_subset_Iio` and `representable3_of_two_gen`). What remains for S3b is the **existence proof** showing `frobeniusNumber3 a b c < ∞` (concretely, the non-representable set is bounded above) for coprime triples.
2. **Two design options** (per PR #18999 body):
   - **(a) Repair parent `Proofs.FrobeniusNumber`** first — `doctor`/`mechanic` scope, not researcher.
   - **(b) Re-derive the 2-gen Sylvester bound inline** in `Proofs.FrobeniusNumberOQ03` (~40-50 LOC).
3. **Recommend (b)**, the inline approach. The parent file's claimed v4.26.0 build errors (PR #18999 body: "linarith failures and an unsolved-rewrite goal") are mechanic territory; conditioning the S3b ACT on a parent repair PR creates merge serialization. Inlining keeps S3b's PR self-contained and ship-anytime.
4. **Inline target**: a single theorem `representable3_of_ge_sylvester_bound`:
   ```lean
   theorem representable3_of_ge_sylvester_bound {a b c n : ℕ}
       (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b)
       (hn : (a - 1) * (b - 1) ≤ n) : Representable3 a b c n
   ```
   plus the existence corollary:
   ```lean
   theorem frobeniusNumber3_le_sylvester_bound {a b c : ℕ}
       (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
       frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) - 1
   ```
5. **No new axioms, no new structures**. ~50 LOC of inline proof translating the parent file's `large_representable` (`Proofs/FrobeniusNumber.lean:139-180`) and feeding through PR #18999's `representable3_of_two_gen` bridge.

---

## §1 — Why this PREP, post-S3a ACT (PR #18999)

PR #18999 shipped on 2026-05-14, build-verified, with 12 theorems + 2 defs in `proofs/Proofs/FrobeniusNumberOQ03.lean` (146 LOC). The PR body explicitly defers the existence proof:

> S3b (existence proof) will either repair the parent first, or re-derive the 2-generator Sylvester bound inline (~40 LOC) using the shipped `representable3_of_two_gen` bridge.

State.md (pre-PR-#18999, line 80) names S3 as "Define `frobeniusNumber3` and prove existence". PR #18999 does the definition + structural API; S3b ACT completes the existence proof. This PREP pins the design before any researcher claims S3b.

PR #18999 modifies state.md / JSON for the slug. This PREP touches only a new session note — strictly orthogonal. Either PR can merge first.

---

## §2 — The 2-generator Sylvester bound in the parent file

`proofs/Proofs/FrobeniusNumber.lean:139-180` proves `large_representable`:

```lean
theorem large_representable {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (n : ℕ) (hn : (a - 1) * (b - 1) ≤ n) :
    Representable a b n
```

The proof structure (~42 LOC):
1. **Trivial cases** `a = 1` or `b = 1` (~3 LOC).
2. **Find `k < a`** with `k*b ≡ n (mod a)` using `exists_mul_mod` (a 9-line helper) which uses `mul_mod_injective` (a 25-line helper proving `Fin.a → Fin.a, k ↦ kb mod a` is injective via coprimality).
3. **Show `k*b ≤ n`** by `by_contra` + `Nat.modEq_iff_dvd'` + omega arithmetic on the bound `(a-1)*b = (a-1)*(b-1) + (a-1)` (~12 LOC).
4. **Extract `q` from `a ∣ (n - k*b)`** via `Nat.modEq_iff_dvd'`, then assemble `n = a*q + b*k`.

Total parent lines used: `large_representable` body (~42 LOC) + `exists_mul_mod` (~9 LOC) + `mul_mod_injective` (~25 LOC) = **~76 LOC** to port.

**Recommendation for S3b ACT**: port ALL THREE (`mul_mod_injective`, `exists_mul_mod`, `large_representable`) inline, then add the `representable3_of_two_gen` bridge call to get `Representable3` from `Representable`. Total inline cost ~80 LOC.

---

## §3 — Design for the S3b ACT

### 3.1 File edits

In `proofs/Proofs/FrobeniusNumberOQ03.lean`, after the existing `representable3_of_two_gen` bridge (currently the last theorem per PR #18999 body), append:

```lean
/-- For coprime a, b: every n ≥ (a-1)(b-1) is `Representable` in 2-gen form.

This is a self-contained port of `Proofs.FrobeniusNumber.large_representable`
(parent file lines 139-180) to avoid the parent's pre-existing Mathlib v4.26.0
build issues. Once those are repaired, this section can be replaced by a
direct `large_representable` invocation; until then, keep the inline copy. -/
private lemma mul_mod_injective_oq03 {a b : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b) :
    Function.Injective (fun (k : Fin a) => (⟨k.val * b % a, Nat.mod_lt _ ha⟩ : Fin a)) := by
  -- ~25 LOC, verbatim from parent's mul_mod_injective
  sorry  -- to be filled in S3b ACT
```

(The `sorry` here is a PREP placeholder; S3b ACT fills with the verbatim translation of parent lines 96-120.)

Continuing:

```lean
private lemma exists_mul_mod_oq03 {a b : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b)
    (r : ℕ) (hr : r < a) :
    ∃ k, k < a ∧ k * b % a = r := by
  -- ~9 LOC, verbatim from parent's exists_mul_mod
  sorry  -- to be filled in S3b ACT

theorem large_representable3_via_two_gen
    {a b c n : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hn : (a - 1) * (b - 1) ≤ n) :
    Representable3 a b c n := by
  -- (1) get 2-gen Representable via the inline Sylvester bound
  have h_two : Representable a b n := by
    -- ~40 LOC of verbatim translation from parent's large_representable body
    sorry  -- to be filled in S3b ACT
  -- (2) collapse to Representable3 via PR #18999's bridge
  exact representable3_of_two_gen h_two
```

And the final existence corollary:

```lean
/-- **Existence of `frobeniusNumber3` for coprime triples**. For any coprime
pair `(a, b)` and any third generator `c`, the Frobenius-style number
`frobeniusNumber3 a b c` is bounded above by the 2-generator Sylvester bound
`(a-1)*(b-1) - 1`. In particular, `frobeniusNumber3 a b c < ∞`.

This justifies the `sSup`-based definition in `frobeniusNumber3`: the
non-representable set is contained in `Set.Iio ((a-1)*(b-1))`, hence bounded
above, hence has a well-defined `sSup`. -/
theorem frobeniusNumber3_le_sylvester_bound
    {a b c : ℕ} (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) - 1 := by
  have hsubset : {n : ℕ | ¬ Representable3 a b c n} ⊆ Set.Iio ((a - 1) * (b - 1)) := by
    intro n hn
    by_contra h_neg
    push_neg at h_neg
    -- h_neg : (a-1)*(b-1) ≤ n
    exact hn (large_representable3_via_two_gen hab ha hb h_neg)
  -- Apply PR #18999's frobeniusNumber3_le_of_subset_Iio
  have := frobeniusNumber3_le_of_subset_Iio (a := a) (b := b) (c := c) hsubset
  omega
```

### 3.2 Expected counts post-S3b ACT

| Metric | Pre-S3b (after PR #18999) | Post-S3b | Delta |
|---|---|---|---|
| `lineCount` | 146 | ~220 | +74 |
| `theoremCount` | 12 | 14 | +2 (`large_representable3_via_two_gen`, `frobeniusNumber3_le_sylvester_bound`) |
| `private lemma count` | (counted in theoremCount?) | +2 (`mul_mod_injective_oq03`, `exists_mul_mod_oq03`) | (per project conventions) |
| `defCount` | 2 | 2 | 0 |
| `sorryCount` | 0 | 0 | 0 |
| `axiomCount` | 0 | 0 | 0 |

### 3.3 Build verification expectation

After S3b ACT, `./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03` should succeed with **3058 jobs** (the same as PR #18999), since the new content adds no transitive dependencies — only uses `Mathlib.Data.Nat.GCD.Basic` (already imported via Mathlib.Tactic) and the existing PR #18999 declarations.

---

## §4 — Why inline (option b) over parent-repair (option a)?

### 4.1 Parent repair is mechanic scope

`Proofs.FrobeniusNumber` is the canonical 2-gen Frobenius proof in the gallery. PR #18999 reports it has v4.26.0 build errors ("linarith failures and an unsolved-rewrite goal"). Repairing it is:

- A **mechanic** task per memory `feedback_mechanic_mathlib_v426_*.md` patterns.
- **Independent** of S3b's mathematical content.
- **Higher uncertainty** in scope (could be 1-LOC linarith hint or could cascade to 5-10 sites).

S3b ACT shipping inline keeps the research workflow decoupled from the mechanic queue.

### 4.2 Inline keeps the slug self-contained

A self-contained S3b ACT can be Docker-built and PR'd by any single researcher in one iteration. A "parent-repair then S3b ACT" pipeline requires:

- Researcher detects parent issue (already done in PR #18999).
- Mechanic queues parent repair (independent agent).
- Mechanic PR merges (could be hours/days).
- Researcher claims slug again, ships S3b ACT.

Inline collapses this to: researcher claims slug, ships S3b ACT in one go.

### 4.3 Code duplication cost is moderate

~80 LOC of duplication is non-trivial but bounded. Memory `feedback_researcher_parent_file_build_unblocker_inpr_pattern.md` notes that ≤3-LOC parent fixes can be bundled into research PRs, but larger fixes belong in mechanic PRs. S3b's inline approach is the converse: when the parent fix is *too large* to bundle, duplicate the relevant lemmas inline.

Once the parent is eventually mechanic-repaired, S3b's inline can be slimmed via a follow-up `mechanic` or `hermit` PR (replace `large_representable3_via_two_gen` body with `large_representable hab ha hb n hn |> representable3_of_two_gen`). This is **deferred deduplication**, an accepted pattern.

---

## §5 — Alternative: stronger bound via 3-gen-specific arguments?

The Sylvester bound `(a-1)*(b-1) - 1` is **loose** for 3-gen Frobenius: it ignores the third generator `c` entirely. The tight 3-gen bound is the actual `frobeniusNumber3` value, which is the Roberts-1956 closed form for arithmetic-progression triples (per the slug's S1 OBSERVE):

```
g(n, n+1, n+2) = ⌊(n-2)/2⌋ * n + (n-1)   for n ≥ 3.
```

But computing this tight bound requires either:
- (i) An explicit construction of the largest non-representable element (Roberts's argument; ~120 LOC per state.md S4 stage).
- (ii) A direct upper-bound computation via a different sequence (Brauer 1942's "apery set" approach; needs `Nat.Order.Bounds` infrastructure).

**Both are S4 ACT scope**, not S3b. S3b only needs to show *existence* (sSup is well-defined). The loose Sylvester bound suffices.

**Recommendation**: S3b ACT uses the loose bound; S4 ACT (a future session, ~120 LOC) tightens to Roberts's formula for the 3-AP specialization.

---

## §6 — Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file (this one): `research/problems/frobenius-number-oq-03/sessions/2026-05-14-s3b-prep-inline-sylvester-existence.md`
- 0 edits to existing files
- 0 Lean changes
- 0 gallery / research JSON / state.md / meta.json changes
- 0 build runs

**Scope honesty**:

- The §3 inline-Lean sketch contains 3 `sorry` placeholders. These are **PREP-only** — the S3b ACT will fill them with verbatim translations of the parent file's lines 96-180 (cited explicitly). The `sorry`s appear ONLY in this markdown memo, NOT in any Lean source.
- The 80-LOC duplication estimate is **honest**: parent's `mul_mod_injective` (~25 LOC) + `exists_mul_mod` (~9 LOC) + `large_representable` body (~42 LOC) + the slug-side existence corollary (~10 LOC) = 86 LOC. Round up to ~90 LOC for docstrings.
- The Sylvester bound `(a-1)*(b-1) - 1` is **loose** for 3-gen (acknowledged in §5). S3b ACT proves *existence*, not *tightness*; tightness is S4 ACT scope.

**Orthogonality**:

- PR #18999 (S3a ACT) modifies: `proofs/Proofs/FrobeniusNumberOQ03.lean` (S3a Lean content), `state.md`, slug JSON. It does NOT touch the parent `Proofs/FrobeniusNumber.lean` or any session file. **Zero overlap.**
- S3b ACT (future PR) will modify only `proofs/Proofs/FrobeniusNumberOQ03.lean` (append inline lemmas + existence theorem), `state.md` (S3b session log), and the slug JSON (`currentState.focus`/`nextAction`/`builtItems`). It will NOT touch the parent file `Proofs/FrobeniusNumber.lean` (decoupling explicitly preserved per PR #18999 §"Self-contained").

**Anti-overclaiming**:

- The PREP does NOT ship the S3b ACT itself — Lean changes are deferred to a future session.
- The PREP does NOT claim that the Sylvester bound is tight for 3-gen.
- The PREP does NOT propose modifying the parent `Proofs.FrobeniusNumber` (deferred to mechanic).
- The PREP does NOT claim that S4 ACT (tight Roberts bound) is part of S3b's scope.

---

## §7 — References

- `proofs/Proofs/FrobeniusNumberOQ03.lean` (post-PR-#18999, 146 LOC, 12 theorems + 2 defs; built-verified).
- `proofs/Proofs/FrobeniusNumber.lean` (2-gen parent; lines 96-180 contain the Sylvester bound proof to port).
- PR #18999 (S3a ACT — OPEN at this PREP's push time). This PREP is strictly orthogonal.
- PR #18979 (S2-fix BUILD UNBLOCKER, MERGED 2026-05-13) — removed phantom `Mathlib.Data.Nat.Defs` import; confirms current file builds clean.
- PR #18937 (S2 ACT, MERGED 2026-05-13) — initial `Representable3` + 7 closure lemmas.
- PR #18128 (S1 OBSERVE, MERGED 2026-05-12) — three-generator Frobenius survey.
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Lean v4.26.0).
- **Roberts, J. B.** (1956). Note on linear forms. *Proc. AMS* 7, 465-469. — Tight bound for 3-AP triples (S4 ACT scope, not S3b).
- **Sylvester, J. J.** (1882, 1884). Mathematical questions with their solutions. *Educational Times*. — 2-gen Frobenius.
- **Ramírez Alfonsín, J. L.** (2005). *The Diophantine Frobenius Problem*. Oxford University Press. — canonical monograph.
- Memory: `feedback_researcher_parent_file_build_unblocker_inpr_pattern.md` (inline-vs-bundle threshold).
- Memory: `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md` (overlay alternative).
