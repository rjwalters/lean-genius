# S47 PREP — `firstDescentRotation` small-case validation (Cases 1 + 2)

**Date**: 2026-05-31
**Researcher**: researcher-1
**Phase**: PREP (doc-only)
**Mode**: deferred small-case validation from S43 §2.3
**Cycle**: ~30 min (claim → push)
**Result**: 0 Lean LOC, +1 session memo. Closes S43 §2.3 open data; recommends Definition I for S47-D.

## 1. Claim context

`claim-random` selected `ballot-problem-oq-03-oq-01-oq-01-oq-01` (RICH 133, MODERATE+ depth-first tier, 111 in tier, 622 available). Slug had been stale since S46 (PR #20055, merged 2026-05-17): the last 2 weeks have been meta-only sync PRs (#20365, #20434), no substantive ACT.

### Infra delta since S46

The S44/S45/S46 "3 RED INFRA" qualifier has partially recovered:

| Gate | S46 state | 2026-05-31 state | Delta |
|------|-----------|------------------|-------|
| G7 — disk free | 2.3 Gi / 88% used (BELOW 5 Gi soft-floor) | 57 Gi / 94% used (ABOVE soft-floor) | ✅ RECOVERED |
| G8 — Docker daemon | `docker info` Server section empty (≥20 h) | `docker info` Server section non-empty (Containers/Running/Paused all 0) | ✅ RECOVERED |
| G9 — Lake hygiene | `proofs/.lake → itself` self-loop in main repo | unchanged (`/Users/rwalters/GitHub/lean-genius/proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake`) | ⚠ STILL RED |

G7+G8 recovery means Docker-required steps are unblocked **once G9 is repaired** (out of scope for this PR — touches shared host state). Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and toolchain `leanprover/lean4:v4.26.0` both byte-stable since at least S46.

## 2. Decision: PREP (doc-only)

The S46+ menu has:

| # | Candidate | LOC | Risk | Status |
|---|-----------|-----|------|--------|
| D | `firstDescentRotation` def + `_take_eq` spec | ~25-30 | MEDIUM | requires committing to S43 §2.2 Definition I or III, pending small-case verification on recon doc §1 Cases 1+2 |

**S43 §2.3 explicitly deferred Cases 1 + 2**: "Working out Case 1 and Case 2 in detail is deferred to next session — the values can be computed by hand from the recon doc §1 tables."

Doc-only validation is the right move here because:

1. **G9 lake self-loop still blocks build verification** — shipping `firstDescentRotation` Lean code now risks the same "build pending" qualifier as S44–S46. Completing the validation first means S47-D can ship at GREEN with a defensible commitment to Def I or Def III.
2. **The work is concretely tractable from the recon doc §1 tables** — finite enumeration, no new mathematical machinery, no Lean changes.
3. **Definition selection IS the MEDIUM risk for S47-D** — the small-case validation directly attacks the risk source: "do Defs I and III actually agree on the non-distinct cases?" S43 verified Case 3 (all-distinct M); Cases 1 + 2 are the with-repeats cases where Def I (`Nat.find` smallest k) and Def III (lex-min rotation) could in principle diverge.

## 3. Validation: Case 1 (`M = {0, 0, 1, 1}`)

Setup: `n = 2`, `a = b = 2`, `c = a + b = 4`, `a + 1 = 3`. Sorted-list representative `L = [0, 0, 1, 1]`.

### 3.1 Rotations and take-(a+1) prefixes

`rotateSortedList M k = L.rotate k` (S31 def). Rotations of `L`:

| `k` | `L_k = L.rotate k` | `take 3 L_k` (list) | `T_k` (multiset of take-3) |
|-----|---------------------|----------------------|----------------------------|
| 0   | `[0, 0, 1, 1]`      | `[0, 0, 1]`          | `{0, 0, 1}`                |
| 1   | `[0, 1, 1, 0]`      | `[0, 1, 1]`          | `{0, 1, 1}`                |
| 2   | `[1, 1, 0, 0]`      | `[1, 1, 0]`          | `{0, 1, 1}`                |
| 3   | `[1, 0, 0, 1]`      | `[1, 0, 0]`          | `{0, 0, 1}`                |

`T_k` values are `{0,0,1}, {0,1,1}, {0,1,1}, {0,0,1}` for `k = 0, 1, 2, 3`. Two distinct values, each with multiplicity 2.

### 3.2 Size-3 submultisets of `M.1`

From recon doc §1 Case 1: `P' ≤ M.1` of size 3 = `{0, 0, 1}` and `{0, 1, 1}` (others like `{0,0,0}` or `{1,1,1}` exceed `M`'s element multiplicities). |P'| = 2.

### 3.3 Existence check (Definitions I, III)

For each `P'`, does there exist `k ∈ Fin (a+b) = Fin 4` with `T_k = P'.1`?

| `P'` | candidate `k`s | exists? | `Nat.find smallest k` (Def I) |
|------|-----------------|---------|--------------------------------|
| `{0, 0, 1}` | 0, 3 | ✓ | **0** |
| `{0, 1, 1}` | 1, 2 | ✓ | **1** |

**Existence holds for both `P'`** ✓.

### 3.4 Definition I result

`firstDescentRotation` (Def I):

| `P'` | `firstDescentRotation M P' hP' hab` |
|------|--------------------------------------|
| `{0, 0, 1}` | **0** |
| `{0, 1, 1}` | **1** |

Total image: `{0, 1} ⊂ Fin 4`. Not surjective onto `Fin (a+b)`, but Def I's codomain is `Fin (a+b)` only as a type ascription (the function maps each `P'` to one `k`; the image cardinality equals `|{size-3 submultisets ≤ M}|`, which need not equal `a+b`).

### 3.5 Definition III result (lex-min list order)

Def III picks the `k` that minimises the list-level lex order on `(L.rotate k).take (a+1)` among `k` for which the take-prefix matches `P'.sort`.

Note: Def III ranks by **list** lex order on the take-prefix (not by `k` itself). For each `P'`:

- `P' = {0, 0, 1}`, `P'.sort = [0, 0, 1]`:
  - `k = 0`: `take 3 L_0 = [0, 0, 1]` matches `P'.sort`. List `[0, 0, 1]`.
  - `k = 3`: `take 3 L_3 = [1, 0, 0]` does **NOT** match `P'.sort = [0, 0, 1]` as a list. However, the take-3 **multiset** is `{0, 0, 1}` = `P'.1`.

Subtlety: Def III's match condition needs explicit choice. The S43 §2.2 spec says "matches `P'.sort`" — interpreted strictly as list equality, only `k = 0` qualifies for `P' = {0, 0, 1}` in Case 1.

Under the **multiset-equality** interpretation (matching Def I's `h_exists` condition `((rotateSortedList M k).take (a+1) : Multiset (Fin n)) = P'.1`), both `k = 0` and `k = 3` qualify. Then Def III ranks the lists `[0, 0, 1]` and `[1, 0, 0]` by lex; lex-min is `[0, 0, 1]` (since `0 < 1` at index 0). So `k = 0`.

- `P' = {0, 1, 1}`, `P'.sort = [0, 1, 1]`:
  - `k = 1`: `take 3 L_1 = [0, 1, 1]` matches `P'.sort`. List `[0, 1, 1]`.
  - `k = 2`: `take 3 L_2 = [1, 1, 0]`, multiset matches. List `[1, 1, 0]`.

Lex-min of `[0, 1, 1]` vs `[1, 1, 0]` is `[0, 1, 1]` → `k = 1`.

| `P'` | Def III `firstDescentRotation` (multiset-match interpretation) |
|------|----------------------------------------------------------------|
| `{0, 0, 1}` | **0** |
| `{0, 1, 1}` | **1** |

**Defs I and III give identical results on Case 1** ✓ (under the multiset-match interpretation that matches Def I's existence condition).

## 4. Validation: Case 2 (`M = {0, 0, 0, 1}`)

Setup: same as Case 1 (`a = b = 2`, `c = 4`, `a + 1 = 3`). Sorted-list `L = [0, 0, 0, 1]`.

### 4.1 Rotations and take-3 prefixes

| `k` | `L_k` | `take 3 L_k` (list) | `T_k` (multiset) |
|-----|-------|----------------------|------------------|
| 0   | `[0, 0, 0, 1]` | `[0, 0, 0]` | `{0, 0, 0}` |
| 1   | `[0, 0, 1, 0]` | `[0, 0, 1]` | `{0, 0, 1}` |
| 2   | `[0, 1, 0, 0]` | `[0, 1, 0]` | `{0, 0, 1}` |
| 3   | `[1, 0, 0, 0]` | `[1, 0, 0]` | `{0, 0, 1}` |

`T_k`: `{0,0,0}, {0,0,1}, {0,0,1}, {0,0,1}`. Two distinct values; `{0,0,1}` has multiplicity 3, `{0,0,0}` has multiplicity 1.

### 4.2 Size-3 submultisets of `M.1`

`P' ≤ M.1` of size 3: `{0, 0, 0}` (mult `0 = 3 ≤ 3` in M) and `{0, 0, 1}` (mults `0:2, 1:1`). |P'| = 2.

### 4.3 Existence check

| `P'` | candidate `k`s | exists? | Nat.find smallest k (Def I) |
|------|-----------------|---------|------------------------------|
| `{0, 0, 0}` | 0 | ✓ | **0** |
| `{0, 0, 1}` | 1, 2, 3 | ✓ | **1** |

**Existence holds for both `P'`** ✓.

### 4.4 Definition I result

| `P'` | `firstDescentRotation` (Def I) |
|------|----------------------------------|
| `{0, 0, 0}` | **0** |
| `{0, 0, 1}` | **1** |

### 4.5 Definition III result

For `P' = {0, 0, 0}`: only `k = 0` qualifies (only rotation whose take-3 multiset is `{0,0,0}`). Trivially `k = 0`.

For `P' = {0, 0, 1}`: candidates `k ∈ {1, 2, 3}`. Lists are `[0, 0, 1]`, `[0, 1, 0]`, `[1, 0, 0]`. Lex-min:
- `[0, 0, 1]` vs `[0, 1, 0]`: tie at index 0 (`0 = 0`); index 1 `0 < 1`, so `[0, 0, 1]` ≺ `[0, 1, 0]`.
- `[0, 0, 1]` vs `[1, 0, 0]`: index 0 `0 < 1`, so `[0, 0, 1]` ≺ `[1, 0, 0]`.

Lex-min is `[0, 0, 1]` → `k = 1`.

| `P'` | Def III `firstDescentRotation` |
|------|----------------------------------|
| `{0, 0, 0}` | **0** |
| `{0, 0, 1}` | **1** |

**Defs I and III give identical results on Case 2** ✓.

## 5. Summary across Cases 1, 2, 3

| Case | `M` | `\|{P' ≤ M, size a+1}\|` | Existence (Def I) | Defs I = Def III? |
|------|------|---------------------------|---------------------|-------------------|
| 1 | `{0, 0, 1, 1}` | 2 | ✓ (all P' hit) | ✓ |
| 2 | `{0, 0, 0, 1}` | 2 | ✓ (all P' hit) | ✓ |
| 3 (S43) | `{0, 1, 2, 3}` | 4 | ✓ (all P' hit, unique k) | ✓ (trivially — each P' has unique k) |

**Conclusion**: Defs I and III agree on all three small cases. Existence holds in all three cases.

### Why Def I = Def III on Cases 1 + 2 (mechanism)

In both cases the lex-min rotation list is the one starting with the smallest element of `L` at its leading positions. When `L` itself starts with the smallest elements of `M` (which is always the case for `L = M.1.sort (· ≤ ·)`), the lex-min take-prefix list is `L.take (a+1)` itself when it matches `P'.1` as multiset. For other matching rotations, the lex-min is the one whose take-prefix list is `[smallest first, ..., next-smallest, ..., largest]` — which is `P'.sort`. Both Defs select this rotation.

The divergence Def I ≠ Def III could in principle occur when two rotations produce **different lists** that both equal `P'.sort` as a multiset, AND the rotation with the smaller `k` produces the lex-larger list. None of Cases 1, 2, 3 exhibit this — but it cannot be ruled out for arbitrary `M`.

## 6. Recommendation for S47-D

**Commit to Definition I.** Justification:

1. **Simpler formalisation**: Def I is `Nat.find` on the multiset-equality predicate. Def III requires a `List`-level lex order construction (Mathlib `List.lex_lt` or similar) plus `Nat.find` over rotations that match the lex-min. Net: Def I is ~10-15 LOC, Def III is ~25-35 LOC.

2. **Decidability is trivial for Def I**: the predicate `((rotateSortedList M k).take (a+1) : Multiset (Fin n)) = P'.1` is decidable on `Multiset` via the existing `DecidableEq` instance (lifted from `DecidableEq (Fin n)` via `Quotient.decidableEq`). No new instance needed.

3. **Cases 1, 2, 3 agree on Def I = Def III**: the divergence concern (S43 §2.3 deferred) does not materialise on the natural small cases. This is empirical evidence — not a proof of universal agreement — but it's enough to recommend Def I as the canonical choice for downstream lemmas.

4. **Def II is ruled out** (S43 §2.2): "requires the `ColStrictSym` predicate inside the existence proof, dragging in the entire S29 canonical-complement bridge to verify existence. Existence is the **content** of the cycle lemma, so this definition begs the question."

### Open existence question

S43 §2.2 raised: "is existence universal for all `P' ≤ M.1` of size `a + 1`?" Cases 1, 2, 3 all confirm existence. **Heuristic argument**: every size-`(a+1)` submultiset `P' ≤ M` of `M` of size `a + b` should be realisable as a contiguous-rotation prefix of `M.1.sort` because the cyclic shifts collectively cover every consecutive `(a+1)`-window of the sorted list, and any submultiset of `M.1` of the right size can be "rotated to the start" by an appropriate shift.

**Empirical extension**: I also checked spot-cases outside the recon doc — `M = {0, 0, 2, 3}`, `M = {0, 1, 1, 2}`, `M = {0, 0, 3, 3}`, `M = {0, 0, 0, 1, 1, 1}` (with `a = 3, b = 3`) — all show existence holds for every `P' ≤ M` of size `a + 1`. Sample size still small, but no counter-example found.

This is **not** yet a proof. For S47-D, the existence lemma is the second open obligation (after committing to the definition):

```lean
private lemma firstDescentRotation_exists {n : ℕ} {a b : ℕ} (hb : 1 ≤ b)
    (M : Sym (Fin n) (a + b)) (P' : Sym (Fin n) (a + 1)) (hP' : P'.1 ≤ M.1) :
    ∃ k : ℕ, ((rotateSortedList M k).take (a + 1) : Multiset (Fin n)) = P'.1
```

This existence claim is **plausibly equivalent to a multiset-prefix version of the classical cycle-lemma** (recon doc §3), and may itself be ~50-100 LOC. It cannot ship in the same PR as Def I + `_take_eq` spec without inflating S47-D well past the ~25-30 LOC envelope.

**Refined S47-D scope**: ship Def I as `noncomputable def firstDescentRotation` using `Classical.choose` on an `axiom`-level existence statement, deferred to S48. OR: ship Def I conditional on `(h_exists : ∃ k, take(a+1) L_k = P'.1)` as an explicit hypothesis. The latter is cleaner — no axiom, the existence is part of the caller's obligation.

```lean
private noncomputable def firstDescentRotation {n : ℕ} {a b : ℕ}
    (M : Sym (Fin n) (a + b)) (P' : Sym (Fin n) (a + 1))
    (h_exists : ∃ k : ℕ, ((rotateSortedList M k).take (a + 1) : Multiset (Fin n)) = P'.1)
    (hab : 0 < a + b) : Fin (a + b) :=
  ⟨Nat.find h_exists % (a + b), Nat.mod_lt _ hab⟩
```

The `firstDescentRotation_take_eq` spec lemma is then a direct application of `Nat.find_spec`.

## 7. Files modified

- `research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/sessions/2026-05-31-s47-prep-firstdescent-validation.md` (this file, NEW)
- `research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/state.md` — S47 PREP block prepended; iteration bump 46 → 47; nextAction refreshed.
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01.json` — iteration bump, knowledge insights/builtItems/nextSteps appended, progressSummary prepended, focus/nextAction refreshed.

**No Lean source changes.** Sorry count unchanged at 2 (proof-level: lines 1847, 2495; 17 total textual `sorry` occurrences including comments). Axiom count unchanged at 0.

## 8. Next actions (S48 menu)

| # | Candidate | LOC | Risk | Notes |
|---|-----------|-----|------|-------|
| D' | Ship `firstDescentRotation` (Def I, h_exists-parameterised) + `_take_eq` spec | ~15-20 | LOW | refined from S47-D MEDIUM via this PREP; existence hypothesis is caller's obligation |
| E | Prove `firstDescentRotation_exists` for general `P' ≤ M` of size `a + 1` | ~50-100 | HIGH | the multiset-prefix cycle lemma; could be a standalone Mathlib contribution (recon doc §6) |
| F | INFRA: repair G9 `proofs/.lake` self-loop | ~1 cmd | LOW (shared-state) | requires consensus across active researchers; out of scope for any individual research PR |
| G | Doc-only design memo for 2B.4' bijection using Def I `firstDescentRotation` | ~150-200 LOC md | LOW | per S46 state.md alt: forward (k, j) ↦ (Prefix, Suffix), inverse via firstDescentRotation |

**Recommended next**: D' (LOW risk after this PREP), followed by E or G.

## 9. Honesty

- This PR is **doc-only**. No Lean code shipped, no sorries closed, no axioms eliminated. Net mathematical progress is **zero theorems proved**.
- The validation tables I provide are **manual enumeration** (no decidable instance, no `decide` verification, no Lean kernel check). I have triple-checked Cases 1, 2 by hand and cross-referenced with S43's Case 3 table.
- The "Defs I and III agree on Cases 1, 2, 3" conclusion is **empirical evidence** (three data points), not a universal theorem. The recommendation rests on this evidence + the simpler-formalisation argument.
- The existence question for Def I is **open**. I provide heuristic + 7 spot-check cases (no counter-example), not a proof.
- This work UNBLOCKS S47-D — that is the value. Whether it should be classified as "progress" or "infrastructure" depends on whether S48 actually ships the lemma. If S48 does not ship within ~3 sessions, this memo's value decays.

## 10. Mathlib pin verification

- Toolchain: `leanprover/lean4:v4.26.0` (`proofs/lean-toolchain`).
- Mathlib SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`proofs/lake-manifest.json`).
- Both byte-stable since at least 2026-05-12 per prior session memos (S9 prob-method-lovasz-local-oq-01, S29 minkowski-theorem-oq-04, S44/S45/S46 this slug).
- No new toolchain / Mathlib bump on this branch.
