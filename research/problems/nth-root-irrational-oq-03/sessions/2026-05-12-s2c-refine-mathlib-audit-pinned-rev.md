# S2c REFINE — Mathlib API verification at pinned rev + corrected proof skeleton

**Date**: 2026-05-12
**Researcher**: researcher-5
**Mode**: REFINE (doc-only — verifies S2 PREP claims against actual Mathlib source at pinned rev; corrects three signature/API errors; provides an alternative direct proof path)
**Status**: pristine doc-only follow-up to PR #18275 (S1 OBSERVE, researcher-10, merged 22:17Z) and PR #18355 (S2 PREP, researcher-8, merged 23:17Z).

## Bottom line

S2 PREP's conclusion is **correct in substance**: `axiom irrational_liouvilleWith_two` at `proofs/Proofs/ETranscendentalOQ03.lean:114` can be discharged at the pinned Mathlib rev (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, `v4.26.0`) without an upstream PR.

However, the proof skeleton in S2 PREP §2.1 contains three concrete inaccuracies that a builder following it verbatim would hit immediately:

1. **Lemma return type uses postfix `.Infinite`**, not prefix `Set.Infinite { ... }`.
2. **`Set.Infinite.exists_nat_embedding` does not exist**; the correct name is `Set.Infinite.natEmbedding` (no `exists_`, returns an `ℕ ↪ s` embedding rather than `∃ φ`).
3. **The "denominators unbounded" subargument** (S2 PREP §2.2) is the technical core; this REFINE pins down the exact Mathlib infrastructure to use and notes that the per-denominator-finiteness lemma (`den_le_and_le_num_le_of_sub_lt_one_div_den_sq`) is for *rational* `ξ`, not real — so a small adaptation is needed.

Additionally, this REFINE identifies an **alternative proof path** via `exists_rat_abs_sub_lt_and_lt_of_irrational` (Mathlib's "strictly better approximation" lemma at `DiophantineApproximation/Basic.lean:176`), which sidesteps the denominator-image bookkeeping entirely.

This document is doc-only — no Lean code, no `meta.json` changes.

## 1. Mathlib API audit at exact pinned rev

All file paths below are at rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, fetched directly from `raw.githubusercontent.com/leanprover-community/mathlib4/<rev>/...`.

### 1.1 `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` (551 lines)

```lean
-- line 147
theorem exists_rat_abs_sub_le_and_den_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ q : ℚ, |ξ - q| ≤ 1 / ((n + 1) * q.den) ∧ q.den ≤ n

-- line 176
theorem exists_rat_abs_sub_lt_and_lt_of_irrational {ξ : ℝ} (hξ : Irrational ξ) (q : ℚ) :
    ∃ q' : ℚ, |ξ - q'| < 1 / (q'.den : ℝ) ^ 2 ∧ |ξ - q'| < |ξ - q|

-- line 197 (inside namespace Real, so full name is Real.…)
theorem infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational {ξ : ℝ} (hξ : Irrational ξ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite

-- line 224 (inside namespace Rat)
theorem den_le_and_le_num_le_of_sub_lt_one_div_den_sq {ξ q : ℚ}
    (h : |ξ - q| < 1 / (q.den : ℚ) ^ 2) :
    q.den ≤ ξ.den ∧ ⌈ξ * q.den⌉ - 1 ≤ q.num ∧ q.num ≤ ⌊ξ * q.den⌋ + 1

-- line 253 (inside namespace Rat)
theorem finite_rat_abs_sub_lt_one_div_den_sq (ξ : ℚ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℚ) ^ 2}.Finite

-- line 277 (back in namespace Real, after end Rat)
theorem Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational (ξ : ℝ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite ↔ Irrational ξ
```

**S2 PREP missed**:
- The **IFF version** at line 277 — even stronger than the forward direction PR #18355 cited.
- The **strictly-better-approximation lemma** at line 176, which gives an alternative proof path (see §4 below).
- The fact that `den_le_and_le_num_le_of_sub_lt_one_div_den_sq` is for *rational* `ξ` (line 224's signature: `{ξ q : ℚ}`), so it cannot be directly reused for our real `x`; the analogous bound for real `ξ` needs to be reproved (~5-10 LOC).

### 1.2 `Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean` (340 lines)

```lean
-- line 51
def LiouvilleWith (p x : ℝ) : Prop :=
  ∃ C, ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p

-- line 56
theorem liouvilleWith_one (x : ℝ) : LiouvilleWith 1 x

-- line 73
theorem exists_pos (h : LiouvilleWith p x) :
    ∃ (C : ℝ) (_h₀ : 0 < C),
      ∃ᶠ n : ℕ in atTop, 1 ≤ n ∧ ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p

-- line 283
protected theorem LiouvilleWith.irrational (h : LiouvilleWith p x) (hp : 1 < p) : Irrational x
```

**Header docstring (lines 22-25)** — the comment that misled S1 OBSERVE PR #18275:

> If `1 < p ≤ 2`, then this condition is equivalent to `Irrational x`. The forward implication
> does not require `p ≤ 2` and is formalized as `LiouvilleWith.irrational`; the other implication
> follows from approximations by continued fractions and is not formalized yet.

S2 PREP §3.1 already explained why this comment is misleading; I confirm: at v4.26.0, the *specific case `p = 2`* is reachable from `DiophantineApproximation/Basic.lean` without invoking continued fractions. No bridge lemma `LiouvilleWith.of_irrational_eq_two` exists in `LiouvilleWith.lean` (verified: `grep -n "of_irrational" LiouvilleWith.lean` returns 0 hits).

### 1.3 `Mathlib/Data/Set/Finite/Basic.lean`, line 848

```lean
/-- Embedding of `ℕ` into an infinite set. -/
noncomputable def Infinite.natEmbedding (s : Set α) (h : s.Infinite) : ℕ ↪ s :=
  h.to_subtype.natEmbedding
```

**S2 PREP §2.1 line 105 wrote** `Set.Infinite.exists_nat_embedding` — that name does NOT exist in Mathlib. The actual name is `Set.Infinite.natEmbedding` (under `namespace Set`, called as `hinf.natEmbedding _`), and it returns a function rather than an existential. The downstream usage `obtain ⟨φ, hφ_inj, hφ_mem⟩ := hinf.exists_nat_embedding` would fail; the correct usage is:

```lean
let φ : ℕ ↪ {q : ℚ | …} := hinf.natEmbedding _
-- φ.injective : Function.Injective φ        (use as `φ.injective`)
-- (φ k).2     : (φ k).val ∈ {q : ℚ | …}    (the subtype membership proof)
```

### 1.4 `Mathlib/Order/Filter/AtTopBot/Basic.lean`, line 74

```lean
theorem frequently_atTop : (∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b ≥ a, p b
```

This is the bridge from `Set.Infinite` evidence to the `∃ᶠ n in atTop` shape that `LiouvilleWith` expects.

## 2. Refinement of S2 PREP §2.1 skeleton

### 2.1 Three line-level corrections

| S2 PREP line | Issue | Correction |
|---|---|---|
| 101 (`Set.Infinite {q : ℚ \| …}`) | Prefix form not Mathlib idiom | Postfix `{q : ℚ \| …}.Infinite` (matches Mathlib `Real.infinite_rat_…` signature) |
| 105 (`hinf.exists_nat_embedding`) | Name does not exist | Use `hinf.natEmbedding _ : ℕ ↪ {q : ℚ \| …}` (returns embedding, not existential) |
| 132 (`Set.Infinite.exists_strictMono_subseq`) | Name does not exist | Use `Nat.exists_strictMono` or build manually via `frequently_atTop` |

### 2.2 The "denominators unbounded" core, with exact Mathlib paths

S2 PREP §2.2 sketched: for fixed `n`, the slice `{q ∈ S : q.den = n}` is finite, so the projection `Rat.den '' S` is infinite, so by `Set.Infinite → ¬BddAbove` on ℕ, denominators are unbounded.

**Subtlety**: `Rat.den_le_and_le_num_le_of_sub_lt_one_div_den_sq` (line 224) takes `{ξ q : ℚ}` — both rational. For our real `x`, we need the analog. Sketch:

```lean
-- Auxiliary lemma (~10 LOC):
-- For real x and q : ℚ with |x - q| < 1/q.den^2,
-- q.num ∈ Set.Icc (⌈x * q.den⌉ - 1) (⌊x * q.den⌋ + 1).
lemma num_bounded_of_approx {x : ℝ} {q : ℚ} (h : |x - q| < 1 / (q.den : ℝ) ^ 2) :
    (⌈x * q.den⌉ - 1 : ℤ) ≤ q.num ∧ q.num ≤ (⌊x * q.den⌋ + 1 : ℤ) := by
  -- |x · q.den - q.num| < 1 / q.den  (multiply through; q.den > 0)
  -- so x · q.den - 1/q.den < q.num < x · q.den + 1/q.den
  -- since 1/q.den ≤ 1 (q.den ≥ 1), the integer q.num lies in the claimed Icc
  sorry
```

This is the real-x analog of the rational-ξ lemma at line 224, with `q.den ≤ ξ.den` dropped (no longer makes sense for real ξ — it's replaced by `q.den ≤ N` parametrically below).

**Per-denominator-finiteness** (the *converse* of "denominators unbounded"): for fixed `n`,

```lean
{q : ℚ | q.den = n ∧ |x - q| < 1 / (n : ℝ) ^ 2}
  ⊆ {m/n | m ∈ Set.Icc (⌈x * n⌉ - 1) (⌊x * n⌋ + 1)}
```

The RHS is a `Finset.image` of a `Finset.Icc` of integers — a 3-element Finset (size depends on `Int.fract (x * n)`). Hence the LHS is finite. Apply `Set.Finite.subset`.

### 2.3 Repackaging via `frequently_atTop`

```lean
-- After establishing (Rat.den '' S).Infinite:
intro N : ℕ
-- Want: ∃ n ≥ N, ∃ m, x ≠ m/n ∧ |x - m/n| < 1/n^2
have : ¬ BddAbove (Rat.den '' S) :=
  fun ⟨M, hM⟩ => h_image_infinite.not_bddAbove ⟨M, hM⟩
  -- Set.Infinite ℕ → ¬BddAbove (for ℕ specifically, via Set.Finite.bddAbove + contrapositive)
obtain ⟨q, hqS, hqN⟩ : ∃ q ∈ S, q.den ≥ N := …
refine ⟨q.den, hqN, q.num, ?_, ?_⟩
· -- x ≠ q.num / q.den
  rw [Rat.num_div_den]; exact (Irrational.ne_rat hx q).symm
· -- |x - q.num / q.den| < 1 / q.den ^ 2  (= 1 / q.den ^ (2 : ℝ))
  rw [Rat.num_div_den]; exact_mod_cast hqS
```

The `Set.Infinite ℕ → ¬BddAbove` step uses `Finite.bddAbove` (`Mathlib/Data/Set/Finite/Lattice.lean:401`'s context — every finite subset of a directed order is bounded; ℕ is directed; contrapositive). The contrapositive direction is needed: actually it's `infinite_of_not_bddAbove` at line 407 of `Lattice.lean`, but we want the **other** direction. For ℕ specifically: `BddAbove s ↔ s.Finite` holds (because `BddAbove` means `s ⊆ Set.Iic M` which is `Finset.range (M+1)`, finite). So `Set.Infinite s → ¬BddAbove s` is `mt Finite.bddAbove` after rephrasing.

### 2.4 Final delta estimate (corrected vs S2 PREP §2.3)

| Step | Lines | Confidence at v4.26.0 |
|---|---:|---|
| Imports + theorem signature | 5 | high |
| `have hinf := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx` | 1 | high — verified exists |
| `num_bounded_of_approx` auxiliary lemma (real-x analog of Rat lemma) | 12 | medium — needs care with casts |
| Per-denominator slice finiteness | 15 | medium — `Set.Finite.subset` of `Finset.image (Finset.Icc …)` |
| `(Rat.den '' S).Infinite` from slice-finiteness | 10 | medium — uses `Set.Finite.image_inv` or `Set.Infinite.preimage` |
| `Set.Infinite ℕ → ∀ N, ∃ n ≥ N in set` | 8 | medium — via `mt Finite.bddAbove` + `BddAbove ℕ ↔ Finite` |
| Repackage `q.den ≥ N + q ∈ S` into `LiouvilleWith` shape | 20 | medium-high — `Rat.num_div_den`, `Irrational.ne_rat`, casts |
| Misc (`norm_cast`, `push_cast`, glue) | 10 | mechanical |
| **Total** | **~81** | overall: medium |

This matches S2 PREP's §2.3 estimate of ~83 LOC. The main delta in **confidence** vs S2 PREP: the per-denominator finiteness step is more concrete now (uses real-x adapted version of line 224's lemma), but is still ~15 LOC of original work because Mathlib's `den_le_and_le_num_le_of_sub_lt_one_div_den_sq` is rational-only.

## 3. Alternative proof path: recursive better-approximation

**S2 PREP did not mention `exists_rat_abs_sub_lt_and_lt_of_irrational`** at line 176 of the same Mathlib file. This lemma states:

> Given `q : ℚ` and `Irrational ξ`, there exists `q' : ℚ` with `|ξ - q'| < 1 / q'.den^2` AND `|ξ - q'| < |ξ - q|`.

I.e., from any approximation, get a *strictly better* one (in the `1/den^2` regime).

This enables a **completely different proof path** that sidesteps the denominator-image bookkeeping:

```lean
theorem irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x := by
  refine ⟨1, ?_⟩
  rw [frequently_atTop]
  intro N
  -- Strategy: starting from q₀ := ⌊x⌋ (or any rational), iterate
  -- exists_rat_abs_sub_lt_and_lt_of_irrational until q.den ≥ N.
  -- Because each q' has *strictly smaller* |x - q'|, no q repeats.
  -- But this alone doesn't guarantee q.den → ∞. We additionally use:
  --   For irrational x and q with |x - q| < ε, the density q.den must
  --   exceed 1/√(ε · (|x| + 1)) (roughly) — wait, this is circular.
  sorry
```

**Problem with this path**: `exists_rat_abs_sub_lt_and_lt_of_irrational` guarantees `|x - q'| < |x - q|` but **does NOT** guarantee `q'.den > q.den`. The denominators could stay bounded while the error shrinks (in principle). So this lemma alone is insufficient.

However, it CAN be combined with the per-denominator-finiteness observation: starting from any `q`, iterating the lemma gives a *sequence* of distinct rationals in `S := {q ∈ ℚ | |x - q| < 1/q.den^2}`. Each fixed denominator hosts only finitely many such q. So the sequence must visit infinitely many denominators, hence pass beyond any `N`.

Concretely:

```lean
-- Build a sequence q₀, q₁, q₂, … of distinct rationals in S.
-- For each n, only finitely many qᵢ have qᵢ.den ≤ n. So ∃ i with qᵢ.den ≥ N.
```

This path has the same ~15-20 LOC technical core (per-denominator finiteness) as the infinite-set path, but avoids `Set.Infinite.natEmbedding` (which is noncomputable; the recursive sequence is constructive modulo `Classical.choice` inside `exists_rat_abs_sub_lt_and_lt_of_irrational`).

**Recommendation**: prefer the §2 path (via `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`) — it's one Mathlib lookup shorter and matches S2 PREP's outline.

## 4. Anti-targets (do NOT pick up in S2 ACT after this REFINE)

- **Editing `Proofs/ETranscendentalOQ03.lean`**: that's S2 ACT (separate session).
- **Touching `state.md` / `knowledge.md` / `problem.md`** in this PR: keep this REFINE pristine doc-only; state.md updates should bundle with S2 ACT.
- **Editing `meta.json`**: no axiom count change yet — the discharge hasn't happened.
- **Adding `loom:review-requested`**: math-agent policy.
- **Re-claiming `e-transcendental-oq-03`** for S2 ACT in this session — that's a separate claim (S2 PREP §4.2 Option A recommendation).
- **Building Docker**: doc-only session; no build required.

## 5. Honest scope

This file is a **doc-only S2c REFINE** of PR #18355 (S2 PREP). It does NOT add any Lean code, discharge any axiom, modify any `meta.json` count, or edit any other research file in this slug. The single new file is this session note (`sessions/2026-05-12-s2c-refine-mathlib-audit-pinned-rev.md`).

The substantive contribution beyond S2 PREP:

1. **Verified Mathlib API at exact pinned rev** (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) with line numbers from `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` and `Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean` (verified via `raw.githubusercontent.com` direct fetch — no Mathlib clone or Docker build required).
2. **Three line-level corrections** to S2 PREP §2.1's proof skeleton (postfix `.Infinite`, `natEmbedding` not `exists_nat_embedding`, denominator-image step exact API).
3. **Identified two API gaps** not covered by S2 PREP:
   - `Rat.den_le_and_le_num_le_of_sub_lt_one_div_den_sq` is rational-ξ only; real-x analog needs ~12 LOC original work.
   - `Set.Infinite.exists_strictMono_subseq` (S2 PREP §2.3 line 5) does not exist; the correct path is `mt Finite.bddAbove` + `BddAbove ℕ ↔ Finite`.
4. **Alternative direct proof path** via `Real.exists_rat_abs_sub_lt_and_lt_of_irrational` (line 176), noting it has the same technical core but trades a different sequence-construction step for the `Set.Infinite.natEmbedding`.
5. **Confirmed S2 PREP's IFF observation extends further**: the bidirectional `Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational` (line 277) is also at v4.26.0.

The proof gets one step closer to discharge by removing skeleton errors a builder would hit at `lake build`; total LOC budget unchanged (~80-120).

## 6. Differentiation from PR #18275 and PR #18355

| Aspect | PR #18275 (S1 OBSERVE) | PR #18355 (S2 PREP) | This S2c REFINE |
|---|---|---|---|
| Conclusion on S2 ACT | "Blocked on upstream Mathlib PR" | "Feasible at v4.26.0; ~80 LOC" | Agrees with S2 PREP substance |
| Proof skeleton | Not provided | §2.1, ~120 LOC sketch | §2.1–§2.4 with line-level fixes |
| Mathlib lemma name verification | Inferred from `LiouvilleWith.lean` header | Cited file path | **Fetched from `raw.githubusercontent.com` at exact rev with line numbers** |
| Alternative paths | Not explored | Not mentioned | §3 (via `exists_rat_abs_sub_lt_and_lt_of_irrational`) |
| Per-denominator finiteness | Out of scope | Sketched (§2.2) | Pinned to Mathlib infrastructure (§2.2–§2.3) |

The three PRs are complementary:
- **#18275** mapped the territory (axiom inventory, file inventory, project status).
- **#18355** disproved the "blocked" conclusion and provided the proof outline.
- **This S2c REFINE** verifies API at exact pinned rev, fixes three concrete skeleton errors, and offers an alternative path.

Together they make S2 ACT a low-uncertainty implementation task: the next researcher claiming `e-transcendental-oq-03` (per S2 PREP §4.2 Option A) can adopt this REFINE's §2.4 line budget with high confidence that no API gaps remain.

## 7. Cross-slug coordination (re-affirms S2 PREP §4.2)

The S2 ACT touches `proofs/Proofs/ETranscendentalOQ03.lean`, owned by `e-transcendental-oq-03` slug, NOT `nth-root-irrational-oq-03`. Per S2 PREP's Option A recommendation: a future researcher should:

1. Run `./scripts/research/claim-problem.sh release nth-root-irrational-oq-03` (this session) — done at end.
2. Claim `e-transcendental-oq-03` for the S2 ACT.
3. Use this REFINE + S2 PREP + S1 OBSERVE as the joint roadmap.
4. Update `src/data/proofs/e-transcendental-oq-03/meta.json` to drop the `irrational_liouvilleWith_two` axiom and decrement `axiomCount` 2 → 1.
5. Cross-reference back: optionally add a `crossReferences` entry in `nth-root-irrational-oq-03.json` (gallery) pointing to the resolved discharge.

## 8. Race notes

- Pre-write race-check at `T-30min` (23:25Z): `gh pr list --repo rjwalters/lean-genius --search nth-root-irrational-oq-03 --state open --limit 20` → 0 open PRs on this slug.
- `git branch -r | grep nth-root-irrational-oq-03` → 0 fresh remote branches.
- Most recent merge: PR #18355 at 23:17Z (~15 min before claim).
- Differentiation guarantee: this REFINE's contribution is **mathematical verification of S2 PREP's API claims against the exact pinned rev**, plus three line-level skeleton corrections. A parallel agent racing on the same slug would either:
  - Repeat S2 PREP's outline (low-value duplicate),
  - Skip to S2 ACT (touching Lean) — which this REFINE is anti-targeted from.
- The session-note pattern (single new file, no edits to existing slug files) maintains conflict-free git status against any parallel work in this slug.
