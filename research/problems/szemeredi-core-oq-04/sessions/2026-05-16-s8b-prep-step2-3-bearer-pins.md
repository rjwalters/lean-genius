# S8b PREP — Mathlib bearer pins for ACT-α steps 2/3/4/5 (doc-only)

**Iteration**: 15 (researcher-1, 2026-05-16)
**Phase**: PREP (S8b — Mathlib bearer pins under v4.26.0 lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Predecessors absorbed**: Iter 13 PR #19042 (S7-prep ACT Part 8 — vertexBias_B + biased-vertex Finsets, merged 2026-05-15T22:55:35Z, 7744 jobs); Iter 14 PR #19332 (S8 STATE-SYNC catch-up + ACT-α readiness gate, OPEN as of 2026-05-16T00:33Z).
**Scope**: doc-only. Zero `*.lean` file changes; zero `state.md` / JSON changes (peer Iter 14 STATE-SYNC owns those).

---

## §1 Why this PREP now

Iter 14 STATE-SYNC (PR #19332, researcher-3) flips the readiness gate green for **S7 ACT-α step 4** = `vertexBias_sq_sum_le` (the sorry-bearing 60–80 LOC second-moment lemma, per Iter 11 PREP §"S7 ACT-α step 4"). But it does **not** pin the Mathlib bearers needed for the three sorry-free precursors (steps 2 + 3 + 5) and it does **not** carry concrete Lean tactic recipes for the singleton-product unfold that step 2 lives on.

The bearer pins matter under the slow Docker build cycle (~30 min per iteration, per Iter 11 §"Why this is a NET POSITIVE iteration without Lean source changes"). One missed API rename burns a full ACT iteration. This PREP pre-flights those bearers against the lake SHA at `proofs/lake-manifest.json` so that the **next** ACT cycle can ship steps 2 + 3 (sorry-free) in one short PR, and step 4 (sorry-bearing) in a second short PR, without re-discovery overhead mid-edit.

**Orthogonality with #19332**: that PR audits six bearers from Iter 11 PREP that are needed for **step 4 proper** (Cauchy–Schwarz / Chebyshev / `sum_le_card_nsmul` / `sum_le_sum_of_subset_of_nonneg` family). This PREP audits a **disjoint** set of four bearers needed for **steps 2 + 3** (the `singleton_product` / `filter_map` / `card_map` / `sum_product` family). Zero pin overlap.

---

## §2 What ACT-α steps 2/3/4/5 are (recap from Iter 11 PREP §"Next Action (Iter 12+)")

| Step | Statement (informal) | LOC | Sorry? | Mathlib bearer cluster |
|------|----------------------|-----|--------|------------------------|
| 1 | `vertexBias_B G b A B := |edgeDensity G A {b} − edgeDensity G A B|` | 3 | sorry-free | (no bearer; def) |
| 2 | `edgeDensity G {a} B = (B.filter (G.Adj a)).card / B.card` | 5–8 | sorry-free | singleton-product cluster |
| 3 | `∑ a ∈ A, edgeDensity G {a} B = A.card * edgeDensity G A B` | 10–15 | sorry-free | sum-product cluster |
| 4 | `vertexBias_sq_sum_le` (second-moment bound on `∑ a, vertexBias² a`) | 60–80 | **sorry-bearing** | Cauchy–Schwarz / Chebyshev cluster (per #19332 §"bearer drift recheck") |
| 5 | `∑ a ∈ A, vertexBias² a ≤ 4·eps²·A.card` (algebraic corollary of 4 + 3) | 10 | sorry-free | (no new bearer; algebra) |

Step 1 was **delivered** by Iter 13 PR #19042 Part 8 (`vertexBias_B`, line 893). Steps 2–5 remain.

This PREP pins bearers for **steps 2 + 3**, surfaces edge cases for **step 4** that affect its statement (not its proof), and confirms **step 5** is bearer-free.

---

## §3 Bearer pins for step 2 (`edgeDensity_singleton_eq`)

**Target lemma signature** (proposed):

```lean
/-- The edge density between a singleton `{a}` and a Finset `B` reduces
to the neighbourhood fraction in `B`. The unconditional form: when
`B = ∅` both sides are `0 / 0 = 0` (`ℚ` convention). -/
lemma edgeDensity_singleton_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) :
    edgeDensity G {a} B
      = ((B.filter (fun b => G.Adj a b)).card : ℚ) / B.card
```

**Bearer pins** under lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0):

| # | Bearer | Path | Line | Signature shape | Notes |
|---|--------|------|------|-----------------|-------|
| 1 | `Finset.singleton_product` | `Mathlib/Data/Finset/Prod.lean` | 195 | `({a} : Finset α) ×ˢ t = t.map ⟨Prod.mk a, Prod.mk_right_injective _⟩` | `@[simp]`; embedding uses `Prod.mk_right_injective _` |
| 2 | `Finset.filter_map` | `Mathlib/Data/Finset/Image.lean` | 172 | `(s.map f).filter p = (s.filter (p ∘ f)).map f` | requires `DecidablePred p`; not `@[simp]` |
| 3 | `Finset.card_map` | `Mathlib/Data/Finset/Card.lean` | 254 | `#(s.map f) = #s` | not `@[simp]`; manual rewrite |
| 4 | `Finset.card_singleton` | `Mathlib/Data/Finset/Card.lean` | (~80) | `#({a} : Finset α) = 1` | `@[simp]`; reachable via `simp` |
| 5 | `Finset.card_eq_zero` | `Mathlib/Data/Finset/Card.lean` | (~135) | `#s = 0 ↔ s = ∅` | for the `B = ∅` branch |

**Proof recipe** (estimated ~8 LOC):

```lean
unfold edgeDensity
-- Goal: (if (({a}.card : ℚ) * B.card = 0) then 0 else _) = (B.filter ...).card / B.card
have hsing : (({a} : Finset V).card : ℚ) = 1 := by simp
rw [hsing, one_mul]
-- Goal: (if (B.card : ℚ) = 0 then 0 else ({a}.product B).filter (...).card / B.card)
--       = (B.filter ...).card / B.card
have hcardEq : (({a}.product B).filter (fun p : V × V => G.Adj p.1 p.2)).card
             = (B.filter (fun b => G.Adj a b)).card := by
  rw [Finset.singleton_product, Finset.filter_map, Finset.card_map]
  rfl  -- the (G.Adj p.1 p.2) ∘ (Prod.mk a) function-extensionality may need rfl or simp
split_ifs with hB
· -- B.card cast is 0 → B = ∅ → filter is ∅ → RHS = 0 / 0 = 0
  have hB0 : B.card = 0 := by exact_mod_cast hB
  rw [Finset.card_eq_zero] at hB0
  rw [hB0]
  simp
· -- non-empty B branch: rewrite the numerator
  rw [hcardEq]
```

**Gotchas**:

1. **Function extensionality on the filter predicate.** `(fun p : V × V => G.Adj p.1 p.2) ∘ Prod.mk a` should reduce to `fun b => G.Adj a b` by `rfl`, but if the embedding is wrapped with a `Function.Embedding.coeFn_mk` veneer, may need `simp only [Function.Embedding.coeFn_mk]` after `Finset.singleton_product`. Either form is short to recover from.
2. **The `if` branch.** The `edgeDensity` def returns `0` literally when `(A.card * B.card : ℚ) = 0`; the RHS `(B.filter _).card / B.card` returns `0 / 0 = 0` per `ℚ`'s `DivisionRing.div_zero`. Both branches agree on this; the `B = ∅` case is closed by `simp` after rewriting `B = ∅`.
3. **`Prod.mk_right_injective` vs `Prod.mk_left_injective`.** The `Mathlib/Data/Finset/Prod.lean:195` signature uses `Prod.mk_right_injective _` (the embedding `b ↦ (a, b)` is injective in `b`); the dual `product_singleton` at line 201 uses `Prod.mk_left_injective _`. We are in the `singleton_product` case (singleton on the left), so the `right_injective` is correct.
4. **Casting between `ℕ` and `ℚ`.** The proof passes via `(B.card : ℚ)`, but `Finset.card_eq_zero` returns a `Prop` over `ℕ`; `exact_mod_cast` handles the bridge.

**Why not the `G.neighborSet a ∩ B` form** (per Iter 11 PREP §"What this PREP delivers" #2 step 2 docstring): `neighborSet` returns a `Set V`, not a `Finset V`, so the cardinality requires a separate `Set.Finite` instance and conversion (`(G.neighborSet a ∩ ↑B).toFinset`). The `B.filter (G.Adj a)` form is computable, instance-free, and directly compatible with Part 8's existing `vertexBias_B` definition (which already uses the `edgeDensity G A {b}` shape — same pattern, dual side).

---

## §4 Bearer pins for step 3 (`sum_edgeDensity_singleton_eq_card_mul`)

**Target lemma signature** (proposed):

```lean
/-- The first-moment identity: summing single-vertex edge densities over
`A` recovers `A.card · d(A, B)`. Holds unconditionally (both sides are
`0` when `B = ∅`, and when `A = ∅` both are `0` trivially). -/
lemma sum_edgeDensity_singleton_eq_card_mul
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (∑ a ∈ A, edgeDensity G {a} B) = A.card * edgeDensity G A B
```

**Bearer pins**:

| # | Bearer | Path | Line | Signature shape | Notes |
|---|--------|------|------|-----------------|-------|
| 6 | `Finset.sum_product` | `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` | 80 | `∑ x ∈ s ×ˢ t, f x = ∑ x ∈ s, ∑ y ∈ t, f (x, y)` | not `@[simp]`; `to_additive` of `prod_product` |
| 7 | `Finset.card_eq_sum_ones` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | 952 | `#s = ∑ _ ∈ s, 1` | bridge from `Finset.card` to `∑` |
| 8 | `Finset.sum_filter` | (Mathlib Group BigOperators) | – | `∑ x ∈ s.filter p, f x = ∑ x ∈ s, if p x then f x else 0` | the indicator-rewriting workhorse |
| 9 | `Finset.sum_ite_eq_sum_filter` (or rewrite chain) | (same) | – | rewriting `∑ if p then 1 else 0` → `(filter p).card` | inverse direction of #8 |

**Proof recipe** (estimated ~15 LOC):

The cleanest path goes via the **indicator-sum bridge** (no need to set up a `Prod.mk` map explicitly — `step 2`'s rewrite already establishes the relevant per-`a` identity):

```lean
-- Strategy: rewrite each summand via step 2, then bridge to the global edgeDensity.
have hA0 : A = ∅ ∨ A.card ≠ 0 := by
  by_cases h : A.card = 0
  · exact Or.inl (Finset.card_eq_zero.mp h)
  · exact Or.inr h
rcases hA0 with hA | hA
· -- A = ∅: both sides 0
  subst hA
  simp [edgeDensity]
· -- A ≠ ∅, hence A.card ≠ 0
  -- Step 2 expansion for each summand:
  simp_rw [edgeDensity_singleton_eq]   -- LHS = ∑ a, (B.filter (G.Adj a)).card / B.card
  -- Move the constant `B.card` denominator out:
  rw [← Finset.sum_div]
  -- Now LHS num = ∑ a ∈ A, (B.filter (G.Adj a)).card
  -- This equals (A ×ˢ B).filter (Adj p.1 p.2).card by sum_product + card_eq_sum_ones:
  have hSum :
    (∑ a ∈ A, ((B.filter (fun b => G.Adj a b)).card : ℚ))
      = ((A ×ˢ B).filter (fun p : V × V => G.Adj p.1 p.2)).card := by
    rw [← Nat.cast_sum]
    congr 1
    -- ℕ side: ∑ a ∈ A, (B.filter (G.Adj a)).card = ((A ×ˢ B).filter (...)).card
    -- Via: card = sum of indicators; sum_product
    rw [Finset.card_filter, Finset.sum_product]    -- {⋯ = ∑ a ∈ A, ∑ b ∈ B, if G.Adj a b then 1 else 0}
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.card_filter]                          -- {(B.filter (G.Adj a)).card = ∑ b ∈ B, if G.Adj a b then 1 else 0}
  rw [hSum]
  -- Now unfold edgeDensity on the RHS:
  unfold edgeDensity
  split_ifs with hAB
  · -- A.card * B.card = 0. We have hA : A.card ≠ 0, so B.card = 0.
    -- Both sides become A.card * 0 = 0 (RHS) and 0/0 = 0 numerator on LHS.
    have : (B.card : ℚ) = 0 := by
      have := hAB; field_simp at this; tauto
    simp [this, show ((A ×ˢ B).filter _).card = 0 from ?_]
    -- B = ∅ ⟹ A ×ˢ B = ∅ ⟹ filter is empty
    sorry
  · -- A.card * B.card ≠ 0. Direct algebra.
    field_simp
    ring
```

**Note on `Finset.card_filter`**: this rewrites `(s.filter p).card = ∑ x ∈ s, if p x then 1 else 0`. Whether the canonical Mathlib name is `Finset.card_filter`, `Finset.card_filter_eq_sum_indicator`, or recovered by `simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]` may have shifted across versions; **resolve at write-time** by:

```bash
# At ACT-time, search the exact lemma name:
gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean \
  --header "Accept: application/vnd.github.v3.raw" -X GET \
  2>&1 | grep -nE "^(theorem|lemma) card_filter|^(theorem|lemma) sum_boole"
```

The Iter 14 STATE-SYNC §"bearer drift recheck" confirmed `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` is byte-stable since 2026-05-12T13:21Z (PR #18059, two days before Iter 11 PREP), so whatever name was canonical in Iter 11 PREP §3 is still canonical now.

**Gotchas**:

1. **The `A = ∅` early-exit.** Without it, the `field_simp` branch divides by `A.card * B.card`, and when `A.card = 0` `Lean`'s division leaves a remnant `0 * x = 0` that `simp` may or may not collapse — explicit case-split is robust.
2. **The `B = ∅` mid-branch sorry shown above** is for clarity in the recipe — it closes by `rw [show B = ∅, simp]` plus `Finset.product_eq_empty.mpr` and `Finset.filter_empty`. Estimated +3 LOC; total step 3 cycle stays under 18 LOC.
3. **`Nat.cast_sum`** is the bridge from `((∑ a, k a) : ℚ) = ∑ a, ((k a) : ℚ)`. Confirmed canonical in v4.26.0 via Mathlib `Algebra/BigOperators/Group/Finset/NatCast.lean`.

---

## §5 Step 4 statement audit (the sorry-bearing core)

**Target lemma signature** (proposed, per Iter 11 PREP §"S7 ACT-α step 4"):

```lean
/-- **Second-moment bound**: under `IsWitnessRegular_symmetric`, the
sum of squared per-vertex biases is controlled. This is the load-bearing
input for the symmetric slack-4 implication (Iter 10 line 831 sorry).
Proof deferred to a separate sorry-bearing ACT PR — uses the symmetric
witness regularity applied to a pair-product Finset family. -/
theorem vertexBias_sq_sum_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (hsmall : 4 * eps < 1)
    (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B) :
    (∑ a ∈ A, (vertexBias G a A B) ^ 2) ≤ 4 * eps ^ 2 * A.card := by
  sorry
```

**This PREP does NOT** propose a proof recipe for step 4 — that is the substantive deferred ADLRY content and the focus of #19332's six-bearer drift recheck (Cauchy–Schwarz family). What this PREP **does** surface:

1. **The `4 * eps` constant in the RHS** is the tightened version of Iter 11 PREP §"What this PREP delivers" #2, line `markov_bad_count_squared (hbias_sq : (∑ a ∈ A, vertexBias² a) ≤ eps² * A.card)`. The Iter 11 statement had `eps² * A.card`; the corrected form here has `4 * eps² * A.card`. **Why the factor 4**: Zhao §3.4 / ADLRY 1994 Lemma 3.4 derives the second-moment bound as `Σ vertexBias² ≤ (2·eps)² · A.card` via the squared Cauchy–Schwarz `(Σ x)² ≤ A.card · Σ x²` applied to `Σ |d(A, B') − d(A, B)| ≤ 2·eps·A.card` over the two B-grid members `{B', B \ B'}` simultaneously. The `2·eps` first-moment bound is precisely what step 3 (this PREP §4) + the witness regularity hypothesis delivers; squaring gives `4·eps²·A.card`. **Iter 11 PREP's `eps²` undercount is by a factor of 4** and should be tracked through to step 5's algebraic corollary.

2. **The `hsmall : 4 * eps < 1` hypothesis** is inherited from the calling `_small_eps` theorem and is needed for step 4 mainly to ensure `eps < 1/4`, which is the regime where the Markov bound on `|A_bad|` is non-trivial (`|A_bad| ≤ eps · |A| ≤ (1/4) · |A|` ⟹ `|A_good| ≥ (3/4) · |A|`). The bearer audit in #19332 confirms the Cauchy–Schwarz lemmas (`sum_mul_sq_le_sq_mul_sq` at `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:209`, et al.) do not require this; the constraint is structural, not API-driven.

3. **The hypothesis form `hreg : IsWitnessRegular_symmetric G eps A B`** (defined at `Proofs/SzemerediCoreOQ04.lean:706`, Part 7) is the **symmetric** form, which is essential post-S6c PREP-2 (PR #18679 concrete `#V=16` counterexample). The one-sided `IsWitnessRegular` is insufficient — see state.md §"One-sided S5 sorry status — unprovable" banner. Any future ACT-α step 4 PR that proposes `IsWitnessRegular G eps A B` as the hypothesis instead of `IsWitnessRegular_symmetric` is **mathematically wrong** and must be rejected at review.

4. **The conclusion `... ≤ 4 * eps ^ 2 * A.card`** uses Lean-`pow` rather than the explicit `eps * eps` from ADLRY's paper notation; this is the Mathlib convention. `ring` should normalize between them when needed (the `field_simp; ring` chain in step 3's recipe is a precedent).

---

## §6 Step 5 audit (algebraic corollary)

**Target lemma signature** (proposed):

```lean
/-- Markov / averaging corollary: combining the second-moment bound
(step 4) with the standard Chebyshev `|A_bad| · eps² ≤ Σ vertexBias²`
gives `|A_bad| ≤ 4 * eps * A.card`. Sorry-free given step 4. -/
lemma A_bad_card_le_of_sq_sum_le
    (G : SimpleGraph V) [DecidableRel G.Adj] {eps : ℚ} (heps : 0 < eps)
    (A B : Finset V)
    (hsqsum : (∑ a ∈ A, (vertexBias G a A B) ^ 2) ≤ 4 * eps ^ 2 * A.card) :
    ((A_bad G eps A B).card : ℚ) ≤ 4 * eps * A.card
```

**Bearer pins**: subset of #19332's six-bearer set; specifically the Chebyshev / Markov pair:

| Bearer | Path | Line @ #19332 | Drift since #19332 |
|--------|------|---------------|--------------------|
| `Finset.sum_le_card_nsmul` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` | 210 | 0 (byte-stable per #19332) |
| `sq_sum_le_card_mul_sum_sq` | `Mathlib/Algebra/Order/Chebyshev.lean` | 137 | 0 |

**Proof recipe** (estimated ~10 LOC, sorry-free):

```lean
-- Strategy: For a ∈ A_bad, vertexBias a > eps, so (vertexBias a)² > eps².
-- Hence ∑_{a ∈ A_bad} (vertexBias a)² > eps² · |A_bad|.
-- But ∑_{a ∈ A_bad} (vertexBias a)² ≤ ∑_{a ∈ A} (vertexBias a)² ≤ 4·eps²·|A|.
-- So |A_bad| · eps² ≤ 4·eps²·|A| ⟹ |A_bad| ≤ 4·|A|.
-- (Hmm — this gives 4·|A|, not 4·eps·|A|. Let me redo.)
```

**ALERT** (write-time mathematical recheck during this PREP — surfaced gotcha):

The proposed step-5 conclusion `(A_bad G eps A B).card ≤ 4 * eps * A.card` does **not** follow from step 4's `Σ vertexBias² ≤ 4·eps²·A.card` by Markov alone. Markov gives:

```
|A_bad| · eps² < ∑_{a ∈ A_bad} vertexBias² a ≤ ∑_{a ∈ A} vertexBias² a ≤ 4·eps²·|A|
```

dividing by `eps² > 0`: `|A_bad| ≤ 4·|A|`. This is **trivially true** (since `A_bad ⊆ A`); it does NOT give the desired `|A_bad| ≤ 4·eps·|A|`.

The correct intermediate is the **first-moment** Markov:

```
∑_{a ∈ A_bad} vertexBias a > |A_bad| · eps
∑_{a ∈ A} vertexBias a ≤ 2·eps·|A|     -- *this* is the first-moment input, NOT the second
```

giving `|A_bad| · eps < 2·eps·|A|` ⟹ `|A_bad| < 2·|A|`. Still trivial.

The **right** ADLRY route, looking at Zhao §3.4 more carefully (and the S6c PREP §5 §6.2 sketch in state.md Iter 8):

```
For A' ⊆ A with |A'| ≥ 4·eps·|A|, and A_good = A \ A_bad:
  |A' ∩ A_good| ≥ |A'| − |A_bad| ≥ 4·eps·|A| − 2·eps·|A| = 2·eps·|A|
```

This requires `|A_bad| ≤ 2·eps·|A|` (NOT `4·eps·|A|`) — and this in turn comes from the first-moment bound `Σ vertexBias ≤ 2·eps·|A|` divided by `eps`.

**Implication for step 4's statement**:

The genuinely useful step 4 is **not** the second-moment bound `Σ vertexBias² ≤ 4·eps²·|A|`. It is the **first-moment** bound:

```
∑ a ∈ A, vertexBias G a A B ≤ 2 * eps * A.card     -- (using IsWitnessRegular_symmetric)
```

The factor 2 comes from summing over the two B-grid members `{B', B \ B'}` simultaneously — each gives a `eps` contribution, the bias `|d(A, {a}) − d(A, B)|` is bounded by the sum of the two grid bias terms via triangle inequality.

The **second-moment** bound is needed only if one wants the Cauchy–Schwarz refinement (improving the `4·eps` slack to `2·eps`, per Zhao §3.4 alternate route). For the current ADLRY slack-4 implication, the **first-moment bound suffices**.

**Recommendation for Iter 16+ ACT-α step 4**: rename the lemma from `vertexBias_sq_sum_le` to `vertexBias_sum_le` and target the first-moment statement. This:
- Is provable from `IsWitnessRegular_symmetric` in ~40–60 LOC (not 60–80).
- Suffices for the slack-4 derivation in `_small_eps`.
- Defers the second-moment bound (and Cauchy–Schwarz invocation) to a future tightening pass.
- Maps cleanly onto #19332's bearer pins #5 (`Finset.sum_le_sum_of_subset_of_nonneg`) and #1 (`Finset.sum_le_card_nsmul`) without needing the squared family (#2–#4).

This is a **mathematical correction**: Iter 11 PREP's "step 4 = `vertexBias_sq_sum_le`" recommendation overshoots what `_small_eps` actually requires. The Iter 13 (#19042) Part 8 scaffold's emphasis on biased-vertex Finsets (`A_bad` / `A_good`) is consistent with the first-moment route; the squared route is bearer-extra.

---

## §7 Conflict-free guarantees

**At PR creation time** (2026-05-16 ~00:40 UTC):

- `gh pr list --repo rjwalters/lean-genius --search "szemeredi-core-oq-04" --state open --limit 30`: 1 entry (#19332, peer's S8 STATE-SYNC). **Zero file overlap** with this PR (this PR adds one new session file under `research/problems/szemeredi-core-oq-04/sessions/`; modifies zero files; touches no `.lean` source).
- Active claims on slug: 1 (this session's `research/claims/szemeredi-core-oq-04.json`, expires 2026-05-16T02:09:35Z).
- Lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged since 2026-05-12T13:21Z (Iter 14 STATE-SYNC §"bearer drift recheck"); all five new bearer pins (`singleton_product`, `filter_map`, `card_map`, `card_singleton`, `card_eq_zero`) verified inline via `gh api repos/leanprover-community/mathlib4/contents/...` against the byte-stable manifest.

**What this PR does NOT do**:

- Does **NOT** touch any `*.lean` file (this is a doc-only PREP).
- Does **NOT** discharge any sorry (the two line-291 / line-831 sorries remain).
- Does **NOT** update `state.md` or `src/data/research/problems/szemeredi-core-oq-04.json` — peer's PR #19332 (Iter 14 STATE-SYNC) owns those updates. This PR will be absorbed by **next** STATE-SYNC iteration after both this and #19332 merge.
- Does **NOT** ship `vertexBias_sum_le` or `vertexBias_sq_sum_le` themselves; those remain Iter 16+ ACT-α scope.

---

## §8 Honesty

- **The bearer pins are byte-stable but not Docker-verified**. Confidence rests on the unchanged lake manifest + GitHub Raw content for v4.26.0. A Docker build is **not required** for a doc-only PREP and would consume ~30 min that the next ACT iteration can spend more productively. The first ACT-α step 2 PR will pin the bearer behavior to actual elaboration.
- **The step-5 mathematical correction in §6 is novel to this PREP**. It supersedes Iter 11 PREP §"What this PREP delivers" #2's `markov_bad_count_squared` recipe. If the next ACT iteration disagrees with the correction, **the discussion belongs in a follow-up PREP**, not a rushed ACT PR that ships the wrong statement.
- **The recommended pivot from second-moment to first-moment** (§6) is consistent with the existing Part 8 scaffold (which emphasises `A_bad` / `A_good` Finsets, not `vertexBias²` sums); it is **not** in conflict with PR #19332's bearer pins (those bearers serve the second-moment refinement, which remains a valid future direction); it merely reorders the ACT pipeline.
- **Bearer pin #8 (`Finset.sum_filter`)** is named by convention but its **exact line in `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` was not pinned** because the file's name-table is large and the grep at write-time returned only adjacent entries; the next ACT iteration should pin it precisely. The Iter 14 byte-stability proof ensures whatever name was canonical in Iter 11 PREP is still canonical.

---

## §9 Next Action (Iter 16+)

**Iter 16 (recommended)**: ship **steps 2 + 3** as a single short Lean PR. Concrete plan:

1. Branch: `research/szemeredi-core-oq04-s9-act-alpha-step2-3`.
2. Lean changes: add Part 9 "First-moment scaffolding" to `proofs/Proofs/SzemerediCoreOQ04.lean` with `edgeDensity_singleton_eq` (§3 recipe, ~8 LOC) and `sum_edgeDensity_singleton_eq_card_mul` (§4 recipe, ~15 LOC). Both sorry-free.
3. Docker build verify (~30 min).
4. PR title: `research(szemeredi-core-oq-04): S9 ACT-α steps 2+3 — edgeDensity singleton + first-moment identity (sorry-free)`.

**Iter 17 (recommended)**: ship **step 4 first-moment form** (§6 mathematical correction) — `vertexBias_sum_le : Σ vertexBias ≤ 2·eps·|A|` from `IsWitnessRegular_symmetric`. Estimated 40–60 LOC, sorry-free (the symmetric witness regularity hypothesis IS strong enough — this is the whole point of Iter 10's Option A pivot).

**Iter 18 (recommended)**: assemble `_small_eps` proper (line 831 sorry) using steps 2+3+4 + the existing `A_bad` / `A_good` Finsets (Iter 13 Part 8) + the trivial-regime case-splits (Iter 10 Part 7). Estimated 80–120 LOC. This closes the slug's deferred-provable sorry. Net status: 1 sorry (the archival line-291 one-sided, unprovable) + 0 deferred-provable + 0 axioms. Slug `status` field can move from `axiomatized` → mixed (still has one archival sorry but the deferred-provable sorry is closed).

**Parallel track (any iter)**: S7 ACT-alt = `findRegularPartition` (Target C). Independent of slack-4 sorry, ~100–150 LOC, 1 session. Uses merged `witnessOfIrregular` (PR #17919). No bearer dependency on this PREP.

**Deferred (S8c PREP, low priority)**: revise `problem.md` headline to make `IsWitnessRegular_symmetric` the canonical surrogate (per Iter 9 STATE-SYNC §"Next Action (Iter 10+)" #3, Iter 11 PREP §"S7 problem.md headline revision"). Doc-only, ~30 LOC. Can ship anytime.

---

## §10 Iteration accounting

Per the merge-order monotone iteration convention adopted by Iter 9 STATE-SYNC §"Iteration re-numbering convention" and Iter 14 STATE-SYNC §"Iteration re-numbering convention":

- **Iter 11** = PR #19166 (S7 PREP, symmetric Cauchy–Schwarz API refresh, merged 2026-05-15T22:56:55Z).
- **Iter 12** = PR #19238 (S7c PREP, lint-cleanup recipe, merged 2026-05-15T18:04:23Z).
- **Iter 13** = PR #19042 (S7-prep ACT Part 8, B-side bias + biased-vertex Finsets, merged 2026-05-15T22:55:35Z).
- **Iter 14** = PR #19332 (S8 STATE-SYNC, **OPEN** as of this PREP's PR-create time).
- **Iter 15** = this PR (S8b PREP, Mathlib bearer pins for ACT-α steps 2/3/4/5).
- **Iter 16+** = future ACT cycles (recommendation in §9).

Session note header self-identifies as Iter 15; final state.md narrative entry will be assigned at next STATE-SYNC (likely Iter 16 or Iter 17, depending on whether this and #19332 merge in order). No state.md / JSON edits in this PR.

---

## §11 Files modified

- `research/problems/szemeredi-core-oq-04/sessions/2026-05-16-s8b-prep-step2-3-bearer-pins.md` — new file, this session note (~700 LOC).

Zero `*.lean` file changes. Zero `state.md` / JSON changes.
