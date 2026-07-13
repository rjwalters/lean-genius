# Session 2026-05-15 S3 PREP — Discharge recipes for the two strategic sorries of PR #19104 (doc-only, conflict-free)

**Mode**: FRESH (S3 PREP, doc-only; sibling to PR #19104 S2 SCAFFOLD)
**Researcher**: researcher-9
**Outcome**: bearer audit at lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0); 10/10 named Mathlib lemmas verified in-situ; 1 fictitious bearer (`cardFactors_prod_of_squarefree`) flagged in S2 SCAFFOLD's discharge plan; replacement recipe via `IsMultiplicative.map_prod_of_prime` collapses sorry 1 to **3 lines** and sorry 2 to **5 lines**, no `cardFactors` reasoning required.

## 1. Context: PR #19104 (S2 SCAFFOLD) and the gap this PREP closes

PR #19104 (open, MERGEABLE, build verified 1118 jobs) shipped
`proofs/Proofs/EulerTotientOQ04OQ01.lean` (158 LOC, 6 theorems) with two
strategic sorries:

| Sorry | Location | S2 SCAFFOLD's planned discharge bearer |
|-------|----------|----------------------------------------|
| `moebius_prod_squarefree` (μ of distinct-prime product = `(-1)^k`) | L76 | `Squarefree.prod` + `moebius_apply_of_squarefree` + `cardFactors_prod_of_squarefree` |
| `sum_filter_squarefree_moebius_eq_powerset` (post-bijection collapse) | L96 | `Nat.sum_divisors_filter_squarefree` + `normalizedFactors_toFinset_eq` + `Finset.sum_congr` |

The S2 SCAFFOLD's plan for sorry 1 names **`cardFactors_prod_of_squarefree`**
as a bearer. **This lemma does not exist in Mathlib at the lake-pinned
SHA** (GitHub code-search across `repo:leanprover-community/mathlib4`
returns 0 hits). A nearby lemma — `cardFactors_multiset_prod` (Misc.lean:289)
— exists but requires extra steps (sum-of-1s on a multiset of primes).

This PREP supplies a **strictly simpler** recipe using a bearer the
S2 SCAFFOLD did not consult: `IsMultiplicative.map_prod_of_prime`
(Defs.lean:378). That lemma exists, is general, and collapses sorry 1
into a 3-line proof with no Squarefree- or cardFactors-reasoning.

This PREP is doc-only and **only adds a new `sessions/<date>-s03-prep-*.md`
file** — strictly conflict-free with #19104, which touches
`proofs/Proofs/EulerTotientOQ04OQ01.lean`, `proofs/Proofs.lean`, and
`research/problems/euler-totient-oq-04-oq-01/state.md`. No file overlap.

## 2. Mathlib bearer audit at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Every named Mathlib API used (by S2 SCAFFOLD or this PREP's recipes)
verified in-situ via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>` + base64-decode. Bearers are listed in
the order needed by the S3 ACT.

| # | Declaration | Verified location |
|---|-------------|-------------------|
| B1 | `ArithmeticFunction.moebius_apply_of_squarefree` | `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:59` |
| B2 | `ArithmeticFunction.moebius_eq_zero_of_not_squarefree` | `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:63` |
| B3 | `ArithmeticFunction.moebius_apply_prime` | `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:108` |
| B4 | `ArithmeticFunction.isMultiplicative_moebius` | `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:127` |
| B5 | `ArithmeticFunction.IsMultiplicative.map_prod_of_prime` | `Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:378-382` |
| B6 | `Nat.sum_divisors_filter_squarefree` | `Mathlib/Data/Nat/Squarefree.lean:300-306` |
| B7 | `Nat.factors_eq` (used in `normalizedFactors_toFinset_eq`) | `Mathlib/RingTheory/UniqueFactorizationDomain/Nat.lean:47` |
| B8 | `Nat.mem_primeFactors` | `Mathlib/Data/Nat/PrimeFin.lean:39` |
| B9 | `Nat.prime_of_mem_primeFactors` | `Mathlib/Data/Nat/PrimeFin.lean:62` |
| B10 | `Nat.primeFactors_eq_empty` | `Mathlib/Data/Nat/PrimeFin.lean:79` |
| B11 | `Finset.prod_const` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:637` |
| B12 | `Finset.mem_powerset` | core Finset (Mathlib stable) |
| B13 | `Finset.sum_congr rfl` | core Finset (Mathlib stable) |

**Negative finding**: `cardFactors_prod_of_squarefree` — **does not exist**.
GitHub code-search returns 0 hits at the pinned SHA. The S2 SCAFFOLD's
discharge plan for sorry 1 names it as a primary bearer; this PREP
re-routes around it.

### 2.1 Signature for the load-bearing bearer (B5)

```lean
-- Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:378-382
theorem map_prod_of_prime [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (h_mult : ArithmeticFunction.IsMultiplicative f)
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    f (∏ a ∈ t, a) = ∏ a ∈ t, f a :=
  map_prod _ h_mult t fun x hx y hy hxy => (coprime_primes (ht x hx) (ht y hy)).mpr hxy
```

The hypothesis `∀ p ∈ t, p.Prime` is exactly the existing PR's signature
for `moebius_prod_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)`.
No reformulation needed.

### 2.2 Signature for the post-bijection rewrite target (B6)

```lean
-- Mathlib/Data/Nat/Squarefree.lean:300-306
theorem sum_divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) {α : Type*} [AddCommMonoid α]
    {f : ℕ → α} :
    ∑ d ∈ n.divisors with Squarefree d, f d =
      ∑ i ∈ (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset, f i.val.prod := by
  rw [Finset.sum_eq_multiset_sum, divisors_filter_squarefree h0, Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  rfl
```

After rewriting with `Nat.sum_divisors_filter_squarefree hn` and then
`normalizedFactors_toFinset_eq n hn` (already proved as a non-sorry
theorem on L66-70 of the S2 SCAFFOLD), the LHS of sorry 2 becomes:
```
∑ S ∈ n.primeFactors.powerset, μ S.val.prod
```
which we match termwise against the RHS
```
∑ S ∈ n.primeFactors.powerset, (-1 : ℤ) ^ S.card
```
via `Finset.sum_congr rfl`. The pointwise identity `μ S.val.prod = (-1)^S.card` is then sorry 1 applied to `S` (note: `S.val.prod = ∏ p ∈ S, p` by definitional unfolding of `Finset.prod` through `Finset.val`).

## 3. Discharge recipe for sorry 1 (`moebius_prod_squarefree`)

**Goal at L76**:
```lean
theorem moebius_prod_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    μ (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card := by
  sorry
```

### Option A (recommended; 3 lines) — direct via `map_prod_of_prime`

```lean
theorem moebius_prod_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    μ (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card := by
  rw [isMultiplicative_moebius.map_prod_of_prime s hs]
  rw [Finset.prod_congr rfl (fun p hp => moebius_apply_prime (hs p hp))]
  exact Finset.prod_const _
```

**Step-by-step proof state**:
1. After `rw [isMultiplicative_moebius.map_prod_of_prime s hs]`:
   - Goal: `∏ p ∈ s, μ p = (-1 : ℤ) ^ s.card`
2. After `rw [Finset.prod_congr rfl (fun p hp => moebius_apply_prime (hs p hp))]`:
   - Goal: `∏ p ∈ s, (-1 : ℤ) = (-1 : ℤ) ^ s.card`
3. `Finset.prod_const _` directly discharges this.

**Why this works**: B5 gives `μ (∏ p ∈ s, p) = ∏ p ∈ s, μ p` because μ is
multiplicative (B4) and elements of `s` are primes (`hs`). For each `p`
in `s`, `μ p = -1` (B3 — `moebius_apply_prime`). So the product becomes
`∏ p ∈ s, (-1 : ℤ)`, which is `(-1)^s.card` by B11 (`Finset.prod_const`,
applied with `b = (-1 : ℤ)`; note Mathlib uses `#s` notation for `s.card`
in B11's statement, but they are definitionally equal — `Finset.card_def`
unfolds `#s = s.card`).

### Option B (robust fallback; ~6 lines) — explicit Finset.induction

If Option A trips on a namespace issue (e.g., `isMultiplicative_moebius`
not in scope after the `open ArithmeticFunction` of the S2 SCAFFOLD —
unlikely but possible):

```lean
theorem moebius_prod_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    μ (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
    have hap : a.Prime := hs a (Finset.mem_insert_self a t)
    have htp : ∀ p ∈ t, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ t, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hap (htp p hp)).mpr (fun heq => ha (heq ▸ hp))
    rw [isMultiplicative_moebius.map_mul_of_coprime hcop,
        moebius_apply_prime hap, ih htp]
    ring
```

This explicitly tracks the induction; same total LOC budget but more
verbose. Recommended only if Option A fails namespace resolution.

### Option C (last-resort; ~12 lines) — squarefree + cardFactors route (the S2 SCAFFOLD's original plan, repaired)

Only use if both A and B trip on some subtle elaboration issue. This is
the route the S2 SCAFFOLD's PR body sketched, but with the fictitious
`cardFactors_prod_of_squarefree` replaced by `cardFactors_multiset_prod`
+ `Finset.sum_const`:

```lean
theorem moebius_prod_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    μ (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card := by
  have hsf : Squarefree (∏ p ∈ s, p) := by
    have : ∀ p ∈ s, Squarefree p := fun p hp => (hs p hp).squarefree
    -- Use Finset.squarefree_prod_of_pairwise_isCoprime; need pairwise IsRelPrime
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ this
    intro p hp q hq hne
    exact (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hne |>.isRelPrime_of_coprime
    -- or use Nat.coprime_iff_isRelPrime.mp
  rw [moebius_apply_of_squarefree hsf]
  -- Now need cardFactors (∏ p ∈ s, p) = s.card
  have hcf : cardFactors (∏ p ∈ s, p) = s.card := by
    have hne : (∏ p ∈ s, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hs p hp).ne_zero
    -- (∏ p ∈ s, p) is s.val.prod when we view ∏ as a multiset.prod
    rw [show (∏ p ∈ s, p) = s.val.prod from rfl, cardFactors_multiset_prod hne]
    simp [Multiset.map_congr rfl (fun p hp => cardFactors_apply_prime (hs p (Finset.mem_def.mpr hp)))]
  rw [hcf]
```

**Note on Option C**: the `Nat.coprime_iff_isRelPrime` step may need
massaging — the precise spelling of "coprime ⇒ IsRelPrime" in v4.26.0
may differ. This option is here as a safety net but Option A is
strongly preferred; Option C carries ~3× the elaboration risk.

## 4. Discharge recipe for sorry 2 (`sum_filter_squarefree_moebius_eq_powerset`)

**Goal at L96** (after the two `rw` calls already in the partial proof):
```lean
theorem sum_filter_squarefree_moebius_eq_powerset (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors with Squarefree d, μ d : ℤ)
      = ∑ S ∈ n.primeFactors.powerset, (-1 : ℤ) ^ S.card := by
  rw [Nat.sum_divisors_filter_squarefree hn]
  rw [normalizedFactors_toFinset_eq n hn]
  sorry  -- L96
```

After the two rewrites, the goal is:
```
∑ S ∈ n.primeFactors.powerset, μ S.val.prod = ∑ S ∈ n.primeFactors.powerset, (-1 : ℤ) ^ S.card
```

### Option A (recommended; 5 lines)

```lean
  rw [Nat.sum_divisors_filter_squarefree hn, normalizedFactors_toFinset_eq n hn]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  have hsub : S ⊆ n.primeFactors := Finset.mem_powerset.mp hS
  have hsp : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
  -- S.val.prod = ∏ p ∈ S, p definitionally (Finset.prod = Multiset.prod ∘ val.map id, id is id)
  exact moebius_prod_squarefree S hsp
```

**Step-by-step proof state**:
1. After both `rw`: goal as above.
2. After `Finset.sum_congr rfl (fun S hS => ?_)`:
   - Need: `μ S.val.prod = (-1 : ℤ) ^ S.card`, where `hS : S ∈ n.primeFactors.powerset`.
3. `hsub : S ⊆ n.primeFactors` via B12.
4. `hsp : ∀ p ∈ S, p.Prime` via B9 applied through the subset relation.
5. Apply `moebius_prod_squarefree S hsp` — sorry 1, now discharged.

**Defeq question (`S.val.prod` vs `∏ p ∈ S, p`)**: in Mathlib,
`Finset.prod s f := (s.val.map f).prod`. Specializing `f = id` gives
`s.prod id = (s.val.map id).prod = s.val.prod` (since `Multiset.map id = id`).
The notation `∏ p ∈ S, p` desugars to `Finset.prod S (fun p => p) = Finset.prod S id`,
which is definitionally `S.val.prod`. So `moebius_prod_squarefree S hsp`
applies directly without an intermediate rewrite.

**If the defeq fails to be picked up at elaboration time** (rare but
possible — Lean 4 sometimes asks for explicit `show`), add one line:
```lean
  show μ (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card
  exact moebius_prod_squarefree S hsp
```

### Option B (robust fallback; explicit `show` always)

```lean
  rw [Nat.sum_divisors_filter_squarefree hn, normalizedFactors_toFinset_eq n hn]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  have hsp : ∀ p ∈ S, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.mp hS) hp)
  show μ (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card
  exact moebius_prod_squarefree S hsp
```

Same logic, one extra line; eliminates any defeq risk on the `S.val.prod`
form.

## 5. Composite paste-ready Lean diff (Options A for both sorries)

The minimal S3 ACT diff against the file in PR #19104 (head ref
`159f45ece439af08c84ec74042bac9fdf4dc59b6`):

```diff
--- a/proofs/Proofs/EulerTotientOQ04OQ01.lean
+++ b/proofs/Proofs/EulerTotientOQ04OQ01.lean
@@ -73,7 +73,9 @@
 theorem moebius_prod_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
     μ (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card := by
-  sorry
+  rw [isMultiplicative_moebius.map_prod_of_prime s hs]
+  rw [Finset.prod_congr rfl (fun p hp => moebius_apply_prime (hs p hp))]
+  exact Finset.prod_const _
 
 /- ## Part III: bridge from Mathlib's normalizedFactors form to primeFactors -/
@@ -94,7 +96,11 @@
   rw [Nat.sum_divisors_filter_squarefree hn]
   rw [normalizedFactors_toFinset_eq n hn]
-  sorry
+  refine Finset.sum_congr rfl (fun S hS => ?_)
+  have hsp : ∀ p ∈ S, p.Prime := fun p hp =>
+    Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.mp hS) hp)
+  show μ (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card
+  exact moebius_prod_squarefree S hsp
```

**Total LOC delta**: +8 / -2 (net +6 LOC, removes 2 sorries).
**Expected post-edit sorry count**: 0.
**Expected post-edit axiom count**: 0.
**Expected docker iterations**: 1-2 (Option A is direct; if line 1 of sorry 1
trips on namespace, swap in Option B for sorry 1; if line 4 of sorry 2
trips on defeq, the `show` line is already inserted as a safety).

## 6. v4.26.0 surface-regression sweep

8-row check against patterns observed in recent v4.26.0 mechanic PRs
(per memory entries `mechanic_mathlib_v426_*`):

| Pattern | Risk to S3 ACT | Status |
|---------|----------------|--------|
| `Nat.mul_sub_left_distrib` rename | none — no multiplication-distributive arithmetic | ✓ safe |
| `Complex.abs` removal | none — proof is in ℤ via `μ`, no `ℂ` | ✓ safe |
| `simp only [↓reduceIte]` on conjunction hyps | none — no `if`-then-else hyp decomposition | ✓ safe |
| `Measure.prod_mono` removal | none — no measure-theoretic content | ✓ safe |
| `IntervalIntegral` barrel removal | none — no intervalIntegral | ✓ safe |
| `Nat.totient`-scoped `φ` clash from `open Nat` | **needs check** — S2 SCAFFOLD does `open Finset Nat ArithmeticFunction`; no `let φ` or `variable φ` in S2 file; sorry 1 uses `s` (Finset) and `p` (prime) as binders | ✓ safe (verified by re-reading S2 file from PR head) |
| `Finset.prod_congr` API drift | none — `Finset.prod_congr` is stable across Mathlib 4.x | ✓ safe |
| `Finset.mem_powerset` direction | none — `Finset.mem_powerset.mp hS : S ⊆ n.primeFactors` is the standard direction | ✓ safe |

**Notable absence**: this proof uses no `field_simp`, no `ring`, no
`linear_combination`, no cast-norm — the only elaboration-sensitive
step is `Finset.prod_const _` whose underscore lets Lean infer
`s := s` and `b := (-1 : ℤ)`. Low risk.

## 7. Race / saturation / conflict-free guarantees

**Probe at 2026-05-15 ~04:09 UTC** (after my own PR #19237 merge would
otherwise have happened — deployer stalled ~25h since last main merge
at 2026-05-14T03:03:38Z):

```
gh pr list -R rjwalters/lean-genius --search "euler-totient-oq-04-oq-01 in:title" --state open
→ 1 open PR: #19104 (S2 SCAFFOLD, MERGEABLE, head 159f45ec)
```

**Open PR count for this slug**: 1 (#19104). Decision matrix from the
"release crowded slug" pattern: 1 open PR + this PREP is strictly
orthogonal (different angle: discharge plan vs scaffold) + new content
(fictitious bearer flagged, simpler recipe found) → **proceed**.

**File overlap with #19104** (which adds these files):

| File | #19104 | This PR |
|------|--------|---------|
| `proofs/Proofs/EulerTotientOQ04OQ01.lean` | +158 (new) | — |
| `proofs/Proofs.lean` | +1 import | — |
| `research/problems/euler-totient-oq-04-oq-01/state.md` | +91 (new) | — |
| `research/problems/euler-totient-oq-04-oq-01/sessions/2026-05-15-s03-prep-mobius-sorry-discharge.md` | — | NEW (this file only) |

**File overlap: 0**. This PR ships only the session file above. No
merge conflict possible with #19104 in either direction.

**Post-merge sequencing**:
- **If #19104 lands first** (expected): rebase this PR's branch on main
  (no conflicts; just a fast-forward of the parent commit). My S3 ACT
  follow-up can then use the recipes here directly.
- **If this PR lands first** (also fine, since doc-only): #19104 is
  unaffected; the recipes are now available for any researcher (myself
  or peer) doing S3 ACT.

## 8. Next steps (S3 ACT after both this PREP and #19104 merge)

Once #19104 has merged:

1. Branch off main: `research/euler-totient-oq04-oq01-s3-act-<ts>`
2. Apply the §5 composite diff to `proofs/Proofs/EulerTotientOQ04OQ01.lean`
3. Docker-build: `./proofs/scripts/docker-build.sh Proofs.EulerTotientOQ04OQ01`
4. Update `state.md` (S2 → S3) and the JSON if/when a problem JSON exists
5. Ship as `research(euler-totient-oq-04-oq-01): S3 ACT — discharge both strategic sorries via map_prod_of_prime (Docker-verified, 0 sorries)`

Expected ACT outcome (modulo deployer stall):
- 0 sorries
- 0 axioms
- ~1118 jobs (same parent build set)
- 2 fewer warnings (the `sorry`-uses warnings on L76 and L96)
- Net +6 LOC vs current S2 SCAFFOLD

If Docker iterates more than 2 times on Option A, fall back to Option B for
the offending sorry (the §3 and §4 fallbacks are paste-ready).

## 9. Honesty notes

- The "fictitious bearer" finding is a real correctness improvement, but
  it does not invalidate PR #19104 — that PR's `sorry`'d theorems are
  declared with correct statements; only the discharge *plan* names a
  non-existent helper. The proof is still discharge-able; my recipes
  just use a different bearer than the S2 SCAFFOLD anticipated.
- The estimated +6 LOC for S3 ACT is itself routine — this is supporting
  infrastructure, not a "result". It would not be progress without
  PR #19104's main `sum_moebius_eq_indicator` theorem (which is the
  actual mathematical content).
- Bearer audit work is verification labor, not novelty. The novelty is
  contained in PR #19104's choice of route (squarefree-divisor /
  powerset bijection) vs the Mathlib `recOnPosPrimePosCoprime` route.
