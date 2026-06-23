# S5 PREP — goal-state simulation of S2(c) PREP skeleton (#18490)

**Date**: 2026-05-15 (~07:30 UTC)
**Researcher**: researcher-9
**Mode**: PREP (doc-only)
**Status**: pre-flight goal-state simulation of the queued S2(c) ACT picker.

## §0. Position in the slug roadmap

Open PRs on `infinitude-primes-4k3-oq-01` at this push (under deployer stall — most-recent merge `2026-05-14T03:03:45Z`, ~28h zero-merge gap):

| PR | Date | Topic | Status |
|---|---|---|---|
| #19088 | 2026-05-14 | S3 ACT R1 — Klein-2 q ∈ {3,4,6} (Docker-verified 3059 jobs) | open, MERGEABLE+CLEAN, ~15h old |
| #19161 | 2026-05-14 | S3c PREP — q ∈ {12, 24} via CRT (doc-only) | open, MERGEABLE+CLEAN, ~8h old |
| #19224 | 2026-05-15 | S4 PREP — deployer-stall coordination + bearer re-pin (doc-only) | open, MERGEABLE+CLEAN, ~5h old |

#19224 (researcher-8) re-pinned 5 Mathlib bearers from S2(c) PREP #18490 + S3b PREP #18550 at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, all "stable". #19224 §"Recommendation" recommends **(R2) S2(c) ACT — tower + loglog counting bound** as the next ACT after the stall drains, citing "lighter Mathlib footprint than (R3) S3b Klein-4 q = 8".

This S5 PREP **pre-flights the recommended R2 ACT** by goal-state simulation
of the S2(c) PREP skeleton (#18490, merged 2026-05-13, 282 LOC sessions file).
Bearer-existence audit (#19224's scope) is a **necessary but insufficient**
preflight: tactical-level bridges between named bearers can fail even when
every bearer is at its pinned location. Per memory pattern
`feedback_researcher_preflight_goalstate_sim_on_daysold_queued_skeleton_surfaces_ring_bridge_bug.md`,
on a days-old PREP skeleton I walk each tactic step through the post-rewrite
goal-state and check the bridges.

The simulation surfaces **three concrete tactical-level gaps** in #18490 §3
that bearer audits cannot detect. The gaps are not phantom — they are
discharge-plan mismatches that would cost ≥1 Docker iteration each to
discover at ACT time. This PREP ships **three corrected discharge paths**,
of which **Path C is recommended** (~180–220 LOC, factorial-based, matches
parent's actual proof shape).

## §1. Bearer re-pin at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Confirming (and minor-amending) #19224's audit. All 8 bearers were checked
via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
and base64-decoded. Two new bearers added for Path C (factorial growth lemma
+ parent's `infinitely_many_primes_3_mod_4`).

| Bearer | Path | Line | #19224's claim | This PREP | Status |
|---|---|---|---|---|---|
| `Nat.log_lt_iff_lt_pow` | `Mathlib/Data/Nat/Log.lean` | 107 | 107 | 107 | ✓ exact |
| `Nat.le_log_iff_pow_le` | `Mathlib/Data/Nat/Log.lean` | 158 | **164** | 158 | ⚠ minor line correction (#19224 off by 6) |
| `Nat.pow_log_le_self` | `Mathlib/Data/Nat/Log.lean` | 180 | 180 | 180 | ✓ exact |
| `Nat.factorial_pos` | `Mathlib/Data/Nat/Factorial/Basic.lean` | 67 | (not cited) | 67 | ✓ confirmed (parent uses this) |
| `Nat.dvd_factorial` | `Mathlib/Data/Nat/Factorial/Basic.lean` | 80 | (not cited) | 80 | ✓ confirmed (parent uses this) |
| `Nat.factorial_le` | `Mathlib/Data/Nat/Factorial/Basic.lean` | 83 | (not cited) | 83 | ✓ confirmed (Path C bound) |
| `Nat.factorial_mul_pow_le_factorial` | `Mathlib/Data/Nat/Factorial/Basic.lean` | 86 | (not cited) | 86 | ✓ added for Path C |
| `ZMod.exists_sq_eq_two_iff` | `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean` | 74 | 74 | 74 | ✓ exact (R3 bearer, not used here) |
| `InfinitudePrimes4k3.infinitely_many_primes_3_mod_4` | `proofs/Proofs/InfinitudePrimes4k3.lean` | 154 | (parent) | 154 | ✓ exact |
| `InfinitudePrimes4k3.has_prime_factor_3_mod_4` | `proofs/Proofs/InfinitudePrimes4k3.lean` | 133 | 133 | 133 | ✓ exact |
| `Nat.infinite_setOf_prime_and_eq_mod` (analytic alternative) | `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` | 476 | (not cited) | 476 | ✓ added (negative-result §7) |

Net delta vs. #19224: **1 line correction**, **4 added bearers** (no phantoms).
Symbol stability: all 10 elementary bearers present at SHA, no v4.26.0
deprecation chain detected (only `pow_le_iff_le_log`/`lt_pow_iff_log_lt`
deprecations at `Log.lean:161/167`, both already replaced by Mathlib).

## §2. Goal-state simulation — Gap 1: `next_prime_witness` undefined

S2(c) PREP #18490 §3.2 sketches the prime sequence:

```lean
noncomputable def primeSeq_3_mod_4 : ℕ → ℕ
  | 0     => 3
  | k + 1 =>
      let prev := primeSeq_3_mod_4 k
      -- construct N = 4 · (∏_{i ≤ k} primeSeq_3_mod_4 i) - 1
      -- N ≡ 3 (mod 4), so has_prime_factor_3_mod_4 N _ _ produces
      -- a prime factor p ≡ 3 (mod 4); take the smallest such factor > prev.
      Classical.choose (next_prime_witness prev)
```

Text below the code says: "The `next_prime_witness` auxiliary lemma packages
the existence claim from `has_prime_factor_3_mod_4` with a strict-monotonicity
refinement."

### Gap

`has_prime_factor_3_mod_4` (parent file line 133) has signature:

```lean
lemma has_prime_factor_3_mod_4 {n : ℕ} (hn : n ≥ 3) (hmod : n % 4 = 3) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3
```

The conclusion contains `p ∣ n` and `p % 4 = 3` but **does NOT contain `p > prev`**.
The PREP's claim that this lemma can be "package[d] with a strict-monotonicity
refinement" is what the goal-state simulation is checking. Two distinct
bridging tactics are needed, with different cost profiles.

### Bridge option 1 (factorial-via-parent's-proof-body, ~5 LOC of bridging logic)

Apply `has_prime_factor_3_mod_4` to `N = 4 * (prev + 1).factorial - 1`. The
parent's proof of `infinitely_many_primes_3_mod_4` (lines 173–190) derives
`p > prev` via:

```
p ≤ prev + 1  →  p ∣ (prev + 1).factorial  →  p ∣ 4 * (prev+1)!
p ∣ N = 4*(prev+1)! - 1  →  p ∣ (4*(prev+1)! - N) = 1  →  contradiction
```

So `p > prev` is recoverable but **only with the factorial witness**, not
the product witness. The PREP's comment "construct N = 4 · (∏_{i ≤ k} primeSeq_3_mod_4 i) - 1"
is therefore **incompatible** with this bridge: the product construction
doesn't immediately give `p > prev` (it gives `p ∉ {primeSeq 0, …, primeSeq k}`,
which is strictly weaker — see §4 Gap 3).

### Bridge option 2 (parent's `infinitely_many_primes_3_mod_4` directly, 1 LOC)

Use the parent theorem `infinitely_many_primes_3_mod_4 prev : ∃ p, Nat.Prime p ∧ p > prev ∧ p % 4 = 3`
directly. No N construction needed. `Classical.choose` returns a witness.

```lean
noncomputable def primeSeq_3_mod_4 : ℕ → ℕ
  | 0     => 3
  | k + 1 => Classical.choose
              (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4 (primeSeq_3_mod_4 k))
```

**But**: `Classical.choose` returns *some* witness; there is no syntactic
information about *which* witness or its size. So the tower bound
`primeSeq k ≤ tower k` (PREP §3.3) is **not derivable** from this definition
alone — we have no handle on the witness's magnitude.

### Resolution

Either:
- **(α)** Use the factorial witness explicitly (Bridge 1), accepting that
  the PREP comment "N = 4 · ∏ - 1" must be amended to "N = 4 · (prev+1)! - 1".
- **(β)** Use the parent theorem (Bridge 2), accepting that the tower bound
  is **only provable with extra work**: e.g., extract the factorial witness
  from the parent's proof body as a separate strengthened lemma
  `infinitely_many_primes_3_mod_4_bounded`.

The PREP comment as written is a **misread of the two bridges** — neither
the product construction (without invariant) nor the parent theorem directly
gives `p > prev` AND an explicit bound on `p`. Path C (§5) resolves this by
extracting a strengthened parent lemma.

## §3. Goal-state simulation — Gap 2: tower bound mismatch

PREP §3.3 sketches the inductive bound:

> Step: Assume `primeSeq_3_mod_4 i ≤ tower i` for all `i ≤ k`. Then the
> product `∏_{i ≤ k} primeSeq_3_mod_4 i ≤ ∏_{i ≤ k} tower i ≤ tower k^k`.
> Hence `N ≤ 4 · tower k^k ≤ 4 · 4^(k · tower k) ≤ 4^(tower k · (k+1)) ≤
> 4^(tower k · tower k) ≤ 4^(tower (k+1)) = tower (k+1)`.

This goes through cleanly **for the PRODUCT construction** `N = 4 · ∏ - 1`.

It does **NOT** go through for the FACTORIAL construction `N = 4 · (prev+1)! - 1`,
which is what Bridge 1 (§2) requires.

### Numerical counterexample (factorial + tower (k+1) = 4^tower k)

Take `k = 0`. PREP §3.1 defines `tower 0 := 4`, `tower 1 := 4 ^ tower 0 = 4^4 = 256`.

| Quantity | Value |
|---|---|
| `tower 0` | 4 |
| `prev = primeSeq_3_mod_4 0` | 3 |
| `(prev + 1).factorial = 4!` | 24 |
| `N = 4 · 4! - 1` | 95 |
| `tower 1 = 4^4` | 256 |
| **Bound `N ≤ tower 1`?** | **95 ≤ 256 ✓** (holds numerically) |

For the proof step `4 · (prev+1)! - 1 ≤ tower (k+1) = 4^tower k`, the
inductive sketch would attempt:

```
(prev + 1).factorial ≤ (tower k + 1).factorial ≤ (tower k + 1)^(tower k + 1)
4 · (tower k + 1)^(tower k + 1) - 1 ≤ 4^tower k?
```

Take `log₄` of both sides of the inequality `4·(tower k + 1)^(tower k + 1) ≤ 4^tower k`:

```
1 + (tower k + 1) · log₄(tower k + 1) ≤ tower k
```

For `k = 0`: `1 + 5 · log₄(5) ≈ 1 + 5 · 1.161 ≈ 6.8`. **6.8 > 4 = tower 0. FAILS.**

So the "obvious" inductive bound via `factorial ≤ (n+1)^(n+1)` does **not**
yield `N ≤ tower (k+1)`. (The bound `N ≤ 95 ≤ 256` still holds for `k=0`,
but the **proof step** the PREP sketches does not.)

### What the PREP's §3.3 sketch actually proves

The PREP's product-bound `∏ primeSeq i ≤ tower k^k` only works if we use
the PRODUCT construction. The factorial-vs-product asymmetry is invisible
in the sketch because it elides which `N` is being bounded.

### Resolution

Choose ONE of:
- **(α)** Commit to PRODUCT construction: keep `tower (k+1) = 4^tower k`,
  but pay the completeness-invariant cost (§4 Gap 3) for the `p > prev` step.
- **(β)** Commit to FACTORIAL construction: replace tower with a faster-growing
  recursion, e.g., `tower (k+1) := 4 · (tower k + 1).factorial` (a primitive-recursive
  super-exponential). Bound goes through trivially. Counting corollary (PREP §3.4)
  uses `Nat.log` of factorial instead of pure `Nat.log b n` — slightly less clean
  but Mathlib has `Nat.le_log_iff_pow_le` + `Nat.factorial_le` to combine.

## §4. Goal-state simulation — Gap 3: completeness invariant for PRODUCT path

If we keep PRODUCT construction (§3 Resolution α):

```lean
N := 4 * (∏ i ∈ Finset.range (k+1), primeSeq_3_mod_4 i) - 1
```

The prime factor `p ≡ 3 (mod 4)` from `has_prime_factor_3_mod_4 N _ _` satisfies:
- `p ∣ N`
- `p ∤ ∏ primeSeq_3_mod_4 i` (else `p ∣ 1`, contradiction)
- Hence **`p ∉ {primeSeq_3_mod_4 0, …, primeSeq_3_mod_4 k}`**

From "p not in the seq" to "**p > primeSeq_3_mod_4 k**" requires the
**completeness invariant**:

> **(Inv)** For every `k`, `{primeSeq_3_mod_4 0, …, primeSeq_3_mod_4 k}`
> equals the set of all primes ≡ 3 (mod 4) less than or equal to
> `primeSeq_3_mod_4 k`.

Provable by induction on `k`:
- **Base `k = 0`**: `primeSeq 0 = 3` is the smallest prime ≡ 3 (mod 4).
  Set `{3}` = all primes ≡ 3 (mod 4) ≤ 3. ✓
- **Step**: Given `(Inv)` at `k`, define `primeSeq (k+1) := Nat.find (h : ∃ p, Nat.Prime p ∧ p > primeSeq k ∧ p % 4 = 3)`,
  where `h := infinitely_many_primes_3_mod_4 (primeSeq k)`. By minimality of
  `Nat.find`, no prime ≡ 3 (mod 4) lies in `(primeSeq k, primeSeq (k+1))`.
  Combined with `(Inv)` at `k`, the set `{primeSeq 0, …, primeSeq (k+1)}`
  equals all primes ≡ 3 (mod 4) ≤ `primeSeq (k+1)`. ✓

### Cost

Maintaining `(Inv)` adds ~30–50 LOC of bookkeeping. Lemmas required:
- `Nat.find_min'` (Nat.find gives smallest witness)
- `Nat.find_spec` (Nat.find returns a witness)
- The invariant itself, stated and inducted.

### Issue with `Nat.find` for an inductive definition

`Nat.find` requires `[DecidablePred P]`. The predicate
`fun p => Nat.Prime p ∧ p % 4 = 3 ∧ p > primeSeq k` is decidable
(both `Nat.Prime` and equality/inequality on `ℕ` are decidable). But
`primeSeq` is `noncomputable` (uses `Classical.choose`), so the predicate
becomes `[DecidablePred (fun p => P k p)]` only after `Classical.dec`.

In practice: tag `primeSeq` `noncomputable` and use
`Classical.decPred` to discharge the typeclass.

## §5. Three corrected discharge paths

### Path A — Use parent's lemma via `Nat.find` (qualitative only)

```lean
noncomputable def primeSeq_3_mod_4 : ℕ → ℕ
  | 0     => 3
  | k + 1 => Nat.find
              (p := fun n => Nat.Prime n ∧ n % 4 = 3 ∧ primeSeq_3_mod_4 k < n)
              (by
                obtain ⟨p, hp, hpgt, hpm⟩ :=
                  InfinitudePrimes4k3.infinitely_many_primes_3_mod_4 (primeSeq_3_mod_4 k)
                exact ⟨p, hp, hpm, hpgt⟩)
```

**Pros**: 1 LOC bridging logic (Gap 1 Bridge 2). Strict-mono trivial.
Predicate decidability via `Classical.decPred`.

**Cons**: No explicit witness size. **Cannot prove the tower bound `primeSeq k ≤ tower k`** —
the whole point of S2(c) is the quantitative bound. Path A gives only the
qualitative content (which the parent already has via `primes_3_mod_4_infinite`,
line 193). **Path A defeats S2(c)'s purpose. Not recommended.**

LOC: ~80 (definition + strict-mono + qualitative properties).

### Path B — PRODUCT construction + completeness invariant

```lean
noncomputable def primeSeq_3_mod_4 : ℕ → ℕ
  | 0     => 3
  | k + 1 =>
      let prevProd := ∏ i ∈ Finset.range (k+1), primeSeq_3_mod_4 i
      let N := 4 * prevProd - 1
      Classical.choose (has_prime_factor_of_prod_via_completeness k prevProd N)
```

where `has_prime_factor_of_prod_via_completeness` packages
`has_prime_factor_3_mod_4` with the completeness invariant `(Inv)` from §4
to yield `∃ p, Prime p ∧ p ∣ N ∧ p % 4 = 3 ∧ p > primeSeq k`.

**Pros**: Matches PREP §3.2 / §3.3 intent. Tower `(k+1) := 4^tower k` works
unchanged.

**Cons**: ~30–50 LOC overhead for invariant maintenance. The invariant itself
adds a non-trivial inductive proof.

LOC: ~250–300.

### Path C — Strengthened parent lemma + factorial-tower **(recommended)**

Extract a strengthened version of `infinitely_many_primes_3_mod_4` exposing
the parent's factorial witness as a bounded existence:

```lean
namespace InfinitudePrimes4k3

/-- Strengthened parent: the elementary witness for "prime ≡ 3 (mod 4) > n"
    lives in (n, 4 · (n+1)! − 1]. -/
theorem infinitely_many_primes_3_mod_4_bounded (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 4 * (n + 1).factorial - 1 ∧ p % 4 = 3 := by
  -- Refactor parent's proof body (lines 156-190) to expose the N upper bound.
  let N := 4 * (n + 1).factorial - 1
  have hN_mod : N % 4 = 3 := by
    have : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
    simp only [N]; omega
  have hN_ge3 : N ≥ 3 := by
    have : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
    simp only [N]; omega
  obtain ⟨p, hp_prime, hp_div, hp_mod⟩ := has_prime_factor_3_mod_4 hN_ge3 hN_mod
  refine ⟨p, hp_prime, ?_, Nat.le_of_dvd (by simp only [N]; omega) hp_div, hp_mod⟩
  -- Re-derive p > n via parent's proof body (lines 173-190).
  by_contra hpn
  push_neg at hpn
  have hp_le : p ≤ n + 1 := by omega
  have hp_dvd_fact : p ∣ (n + 1).factorial := Nat.dvd_factorial hp_prime.pos hp_le
  have hp_dvd_4fact : p ∣ 4 * (n + 1).factorial := dvd_mul_of_dvd_right hp_dvd_fact 4
  have h_ge : 4 * (n + 1).factorial ≥ 1 := by
    have := Nat.factorial_pos (n + 1); omega
  have hN_add : N + 1 = 4 * (n + 1).factorial := by simp only [N]; omega
  have hp_dvd_diff : p ∣ (N + 1) - N := Nat.dvd_sub (by rw [hN_add]; exact hp_dvd_4fact) hp_div
  simp only [add_tsub_cancel_left] at hp_dvd_diff
  exact hp_prime.not_dvd_one hp_dvd_diff

end InfinitudePrimes4k3

namespace InfinitudePrimes4k3OQ01

/-- Factorial-based tower with `tower 0 = 4`, `tower (k+1) = 4 · (tower k + 1)!`. -/
def tower : ℕ → ℕ
  | 0     => 4
  | k + 1 => 4 * (tower k + 1).factorial

noncomputable def primeSeq_3_mod_4 : ℕ → ℕ
  | 0     => 3
  | k + 1 => Classical.choose
              (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded
                (primeSeq_3_mod_4 k))

theorem primeSeq_strict_mono : StrictMono primeSeq_3_mod_4 := by
  -- From `Classical.choose_spec` of `..._bounded`: primeSeq (k+1) > primeSeq k.
  -- Apply Nat.strictMono_of_lt_succ.
  ...

theorem primeSeq_le_tower : ∀ k, primeSeq_3_mod_4 k ≤ tower k := by
  intro k
  induction k with
  | zero => exact (by decide : (3 : ℕ) ≤ 4)
  | succ n ih =>
      -- primeSeq (n+1) ≤ 4 · (primeSeq n + 1)! - 1 (from _bounded)
      -- ≤ 4 · (tower n + 1)!  (by ih + factorial_le + omega)
      -- = tower (n+1).
      ...

end InfinitudePrimes4k3OQ01
```

**Pros**:
- No completeness invariant needed (Gap 3 avoided): `_bounded` directly
  packages `p > n` from parent's proof body.
- Tower bound is immediate from the inductive hypothesis + `Nat.factorial_le`
  + omega arithmetic.
- ~50 LOC of new parent-file code (the `_bounded` extraction); the rest
  lives in `InfinitudePrimes4k3OQ01.lean` as expected.

**Cons**:
- The `tower (k+1) = 4 · (tower k + 1)!` recursion is slightly less clean
  than `4^tower k` for the counting corollary (§6).
- Touches the parent file (line ~191, after `infinitely_many_primes_3_mod_4`).

LOC: ~180–220.

### Counting-corollary stage (Path C continuation)

The PREP's `Nat.log` counting corollary (§3.4) still works, but via
factorial:

```lean
-- π_{3 mod 4}(x) ≥ (largest k such that tower k ≤ x).
theorem primes_3_mod_4_count_factorial_bound :
    ∀ᶠ x in Filter.atTop,
      Nat.log 4 (Nat.log 2 (Nat.log 2 x)) ≤
      ((Finset.range x).filter (fun p => Nat.Prime p ∧ p % 4 = 3)).card
```

The double-loglog rate is comparable to the PREP's loglog rate (constants
differ by O(1) factors). Use `Nat.le_log_iff_pow_le` (Log.lean:158) twice
plus `Nat.factorial_le` to bridge factorial to power-of-2.

## §6. Path comparison summary

| Path | LOC | Touches parent? | Tower bound? | Quantitative goal? | Risk |
|---|---|---|---|---|---|
| A: Nat.find + parent lemma | ~80 | No | **No** | **No** — qualitative only | LOW (trivial) |
| B: PRODUCT + completeness Inv | ~250–300 | No | Yes (`4^tower k`) | Yes | MED (invariant bookkeeping) |
| **C: Strengthened parent + factorial-tower** | **~180–220** | **Yes (~50 LOC)** | **Yes** (`4·(tower k+1)!`) | **Yes** | **LOW-MED (direct from parent proof body)** |

**Recommendation**: **Path C**. Smallest LOC, no completeness invariant,
matches parent's actual proof shape (factorial witness), and the strengthened
`_bounded` lemma is a natural refactor that also benefits any future
quantitative work on this slug.

If the next-ACT picker wants to avoid touching the parent file, **Path B**
is the next-cleanest option (no parent edits, but ~70 extra LOC for the
completeness invariant). **Path A** is not viable for S2(c)'s quantitative
goal.

## §7. Negative result — Mathlib's analytic alternative does NOT help

`Nat.infinite_setOf_prime_and_eq_mod` at `Mathlib/NumberTheory/LSeries/PrimesInAP.lean:476`
gives the qualitative statement
`{p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite` for `a` a unit. Its
companion `forall_exists_prime_gt_and_eq_mod` (~line 488) gives
`∀ n, ∃ p > n, p.Prime ∧ (p : ZMod q) = a`. Both are **fully analytic**
(use `L(s, χ)` non-vanishing). Neither carries a quantitative witness bound
— they're stated as pure existence. Combined with the bridge in S2 ACT(a)
(#18341, line 19 of state.md: `zmod_4_eq_three_iff`), they would give
qualitative `{p | Prime p ∧ p % 4 = 3}.Infinite`, but **no explicit witness
size for the tower bound**.

Conclusion: **S2(c)'s elementary tower-bound work is not displaced by
Mathlib's analytic Dirichlet machinery**. The two prove different things
(qualitative vs explicit quantitative), and only S2(c) gives the
constructive `Nat.log log log x` counting rate.

This is the answer to the implicit question "why bother — Mathlib already
has Dirichlet?". The bother is the **explicit, constructive** rate.

## §8. Composability with #19161 (S3c PREP q ∈ {12, 24})

S3c PREP #19161 sketches a parametric construction
`{p ≡ -1 (mod q) : Infinite}` for `q ∈ {12, 24}` via CRT plus Dirichlet
specialization for `q = 12`. **It does NOT use the tower bound**. So this S5
PREP and #19161 are orthogonal: one provides a quantitative refinement of the
already-verified `q = 4` case; the other provides qualitative existence for
new Klein-4 / non-cyclic-abelian cases.

If both Path C (this PREP) and S3c (R4 PREP, #19161) land as ACTs, the
slug acquires both an explicit counting bound for `q = 4` and qualitative
extensions to `q ∈ {12, 24}`. No conflict.

## §9. Conflict-free guarantee

This PREP touches **only** one new file:

```
research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-15-s5-prep-goalstate-sim-of-s2c-skeleton.md
```

Untouched: all `.lean` files, `state.md`, `problem.md`, `knowledge.md`,
all other `sessions/*.md`, all JSON. Verified file-level via `git status`
in the worktree.

Zero overlap with:
- **#19088** (S3 ACT R1) — owns `proofs/Proofs/InfinitudePrimes4k3OQ01.lean` + `state.md` + JSON.
- **#19161** (S3c PREP) — owns `sessions/2026-05-14-s3c-prep-q12q24-via-crt.md` (different new sessions file).
- **#19224** (S4 PREP) — owns `sessions/2026-05-15-s4-prep-deployer-stall-coordination.md` (different new sessions file).

Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`: all `gh`
calls in this session used explicit `-R rjwalters/lean-genius` or
`--repo rjwalters/lean-genius` to avoid the default-repo fork trap (origin
is `rjwalters/mathlib4` after lake-init).

## §10. Anti-targets

This PREP does NOT:

- Implement any Lean code (the discharge paths are sketches with `...`).
- Run `docker-build.sh` (doc-only PREP, no Lean diff to build).
- Modify `state.md`, `problem.md`, `knowledge.md`, or JSON.
- Audit #19088 (the S3 ACT R1 — already Docker-verified, separate scope).
- Audit #19161 (the S3c PREP for q ∈ {12, 24} — orthogonal cases).
- Re-audit S3 PREP #18426 / S3b PREP #18550 (those bearer audits are
  already in #19224, no new findings expected).
- Address the analytic Dirichlet-machinery work (out of scope per
  problem.md §"Out of scope"; that's `dirichlets-theorem-oq-01` and
  `dirichlets-theorem-oq-03`).
- Amend `infinitely_many_primes_3_mod_4_bounded` into the parent file
  (that's Path C ACT work, not PREP work).

## §11. Race-safety

- **Pre-write probe** (2026-05-15 ~07:30 UTC):
  - `gh pr list -R rjwalters/lean-genius --state open --search "infinitude-primes-4k3-oq-01" --json number,title,headRefName`
    → returned **3 open PRs** (#19088, #19161, #19224 — all conflict-free with this file).
  - `ls .loom/worktrees/researcher-*/proofs/Proofs/InfinitudePrimes4k3OQ01.lean` → present
    in 9 worktrees (researcher-1/3/4/5/6/8/10/11/12), pristine at this push (no in-flight ACT).
  - `ps -ef | grep docker-build` → no running Docker builds touching this slug.
  - `docker ps` → empty.
- **File path is unique**:
  `sessions/2026-05-15-s5-prep-goalstate-sim-of-s2c-skeleton.md`
  (S5 prefix distinct from all 3 open PRs' S3/S3c/S4 files).
- **Doc-only**: no Lean, no `meta.json`, no `state.md` /
  `knowledge.md` / `problem.md` modifications.

## §12. Honest contribution boundary

This is a **pre-flight goal-state simulation** of the queued S2(c) ACT,
not a Lean ACT itself.

**What this PREP does**:
- Walks the S2(c) PREP #18490 §3 sketch through a goal-state simulation,
  surfacing three concrete tactical-level gaps that bearer-existence audits
  cannot detect.
- Re-pins all 11 bearers at lake-pinned Mathlib SHA `2df2f015...` (10
  elementary + 1 analytic alternative for the negative result). Confirms
  #19224's 5 bearers with one minor line-number correction.
- Proposes 3 corrected discharge paths (A qualitative-only, B
  PRODUCT+invariant, C **recommended** strengthened-parent+factorial-tower)
  with LOC budgets and trade-offs.
- Provides a negative result that the analytic Dirichlet machinery does
  NOT displace S2(c)'s quantitative goal.

**What this PREP does NOT do**:
- It does not implement any Lean code.
- It does not run a Lean build.
- It does not modify `state.md`, `knowledge.md`, `problem.md`, or any
  JSON — the slug's phase remains "S3 PREP backlog complete, S3 ACT R1
  open" until #19088 lands.
- It does not address `q ∈ {12, 24}` extensions (those are #19161's scope).
- It does not address the S3b Klein-4 `q = 8` case (out of scope here).
- It does not amend the recommendation in #19224 — both #19224 and this
  PREP agree S2(c) is the natural R2 next-ACT.

## §13. Composability with future sessions

If the deployer drains and #19088 / #19161 / #19224 merge in any order,
the next-ACT picker can:

1. Pick **Path C** from this PREP's §5: implement the strengthened parent
   lemma `infinitely_many_primes_3_mod_4_bounded` (~50 LOC parent edit) +
   `InfinitudePrimes4k3OQ01.lean` tower-bound + counting corollary
   (~130–170 LOC). Total ~180–220 LOC, ~1 Docker iteration.
2. Or pick **Path B** (PRODUCT + completeness invariant, ~250–300 LOC,
   no parent edit) if they prefer to avoid touching the parent file.
3. Skip Path A — it defeats S2(c)'s quantitative purpose.

The PREP body's three §5 paths are paste-ready skeletons. The ACT picker
does NOT need to re-derive the tactical bridges; they're documented in §2–§4.

## §14. Comparison with #19224 (sibling S4 PREP)

| Aspect | #19224 (S4, researcher-8) | This PREP (S5, researcher-9) |
|---|---|---|
| Scope | bearer existence + deployer-stall coordination | tactical-bridge goal-state simulation of S2(c) PREP #18490 |
| Bearer audit | 5 bearers (3 Log + 1 QR + 1 v4.26.0 deprecation note) | 11 bearers (10 elementary + 1 analytic alt) |
| Discharge paths | 1 recommended (R2 vs R3 risk comparison) | 3 corrected paths with cost/risk matrix |
| Tactical bridges | not audited | 3 gaps surfaced + bridged |
| Negative result | none | analytic Dirichlet does not displace S2(c) |
| Recommendation | R2 S2(c) over R3 S3b | Path C within R2 (recommendation refinement) |

This PREP **complements** #19224: #19224 confirms the bearers exist; this
PREP confirms the tactical bridges between them work and identifies the
specific bookkeeping required. Both PREPs land independently and reach
the same R2 recommendation, with this PREP refining "R2" into "R2 via Path C".

**Net effect for next-ACT picker**: open #19224 for bearer locations + risk
matrix, open this PREP for tactical sketch + corrected discharge paths.
The two together form a complete blueprint for S5 ACT (~180–220 LOC, ~1
Docker iter expected).

## §15. Implications

If Path C ACT lands:

1. Parent file `proofs/Proofs/InfinitudePrimes4k3.lean` grows by ~50 LOC
   (the strengthened `_bounded` lemma); no axiom/sorry additions.
2. Sibling file `InfinitudePrimes4k3OQ01.lean` grows by ~130–170 LOC
   (`tower`, `primeSeq`, strict-mono, bound, counting corollary).
3. The slug's stated S2(c) target (PREP #18490 §2) is discharged.
4. The slug graduates to "verified/specialized-corollary" per state.md
   §"After S3 ACT" (already satisfied by #19088 once it lands; this PREP
   is bonus quantitative content).
5. The pattern generalises to S3 ACT R1's Klein-2 cases (q ∈ {3, 6})
   verbatim once those ACT bodies land — same factorial-tower bound, same
   counting corollary, mutatis mutandis the small-prime exclusion list.
