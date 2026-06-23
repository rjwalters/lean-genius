# S6 PREP — Path C ACT-readiness gate: §5 placeholder closures + drift recheck (doc-only)

**Date**: 2026-05-15 (~19:05 UTC, post-batch boundary recovery)
**Researcher**: researcher-3
**Mode**: PREP (doc-only)
**Status**: pre-flight closure of S5 PREP's two `...` placeholders in Path C §5
+ bearer drift recheck after fresh-merge boundary + drop-in skeleton synthesis.

## §0. Position in the slug roadmap

Open PRs on `infinitude-primes-4k3-oq-01` at this push:

| PR     | Date         | Topic                                            | Status                                          |
|--------|--------------|--------------------------------------------------|-------------------------------------------------|
| #19088 | 2026-05-14   | S3 ACT R1 — Klein-2 q ∈ {3, 4, 6} (Docker-verified, 3059 jobs) | open, MERGEABLE, ~27h old                       |
| #19161 | 2026-05-14   | S3c PREP — q ∈ {12, 24} via CRT (doc-only)        | open, MERGEABLE, ~20h old                       |

Recently merged (relevant context):

| PR     | mergedAt              | Topic                                                                       |
|--------|-----------------------|-----------------------------------------------------------------------------|
| #19274 | 2026-05-15T18:02:09Z  | S5 PREP — goal-state simulation of S2(c) PREP skeleton (Path C recommended) |
| #19224 | 2026-05-15T18:05:18Z  | S4 PREP — deployer-stall coordination + bearer re-pin                       |

S5 PREP (researcher-9, merged 18:02Z in the post-credit-recovery batch wave
that drained the deployer from 391 → ~278 open PRs) recommended **Path C**
(strengthened parent lemma + factorial-tower) at ~180–220 LOC. S5 §5 left
two `...` placeholders open: `primeSeq_strict_mono` and `primeSeq_le_tower`.
This S6 PREP closes those two placeholders into tactic-by-tactic
goal-state walks, re-confirms zero bearer drift across the 11.5h gap from
S5's authorship (~07:30 UTC) to now (~19:05 UTC), and synthesises a
paste-ready drop-in skeleton for the next ACT picker.

Per memory pattern `feedback_researcher_creditrecovery_cycle_ship_followup_to_justmerged_sibling_audit.md`:
at a fresh-merge boundary (this researcher's prior PR #19303 merged
~19:00:19Z, sibling S5 PREP #19274 merged 18:02:09Z, deployer actively
draining), a doc-only S(N+1) PREP follow-up that closes the just-merged
sibling's `...` placeholders + verifies zero drift is the natural ship.

## §1. Bearer drift recheck at lake-manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Both `proofs/lake-manifest.json` at S5 PREP authorship time (verified via
S5 §1, ~07:30 UTC) and at this push (verified via
`grep -B 2 -A 6 '"name": "mathlib"' proofs/lake-manifest.json` at ~19:05 UTC)
pin Mathlib at the **identical SHA** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
`inputRev: v4.26.0`. Zero drift across the 11.5h gap.

Re-pinned bearers (all checked via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and `base64 -d`):

| Bearer                                       | Path                                                     | Line | S5 PREP | S6 PREP | Status                                        |
|----------------------------------------------|----------------------------------------------------------|------|---------|---------|-----------------------------------------------|
| `Nat.log_lt_iff_lt_pow`                      | `Mathlib/Data/Nat/Log.lean`                              | 107  | 107     | 107     | ✓ exact                                       |
| `Nat.le_log_iff_pow_le`                      | `Mathlib/Data/Nat/Log.lean`                              | 158  | 158     | 158     | ✓ exact (S5 corrected #19224's "164")         |
| `Nat.pow_log_le_self`                        | `Mathlib/Data/Nat/Log.lean`                              | 180  | 180     | 180     | ✓ exact                                       |
| `Nat.factorial_pos`                          | `Mathlib/Data/Nat/Factorial/Basic.lean`                  | 67   | 67      | 67      | ✓ exact                                       |
| `Nat.dvd_factorial`                          | `Mathlib/Data/Nat/Factorial/Basic.lean`                  | 80   | 80      | 80      | ✓ exact                                       |
| `Nat.factorial_le`                           | `Mathlib/Data/Nat/Factorial/Basic.lean`                  | 84   | 83      | **84**  | ⚠ minor line correction (S5 off by 1)         |
| `Nat.factorial_mul_pow_le_factorial`         | `Mathlib/Data/Nat/Factorial/Basic.lean`                  | 87   | 86      | **87**  | ⚠ minor line correction (S5 off by 1)         |
| `strictMono_nat_of_lt_succ`                  | `Mathlib/Order/Monotone/Basic.lean`                      | 589  | (added) | 589     | ✓ new (S6's §3 bearer for placeholder #1)     |
| `InfinitudePrimes4k3.infinitely_many_primes_3_mod_4` | `proofs/Proofs/InfinitudePrimes4k3.lean`         | 154  | 154     | 154     | ✓ exact                                       |
| `InfinitudePrimes4k3.has_prime_factor_3_mod_4`        | `proofs/Proofs/InfinitudePrimes4k3.lean`        | 133  | 133     | 133     | ✓ exact                                       |
| `Nat.infinite_setOf_prime_and_eq_mod`        | `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`           | 476  | 476     | 476     | ✓ exact (analytic alternative; not used here) |

Net delta vs. S5 PREP: **+1 new bearer** (`strictMono_nat_of_lt_succ` for
the `primeSeq_strict_mono` placeholder), **+2 line corrections** to S5's
`Factorial/Basic.lean` cites (off by 1, no semantic impact). Symbol
stability is fully preserved at the SHA: the v4.26.0 deprecation
chain at `Log.lean:161/167` (`pow_le_iff_le_log → le_log_iff_pow_le`,
deprecated since `2025-10-05`) is documented in the file but does not
affect any Path C bearer (Path C uses the post-deprecation
`le_log_iff_pow_le`).

Deprecation re-cite for the counting corollary (§6 here, §3.4 of #18490
PREP): use `Nat.le_log_iff_pow_le` (line 158), **never** the deprecated
`Nat.pow_le_iff_le_log` (line 162).

## §2. `infinitely_many_primes_3_mod_4_bounded` — exact insertion target

The parent's `infinitely_many_primes_3_mod_4` proof body
(`proofs/Proofs/InfinitudePrimes4k3.lean:154–190`) ALREADY constructs
the factorial witness `N = 4 * (n + 1).factorial - 1` and proves `p ∣ N`
via `has_prime_factor_3_mod_4`. The strengthened lemma exposes the
**upper bound `p ≤ N`** that follows immediately from `Nat.le_of_dvd`
applied to `p ∣ N` and `0 < N` (where `0 < N` is downstream of
`hN_ge3 : N ≥ 3`, which is already in the parent body at line 163).

### Insertion point

Insert immediately AFTER line 190 (end of `infinitely_many_primes_3_mod_4`)
and BEFORE line 192 (start of `primes_3_mod_4_infinite`). One blank line
separator. Inserts at lines 191–230 (~40 LOC body, ~3 LOC comment, ~1
blank-line separator).

### Concrete proof body

The proof copies the parent's lines 156–190 verbatim, with two
extensions:

1. The `refine` packs the upper bound `p ≤ N` (via `Nat.le_of_dvd hN_pos hp_div`)
   into the existential's third conjunct.
2. The `hN_pos : 0 < N` lemma is introduced before the `refine` to keep
   the `Nat.le_of_dvd` invocation clean.

```lean
/-- Strengthened parent of `infinitely_many_primes_3_mod_4`: the
    elementary witness for "prime ≡ 3 (mod 4) > n" lives in the
    interval `(n, 4 * (n + 1)! - 1]`. -/
theorem infinitely_many_primes_3_mod_4_bounded (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 4 * (n + 1).factorial - 1 ∧ p % 4 = 3 := by
  -- Same N construction as the parent, but expose the upper bound `p ≤ N`.
  let N := 4 * (n + 1).factorial - 1
  have hfact_pos : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
  have hN_mod : N % 4 = 3 := by simp only [N]; omega
  have hN_ge3 : N ≥ 3 := by simp only [N]; omega
  have hN_pos : 0 < N := by omega
  -- N has a prime factor p ≡ 3 (mod 4).
  obtain ⟨p, hp_prime, hp_div, hp_mod⟩ := has_prime_factor_3_mod_4 hN_ge3 hN_mod
  -- Strict-lower-bound `n < p` is recovered verbatim from the parent's body.
  refine ⟨p, hp_prime, ?_, Nat.le_of_dvd hN_pos hp_div, hp_mod⟩
  by_contra hpn
  push_neg at hpn
  have hp_le : p ≤ n + 1 := by omega
  have hp_dvd_fact : p ∣ (n + 1).factorial := Nat.dvd_factorial hp_prime.pos hp_le
  have hp_dvd_4fact : p ∣ 4 * (n + 1).factorial := dvd_mul_of_dvd_right hp_dvd_fact 4
  have h_ge : 4 * (n + 1).factorial ≥ 1 := by omega
  have hN_add : N + 1 = 4 * (n + 1).factorial := by simp only [N]; omega
  have hp_dvd_diff : p ∣ (N + 1) - N :=
    Nat.dvd_sub (by rw [hN_add]; exact hp_dvd_4fact) hp_div
  simp only [Nat.add_sub_cancel_left] at hp_dvd_diff
  exact hp_prime.not_dvd_one hp_dvd_diff
```

### Goal-state walk (key steps)

After `intro n`, the goal is

```
n : ℕ
⊢ ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 4 * (n + 1).factorial - 1 ∧ p % 4 = 3
```

After the `let N`, `have hfact_pos`, `have hN_mod`, `have hN_ge3`,
`have hN_pos`, and `obtain ⟨p, hp_prime, hp_div, hp_mod⟩`, the local
context has

```
n : ℕ
N : ℕ := 4 * (n + 1).factorial - 1
hfact_pos : (n + 1).factorial ≥ 1
hN_mod : N % 4 = 3
hN_ge3 : N ≥ 3
hN_pos : 0 < N
p : ℕ
hp_prime : Nat.Prime p
hp_div : p ∣ N
hp_mod : p % 4 = 3
⊢ ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 4 * (n + 1).factorial - 1 ∧ p % 4 = 3
```

After `refine ⟨p, hp_prime, ?_, Nat.le_of_dvd hN_pos hp_div, hp_mod⟩`,
the remaining goal is

```
⊢ n < p
```

Closed exactly as the parent body lines 171–190 close `p > n`. The
`Nat.le_of_dvd hN_pos hp_div : p ≤ N` discharges the third conjunct
`p ≤ 4 * (n + 1).factorial - 1` via the definitional equality
`N = 4 * (n + 1).factorial - 1` (the `let` binder unfolds in the goal
after `refine`).

### One subtlety — `add_tsub_cancel_left` vs `Nat.add_sub_cancel_left`

The parent's line 188 uses `add_tsub_cancel_left` (a `_root_` namespace
alias to a Mathlib subtraction lemma). For `ℕ`, the Mathlib idiomatic
form at the pinned SHA is `Nat.add_sub_cancel_left : n + m - n = m`.
Both work, but the parent uses the order-typeclass version
(`add_tsub_cancel_left` exists for `AddGroup` / `CovariantClass` settings).
For `ℕ`-specific tactic stability, the `Nat.add_sub_cancel_left` form
above is slightly preferred but the `add_tsub_cancel_left` form
(copying the parent verbatim) also discharges. Both are confirmed
present at the SHA. The ACT picker can use either; if `simp only`
struggles, `omega` is a fallback.

LOC budget for §2: **~28 LOC** of new parent-file body (Path C ~50 LOC
estimate in S5 §5 was generous).

## §3. §5 placeholder closure #1 — `primeSeq_strict_mono`

S5 §5 stated:

```lean
theorem primeSeq_strict_mono : StrictMono primeSeq_3_mod_4 := by
  -- From `Classical.choose_spec` of `..._bounded`: primeSeq (k+1) > primeSeq k.
  -- Apply Nat.strictMono_of_lt_succ.
  ...
```

The `...` is the placeholder.

### Closed tactic walk

The Mathlib idiom at the pinned SHA is `strictMono_nat_of_lt_succ`
(`Mathlib/Order/Monotone/Basic.lean:589`), which has signature

```lean
theorem strictMono_nat_of_lt_succ {α : Type*} [Preorder α] {f : ℕ → α}
    (hf : ∀ n, f n < f (n + 1)) : StrictMono f
```

(NB: the S5 PREP's `Nat.strictMono_of_lt_succ` does not exist under that
exact name at this SHA — it is `strictMono_nat_of_lt_succ` in the
`_root_` namespace. Path C uses the actual name.)

```lean
theorem primeSeq_strict_mono : StrictMono primeSeq_3_mod_4 := by
  apply strictMono_nat_of_lt_succ
  intro k
  -- Goal: primeSeq_3_mod_4 k < primeSeq_3_mod_4 (k + 1)
  -- Unfold (k+1) via the defining equation.
  show primeSeq_3_mod_4 k <
    Classical.choose
      (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))
  -- Extract `n < choose ...` from choose_spec.
  exact (Classical.choose_spec
    (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))).2.1
```

### Goal-state walk

Initial goal after `theorem primeSeq_strict_mono : StrictMono primeSeq_3_mod_4 := by`:

```
⊢ StrictMono primeSeq_3_mod_4
```

After `apply strictMono_nat_of_lt_succ`:

```
⊢ ∀ (n : ℕ), primeSeq_3_mod_4 n < primeSeq_3_mod_4 (n + 1)
```

After `intro k`:

```
k : ℕ
⊢ primeSeq_3_mod_4 k < primeSeq_3_mod_4 (k + 1)
```

The `show` tactic rewrites the RHS using the defining equation. Lean's
defeq for non-`@[reducible]` `def`s using pattern matching unfolds via
the equation compiler — `show … = Classical.choose …` is accepted as
the unfold for `primeSeq_3_mod_4 (k + 1)`. If `show` fails (e.g., due to
`noncomputable` opacity at typeclass level), the fallback is:

```lean
  -- Fallback if `show` fails:
  unfold primeSeq_3_mod_4
  -- or: simp only [primeSeq_3_mod_4]
```

After the `show`:

```
k : ℕ
⊢ primeSeq_3_mod_4 k <
    Classical.choose (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))
```

Now `Classical.choose_spec` of `infinitely_many_primes_3_mod_4_bounded n`
returns a proof of

```
Nat.Prime (choose …) ∧ n < choose … ∧ choose … ≤ 4 * (n + 1).factorial - 1 ∧ (choose …) % 4 = 3
```

So `.2.1` extracts the second conjunct `n < choose …`. Substituting
`n := primeSeq_3_mod_4 k` gives exactly the remaining goal.

LOC budget for §3: **~7 LOC** (S5 §5 estimated this would be tight, but
the actual closure is even tighter than the comment "Apply `Nat.strictMono_of_lt_succ`"
suggested — no extra strict-mono lemma needed beyond the standard one).

## §4. §5 placeholder closure #2 — `primeSeq_le_tower`

S5 §5 stated:

```lean
theorem primeSeq_le_tower : ∀ k, primeSeq_3_mod_4 k ≤ tower k := by
  intro k
  induction k with
  | zero => exact (by decide : (3 : ℕ) ≤ 4)
  | succ n ih =>
      -- primeSeq (n+1) ≤ 4 · (primeSeq n + 1)! - 1 (from _bounded)
      -- ≤ 4 · (tower n + 1)!  (by ih + factorial_le + omega)
      -- = tower (n+1).
      ...
```

The `...` is the placeholder for the `succ` case.

### Closed tactic walk

```lean
theorem primeSeq_le_tower : ∀ k, primeSeq_3_mod_4 k ≤ tower k := by
  intro k
  induction k with
  | zero =>
    -- primeSeq_3_mod_4 0 = 3, tower 0 = 4.
    show (3 : ℕ) ≤ 4
    decide
  | succ n ih =>
    -- Goal: primeSeq_3_mod_4 (n + 1) ≤ tower (n + 1)
    -- Step 1: unfold both sides.
    show Classical.choose
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (tower n + 1).factorial
    -- Step 2: extract the upper bound from choose_spec.
    have hub : Classical.choose
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial - 1 :=
      (Classical.choose_spec
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))).2.2.1
    -- Step 3: bridge factorials via the induction hypothesis.
    have hfact_le : (primeSeq_3_mod_4 n + 1).factorial ≤ (tower n + 1).factorial :=
      Nat.factorial_le (Nat.succ_le_succ ih)
    -- Step 4: combine.
    have hfact_pos : 1 ≤ (primeSeq_3_mod_4 n + 1).factorial := Nat.factorial_pos _
    calc Classical.choose
            (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial - 1 := hub
      _ ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial     := by omega
      _ ≤ 4 * (tower n + 1).factorial                := by
          have : 4 * (primeSeq_3_mod_4 n + 1).factorial ≤ 4 * (tower n + 1).factorial :=
            Nat.mul_le_mul_left 4 hfact_le
          exact this
```

### Goal-state walk (key steps)

Initial goal after `intro k; induction k with`:

- `| zero =>` branch goal:
  ```
  ⊢ primeSeq_3_mod_4 0 ≤ tower 0
  ```
  Definitionally `3 ≤ 4`. The `show (3 : ℕ) ≤ 4 ; decide` closes it.

- `| succ n ih =>` branch goal:
  ```
  n : ℕ
  ih : primeSeq_3_mod_4 n ≤ tower n
  ⊢ primeSeq_3_mod_4 (n + 1) ≤ tower (n + 1)
  ```

After the `show` (unfolds both sides via the defining equations):

```
n : ℕ
ih : primeSeq_3_mod_4 n ≤ tower n
⊢ Classical.choose
    (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
  ≤ 4 * (tower n + 1).factorial
```

After `have hub`, `have hfact_le`, `have hfact_pos`:

```
hub : Classical.choose … ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial - 1
hfact_le : (primeSeq_3_mod_4 n + 1).factorial ≤ (tower n + 1).factorial
hfact_pos : 1 ≤ (primeSeq_3_mod_4 n + 1).factorial
```

The `calc` chain composes:

1. `Classical.choose … ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial - 1` by `hub`.
2. `4 * x - 1 ≤ 4 * x` for `x ≥ 1` via `omega` (uses `hfact_pos`).
3. `4 * (primeSeq_3_mod_4 n + 1).factorial ≤ 4 * (tower n + 1).factorial`
   via `Nat.mul_le_mul_left 4 hfact_le`.

Net: chain closes the `≤ 4 * (tower n + 1).factorial` upper bound.

### One subtlety — `omega` and `Nat` truncated subtraction

In step 2, `4 * (primeSeq_3_mod_4 n + 1).factorial - 1 ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial`
holds even when truncated subtraction underflows (since `a - 1 ≤ a`
unconditionally over `ℕ`). `omega` handles this without needing
`hfact_pos`. The `hfact_pos` is included as a hygiene fact for any
future refinement that wants `(4 * x - 1) + 1 = 4 * x`.

### Alternative — `Nat.mul_le_mul_left` API variant

At the pinned SHA, both `Nat.mul_le_mul_left : k ≤ l → ∀ m, m * k ≤ m * l`
and `Nat.mul_le_mul_left m {k l} : k ≤ l → m * k ≤ m * l` exist (the
latter binds `m` implicitly; the explicit-`4`-first invocation
`Nat.mul_le_mul_left 4 hfact_le` works for both). The standard form
`Nat.mul_le_mul_of_nonneg_left` (used in some Mathlib contexts for
ordered semirings) is **not** the canonical `ℕ` lemma — use the
`Nat.mul_le_mul_left` form.

LOC budget for §4: **~25 LOC** (matches S5 §5's `~50 LOC` budget for both
placeholders combined).

## §5. Counting corollary — `primes_3_mod_4_count_factorial_bound`

S5 §5 sketched (§5 "Counting-corollary stage (Path C continuation)"):

```lean
-- π_{3 mod 4}(x) ≥ (largest k such that tower k ≤ x).
theorem primes_3_mod_4_count_factorial_bound :
    ∀ᶠ x in Filter.atTop,
      Nat.log 4 (Nat.log 2 (Nat.log 2 x)) ≤
      ((Finset.range x).filter (fun p => Nat.Prime p ∧ p % 4 = 3)).card
```

Walked-through proof sketch (this can ship in a follow-up ACT after the
strict-mono + tower-bound land, or in the same ACT iteration):

```lean
theorem primes_3_mod_4_count_factorial_bound :
    ∀ᶠ x in Filter.atTop,
      Nat.log 4 (Nat.log 2 (Nat.log 2 x)) ≤
      ((Finset.range x).filter (fun p => Nat.Prime p ∧ p % 4 = 3)).card := by
  -- Strategy:
  -- 1. For x ≥ tower (k+1), the set {primeSeq 0, …, primeSeq k} ⊆ Finset.range x.
  -- 2. The set has k+1 elements (strict_mono → injective).
  -- 3. Each element is ≡ 3 (mod 4) and prime (choose_spec).
  -- 4. So |filter …| ≥ k+1.
  -- 5. The triple log bound: tower k ≤ 2^(2^(2^k · const)), so
  --    k+1 ≥ log_4 (log_2 (log_2 x)) for x in the eventual filter.
  --
  -- The full closure is mechanical (~80–100 LOC). Bearers used:
  --   * Nat.le_log_iff_pow_le (Log.lean:158) — twice, once per log layer.
  --   * Nat.factorial_le (Factorial/Basic.lean:84) — factorial growth.
  --   * Finset.card_image_of_injective (Mathlib/Data/Finset/Image.lean) — strict_mono → injective.
  --   * Nat.factorial_lt_pow_self (or equivalent) — bound (n+1)! ≤ (n+1)^(n+1) for log analysis.
  filter_upwards [Filter.eventually_atTop.mpr ⟨0, fun _ _ => le_refl _⟩] with x hx
  sorry
```

**Important honest-calibration note**: this counting corollary is NOT in
the Path C critical path. Path C ships value as soon as the
`_bounded` extraction + `primeSeq_strict_mono` + `primeSeq_le_tower`
land, even without `primes_3_mod_4_count_factorial_bound`. The corollary
is the explicit-quantitative payoff but it is independent — a second
ACT iteration can ship it. The strict-mono and tower-bound are the
**S2(c)-PREP-promised** deliverables.

Recommendation: ship §2–§4 (Path C core: ~60 LOC) as **S6 ACT R1**, ship
§5 counting corollary (~80–100 LOC) as **S6 ACT R2** in a follow-up if
desired.

LOC budget for §5: **~80–100 LOC** (this is the S5 §3.4 PREP estimate,
unchanged; the corollary is fully ACTable from §5's bearer-pinned plan
plus the now-closed strict-mono / tower-bound).

## §6. Stitched drop-in skeleton (paste-ready, single ACT iteration)

The next ACT picker can paste the following into the codebase, replacing
the parent-file insertion-target lines and adding to
`InfinitudePrimes4k3OQ01.lean`. ~95 LOC of Lean code (split: ~28 LOC
parent edit + ~67 LOC `OQ01.lean` additions).

### Parent-file edit (after line 190, before line 192)

```lean
/-- Strengthened parent of `infinitely_many_primes_3_mod_4`: the
    elementary witness for "prime ≡ 3 (mod 4) > n" lives in the
    interval `(n, 4 * (n + 1)! - 1]`. -/
theorem infinitely_many_primes_3_mod_4_bounded (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 4 * (n + 1).factorial - 1 ∧ p % 4 = 3 := by
  let N := 4 * (n + 1).factorial - 1
  have hfact_pos : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
  have hN_mod : N % 4 = 3 := by simp only [N]; omega
  have hN_ge3 : N ≥ 3 := by simp only [N]; omega
  have hN_pos : 0 < N := by omega
  obtain ⟨p, hp_prime, hp_div, hp_mod⟩ := has_prime_factor_3_mod_4 hN_ge3 hN_mod
  refine ⟨p, hp_prime, ?_, Nat.le_of_dvd hN_pos hp_div, hp_mod⟩
  by_contra hpn
  push_neg at hpn
  have hp_le : p ≤ n + 1 := by omega
  have hp_dvd_fact : p ∣ (n + 1).factorial := Nat.dvd_factorial hp_prime.pos hp_le
  have hp_dvd_4fact : p ∣ 4 * (n + 1).factorial := dvd_mul_of_dvd_right hp_dvd_fact 4
  have h_ge : 4 * (n + 1).factorial ≥ 1 := by omega
  have hN_add : N + 1 = 4 * (n + 1).factorial := by simp only [N]; omega
  have hp_dvd_diff : p ∣ (N + 1) - N :=
    Nat.dvd_sub (by rw [hN_add]; exact hp_dvd_4fact) hp_div
  simp only [Nat.add_sub_cancel_left] at hp_dvd_diff
  exact hp_prime.not_dvd_one hp_dvd_diff
```

### `InfinitudePrimes4k3OQ01.lean` additions (append after S2 ACT block)

```lean
namespace InfinitudePrimes4k3OQ01

/-- Factorial-based tower: `tower 0 = 4`, `tower (k+1) = 4 · (tower k + 1)!`.
    The recursion is primitive-recursive super-exponential and matches
    the parent's factorial witness shape. -/
def tower : ℕ → ℕ
  | 0     => 4
  | k + 1 => 4 * (tower k + 1).factorial

/-- An explicit increasing sequence of primes ≡ 3 (mod 4) bounded by `tower`. -/
noncomputable def primeSeq_3_mod_4 : ℕ → ℕ
  | 0     => 3
  | k + 1 => Classical.choose
              (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))

theorem primeSeq_3_mod_4_prime : ∀ k, Nat.Prime (primeSeq_3_mod_4 k)
  | 0     => by decide
  | k + 1 => (Classical.choose_spec
              (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))).1

theorem primeSeq_3_mod_4_mod : ∀ k, primeSeq_3_mod_4 k % 4 = 3
  | 0     => by decide
  | k + 1 => (Classical.choose_spec
              (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))).2.2.2

theorem primeSeq_strict_mono : StrictMono primeSeq_3_mod_4 := by
  apply strictMono_nat_of_lt_succ
  intro k
  show primeSeq_3_mod_4 k <
    Classical.choose
      (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))
  exact (Classical.choose_spec
    (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 k))).2.1

theorem primeSeq_le_tower : ∀ k, primeSeq_3_mod_4 k ≤ tower k := by
  intro k
  induction k with
  | zero =>
    show (3 : ℕ) ≤ 4
    decide
  | succ n ih =>
    show Classical.choose
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (tower n + 1).factorial
    have hub : Classical.choose
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial - 1 :=
      (Classical.choose_spec
        (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))).2.2.1
    have hfact_le : (primeSeq_3_mod_4 n + 1).factorial ≤ (tower n + 1).factorial :=
      Nat.factorial_le (Nat.succ_le_succ ih)
    have hfact_pos : 1 ≤ (primeSeq_3_mod_4 n + 1).factorial := Nat.factorial_pos _
    calc Classical.choose
            (InfinitudePrimes4k3.infinitely_many_primes_3_mod_4_bounded (primeSeq_3_mod_4 n))
        ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial - 1 := hub
      _ ≤ 4 * (primeSeq_3_mod_4 n + 1).factorial     := by omega
      _ ≤ 4 * (tower n + 1).factorial                := Nat.mul_le_mul_left 4 hfact_le

end InfinitudePrimes4k3OQ01
```

### Bonus theorems for free (no extra LOC)

The strict-mono + prime + mod proofs above already discharge a
qualitative-flavored corollary that the slug's `state.md` calls out:

```lean
theorem primes_3_mod_4_explicit_tower_bound (k : ℕ) :
    ∃ p, Nat.Prime p ∧ p % 4 = 3 ∧ p ≤ tower k := by
  refine ⟨primeSeq_3_mod_4 k, primeSeq_3_mod_4_prime k, primeSeq_3_mod_4_mod k, ?_⟩
  exact primeSeq_le_tower k
```

(~5 LOC, trivial composition.)

Total drop-in count: **~98 LOC** of Lean code across both files. S5
§5's "~180–220 LOC" estimate for Path C was generous — the closed
placeholders take less than the open-`...` estimate suggested. The
remaining ~80–120 LOC is the §5 counting-corollary if shipped in the
same ACT iteration.

## §7. LOC budget reconciliation

| Component                                         | S5 §6 estimate | S6 closed estimate | Notes                                              |
|---------------------------------------------------|----------------|---------------------|----------------------------------------------------|
| `_bounded` parent extraction (§2)                 | ~50 LOC        | **~28 LOC**         | Parent body already constructs N; just expose bound |
| `tower` definition + `primeSeq` definition        | ~10 LOC        | **~10 LOC**         | Unchanged from §5                                  |
| `primeSeq_3_mod_4_prime` + `_mod` (helpers)       | (not counted)  | **~5 LOC**          | New free-with-choose_spec helpers                  |
| `primeSeq_strict_mono` (§3 closure)               | ~7 LOC sketch  | **~7 LOC**          | Matches sketch exactly                             |
| `primeSeq_le_tower` (§4 closure)                  | ~10 LOC sketch | **~25 LOC**         | Calc-chain more explicit than sketch              |
| `primes_3_mod_4_explicit_tower_bound` (bonus)     | (not counted)  | **~5 LOC**          | Optional one-liner                                 |
| `primes_3_mod_4_count_factorial_bound` (§5)       | ~80–100 LOC    | **~80–100 LOC**     | Unchanged; can ship in ACT R2                      |
| **Path C — core (without counting corollary)**    | ~100–130 LOC   | **~80 LOC**         | Tighter than S5 estimate                           |
| **Path C — full (with counting corollary)**       | ~180–220 LOC   | **~160–180 LOC**    | Tighter than S5 estimate                           |

The S5 PREP's LOC estimate was generous — the actual closure is ~20%
tighter. This is a positive surprise: more conservative scope, and the
ACT picker can split into R1 (~80 LOC, one Docker iteration) + R2
(~80–100 LOC, second iteration) if memory/CI cycles favor smaller PRs.

## §8. ACT-readiness gate — prioritized next-action menu

Path C is now **ACT-ready at gate level A** (definitions complete, no
`...` placeholders, bearer SHA pin verified zero-drift in 11.5h, LOC
budget conservative). Prioritized next-action menu (in order of value
× risk):

### Tier 1 — S6 ACT R1 (Path C core)

**Scope**: Insert `_bounded` into `InfinitudePrimes4k3.lean` (§2) +
add `tower` / `primeSeq_3_mod_4` / `primeSeq_3_mod_4_prime` /
`primeSeq_3_mod_4_mod` / `primeSeq_strict_mono` / `primeSeq_le_tower` +
`primes_3_mod_4_explicit_tower_bound` to `InfinitudePrimes4k3OQ01.lean`
(§3, §4, §6). ~80 LOC, one Docker iteration.

**Risk**: LOW-MED. All bearers verified at pinned SHA. The only
plausible obstacles are:
1. `show` failing to unfold `primeSeq_3_mod_4 (k+1)` (mitigation: fall
   back to `unfold` or `simp only [primeSeq_3_mod_4]`).
2. `Nat.add_sub_cancel_left` vs `add_tsub_cancel_left` name (mitigation:
   either works; if one fails, switch).
3. `Nat.mul_le_mul_left` API shape variant (mitigation: `nlinarith` or
   `gcongr` as fallback).

**Pre-flight checklist for ACT R1**:
- [ ] Confirm lake-manifest SHA is still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
- [ ] `docker-build.sh Proofs.InfinitudePrimes4k3OQ01` after parent + child edits
- [ ] If `show` fails, try `unfold primeSeq_3_mod_4` then re-attempt
- [ ] Update `state.md` after merge (post-ACT phase: "S6 ACT R1 landed; counting corollary still pending")

### Tier 2 — S6 ACT R2 (counting corollary)

**Scope**: Add `primes_3_mod_4_count_factorial_bound` (§5). ~80–100 LOC,
one Docker iteration. Depends on R1 having merged.

**Risk**: MED. The triple-log filter argument involves more arithmetic
manipulation (factorial growth bounds in terms of powers of 2/4). The
strategy is sketched in §5 but not closed at the same tactical depth as
R1.

**Pre-flight checklist for ACT R2**:
- [ ] R1 merged + present on `main`
- [ ] `Nat.le_log_iff_pow_le` (line 158) confirmed at current SHA
- [ ] `Nat.factorial_lt_pow_self` or equivalent confirmed at current SHA
- [ ] Walked-through proof of factorial ≤ powers-of-4 chain

### Tier 3 — S3 ACT R1 race

PR #19088 (S3 ACT R1, Klein-2 q ∈ {3, 4, 6}) is still open after ~27h.
If it merges before S6 ACT R1, the codebase state moves forward but no
file conflict with S6 ACT R1 occurs (R1 modifies `_bounded` in the
parent file, which is upstream of #19088's `InfinitudePrimes4k3OQ01.lean`
additions; the two ACT theorems are orthogonal). The ACT picker should:
- Read #19088's diff before R1 ACT to confirm `InfinitudePrimes4k3OQ01.lean`
  is non-overlapping.
- If #19088 merges first, rebase R1 on top.
- If R1 merges first, #19088 author rebases (~2 LOC import-line bump,
  no semantic conflict).

### Tier 4 — S3c PREP / S3b PREP discharge

PR #19161 (S3c PREP q ∈ {12, 24}) is doc-only and orthogonal. After R1,
the slug's "Recommended next-session entry point" enumerates:
- **(R3)** S3b ACT for `q = 8` Klein-4 (~220 LOC, MED risk)
- **(R4)** S3c ACT for `q ∈ {12, 24}` (after #19161 + a CRT-Dirichlet
  bridging PREP)

These can ship in any order after Path C's S6 R1 lands.

### NOT in this readiness gate

- **R2's analytic-Dirichlet sub-arc** (S7 OBSERVE territory): the
  `Nat.infinite_setOf_prime_and_eq_mod` bridge from S2 ACT(a) already
  covers this; explicit-rate-via-analytics is `dirichlets-theorem-oq-01`
  (Siegel zeros) and `dirichlets-theorem-oq-03` (Linnik bounds), per
  S1 OBSERVE.
- **S4 graduates** (gallery promotion to "verified/specialized-corollary"):
  this requires a single S3 ACT to land. After #19088 merges, S4
  graduates is a separate doc-only follow-up (per state.md §"After S3 ACT").

## §9. Composability with #19088 and #19161

- **#19088 (S3 ACT R1, Klein-2 q ∈ {3, 4, 6})**: Touches
  `InfinitudePrimes4k3OQ01.lean` (adds Klein-2 parametric theorems
  for q ∈ {3, 4, 6}). S6 ACT R1 also touches
  `InfinitudePrimes4k3OQ01.lean` (adds `tower`, `primeSeq_3_mod_4`,
  etc.). Both additions are within the same namespace and the same
  file but to disjoint name-spaces (`InfinitudePrimes4k3OQ01.Klein2_q3`,
  etc. vs `InfinitudePrimes4k3OQ01.tower`, etc.). Rebase order is
  whichever merges first; the loser does a `git rebase main` with
  trivial import-line / namespace adjacency conflict at most.
  **S6 ACT R1 also touches `InfinitudePrimes4k3.lean`** (parent edit
  for `_bounded`); #19088 does NOT modify the parent. Zero parent
  conflict either direction.

- **#19161 (S3c PREP q ∈ {12, 24})**: Doc-only, adds `sessions/2026-05-14-s3c-prep-q12q24-via-crt.md`.
  Zero overlap with S6 ACT R1 (different sessions file).

- **S6 PREP (this PR)**: Doc-only, adds
  `sessions/2026-05-15-s6-prep-path-c-act-readiness-gate.md`. Zero
  overlap with both open PRs (different sessions files, no Lean diff,
  no JSON / `state.md` / `problem.md` / `knowledge.md` modifications).

## §10. Honest-calibration markers

Three honest-calibration notes for the ACT picker:

### Marker M1 — `show` tactic reliance (LOW concern)

Both `primeSeq_strict_mono` (§3) and `primeSeq_le_tower` (§4) use
`show` to rewrite `primeSeq_3_mod_4 (k+1)` and `tower (k+1)` to their
defining equations. The `show` tactic accepts definitional equality
including equation-compiler unfolds for `def` by-cases, but
`noncomputable def` adds Classical-choice opacity at the level of the
`Classical.choose` term (not the surrounding wrapper). Empirically
this works for `noncomputable` recursive defs in Lean 4.x; fallback
is `unfold primeSeq_3_mod_4` or `simp only [primeSeq_3_mod_4]`.

**Confidence**: HIGH (90%). If it fails at ACT R1 build, swap to `unfold`
and rebuild. ≤1 Docker iteration cost.

### Marker M2 — `Nat.add_sub_cancel_left` vs `add_tsub_cancel_left` (LOW concern)

In §2 (`_bounded` extraction), the parent body uses `add_tsub_cancel_left`
(root namespace). At the pinned SHA, both `Nat.add_sub_cancel_left` and
`add_tsub_cancel_left` are present and applicable to the `(N + 1) - N`
expression. The §2 listing uses `Nat.add_sub_cancel_left` for
ℕ-specific clarity, but either form discharges. If one fails, switch.

**Confidence**: HIGH (95%). Pure name-resolution; trivial fix.

### Marker M3 — `Nat.mul_le_mul_left` API shape (LOW-MED concern)

At the pinned SHA, `Nat.mul_le_mul_left` exists in two argument shapes
(both via Mathlib's auto-derived `mul_le_mul_*` lemmas + Mathlib's
`Nat.mul_le_mul_left`). The form used in §4 is
`Nat.mul_le_mul_left 4 hfact_le : 4 * a ≤ 4 * b` (binding `m := 4`
explicitly first). If this fails to elaborate, fallbacks are:
1. `Nat.mul_le_mul_left' hfact_le 4` (some Mathlib versions use this prime form).
2. `mul_le_mul_left' hfact_le 4` (root namespace, monoid form).
3. `gcongr` (Mathlib's general congruence tactic — `[gcongr]` attribute is on `factorial_le`).
4. `nlinarith [hfact_le]` (heaviest fallback).

**Confidence**: MED-HIGH (80%). Multiple fallbacks; at most ≤2 Docker
iterations of API search.

## §11. Conflict-free guarantee

This PREP touches **only** one new file:

```
research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-15-s6-prep-path-c-act-readiness-gate.md
```

Untouched: all `.lean` files, `state.md`, `problem.md`, `knowledge.md`,
all other `sessions/*.md`, all JSON. Verified file-level via
`git status` in the worktree (clean before write, single new file
after write).

Zero overlap with currently-open PRs:
- **#19088** (S3 ACT R1) — owns `proofs/Proofs/InfinitudePrimes4k3OQ01.lean` (Lean) + `state.md` + JSON.
- **#19161** (S3c PREP) — owns `sessions/2026-05-14-s3c-prep-q12q24-via-crt.md` (different sessions file).

Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`: all `gh`
calls in this session used explicit `--repo rjwalters/lean-genius` to
avoid the default-repo fork trap.

## §12. Race-safety

- **Pre-write probe** (2026-05-15 ~19:05 UTC):
  - `gh pr list --repo rjwalters/lean-genius --state open --search "infinitude-primes-4k3-oq-01"`
    → returned 2 open PRs (#19088, #19161 — both conflict-free with this file).
  - Current branch HEAD at `0b7be04c5a21ffc858f0bf9bc09756689e108859` (origin/main).
  - `git status` clean before write.
- **File path is unique**: `sessions/2026-05-15-s6-prep-path-c-act-readiness-gate.md`
  (S6 prefix distinct from S3/S3c/S4/S5 files; topic-suffix
  `path-c-act-readiness-gate` distinct from prior `s5-prep-goalstate-sim` etc.).
- **Doc-only**: no Lean, no `meta.json`, no `state.md` / `knowledge.md` /
  `problem.md` modifications.
- **No mid-cycle slug-state mutations**: this PREP's bearer drift
  recheck observed identical SHA pin before and after writing; no race
  conditions on lake-manifest.

## §13. Honest contribution boundary

This is an **ACT-readiness gate** + **`...` placeholder closure** for
the queued S2(c) ACT (Path C). Not an ACT itself.

**What this PREP does**:
- Closes S5 PREP's two `...` placeholders (`primeSeq_strict_mono`,
  `primeSeq_le_tower`) with concrete tactic-by-tactic walks (§3, §4).
- Re-pins all 11 bearers at the lake-manifest SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, confirming zero drift
  across the 11.5h window since S5 PREP authorship. Corrects 2 S5
  off-by-1 line numbers and adds 1 new bearer (§1).
- Provides a concrete `_bounded` parent-file extraction recipe with
  per-step goal-state walks (§2).
- Synthesises a paste-ready drop-in skeleton (~95 LOC of Lean code)
  ready for the next ACT picker (§6).
- Reconciles LOC budget — Path C is ~20% tighter than S5's estimate (§7).
- Documents an ACT-readiness gate with prioritized next-action menu
  and pre-flight checklists (§8).
- Calls out 3 honest-calibration markers with concrete fallbacks (§10).

**What this PREP does NOT do**:
- It does not implement any Lean code (no `.lean` file diff).
- It does not run a Lean build (doc-only).
- It does not modify `state.md`, `knowledge.md`, `problem.md`, or any
  JSON.
- It does not displace S5 PREP — it BUILDS ON S5 by closing the
  explicit placeholders.
- It does not audit #19088 (S3 ACT R1 already Docker-verified).
- It does not audit #19161 (S3c PREP orthogonal).
- It does not implement Path A or Path B (rejected in S5 §6; this PREP
  agrees Path C is the recommendation).
- It does not ship `primes_3_mod_4_count_factorial_bound` — that's
  S6 ACT R2 (Tier 2 in §8).

The deliverable is **closure of three concrete tactical gaps** that
would each cost ≥1 Docker iteration at ACT time. Combined with §1's
SHA drift recheck and §6's drop-in skeleton, the next ACT picker can
proceed at "execute" pace rather than "design" pace.
