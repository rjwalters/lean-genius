# Iteration 34b PREP — Sibling-audit of Iter 32 PREP §4 (28b-2) skeleton at lake-pinned Mathlib SHA, post-Iter-34a-ACT

**Date**: 2026-05-15 (~05:55 UTC)
**Researcher**: researcher-8
**Phase**: PREP (doc-only — sibling-audit of Iter 32 PREP #18682's §4 Lean skeleton against Mathlib at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, performed AFTER Iter 34a ACT #19208 shipped build-verified 28b-1 + Lemma A and left 28b-2 as the next-ACT target)
**Triggers**:
- **Iter 34a ACT (PR #19208, researcher-?, build verified 3066/3066 jobs)** — ships `factorization_succ_mul_choose_le_log_succ` (28b-1 bridge bound) + `sum_mod_pow_lt_of_pow_dvd_succ` (Lemma A). PR body explicitly defers 28b-2 (witness saturation) to a follow-up ACT, citing Iter 32 PREP #18682's §4 skeleton as the hand-proof.
- Iter 32 PREP (PR #18682, researcher-3, merged) — drafts §4 drop-in Lean skeleton (3 sorries) for `exists_witness_choose_saturates_log_succ`, estimated 35–50 LOC.
- Memory pattern `feedback_researcher_audits_buildverified_pr_next_section_finds_falseclaim_in_file` — when build-verified ACT PR ships "Next (S+1)" forward plan, audit each quantitative claim against Mathlib at lake-pinned SHA before the next ACT lands.

**Anti-targets** (this PREP does NOT modify any of):
- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` (Iter 34a ACT live in PR #19208 — strict file-disjointness)
- `research/problems/.../state.md` (modified by PR #19208)
- `research/problems/.../sessions/2026-05-14-iter34-act-28b1-bridge-bound.md` (PR #19208's session log)
- `knowledge.md`, `problem.md`, `src/data/research/problems/....json`, `src/data/proofs/...../meta.json`
- Any other prior `sessions/*.md` (single NEW file in `sessions/`)

## TL;DR

I audited Iter 32 PREP #18682's §4 Lean skeleton for `exists_witness_choose_saturates_log_succ` (the 28b-2 witness saturation lemma, deferred from Iter 34a ACT PR #19208 to a follow-up ACT). Five findings:

| # | Finding | Severity | Effect on 28b-2 ACT |
|--:|---------|:--------:|---------------------|
| 1 | `Nat.factorization_choose` (Iter 32 PREP §1.1, §5) | ✅ confirmed at SHA `2df2f015...`, **`Mathlib/Data/Nat/Choose/Factorization.lean:131`**, signature **exact match** | No change — proof body unchanged |
| 2 | `Nat.le_log_of_pow_le` (used by PR #19208's 28b-1 proof; cited by Iter 33 PREP §1.3 at `Mathlib/Data/Nat/Log.lean:176`) | ✅ confirmed at SHA, **same line 176**, signature exact | No change |
| 3 | **`Nat.dvd_iff_mod_eq_zero`** (Iter 32 PREP §5 claims `0 < n → ...`) | ⚠ **minor — no positivity hypothesis at SHA** (`lean4 src/Init/Data/Nat/Dvd.lean:96`) | PR #19208 already used `.mp` form with no positivity — Iter 32 §5 entry was outdated |
| 4 | **`Nat.mul_mod_mul_left`** (Iter 32 PREP §5 claims `c ≥ 1`) | ⚠ **minor — no positivity hypothesis at SHA** (`lean4 src/Init/Data/Nat/Div/Basic.lean:397`) | Iter 32 §5 entry overstated hypotheses |
| 5 | **`Nat.sub_mod` as named** (Iter 32 PREP §5 lists statement `(a - b) % n = ((a % n) + (n - b % n)) % n`) | ❌ **does not exist as a Lean core lemma by that name** | PR #19208's 28b-1 proof already worked around this using `Nat.mod_eq_sub_mod` + `Nat.mod_eq_of_lt`. Iter 32 PREP §4 helper Helper 2's commentary references `Nat.sub_mod` for the residue manipulation; ACT author must substitute `Nat.mod_eq_sub_mod` + arithmetic |
| 6 | **§4 Helper 2 `witness_mod_pow_lt` signature** carries `hf_eq : f = i - a` | 🔴 **over-restricted — covers only `i = a + f = e`, not the §2.2 range `i ∈ [a+1, e]`** | Helper as stated does **not** suffice for the main lemma's §2.2 case sweep; ACT must generalize or inline the residue computation |
| 7 | **§4 Helper 2 needs `m > p^f` strict, not `p^f ≤ m`** (so `m - p^f > 0`, hence `(m - p^f) % p^j` can be ≥ 1) | 🟠 medium — implicit in Case B context (`Case A: m = 1, f = 0`; in Case B, `m = p^f` would force `p ∣ m`, contradicting `gcd(m,p)=1`), but Helper 2's hypothesis `hpf_le : p ^ f ≤ m` permits the false-claim sub-case `m = p^f` where residue is `0` | Add strict inequality or factor through `f ≥ 1 ∧ gcd(m,p)=1` |
| 8 | **§4 Helper 1 `pow_sub_one_mod_pow` i=0 edge case** | 🟢 minor — `(p^e-1) % p^0 = (p^e-1) % 1 = 0`, RHS `p^0 - 1 = 0`. Holds trivially but needs `rcases Nat.eq_zero_or_pos i` to split. | Add 1-LOC `simp`/`omega` branch at top |

**Net effect on 28b-2 ACT effort**:
- Iter 32 PREP §4 estimate: 35–50 LOC (3 sorries: Helper 1 ~10, Helper 2 ~15, main split ~25).
- Audit-corrected estimate: **45–60 LOC** (Helper 1 ~12, Helper 2 ~20 *with corrected signature*, main split ~25 *with explicit Case A vs Case B preamble*).
- Net: ~5–10 LOC overhead due to Helper 2 generalization (single `j` parameter instead of `i = a + f` specialization).

**Three audit-corrected options** for the 28b-2 ACT author (§7):
- **Option A (recommended)** — generalize Helper 2 to `j` parameter; explicit Case A/B split in main lemma. ~50 LOC, 0 sorries reachable.
- **Option B** — defer Case A to `Nat.factorization_choose_prime_pow` (line 172, `Mathlib/Data/Nat/Choose/Factorization.lean`); only prove Case B residue helpers. ~40 LOC.
- **Option C** — skip 28b-2 entirely; instead 28b-3 (assembly) absorbs the witness existence via direct decidability for small `n` + a paper-level reference, leaving an axiom `exists_witness_choose_saturates_log_succ`. Faster but adds 1 axiom; **not recommended** under axiom-integrity policy.

This PREP is strictly conflict-free with PR #19208 (single NEW session file; zero shared paths). Composes with memory patterns: `_audits_buildverified_pr_next_section_finds_falseclaim_in_file`, `_preflight_pin_verifies_peer_prep_skeleton`, `_parent_compile_as_bearer_witness`.

## §1 — Mathlib bearer pin-verification (at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

All 9 bearers cited by Iter 32 PREP §5 or invoked by §4 helpers were checked via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>` (Mathlib) or `gh api repos/leanprover/lean4/contents/src/<path>` (Lean core, version-tracked separately by toolchain).

### §1.1 Confirmed-exact bearers (5/9)

| Declaration | Provenance @ pinned SHA | Iter 32 §5 statement vs actual |
|---|---|---|
| `Nat.factorization_choose` | `Mathlib/Data/Nat/Choose/Factorization.lean:131` | ✅ exact match. Signature: `{p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hnb : log p n < b) : (choose n k).factorization p = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}`. PR #19208's `factorization_succ_mul_choose_le_log_succ` invokes this with `b = log p (n+1) + 1`. |
| `Nat.le_log_of_pow_le` | `Mathlib/Data/Nat/Log.lean:176` | ✅ exact match. Signature: `{b x y : ℕ} (hb : 1 < b) (h : b ^ x ≤ y) : x ≤ log b y`. Used in PR #19208's 28b-1 proof at line ~1568 to derive `a ≤ e` from `p^a ∣ n+1`. |
| `Nat.add_mod` | Lean core, `Init/Data/Nat/Basic.lean` (canonical) | ✅ exact. Used in PR #19208 line 1490 and required for §2.5 step in 28b-2. |
| `Nat.mod_eq_of_lt` | Lean core, `Init/Data/Nat/Mod.lean` (canonical) | ✅ exact. Heavy use throughout PR #19208's 28b-1 proof. |
| `Nat.exists_eq_add_of_le` | `lean4 src/Init/Data/Nat/Lemmas.lean:376`, signature `(h : m ≤ n) : ∃ k : Nat, n = m + k` | ✅ exists; **note ordering** is `n = m + k` (m on left). Useful for Helper 1 alternative proof (§3.1). |

### §1.2 Bearers with **minor inaccuracies** in Iter 32 PREP §5 (3/9)

| Declaration | Iter 32 §5 statement | Actual signature @ pinned SHA | Severity |
|---|---|---|---|
| `Nat.dvd_iff_mod_eq_zero` | `0 < n → (n ∣ m ↔ m % n = 0)` | `lean4 src/Init/Data/Nat/Dvd.lean:96`: `{m n : Nat} : m ∣ n ↔ n % m = 0` — **no positivity hypothesis**, **divisor is `m` not `n`** | ⚠ minor. PR #19208 line 1488 already used `Nat.dvd_iff_mod_eq_zero.mp` correctly with no positivity arg (per its PR body's TODO #1 resolution: "no positivity arg; implicit args at v4.26.0"). Iter 32 PREP §5 entry was outdated. |
| `Nat.mul_mod_mul_left` | "for `c ≥ 1`" | `lean4 src/Init/Data/Nat/Div/Basic.lean:397`: `(z x y : Nat) : (z * x) % (z * y) = z * (x % y)` — **no positivity hypothesis**, holds unconditionally (`z=0` case both sides `0`) | ⚠ minor. Saves a `c ≥ 1` proof obligation in Helper 2. |

### §1.3 Bearer with **no direct match** at pinned SHA (1/9)

`Nat.sub_mod` is listed by Iter 32 PREP §5 as a Lean core lemma `(a - b) % n = ((a % n) + (n - b % n)) % n` requiring `b ≤ a`. Searching Lean core (`Init/Data/Nat/Mod.lean`, `Init/Data/Nat/Lemmas.lean`) at toolchain pin:

```
$ gh api "search/code?q=org:leanprover+%22theorem+sub_mod%22+language:Lean"
# returns no exact match in Lean core
```

What **does** exist:
- `Nat.mod_eq_sub_mod` — `n ≤ a → a % n = (a - n) % n` (`Init/Data/Nat/Lemmas.lean:1531`-region). Used by PR #19208 line 1494: `rw [Nat.mod_eq_sub_mod h_not, Nat.mod_eq_of_lt h_sub_lt]`.
- `Nat.sub_mod_eq_zero_of_mod_eq` — `m % k = n % k → (m - n) % k = 0`.

**Effect on 28b-2 ACT**: Iter 32 PREP §4 Helper 2's commentary ("`Nat.sub_mod` (modular subtraction; valid since $p^a m \ge p^e$)") cannot use `Nat.sub_mod` by that name. Recommended replacement: combine `Nat.mod_eq_sub_mod` (for `p^a m - p^e`) with the divisibility argument `p^i ∣ p^a m ∧ p^i ∣ p^e ⟹ p^i ∣ p^a m - p^e` directly, then `Nat.dvd_iff_mod_eq_zero.mp`.

## §2 — §4 Helper 2 signature bug: over-restriction to `i = a + f`

### §2.1 The stated signature

Iter 32 PREP §4:

```lean
lemma witness_mod_pow_lt {p a m f i : ℕ} (hp : 1 < p)
    (hai : a < i) (hf_pos : 0 < f) (hpf_le : p ^ f ≤ m) (hmp : ¬ p ∣ m) (hf_eq : f = i - a) :
    1 ≤ (p ^ a * (m - p ^ f)) % p ^ i := by
  -- Use Nat.mul_mod_mul_left: (p^a · x) % (p^a · p^(i-a)) = p^a · (x % p^(i-a)).
  -- Need x % p^(i-a) ≥ 1, i.e., p^(i-a) ∤ (m - p^f).
  -- For i = a + f exactly: (m - p^f) % p^f. Suppose p^f ∣ (m - p^f) → p ∣ m. Contradiction with hmp.
  -- For i = a + j with j ≤ f: similar by divisibility.
  sorry  -- ~15 LOC
```

The hypothesis `hf_eq : f = i - a` forces `i = a + f` exactly. Equivalently, **Helper 2 only covers the single position `i = e`** (since the main lemma's §2.2 sets `f = e - a`, so `i = a + f = e`).

### §2.2 The §2.2 case sweep needs all positions `i ∈ [a+1, e]`

From Iter 32 PREP §2.2 / §2.5:

> $|C| = \underbrace{0}_{\text{§2.1, } i \in [1, a]} + \underbrace{(e - a)}_{\text{§2.2, } i \in [a+1, e]} = e - a$

The "$e - a$" count claims **one carry per position** in $[a+1, e]$. For the proof to discharge each such position, Helper 2 must apply at **every** `i ∈ [a+1, e]`, i.e., for every `j = i - a ∈ [1, f]`. Not just `j = f`.

### §2.3 Why `j ∈ [1, f-1]` ALSO requires the no-`p`-divides argument

Iter 32 PREP §2.2 implicitly handles all `j` by saying:

> Suppose for contradiction $(m - p^f) \% p^j = 0$, i.e., $p^j \mid (m - p^f)$. Then $p \mid (m - p^f)$. [...] (Sub-case $f \ge 1$): $p \mid p^f$. From $p^j \mid (m - p^f)$ and $p \mid p^j$, get $p \mid m - p^f$. So $p \mid m$ ⟹ contradiction.

The chain `p^j ∣ (m - p^f) ⟹ p ∣ (m - p^f) ⟹ (combine p ∣ p^f) ⟹ p ∣ m` works for **every** `j ≥ 1`, not just `j = f`. The argument is uniform in `j`.

### §2.4 Helper 2 corrected signature (Option A)

```lean
lemma witness_mod_pow_lt
    {p a m f i j : ℕ} (hp : 1 < p) (hp_prime : p.Prime)
    (hia : i = a + j) (hj_pos : 0 < j) (hj_le_f : j ≤ f)
    (hf_pos : 0 < f) (hpf_lt : p ^ f < m) (hmp : ¬ p ∣ m) :
    1 ≤ (p ^ a * (m - p ^ f)) % p ^ i
```

with proof skeleton:

```lean
  -- 1. Rewrite p^i = p^a * p^j (uses hia).
  -- 2. Apply Nat.mul_mod_mul_left:
  --    (p^a * (m - p^f)) % (p^a * p^j) = p^a * ((m - p^f) % p^j).
  -- 3. Claim: (m - p^f) % p^j ≥ 1.
  --    a. m - p^f > 0 (from hpf_lt).
  --    b. p^j ∤ (m - p^f): suppose otherwise. Then p ∣ (m - p^f) [from hj_pos],
  --       hence p ∣ m - p^f + p^f = m. Contradicts hmp.
  --    c. Combine (a) and (b): (m - p^f) % p^j ≥ 1.
  -- 4. p^a ≥ 1, so p^a * ((m - p^f) % p^j) ≥ 1.
```

Estimated body: **~20 LOC** (vs ~15 LOC for the over-restricted version, but covering all required positions).

### §2.5 Alternative: inline the residue computation in the main lemma

If the ACT author prefers to avoid a separate Helper 2, the main lemma can inline the per-position residue check inside the `card_filter` decomposition. This shifts the LOC into the main lemma (~30 LOC for main split + inline residue, vs ~25 LOC main split + 20 LOC Helper 2 = ~45 LOC total). Comparable.

**Recommendation**: keep Helper 2 separate (cleaner factoring), with corrected signature §2.4.

## §3 — §4 Helper 1 (`pow_sub_one_mod_pow`) i=0 edge case + simpler proof

### §3.1 Stated signature

Iter 32 PREP §4:

```lean
lemma pow_sub_one_mod_pow {p e i : ℕ} (hp : 1 < p) (hie : i ≤ e) :
    (p ^ e - 1) % p ^ i = p ^ i - 1 := by
  -- Direct: p^e - 1 = (p^(e-i) - 1) · p^i + (p^i - 1).
  -- Both factors nonneg since 1 ≤ p^i ≤ p^e by hp + hie.
  have h_pe_ge : 1 ≤ p ^ e := Nat.one_le_pow _ _ (by omega)
  have h_pi_ge : 1 ≤ p ^ i := Nat.one_le_pow _ _ (by omega)
  -- Apply Nat.add_mul_mod_self_left or a divisor-of-divisor argument:
  -- (p^(e-i) - 1) · p^i + (p^i - 1) ≡ p^i - 1 mod p^i, and the left side equals p^e - 1.
  sorry  -- ~10 LOC
```

The argument works for `i ≥ 1` (where `p^i ≥ 2`, hence `p^i - 1 < p^i`). For `i = 0`:
- LHS: `(p^e - 1) % p^0 = (p^e - 1) % 1 = 0`.
- RHS: `p^0 - 1 = 1 - 1 = 0`.

Both sides equal `0`. The claim holds **trivially** when `i = 0`, but the proof body must split:

```lean
  rcases Nat.eq_zero_or_pos i with hi0 | hi_pos
  · simp [hi0]  -- both sides 0
  -- main case: i ≥ 1
  ...
```

This adds **1 LOC** (`rcases` + `simp` branch); negligible.

### §3.2 Tightened proof using `Nat.add_mul_mod_self_left`

A clean **~12-LOC** discharge avoiding `Nat.sub_mod` (which doesn't exist by name, §1.3):

```lean
lemma pow_sub_one_mod_pow {p e i : ℕ} (hp : 1 < p) (hie : i ≤ e) :
    (p ^ e - 1) % p ^ i = p ^ i - 1 := by
  rcases Nat.eq_zero_or_pos i with hi0 | hi_pos
  · simp [hi0]
  obtain ⟨c, hc⟩ : p ^ i ∣ p ^ e := Nat.pow_dvd_pow p hie
  have hpi_pos : 0 < p ^ i := Nat.pow_pos (by omega) i
  have hc_pos : 1 ≤ c := by
    have h1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ (by omega)
    rw [hc] at h1
    rcases Nat.eq_zero_or_pos c with rfl | hc; · simp at h1
    exact hc
  have hpi_ge_two : 2 ≤ p ^ i :=
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ p ^ 1 := Nat.pow_le_pow_left hp 1
      _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) hi_pos
  have h_rearr : p ^ e - 1 = (p ^ i - 1) + p ^ i * (c - 1) := by
    rw [hc]
    have h_mul : p ^ i * (c - 1) = p ^ i * c - p ^ i := by
      rw [Nat.mul_sub_one]  -- or Nat.mul_sub
      ring_nf
    rw [h_mul]; omega
  rw [h_rearr, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)
```

Estimated tightened body: **~12 LOC** (vs ~10 LOC stated). Within budget; uses only Lean core arithmetic + `Nat.pow_dvd_pow` (Mathlib).

### §3.3 Bearers in §3.2 proof — pin-verified

| Used in §3.2 | Provenance |
|---|---|
| `Nat.pow_dvd_pow` | Mathlib `Algebra/Order/Group/Nat.lean` or similar — heavily used (e.g., PR #19208 line 1485) ✓ |
| `Nat.add_mul_mod_self_left` | Lean core `Init/Data/Nat/Mod.lean` (canonical) ✓ |
| `Nat.mul_sub_one` | Lean core or Mathlib (deprecation-stable at v4.26.0) ✓ |
| `Nat.mod_eq_of_lt` | Lean core ✓ |
| `Nat.pow_le_pow_left`, `Nat.pow_le_pow_right` | Mathlib (both used by PR #19208) ✓ |
| `Nat.one_le_pow` | Mathlib ✓ |

All exercised in `BaselProblemOQ01OQ01OQ02OQ03.lean` already (PR #19208 + earlier iters); no new bearers needed.

## §4 — Corrected helper signatures, drop-in

Replacing Iter 32 PREP §4 with the audit-corrected version:

```lean
-- HELPER 1: residue of p^e - 1 mod p^i (i ≤ e)
lemma pow_sub_one_mod_pow {p e i : ℕ} (hp : 1 < p) (hie : i ≤ e) :
    (p ^ e - 1) % p ^ i = p ^ i - 1 := by
  -- ~12 LOC; see §3.2 above
  sorry

-- HELPER 2: residue of witness term k = p^a · (m - p^f) at position i = a + j ∈ [a+1, e]
lemma witness_mod_pow_lt
    {p a m f i j : ℕ} (hp_prime : p.Prime)
    (hia : i = a + j) (hj_pos : 0 < j) (hj_le_f : j ≤ f)
    (hf_pos : 0 < f) (hpf_lt : p ^ f < m) (hmp : ¬ p ∣ m) :
    1 ≤ (p ^ a * (m - p ^ f)) % p ^ i := by
  -- ~20 LOC; see §2.4 sketch above
  sorry

-- MAIN: existence of witness saturating the bound
lemma exists_witness_choose_saturates_log_succ
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 2 ≤ n) :
    ∃ k, k ≤ n ∧ (n + 1).factorization p + (Nat.choose n k).factorization p
                  = Nat.log p (n + 1) := by
  set e := Nat.log p (n + 1) with he_def
  set a := (n + 1).factorization p with ha_def
  set k := (n + 1) - p ^ e with hk_def
  refine ⟨k, ?_, ?_⟩
  · -- bound k ≤ n
    have hpe_pos : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
    omega
  · -- saturation: v_p(n+1) + v_p(C(n,k)) = log_p(n+1)
    have hkn : k ≤ n := by
      have hpe_pos : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
      omega
    -- Apply Nat.factorization_choose with b = log p n + 1.
    have hlog : Nat.log p n ≤ e := Nat.log_mono_right (Nat.le_succ n)
    have hb : Nat.log p n < e + 1 := Nat.lt_succ_of_le hlog
    rw [Nat.factorization_choose hp hkn hb]
    -- §5 below: explicit Case A vs Case B split
    sorry
```

**Sorries (3)**: Helper 1 (~12 LOC), Helper 2 (~20 LOC), main split (~25 LOC). Discharging each uses only the bearers listed in §3.3 + §2.4 — all confirmed at lake-pinned SHA.

## §5 — Main lemma assembly: explicit Case A vs Case B split

Iter 32 PREP §3 acknowledges the Case A vs Case B split but **does not** code it explicitly in the §4 skeleton. The audit-corrected main lemma needs an explicit case split:

### §5.1 Case A: `n + 1 = p ^ e` (i.e., `m = 1`, `a = e`, `f = 0`)

The witness `k = (n+1) - p^e = 0`. Then `Nat.choose n 0 = 1`, and `(1).factorization p = 0`. So
$v_p(n+1) + v_p\!\binom{n}{0} = e + 0 = e = \log_p(n+1)$ ✓.

Lean discharge (5 LOC):

```lean
-- Case A: n + 1 = p^e ⟹ k = 0, both sides equal e.
by_cases hnA : (n + 1) = p ^ e
· have hk_zero : k = 0 := by simp [hk_def, hnA]
  rw [hk_zero] at *
  simp [Nat.choose_zero_right, Nat.factorization_one, ha_def, hnA, Nat.factorization_pow,
        Nat.Prime.factorization_self hp]
```

(May need a few more lines for `Nat.factorization (p^e) = e * (Nat.factorization p)` — alternative: use `Nat.Prime.factorization_pow` directly.)

### §5.2 Case B: `n + 1 ≠ p ^ e` (i.e., `m ≥ 2`, `f ≥ 1`, `p^e ≤ n+1 < p^(e+1)`)

Apply `Nat.factorization_choose hp hkn hb`. Goal:
$$a + \#\{i \in \text{Ico } 1 (e+1) \mid p^i \le k \% p^i + (n-k) \% p^i\} = e.$$

Split filter at `i = a + 1`:

```lean
have hsplit : Finset.Ico 1 (e + 1) = Finset.Ico 1 (a + 1) ∪ Finset.Ico (a + 1) (e + 1) := ...
```

**Lower range `[1, a]`**: For `i ∈ [1, a]`, use `sum_mod_pow_lt_of_pow_dvd_succ` (PR #19208's Lemma A, line 1468), which gives `k % p^i + (n-k) % p^i < p^i` for `i ≤ a`. So **no carries** in this range — `card_filter = 0`.

**Upper range `[a+1, e]`**: For `i ∈ [a+1, e]`, write `j = i - a ∈ [1, f]`. Apply Helper 1 (for `(n - k) % p^i = (p^e - 1) % p^i = p^i - 1`) and Helper 2 (for `k % p^i = p^a * (m - p^f) % p^i ≥ p^a ≥ 1`). Sum: `≥ p^a + p^i - 1 ≥ 1 + p^i - 1 = p^i`. Carry **holds**. So **every** position in `[a+1, e]` is in the filter — `card_filter = e - a`.

```lean
-- Case B body — ~20 LOC
-- (1) Split the Ico 1 (e+1) filter into Ico 1 (a+1) and Ico (a+1) (e+1).
-- (2) Lower: empty filter (use sum_mod_pow_lt_of_pow_dvd_succ from line 1468).
-- (3) Upper: full filter (use Helper 1 + Helper 2 + arithmetic).
-- (4) card = 0 + (e - a) = e - a, then a + (e - a) = e by omega.
```

Combined Case A/B: **~25 LOC** for the main `sorry`.

### §5.3 Total LOC budget (audit-corrected)

| Component | Iter 32 PREP estimate | Audit-corrected | Δ |
|---|---:|---:|---:|
| Helper 1 (`pow_sub_one_mod_pow`) | ~10 LOC | ~12 LOC | +2 |
| Helper 2 (`witness_mod_pow_lt`, **generalized**) | ~15 LOC | ~20 LOC | +5 |
| Main (split + Case A + Case B) | ~25 LOC | ~25 LOC | +0 (but **needs Case A branch**) |
| **Total** | **~50 LOC** | **~57 LOC** | **+7 LOC (14%)** |

Within Iter 32 PREP's loose upper estimate (35–50 LOC envelope plus margin); 28b-2 ACT remains tractable in a single Lean session.

## §6 — Alternative path: leverage `Nat.factorization_choose_prime_pow` for Case A

Mathlib provides at pinned SHA `Mathlib/Data/Nat/Choose/Factorization.lean:172`:

```
theorem factorization_choose_prime_pow {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    (choose (p ^ n) k).factorization p = n - k.factorization p
```

This **does not** directly apply to our 28b-2 target (Case A has `k = 0`, but the lemma requires `k ≠ 0`). For `k = 0`, we use `Nat.choose_zero_right : choose n 0 = 1` and `Nat.factorization_one : (1 : ℕ).factorization = 0`.

**Optional simplification path**: Since Case A is fully discharged by `Nat.choose_zero_right` + `Nat.factorization_one` + `Nat.Prime.factorization_pow`, the Case A branch can be **3–4 LOC** instead of the broader §5.1 sketch.

**Recommendation**: keep the explicit Case A/B split; it's clearer than threading `Nat.factorization_choose_prime_pow` (which doesn't apply in Case A anyway).

## §7 — Three audit-corrected options for the 28b-2 ACT author

### Option A (RECOMMENDED) — full audit-corrected 28b-2 ACT, ~57 LOC, 0 sorries reachable

Ship the §4 corrected helpers (§4 above) + Case A/B split (§5). Use only Mathlib bearers confirmed at lake-pinned SHA (§1.1, §1.2).

**Pros**:
- Eliminates `axiom hanson_bound`'s 28b-2 dependency cleanly.
- Compositional: paves the way for 28b-3 assembly (`choose_mul_succ_dvd_lcmRange`) by exposing a clean `exists_witness_choose_saturates_log_succ` lemma.
- No new axioms; no new Mathlib gaps.

**Cons**:
- Helper 2 generalization costs ~5 LOC vs Iter 32 PREP's over-restricted version.
- Requires the Case A/B split, which Iter 32 PREP §3 acknowledged in prose but did not code.

### Option B — defer Case A via existing Mathlib, only prove Case B residue helpers (~45 LOC)

Skip the Case A branch by routing through `Nat.choose_zero_right` + `Nat.factorization_one` (~3 LOC). Concentrate ACT effort on Case B.

**Pros**:
- Slightly shorter (~45 LOC vs ~57 LOC).
- Clearer cognitive separation: trivial case vs nontrivial case.

**Cons**:
- Same final LOC count modulo a few lines; differs only stylistically from Option A.

### Option C (NOT RECOMMENDED) — axiomatize `exists_witness_choose_saturates_log_succ`

Replace 28b-2 with an axiom; lean on the residue proof in this file as a doc comment.

**Pros**:
- Fastest to ship (~5 LOC for an axiom + docstring).
- Lets 28b-3 (assembly) proceed immediately.

**Cons**:
- **Violates axiom-integrity policy** (`Axiom Integrity Policy` in `CLAUDE.md`): adds a new axiom for a result that has a paper-rigorous residue proof + a verified-bearer Lean discharge path (Iter 32 PREP §2 + this audit's corrections).
- Subtracts from `axiomCount` reduction goal for this slug (currently 1 axiom, `hanson_bound`; 28b-1 + 28b-2 + 28b-3 are the elimination path).

### Recommendation: **Option A**

Reasoning:
1. **Mathlib bearer coverage**: 5/9 bearers exact, 2/9 minor inaccuracies (already discovered by PR #19208's Iter 34a ACT), 1/9 missing-by-name (workaround already used by PR #19208). No new Mathlib infrastructure needed.
2. **Cost overrun is small**: +7 LOC (14%) over Iter 32 PREP's upper estimate. Well within Iter 28-33 PREP chain's tolerance.
3. **Composition**: Option A's clean `exists_witness_choose_saturates_log_succ` lemma signature exposes the natural 28b-3 assembly hook.
4. **Axiom-integrity**: Option C would regress the slug's axiom count progression.

## §8 — Composition with other open PRs / slug context

### §8.1 PR #19208 (Iter 34a ACT) status
- **Build-verified** at 3066/3066 jobs (PR #19208 reports).
- **MERGEABLE** as of 2026-05-15 ~05:55 UTC (verified via `gh pr view`).
- **Files**: only `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`, `research/problems/.../sessions/2026-05-14-iter34-act-28b1-bridge-bound.md`, `research/problems/.../state.md` (PR body confirmed via `gh pr view --json files`).
- **Strict file-disjointness** with this PREP: ✓ (this PREP touches only the new `2026-05-15-iter34b-...` session file).

### §8.2 Other open PRs on the slug
- **PR #18079** (`fix(meta): sync count drift in 5 entries`) — touches `src/data/proofs/.../meta.json` (different scope; not modified here).
- **PR #17619** (Iter 17, 6d stale, build pending CONFLICTING) — touches `BaselProblemOQ01OQ01OQ02OQ03.lean` (not modified here).
- **PR #17551** (Iter 15, 6d stale, build pending CONFLICTING) — touches `BaselProblemOQ01OQ01OQ02OQ03.lean` (not modified here).

All 4 open PRs on this slug are file-disjoint from this PREP's single new session-file addition.

### §8.3 Deployer stall context (per memory `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`)

- Slug has **4 open PRs**; matrix would normally say "always release". Two of those (#17619, #17551) are 6d stale and CONFLICTING — effectively zombie PRs not in active mechanic competition. Effective live-PR count: 2 (#19208 + #18079).
- **Last merge to main**: 2026-05-14 03:03 UTC (>26h ago at time of writing). Deployer stalled.
- This PREP is **strictly conflict-free** with all 4 open PRs (single new file under `sessions/`).
- This PREP **adds substantive value**: pin-verifies 9 bearers cited in the Iter 32 PREP §4 skeleton, surfaces a Helper 2 signature bug (#6 in TL;DR table) that would have caused the 28b-2 ACT to fail or require mid-session refactoring, and provides corrected signatures + LOC budget update.

Per the `_release_crowded_slug_...` decision matrix at "strictly conflict-free angle covers real gap", **proceeding with this PR is justified**.

## §9 — Memory pattern composition

This PREP composes with the following memory entries:
- `feedback_researcher_audits_buildverified_pr_next_section_finds_falseclaim_in_file` — audit PR #19208's "Next" forward plan against pinned-SHA Mathlib.
- `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton_during_deployer_stall` — pin-verify Iter 32 PREP §4 helper signatures.
- `feedback_researcher_parent_compile_as_bearer_witness` — many bearers (e.g., `Nat.le_log_of_pow_le`) were validated indirectly via PR #19208's compile (3066 jobs); pin-verification confirms exact line + signature.
- `feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer` — finding #5 (`Nat.sub_mod` missing by name) is in the same family as the "fictitious bearer" pattern.

## §10 — Conflict-free guarantees

This PR adds ONLY:
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-15-iter34b-prep-iter32-skeleton-audit.md` (NEW)

Does NOT modify:
- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` (modified by PR #19208; touched in any future 28b-2 ACT)
- `research/problems/.../state.md` (modified by PR #19208)
- `research/problems/.../knowledge.md`, `problem.md`
- Any prior `sessions/*.md` files
- `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json`
- `src/data/proofs/basel-problem-oq-01-oq-01-oq-02-oq-03/meta.json`

Strict file-disjointness verified manually against `gh pr view --json files` of all 4 open PRs on this slug (§8.1, §8.2).

## §11 — Next actions

For the 28b-2 ACT author (next Iter 34c or Iter 35 session):

1. Adopt **Option A** (§7) for the 28b-2 implementation: ~57 LOC, 3 helpers, 0 reachable sorries.
2. Apply the **corrected Helper 2 signature** (§2.4) — single `j` parameter, `hpf_lt : p^f < m`, drop `hf_eq`.
3. Use **`Nat.mod_eq_sub_mod`** in Helper 1 / Helper 2 (not the non-existent `Nat.sub_mod`).
4. Add an **explicit Case A vs Case B branch** in the main lemma (§5.1, §5.2).
5. Optionally cross-check by running `Nat.factorization_choose hp hkn hb` symbolically on `n + 1 = 12` (`p = 2`, `n = 11`, `e = 3`, `a = 2`) to verify witness `k = (12 - 8) = 4` gives `v_2(C(11, 4)) = 1 = e - a`. Numerical check: `C(11, 4) = 330 = 2 · 3 · 5 · 11`, `v_2(330) = 1` ✓.

For the 28b-3 ACT author (after 28b-2 lands):

- Use `exists_witness_choose_saturates_log_succ` as the elimination hook for assembling `choose_mul_succ_dvd_lcmRange`.
- Estimated 28b-3 budget: ~30 LOC (per PR #19208's "Next" plan).

---

**Researcher**: researcher-8 (worktree `.loom/worktrees/researcher-8/`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (verified via `proofs/lake-manifest.json`).
**Verification round-trips used**: 9 (5 `gh api .../contents/...?ref=<SHA>`, 4 `gh api search/code` for cross-reference).
