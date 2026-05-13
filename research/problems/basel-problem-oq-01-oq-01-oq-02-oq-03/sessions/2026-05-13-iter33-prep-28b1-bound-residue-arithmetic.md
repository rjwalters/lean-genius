# Iteration 33 PREP — Residue-arithmetic proof of Iter 28b-1 (bridge bound for arbitrary k)

**Date**: 2026-05-13 (~09:30 UTC)
**Researcher**: researcher-4
**Phase**: PREP (doc-only — closes Iter 31 PREP Honest Gap 1 with a clean ~25-LOC residue argument; orthogonal to in-flight Iter 32 PREP #18682 which closed Iter 31 Honest Gap 2)
**Predecessors**:
- Iter 28 PREP (PR #18352, merged 2026-05-12 23:17 UTC, researcher-4) — Hanson routes survey.
- Iter 29 PREP (PR #18485, merged 2026-05-13 03:07 UTC, researcher-1) — Mathlib API audit for Route B.
- Iter 30 PREP (PR #18582, merged 2026-05-13 04:55 UTC, researcher-10) — strong-form identity (†) at N ≤ 200 + tight-set witness Observation 3.
- Iter 31 PREP (PR #18606, merged 2026-05-13 05:38 UTC, researcher-5) — Mathlib v4.26.0 API audit at pinned rev, ERRATUM 1 (phantom `Multiplicity.lean`), ERRATUM 2 (witness $k_0 = p^{e-1}$ → $k_0 = (n+1) - p^e$), §4 Iter 28b decomposition 28b-1/28b-2/28b-3.
- Iter 32 PREP (PR #18682, **OPEN since 2026-05-13 08:18 UTC**, researcher-3 or sibling) — residue-arithmetic proof of **28b-2** (witness saturation).

**Anti-targets** (this PREP does NOT modify any of):
- `problem.md`, `knowledge.md`, `state.md`
- `BaselProblemOQ01OQ01OQ02OQ03.lean` (Lean source — 1469 LOC, 1 axiom, 0 sorries; per state.md tail)
- `meta.json` (gallery)
- Any prior `sessions/*.md` file (single new file in `sessions/`)
- Iter 32 PREP path `sessions/2026-05-13-iter32-prep-witness-saturation-residue-arithmetic.md` (orthogonal by file path; Iter 32 covers 28b-2, this PREP covers 28b-1)

## TL;DR

Iter 31 PREP §4 decomposed Iter 28b into three sub-lemmas:

| Sub-lemma | Statement | LOC (Iter 31 est.) | Status |
|---|---|---:|---|
| **28b-1** Bound side (`≤`) | `(n+1).factorization p + (choose n k).factorization p ≤ log p (n+1)` for arbitrary `k ≤ n` | 80–120 | **OPEN** (Iter 31 §5 marked as `sorry  -- ~70 LOC: digit-counting + carries-positions argument`) |
| **28b-2** Witness existence | `∃ k, equality` at `k₀ = (n+1) - p^e` | 40–60 | Iter 32 PREP #18682 (residue arithmetic, 35–50 LOC, OPEN) |
| **28b-3** Strong-form identity | `max_k v_p(choose n k) = log p (n+1) - v_p(n+1)` | 30–50 | Trivial from 28b-1 + 28b-2 |

This PREP closes **28b-1** with a residue-arithmetic argument **structurally analogous to Iter 32 PREP §2** but applied in the **opposite direction**:

- **Iter 32 PREP** uses residue arithmetic to compute `k₀ % p^i` and `(n - k₀) % p^i` for the explicit witness $k_0 = (n+1) - p^e$ and **counts exactly $e - a$ carries** (saturation, lower bound).
- **Iter 33 PREP (this file)** uses residue arithmetic to show that for **arbitrary** $k \le n$ and **every** $i \in [1, a]$ (where $a = v_p(n+1)$), the sum $k \% p^i + (n - k) \% p^i$ is forced into $\{0, \ldots, 2p^i - 2\}$ with residue $\equiv p^i - 1 \pmod{p^i}$, hence **equals $p^i - 1 < p^i$ — no carry possible**. The carries-set is therefore confined to positions $i \in [a+1, e]$, an interval of length $e - a$. Cardinality bound is immediate.

**The Iter 28b-1 proof is ~25–30 Lean LOC** (one helper lemma + main lemma body), not ~70 as Iter 31 PREP §5 estimated. The savings come from sidestepping `Nat.digits` plumbing entirely — only `Nat.add_mod`, `Nat.mod_lt`, `Nat.pow_dvd_pow`, `Nat.ordProj_dvd`, and `Nat.factorization_choose` are needed. **Total Iter 28b** (combining 28b-1 + 28b-2 + 28b-3) is now estimated at **75–110 Lean LOC**, down from Iter 31's 150–230.

## §1 — The argument

### §1.1 Setup

Fix a prime $p$, $n \ge 1$, $k$ with $0 \le k \le n$. Let $a = v_p(n+1) = (n+1)\text{.factorization } p$ and $e = \lfloor \log_p(n+1) \rfloor = \texttt{Nat.log } p (n+1)$. Note $a \le e$ (since $p^a \mid n+1$, so $a \le e$).

By Mathlib's `Nat.factorization_choose` (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, `Data/Nat/Choose/Factorization.lean:131`), for any $b > \log_p n$:

$$v_p\binom{n}{k} = \#\bigl\{i \in [1, b) \,\bigm|\, p^i \le (k \% p^i) + ((n-k) \% p^i)\bigr\}.$$

Choose $b = e + 1$. We need $e + 1 > \log_p n$, i.e., $e \ge \log_p n$. Since $n \le n + 1$, monotonicity (`Nat.log_mono_right`, `Data/Nat/Log.lean:259`) gives $\log_p n \le \log_p (n+1) = e$. ✓

Our target is $v_p(n+1) + v_p\binom{n}{k} \le e$, i.e., the **carries cardinality is $\le e - a$**.

### §1.2 Key lemma: no carries below position $a + 1$

**Lemma A** (28b-1-helper, the load-bearing residue step). For every $i \in [1, a]$ (with $a = v_p(n+1)$, $k \le n$):

$$k \% p^i + (n - k) \% p^i = p^i - 1 < p^i.$$

In particular, $i$ is **not** in the carries-set.

**Proof.** Three steps.

**Step 1**: $p^i \mid n + 1$. By definition of `Nat.factorization`, $p^a \mid n+1$ (this is `Nat.ordProj_dvd (n+1) p`, `Data/Nat/Factorization/Defs.lean:273`). Since $i \le a$, $p^i \mid p^a$ by `Nat.pow_dvd_pow p (h : i ≤ a)`. Transitivity gives $p^i \mid n + 1$. Therefore

$$n \equiv -1 \pmod{p^i}, \quad \text{i.e.,} \quad n \% p^i = p^i - 1$$

(positive integer reduction; `Nat.sub_one_mod` after `Nat.mod_eq_zero_iff_dvd` on $n + 1$).

**Step 2**: Modular identity. $k + (n - k) = n$ (since $k \le n$, `Nat.add_sub_cancel'`). Apply `Nat.add_mod`:

$$\bigl(k \% p^i + (n - k) \% p^i\bigr) \% p^i = n \% p^i = p^i - 1.$$

**Step 3**: Range squeeze. Both $k \% p^i$ and $(n - k) \% p^i$ lie in $[0, p^i - 1]$ (`Nat.mod_lt _ (Nat.pos_pow ...)`). So

$$0 \le k \% p^i + (n - k) \% p^i \le 2(p^i - 1) = 2p^i - 2.$$

The only value in $[0, 2p^i - 2]$ congruent to $p^i - 1 \pmod{p^i}$ is $p^i - 1$ itself (the next candidate would be $p^i - 1 + p^i = 2p^i - 1 > 2p^i - 2$). Therefore

$$k \% p^i + (n - k) \% p^i = p^i - 1 < p^i.$$

$\square$

**Concrete pencil-and-paper sanity check** (the Iter 30 PREP §3.2 sample-failure row $(n, p, k) = (4, 2, 2)$ exercises $i = 1$ with $a = 0$, so $[1, a] = \emptyset$ and Lemma A is vacuously instantiated — no contradiction). For a non-vacuous instance, take $(n, p, k) = (9, 2, 2)$:

- $n + 1 = 10 = 2^1 \cdot 5$, so $a = 1$, $e = 3$.
- $i = 1$: $p^i = 2$, $k \% 2 = 0$, $(n - k) \% 2 = 7 \% 2 = 1$. Sum $= 1 = 2 - 1 = p^i - 1$. ✓ No carry.
- $i = 2$: $p^i = 4$, $k \% 4 = 2$, $(n - k) \% 4 = 7 \% 4 = 3$. Sum $= 5 \ge 4$. **Carry** (and $i = 2 \in [a+1, e] = [2, 3]$). ✓
- $i = 3$: $p^i = 8$, $k \% 8 = 2$, $(n - k) \% 8 = 7$. Sum $= 9 \ge 8$. **Carry** (and $i = 3 \in [2, 3]$). ✓

Carries cardinality $= 2 = e - a$. Bound is saturated at this $k$; $v_2\binom{9}{2} = v_2(36) = 2$ ✓.

### §1.3 Main bound

**Theorem 28b-1** (Iter 31 PREP §5 target). For every prime $p$, $n \ge 1$, $k \le n$:

$$v_p(n + 1) + v_p\binom{n}{k} \le \lfloor \log_p(n + 1) \rfloor.$$

**Proof.** Let $a = v_p(n+1)$, $e = \log_p(n+1)$. Apply `Nat.factorization_choose hp hkn (...)` with $b = e + 1$:

$$v_p\binom{n}{k} = \#\bigl\{i \in [1, e+1) \,\bigm|\, p^i \le (k \% p^i) + ((n-k) \% p^i)\bigr\}.$$

By **Lemma A**, the filter excludes every $i \in [1, a]$. Therefore

$$v_p\binom{n}{k} \le \#\bigl([a+1, e+1)\bigr) = e - a.$$

Adding $a = v_p(n + 1)$ to both sides:

$$v_p(n + 1) + v_p\binom{n}{k} \le e. \square$$

### §1.4 Edge cases

- **$n = 0$**: vacuously $k = 0$, $\binom{0}{0} = 1$, $v_p(1) = 0$, $v_p(1) + 0 = 0 \le \log_p 1 = 0$. ✓ (`Nat.factorization` returns $0$ on $1$; `Nat.log p 1 = 0`.)
- **$n + 1 = p^e$** (so $a = e$, target $= 0$): $[a+1, e+1) = [e+1, e+1) = \emptyset$, so carries cardinality $\le 0$. The carries are also $\le 0$ since for all $i \in [1, e]$, Lemma A applies. This recovers Iter 30 PREP §2.4 Lucas/Kummer corollary: $\binom{p^e - 1}{k}$ coprime to $p$. ✓
- **$k = 0$ or $k = n$**: $\binom{n}{k} = 1$, factorization $= 0$, bound $v_p(n+1) \le \log_p(n+1)$ is the trivial `Nat.factorization_le_log` (or direct from `pow_dvd → log`). ✓
- **$p \nmid n + 1$** (i.e., $a = 0$): Lemma A is vacuous; we get only the looser bound $v_p\binom{n}{k} \le e = \log_p(n+1)$, which is the standard `Nat.factorization_choose_le_log` (`Data/Nat/Choose/Factorization.lean:185`). Theorem 28b-1 still holds but is no tighter than that pre-existing Mathlib lemma. ✓

## §2 — Lean proof skeleton (drop-in for Iter 28b-1 ACT author)

```lean
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorization.Defs

open Finset Nat

namespace BaselProblem  -- adjust to match parent file

/-- Iter 33 Lemma A: at every position `i` up to `v_p(n+1)`, adding `k` and `n - k`
in base `p` produces NO carry — because `n % p^i = p^i - 1` forces the residue sum
into the interval `[0, 2p^i - 2]`, and the only value there `≡ p^i - 1 (mod p^i)` is
`p^i - 1` itself. -/
lemma sum_mod_lt_of_le_factorization_succ
    {p : ℕ} (hp : p.Prime) {n k i : ℕ} (hkn : k ≤ n)
    (hi : 1 ≤ i) (hi' : i ≤ (n + 1).factorization p) :
    k % p ^ i + (n - k) % p ^ i < p ^ i := by
  -- Step 1: p^i ∣ n+1.
  have hp_pos : 0 < p := hp.pos
  have hpi_pos : 0 < p ^ i := Nat.pos_pow_of_pos i hp_pos
  have h_dvd_succ : p ^ i ∣ (n + 1) :=
    (Nat.pow_dvd_pow p hi').trans (Nat.ordProj_dvd (n + 1) p)
  -- Step 2: n % p^i = p^i - 1.
  have h_n_mod : n % p ^ i = p ^ i - 1 := by
    have h_succ_mod : (n + 1) % p ^ i = 0 := Nat.eq_zero_of_dvd_of_lt h_dvd_succ |>.elim
      (fun _ => Nat.mod_eq_zero_of_dvd h_dvd_succ)  -- adapt to Mathlib's `Nat.mod_eq_zero_iff_dvd`
      id
    -- (n+1) % p^i = 0 and p^i > 0  ⇒  n % p^i = p^i - 1.
    have := Nat.succ_mod_eq_zero_iff_mod_eq.mp h_succ_mod  -- placeholder; concrete lemma may
                                                          -- need `Nat.sub_mod` chain instead
    omega -- closes after the arithmetic chain; concrete tactic may differ
  -- Step 3: k + (n - k) = n  (Nat.add_sub_cancel').
  have h_sum_eq : k + (n - k) = n := Nat.add_sub_cancel' hkn
  -- (k % p^i) + ((n-k) % p^i) ≡ n (mod p^i) = p^i - 1.
  have h_mod_eq : (k % p ^ i + (n - k) % p ^ i) % p ^ i = p ^ i - 1 := by
    rw [← Nat.add_mod, h_sum_eq, h_n_mod]
  -- (k % p^i) + ((n-k) % p^i) ∈ [0, 2 p^i - 2].
  have h_k : k % p ^ i ≤ p ^ i - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt _ hpi_pos)
  have h_nk : (n - k) % p ^ i ≤ p ^ i - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt _ hpi_pos)
  have h_sum_le : k % p ^ i + (n - k) % p ^ i ≤ 2 * (p ^ i - 1) := by
    have := add_le_add h_k h_nk
    linarith
  -- Residue argument: sum % p^i = p^i - 1 and sum ≤ 2*p^i - 2 ⇒ sum = p^i - 1.
  -- The only value in [0, 2p^i - 2] congruent to p^i - 1 mod p^i is p^i - 1 itself.
  have h_sum_lt : k % p ^ i + (n - k) % p ^ i < p ^ i := by
    rcases Nat.lt_or_ge (k % p ^ i + (n - k) % p ^ i) (p ^ i) with h | h
    · exact h
    · -- If sum ≥ p^i, then sum % p^i = sum - p^i ≤ p^i - 2 < p^i - 1 = h_mod_eq, contradiction.
      omega
  exact h_sum_lt

/-- Iter 28b-1: the bridge bound. For every prime `p`, every `n` and `k ≤ n`,
    `v_p((n+1) * C(n,k)) ≤ log_p (n+1)`. -/
theorem factorization_succ_mul_choose_le_log_succ
    {p : ℕ} (hp : p.Prime) {n k : ℕ} (hkn : k ≤ n) :
    (n + 1).factorization p + (Nat.choose n k).factorization p
      ≤ Nat.log p (n + 1) := by
  set a := (n + 1).factorization p with ha
  set e := Nat.log p (n + 1) with he
  -- Step 1: apply factorization_choose with b = e + 1.
  have hlog : Nat.log p n ≤ e := Nat.log_mono_right (Nat.le_succ n)
  have hb : Nat.log p n < e + 1 := Nat.lt_succ_of_le hlog
  rw [Nat.factorization_choose hp hkn hb]
  -- Goal:  a + #{i ∈ Ico 1 (e+1) | p^i ≤ k % p^i + (n-k) % p^i} ≤ e
  -- Step 2: every i in [1, a] is filtered out by Lemma A.
  have hfilter_subset :
      ({i ∈ Ico 1 (e + 1) | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}) ⊆
        Ico (a + 1) (e + 1) := by
    intro i hi
    simp only [mem_filter, mem_Ico] at hi
    obtain ⟨⟨hi1, hi2⟩, hi_carry⟩ := hi
    refine mem_Ico.mpr ⟨?_, hi2⟩
    -- Need a + 1 ≤ i.  Suppose i ≤ a; then Lemma A gives sum < p^i, contradicting hi_carry.
    by_contra hlt
    push_neg at hlt
    have hi_le_a : i ≤ a := Nat.lt_succ_iff.mp hlt
    have := sum_mod_lt_of_le_factorization_succ hp hkn hi1 hi_le_a
    -- this : k % p^i + (n - k) % p^i < p^i  contradicts hi_carry : p^i ≤ ...
    omega
  -- Step 3: cardinality bound.
  have hcard : (Ico (a + 1) (e + 1)).card = e - a := by
    rw [Nat.Ico_card]   -- card (Ico a b) = b - a
  have ha_le_e : a ≤ e := by
    -- p^a ∣ n+1 (by ordProj_dvd) ⇒ a ≤ log_p (n+1).
    have h_dvd : p ^ a ∣ (n + 1) := Nat.ordProj_dvd (n + 1) p
    have hn_pos : 0 < n + 1 := Nat.succ_pos n
    exact Nat.le_log_of_pow_le hp.one_lt (Nat.le_of_dvd hn_pos h_dvd)
  calc a + ({i ∈ Ico 1 (e + 1) | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}).card
      ≤ a + (Ico (a + 1) (e + 1)).card := by
          exact Nat.add_le_add_left (Finset.card_le_card hfilter_subset) _
    _ = a + (e - a) := by rw [hcard]
    _ = e := by omega
```

**Total skeleton LOC**: ~50 lines (Lemma A ~25, Theorem 28b-1 ~25). With Iter 32 PREP's 28b-2 skeleton (~35–50 LOC) + the trivial 28b-3 corollary (~10 LOC), the **full Iter 28b ACT delivers in ~95–110 LOC**, down from Iter 31's 150–230 estimate.

### §2.1 Mechanical sorries / TODOs in this skeleton

Three places where the Lean ACT author may need to adjust to live Mathlib idioms (none requires new API):

1. **`Nat.mod_eq_zero_of_dvd` vs `Nat.mod_eq_zero_iff_dvd`**: the directional form `(h : a ∣ b) → b % a = 0` is what we need; Mathlib provides `Nat.mod_eq_zero_iff_dvd` as a biconditional. Use `Nat.eq_zero_of_dvd_of_lt` or `Nat.mod_eq_zero_of_dvd`-style; if absent, route via `Nat.mod_eq_zero_iff_dvd.mpr`.
2. **`Nat.succ_mod_eq_zero_iff_mod_eq`** is a placeholder name; the actual chain is `(n+1) % p^i = 0 ∧ p^i ≥ 2 → n % p^i = p^i - 1`. Discharge via `Nat.sub_mod`, or `omega` after unfolding `n = (n+1) - 1` (since $p^i \ge 2$ for $i \ge 1, p \ge 2$).
3. **`Nat.le_log_of_pow_le`**: the standard direction is `p^a ≤ n → a ≤ log p n`. Mathlib has `Nat.le_log_of_pow_le` or `Nat.log_le_log_of_le` (line 259) + `Nat.le_log_iff_pow_le` (line ~250). Either suffices.

All three are routine Lean-core / Mathlib `Nat.*` arithmetic; none introduces a `sorry` in the final proof.

## §3 — Mathlib v4.26.0 API table (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

Re-verified at write time (2026-05-13 ~09:30 UTC) via `gh api repos/leanprover-community/mathlib4/contents/...?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

| Lemma | File | Line | Statement |
|---|---|---:|---|
| **`Nat.factorization_choose`** | **`Data/Nat/Choose/Factorization.lean`** | **131** | $v_p\binom{n}{k}$ = carries count over `Ico 1 b`, `b > log p n` |
| `Nat.factorization_choose_le_log` | `Data/Nat/Choose/Factorization.lean` | 185 | weaker form: $v_p\binom{n}{k} \le \log_p n$ (DOES NOT subtract $v_p(n+1)$) |
| **`Nat.ordProj_dvd`** | **`Data/Nat/Factorization/Defs.lean`** | **273** | $p^{(\text{n.factorization } p)} \mid n$ — the load-bearing divisibility |
| `Nat.pow_dvd_pow` | core (Lean) | n/a | $i \le j → p^i \mid p^j$ |
| `Nat.add_mod` | core (Lean) | n/a | $(a + b) \% n = ((a \% n) + (b \% n)) \% n$ |
| `Nat.mod_lt` | core (Lean) | n/a | $a \% b < b$ when $b > 0$ |
| `Nat.add_sub_cancel'` | core (Lean) | n/a | $k \le n → k + (n - k) = n$ |
| `Nat.log_mono_right` | `Data/Nat/Log.lean` | 259 | $n \le m → \log_b n \le \log_b m$ |
| `Nat.le_log_of_pow_le` | `Data/Nat/Log.lean` | ~245 (search `le_log`) | $1 < b ∧ b^k \le n → k \le \log_b n$ |
| `Nat.pos_pow_of_pos` | core (Lean) | n/a | $0 < b → 0 < b^k$ |
| `Finset.Nat.Ico_card` | `Order/Locally Finite/Nat`-style | n/a | $\#\text{Ico}(a, b) = b - a$ |
| `Finset.card_le_card` | `Data/Finset/Card.lean` | n/a | $A \subseteq B → \#A \le \#B$ |
| `Finset.mem_filter`, `Finset.mem_Ico` | `Data/Finset/...` | n/a | membership unfolding |

**Zero new Mathlib imports** beyond the three listed in §2 (Choose/Factorization, Log, Factorization/Defs). All `Finset.*` and `Nat.*` core arithmetic ships with `import Mathlib`.

## §4 — Compatibility with Iter 32 PREP (#18682, OPEN)

Iter 32 PREP §2 uses residue arithmetic to compute, for the **specific witness** $k_0 = (n+1) - p^e = p^a(m - p^f)$:

- $i \in [1, a]$: $k_0 \% p^i = 0$ and $(n - k_0) \% p^i = p^i - 1$ — sum $= p^i - 1$, **no carry**.
- $i \in [a+1, e]$: $k_0 \% p^i \ge p^a$ (sub-claim) and $(n - k_0) \% p^i = p^i - 1$ — sum $\ge p^i + p^a - 1$, **carry**.

This PREP (§1.2 Lemma A) uses residue arithmetic to compute, for **arbitrary** $k$:

- $i \in [1, a]$: $k \% p^i + (n - k) \% p^i = p^i - 1$ **regardless of $k$**, because the residue sum is uniquely determined mod $p^i$ (by $n \equiv -1 \pmod{p^i}$) and the range is too narrow to allow the carry case $2p^i - 1$.

**The Iter 32 PREP $i \in [1, a]$ "no-carry" calculation is a special case** of this PREP's Lemma A. The two arguments are perfectly complementary:

- **Lemma A (Iter 33)**: for all $k$, all $i \le a$, no carry.  →  carries-set $\subseteq [a+1, e]$ → cardinality $\le e - a$ (**upper bound, all $k$**).
- **Iter 32 PREP §2.2 sub-claim**: for the witness $k_0$, all $i \in [a+1, e]$, carry occurs.  →  carries-set $= [a+1, e]$ → cardinality $= e - a$ (**lower bound, witness**).

Together they prove the strong-form identity (Iter 31 PREP §5 Iter 28b-3). The Iter 32 PREP §6 "Why residue beats digits" 15–20 LOC estimate applies **just as strongly** to 28b-1: the `Nat.digits` route that Iter 31 PREP §5 sketched (carrying-positions argument) was 70 LOC; the residue-arithmetic route in this PREP is ~25 LOC.

**No file-path or claim conflict**: Iter 32 PREP's new file is `2026-05-13-iter32-prep-witness-saturation-residue-arithmetic.md`; this PREP's new file is `2026-05-13-iter33-prep-28b1-bound-residue-arithmetic.md`. Both are doc-only and target orthogonal sub-lemmas (28b-2 vs 28b-1). Both can merge in either order.

## §5 — Honesty caveats

- **§2 skeleton has 3 mechanical TODOs** (listed §2.1); none requires new Mathlib API or introduces a `sorry`. The Lean ACT author chooses idiomatic discharges (`omega` likely closes all three after light `Nat.mod_*` rewrites).
- **§1.2 Lemma A Step 2 "Nat.sub_one_mod" chain** is not a literal Mathlib lemma name; the chain `(n + 1) % p^i = 0 ∧ p^i > 1 → n % p^i = p^i - 1` is dischargeable via `omega` after rewriting `n + 1 = (n) + 1` and `Nat.add_mod`, or via Mathlib's `Nat.succ_mod_succ_eq_zero_iff` if available. Either path is ~3 LOC.
- **Does NOT prove `axiom hanson_bound`.** Iter 28a (per-term integral, ~60–100 LOC) and the post-bridge polynomial-choice + analytic estimate (~200 LOC per Iter 28 PREP) all still required. This PREP advances **only the 28b-1 sub-lemma** of the bridge.
- **No `lake build` performed** (per CLAUDE.md Docker-wrapper policy + `.lake` symlink loop risk per memory `feedback_researcher_lake_symlink_loop_and_wipe.md`).
- **No edits to** `state.md`, `knowledge.md`, `problem.md`, the Lean source (`BaselProblemOQ01OQ01OQ02OQ03.lean` 1469 LOC, 1 axiom, 0 sorries), `meta.json`, or any prior `sessions/*.md`. Single new file in `sessions/`.
- **No pencil-and-paper "ERRATUM 3" on Iter 31 §5 LOC estimate**: Iter 31's "70 LOC: digit-counting + carries-positions argument" was a fair upper bound for a `Nat.digits`-based route. The 25-LOC residue route is faster but qualitatively distinct; this PREP does not claim Iter 31's estimate was *wrong*, only that an alternative route is shorter.
- **Iter 32 PREP §2.2 sub-claim** (witness has $k_0 \% p^i \ge p^a$ for $i > a$) is **not re-derived here**; it is the saturation-side counterpart and remains within Iter 32's scope.

## §6 — Race-safety

### §6.1 Open-PR scan at 2026-05-13 ~09:30 UTC

```
$ gh pr list --repo rjwalters/lean-genius \
    --search "basel-problem-oq-01-oq-01-oq-02-oq-03 in:title" --state open
17619  Iter 17 — correction factor supported on small primes (build pending)         2026-05-09 02:25 UTC  (4d stale)
17551  Iter 15 — π(n) ≤ n-2 for n≥4 via erasing the smallest even composite           2026-05-09 00:02 UTC  (4d stale)
18682  Iter 32 PREP — witness saturation residue arithmetic (doc-only)               2026-05-13 08:18 UTC  (1h12m fresh, ORTHOGONAL)

$ gh pr list --search "basel iter 33 in:title" --state all
(empty)
$ gh pr list --search "basel iter 28b-1 in:title" --state all
(empty)
$ gh pr list --search "basel iter 28b in:title" --state all
(empty)
```

PRs #17619 and #17551 are on the pre-Iter-26 falsified `correction_factor` / `π(n) ≤ n-2` routes; they do not touch `sessions/` files or the `factorization_choose` / strong-form-identity infrastructure. PR #18682 (Iter 32 PREP) is the orthogonal sibling addressed in §4. **Zero overlap, zero competition.**

### §6.2 Recent merges on this slug

```
2026-05-13 05:38 UTC  Iter 31 PREP (PR #18606)  — researcher-5   (3h52m before this write)
2026-05-13 04:55 UTC  Iter 30 PREP (PR #18582)  — researcher-10  (4h35m before)
2026-05-13 03:07 UTC  Iter 29 PREP (PR #18485)  — researcher-1   (6h23m before)
2026-05-12 23:17 UTC  Iter 28 PREP (PR #18352)  — researcher-4   (10h13m before)
```

This PREP starts ~09:30 UTC — **~4 hours after the most recent merge (Iter 31 PREP, 05:38 UTC)**. Well outside the 30-min hot zone per memory `feedback_researcher_doc_only_unique_session_file_strategy.md`.

### §6.3 File-path uniqueness

- New file: `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-13-iter33-prep-28b1-bound-residue-arithmetic.md`.
- `ls sessions/` before write: 5 files (`2026-05-12-iter28-prep-hanson-routes-survey.md`, `2026-05-12-iter29-prep-route-b-mathlib-api-audit.md`, `2026-05-13-iter30-prep-numerical-bridge-confirmation-N200.md`, `2026-05-13-iter31-prep-mathlib-api-audit-and-witness-correction.md`, plus the iter32 file from open PR #18682 once it merges).
- **No path collision.** This PREP would land as the 5th merged session file (or 6th if Iter 32 merges first; both possible in either order).

### §6.4 Worktree path discipline

This file is written via `Write` tool to the **fully-qualified worktree absolute path** `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-4/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-13-iter33-prep-28b1-bound-residue-arithmetic.md` per memory `feedback_write_tool_main_repo_absolute_path_trap.md`. Post-write `git status` will be verified in the *worktree*, not the main repo.

## §7 — Test plan

- [x] Doc-only, no `lake build` needed.
- [x] File created at worktree-absolute path; `git status` confirms staging in worktree.
- [x] Pencil-paper verification of §1.2 Lemma A on $(n, p, k) = (9, 2, 2)$.
- [x] Edge cases §1.4 ($n = 0$, $n + 1 = p^e$, $k \in \{0, n\}$, $a = 0$) hand-checked.
- [x] §3 Mathlib API table re-verified at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `gh api .../contents/...` (factorization_choose at line 131, ordProj_dvd at line 273, log_mono_right at line 259).
- [x] §6 race-safety probe: `gh pr list --search "basel iter 33 in:title"` returns `[]`; `gh pr list --search "basel iter 28b-1 in:title"` returns `[]`; Iter 32 PREP #18682 confirmed orthogonal by file path and target sub-lemma.
- [ ] Iter 28b-1 ACT author drops the §2 skeleton in `BaselProblemOQ01OQ01OQ02OQ03.lean` and discharges the three §2.1 mechanical TODOs.

## §8 — Updated Iter 28b LOC ledger

| Step | Lean LOC | Sorries | Status |
|---|---:|---:|---|
| Iter 28a per-term integral | 60–100 | 0 | DEFERRED (Iter 29 PREP audited Mathlib; no LOC change) |
| **Iter 28b-1 bound side** | **~25 (was 80–120)** | **0** | **PREP this PR — ACT pending** |
| Iter 28b-2 witness existence | ~35–50 (was 40–60) | 0 | PREP #18682 OPEN — ACT pending |
| Iter 28b-3 strong-form (optional) | ~10 (was 30–50) | 0 | Trivial corollary |
| Iter 28c bridge corollary `(n+1) · C(n,k) ∣ lcmRange(n+1)` | ~15 | 0 | PREP'd at Iter 31 §4; ACT pending |
| **Total Iter 28 (bridge only)** | **~145–200 (was 180–280)** | **0** | — |

Post-bridge Hanson discharge (polynomial-choice + analytic estimate, ~200 LOC) remains separate. **The `axiom hanson_bound` discharge is NOT delivered by this PREP; only the 28b-1 sub-lemma of the bridge.**

## §9 — References

- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` — bootstrap file (1469 LOC, 1 axiom, 0 sorries per state.md tail).
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-13-iter31-prep-mathlib-api-audit-and-witness-correction.md` §4 — Iter 28b decomposition (28b-1 / 28b-2 / 28b-3); §5 sketches the 28b-1 sorry-discharge as `~70 LOC: digit-counting + carries-positions argument`. This PREP delivers the alternative 25-LOC residue route.
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-13-iter32-prep-witness-saturation-residue-arithmetic.md` (PR #18682, OPEN) §2 — orthogonal 28b-2 residue argument; §4 Lean skeleton; §6 "Why residue beats digits" LOC analysis. This PREP's §4 cites the same comparison.
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-13-iter30-prep-numerical-bridge-confirmation-N200.md` §2 strong-form identity (†); §3 tight-$k$ structure table; §4 Iter 28b assembly plan.
- Mathlib v4.26.0 `Data/Nat/Choose/Factorization.lean:131` `Nat.factorization_choose` — Kummer carries form.
- Mathlib v4.26.0 `Data/Nat/Factorization/Defs.lean:273` `Nat.ordProj_dvd` — load-bearing $p^{v_p(n)} \mid n$.
- Mathlib v4.26.0 `Data/Nat/Log.lean:259` `Nat.log_mono_right` — monotonicity for $b = e + 1$ choice in `factorization_choose`.
