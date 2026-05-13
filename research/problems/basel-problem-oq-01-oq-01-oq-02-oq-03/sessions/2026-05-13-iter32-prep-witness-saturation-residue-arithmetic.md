# Iteration 32 PREP — Rigorous residue-arithmetic proof that Iter 31's witness $k = (n+1) - p^e$ saturates the bound

**Date**: 2026-05-13 (~08:15 UTC)
**Researcher**: researcher-4
**Phase**: PREP (doc-only — closes Iter 31 Honest Gap 2 with a rigorous residue-arithmetic case analysis)
**Predecessors**:
- Iter 28 PREP (PR #18352, merged 2026-05-12 23:17 UTC, researcher-4) — Hanson routes survey.
- Iter 29 PREP (PR #18485, merged 2026-05-13 03:07 UTC, researcher-1) — Mathlib audit for Route B.
- Iter 30 PREP (PR #18582, merged 2026-05-13 05:05 UTC, researcher-10) — numerical bridge at $N \le 200$ + strong-form identity statement.
- **Iter 31 PREP (PR #18606, merged 2026-05-13 06:01 UTC, researcher-5) — Mathlib API audit + corrected closed-form witness $k_0 = (n+1) - p^e$**.

**Anti-targets** (this PREP does NOT modify any of):
- `problem.md`, `knowledge.md`, `state.md`
- `BaselProblemOQ01OQ01OQ02OQ03.lean` (Lean source — 1469 LOC, 1 axiom, 0 sorries)
- `meta.json` (gallery)
- Any prior `sessions/*.md` file (single new file in `sessions/`)

## TL;DR

Iter 31 PREP §3.4 closed-form witness $k_0 = (n+1) - p^e$ (where $e = \lfloor \log_p(n+1) \rfloor$) is empirically verified 5064/5064 at $N \le 200$, but the §3.4 "Why this works" argument was admitted as a sketch (Iter 31 Honest Gap 2): *"every nonzero digit of $k$ at a position $< e$ creates a carry"* relies on a `Nat.digits` per-position analysis that the PREP does not develop.

This PREP **closes Iter 31 Honest Gap 2** by recasting the witness-saturates-bound proof in **residue arithmetic** (mod-$p^i$) — which matches the carries form `#{i ∈ Ico 1 b | p^i ≤ k % p^i + (n-k) % p^i}` of `Nat.factorization_choose` (Mathlib v4.26.0, `Mathlib/Data/Nat/Choose/Factorization.lean:131`) **directly**, without going through `Nat.digits` machinery at all.

Three deliverables:

| §  | Content | Outcome |
|----|---------|---------|
| §2 | Residue-arithmetic proof of witness saturation: for $k = (n+1) - p^e$, the per-position carry condition $p^i \le k \% p^i + (n-k) \% p^i$ **fails** at positions $i \in [1, a]$ (where $a = v_p(n+1)$) and **holds** at positions $i \in [a+1, e]$. Hence carry count = $e - a$ = target. | Closes Iter 31 Honest Gap 2 (rigor) |
| §3 | Two-case structure: (Case A) $n+1 = p^e$ exactly, target = 0; (Case B) $n+1 \ne p^e$, target $= e - a$. Iter 31 §3.4 had Case A only as a parenthetical aside; this PREP develops it explicitly. | Resolves the "$m = p^f$" parenthetical |
| §4 | Drop-in Lean proof skeleton for Iter 28b-2 (`exists_witness_choose_saturates_log_succ`) using only residue lemmas (`Nat.add_mod`, `Nat.sub_mod`, `Nat.mod_pow_self`, `Nat.pow_mod`), entirely avoiding `Nat.digits`. Refines Iter 31 §5's 40–60 LOC estimate down to 35–50 LOC. | Tightens Iter 28b-2 estimate |

This PREP **does not** address Iter 28b-1 (the $\le$ bound for arbitrary $k$); that is a separate digit-counting argument deferred to a future PREP.

## §1 — Restatement of the target and the witness

### §1.1 The bound to saturate

From Iter 31 PREP §2 (definition copied here for self-containment):

$$
\boxed{
v_p(n+1) + v_p\!\binom{n}{k} \le \log_p(n+1) \qquad (\star)
}
$$

The witness lemma (Iter 28b-2 in Iter 31 PREP §4):

```lean
lemma exists_witness_choose_saturates_log_succ
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 2 ≤ n) :
    ∃ k, k ≤ n ∧ (n + 1).factorization p + (Nat.choose n k).factorization p
                  = Nat.log p (n + 1)
```

with witness

$$k_0 \;=\; (n+1) - p^e, \qquad e := \lfloor \log_p (n+1) \rfloor.$$

### §1.2 Notation pinned for this PREP

- $a := v_p(n+1)$.
- $e := \lfloor \log_p(n+1) \rfloor$ (so $p^e \le n+1 < p^{e+1}$).
- $m := (n+1) / p^a$ (so $n+1 = p^a m$ with $\gcd(m, p) = 1$, by definition of $v_p$).
- $f := e - a$ (so $p^f \le m < p^{f+1}$).
- Target: $e - a = f$.
- $k = k_0 = (n+1) - p^e = p^a m - p^a p^f = p^a (m - p^f)$.
- $n - k = (n+1) - 1 - ((n+1) - p^e) = p^e - 1$.

**Sign / bounds checks**:

- $m - p^f \ge 0$: from $p^f \le m$.
- $k \ge 0$: from $m \ge p^f$ and $p^a \ge 1$.
- $k \le n$: from $p^e \ge 1$, so $k = (n+1) - p^e \le n$.
- $n - k = p^e - 1$: by direct substitution.
- $n - k \ge 0$ iff $p^e \ge 1$ ✓.

These checks all pass at $n = 0$ trivially (give $k = 0$, but the hypothesis $2 \le n$ rules out the edge case anyway; the formula remains well-defined).

## §2 — Residue-arithmetic proof of saturation

We show that for the witness $k = k_0$, the carry-counting set

$$C \;:=\; \{ i \in [1, b) : p^i \le k \% p^i + (n - k) \% p^i \}$$

(from `Nat.factorization_choose`, with $b = \log_p n + 1$) satisfies $|C| = e - a$. The strategy is **per-position case analysis** on $i$, using:

- $(n - k) = p^e - 1$ (fixed for our $k$).
- Compute $k \% p^i$ and $(n - k) \% p^i$ as a function of $i$.
- Decide whether $p^i \le k \% p^i + (n - k) \% p^i$.

### §2.1 Position $i \in [1, a]$ — carry fails (no carries here)

For $1 \le i \le a$:

**Compute $(n - k) \% p^i = (p^e - 1) \% p^i$.** Since $i \le a \le e$, $p^i \mid p^e$. Then
$$p^e - 1 = (p^{e-i} - 1) \cdot p^i + (p^i - 1)$$
(check: $(p^{e-i} - 1) \cdot p^i + p^i - 1 = p^e - p^i + p^i - 1 = p^e - 1$ ✓). So
$$(p^e - 1) \% p^i \;=\; p^i - 1.$$

**Compute $k \% p^i$.** Write $k = p^a m - p^e$. For $i \le a$, $p^i \mid p^a$, so $p^a m \% p^i = 0$. Likewise $p^i \mid p^e$, so $p^e \% p^i = 0$. By `Nat.sub_mod` (modular subtraction; valid since $p^a m \ge p^e$):
$$k \% p^i = (p^a m - p^e) \% p^i = (0 - 0) \% p^i = 0.$$

(More carefully: `Nat.sub_mod` for $\mathbb{N}$ requires the subtractor to be at most the subtractee, which we have; equivalently, $p^i \mid p^a m$ and $p^i \mid p^e$, so $p^i \mid (p^a m - p^e)$.)

**Carry test**:
$$k \% p^i + (n - k) \% p^i = 0 + (p^i - 1) = p^i - 1.$$
The condition $p^i \le p^i - 1$ is **false**. So $i \notin C$.

**Conclusion for §2.1**: positions $i \in [1, a]$ contribute **zero** carries.

### §2.2 Position $i \in [a+1, e]$ — carry holds (one per position)

For $a < i \le e$:

**Compute $(n - k) \% p^i$.** Same calculation as §2.1: $(p^e - 1) \% p^i = p^i - 1$ (uses only $i \le e$).

**Compute $k \% p^i$.** Write $k = p^a (m - p^f)$. Since $i > a$, write $i = a + j$ with $j \ge 1$. Then $p^i = p^a p^j$, and
$$k \% p^i = (p^a (m - p^f)) \% (p^a p^j) = p^a \cdot ((m - p^f) \% p^j).$$
(uses `Nat.mul_mod_mul_left` or equivalent: $(p^a \cdot x) \% (p^a \cdot y) = p^a \cdot (x \% y)$.)

**Sub-claim**: $(m - p^f) \% p^j \ge 1$.

We use $\gcd(m, p) = 1$. Suppose for contradiction $(m - p^f) \% p^j = 0$, i.e., $p^j \mid (m - p^f)$. Then $p \mid (m - p^f)$. But $p \mid p^f$ iff $f \ge 1$:

- **Sub-case $f = 0$**: $p^f = 1$, so $m - p^f = m - 1$. Then $p \mid m - 1$, i.e., $m \equiv 1 \pmod p$. This is consistent with $\gcd(m, p) = 1$; the sub-claim could fail. Wait — let's re-examine.

  Actually for $f = 0$, $p^f = 1$, and $j \in [1, e - a]$ but $e - a = f = 0$, so the range $[a+1, e]$ is empty. **Case $f = 0$ has no $i \in (a, e]$.** So we never enter §2.2 when $f = 0$.

- **Sub-case $f \ge 1$**: $p \mid p^f$. From $p^j \mid (m - p^f)$ and $p \mid p^j$, get $p \mid m - p^f$. So $p \mid m$ (since $p \mid p^f$). But $\gcd(m, p) = 1$ ⟹ $p \nmid m$. Contradiction.

So $(m - p^f) \% p^j \ge 1$ whenever $i \in [a+1, e]$ (which forces $f \ge 1$).

**Carry test**:
$$k \% p^i + (n - k) \% p^i = p^a \cdot ((m - p^f) \% p^j) + (p^i - 1) \ge p^a \cdot 1 + (p^i - 1) = p^a + p^i - 1.$$
Need $p^i \le p^a + p^i - 1$, i.e., $1 \le p^a$. **True** (since $p \ge 2$ and $a \ge 0$). So $i \in C$.

**Conclusion for §2.2**: positions $i \in [a+1, e]$ each contribute **one** carry, giving $e - a$ total.

### §2.3 Position $i > e$ — no carries (and the range is empty when $b = \log_p n + 1$)

The carry filter uses $i \in [1, b)$ with $b > \log_p n$. The minimal choice $b = \log_p n + 1$ gives $i \in [1, \log_p n]$.

**Case A**: $n+1 = p^e$ (i.e., $m = 1$, $a = e$, $f = 0$). Then $n = p^e - 1$, $\log_p n = \log_p (p^e - 1) = e - 1$. The filter range is $[1, e-1] = [1, a]$ (since $a = e$ gives $[1, a-1]$, hmm let me recompute):

Actually $\log_p n = e - 1$ and the filter is $[1, e - 1]$, so $i \le e - 1 < a$. By §2.1, no carries. Carry count = $0 = e - a$. ✓

**Case B**: $n+1 \ne p^e$ (i.e., $m \ge 2$, $f \ge 1$, $n \ge p^e$). Then $\log_p n = e$ (since $p^e \le n < p^{e+1}$). The filter range is $[1, e]$. By §2.1, no carries in $[1, a]$; by §2.2, one carry per position in $[a+1, e]$, giving $e - a$ total. ✓

### §2.4 No position $i > e$ in any case

For $i = e + 1$ (would be in the filter only if Case B and $\log_p n \ge e + 1$, but $\log_p n = e$ in Case B): outside the filter. **Filter never reaches position $> e$.** So §2.3 is trivially satisfied — there's no need to analyze residue arithmetic above $e$.

### §2.5 Total

$$|C| = \underbrace{0}_{\text{§2.1, } i \in [1, a]} + \underbrace{(e - a)}_{\text{§2.2, } i \in [a+1, e]} = e - a = f.$$

This matches the target $\log_p(n+1) - v_p(n+1) = e - a$.

By `Nat.factorization_choose`:
$$v_p\!\binom{n}{k_0} = |C| = e - a.$$

Adding $v_p(n+1) = a$:
$$v_p(n+1) + v_p\!\binom{n}{k_0} = a + (e - a) = e = \log_p(n+1).$$

The bound $(\star)$ is **saturated**. ∎

## §3 — Two-case split, the $m = p^f$ aside resolved

Iter 31 PREP §3.4 last paragraph:

> ... actually one must be careful: when $m = p^f$ exactly, $k = 0$ and target $= 0$, consistent.

Here we develop the case explicitly. **$m = p^f$ requires $\gcd(m, p) = 1$ + $m = p^f$ ⟹ $f = 0$, $m = 1$.** This is Case A above ($n+1 = p^e$). The witness becomes $k_0 = (n+1) - p^e = 0$.

- $\binom{n}{0} = 1$, so $v_p\!\binom{n}{0} = 0 = f$ (target).
- $v_p(n+1) = e$, so $a = e$, $f = e - a = 0$.
- $(\star)$ saturates as $e + 0 = e$.

So Case A is **completely degenerate but well-defined**: $k_0 = 0 \in [0, n]$, and the formula returns target = 0 by direct evaluation. No special-case handling is needed in the Lean proof beyond letting `simp` or `decide` close the $k = 0$ branch.

For Case B ($m \ge 2$, $f \ge 1$): the residue argument in §2.2 strictly requires $f \ge 1$ to derive the contradiction $p \mid m$. So §2.2 is **vacuously inactive** in Case A — there are no positions to check.

The two cases unify under the **uniform** residue-arithmetic statement of §2 because:

- §2.1 covers $i \in [1, a]$, which includes the entire filter $[1, \log_p n]$ in Case A.
- §2.2 covers $i \in [a+1, e]$, which is empty in Case A and equal to the filter tail in Case B.

This is cleaner than Iter 31 §3.4's `Nat.digits`-based sketch, which had to make the "every nonzero digit creates a carry" argument and then patch the $m = p^f$ case.

## §4 — Drop-in Lean proof skeleton for Iter 28b-2

**Refines** Iter 31 PREP §5 lemma `exists_witness_choose_saturates_log_succ` (40–60 LOC estimate). With residue arithmetic instead of `Nat.digits`, the proof body decomposes cleanly:

```lean
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Factorization.Basic

open Finset

-- helper lemma 1: residue of p^e - 1 mod p^i for i ≤ e
lemma pow_sub_one_mod_pow {p e i : ℕ} (hp : 1 < p) (hie : i ≤ e) :
    (p ^ e - 1) % p ^ i = p ^ i - 1 := by
  -- Direct: p^e - 1 = (p^(e-i) - 1) · p^i + (p^i - 1).
  -- Both factors nonneg since 1 ≤ p^i ≤ p^e by hp + hie.
  have h_pe_ge : 1 ≤ p ^ e := Nat.one_le_pow _ _ (by omega)
  have h_pi_ge : 1 ≤ p ^ i := Nat.one_le_pow _ _ (by omega)
  -- Apply Nat.add_mul_mod_self_left or a divisor-of-divisor argument:
  -- (p^(e-i) - 1) · p^i + (p^i - 1) ≡ p^i - 1 mod p^i, and the left side equals p^e - 1.
  sorry  -- ~10 LOC

-- helper lemma 2: residue of k = p^a · (m - p^f) mod p^i for a ≤ i ≤ e where f = e - a
lemma witness_mod_pow_lt {p a m f i : ℕ} (hp : 1 < p)
    (hai : a < i) (hf_pos : 0 < f) (hpf_le : p ^ f ≤ m) (hmp : ¬ p ∣ m) (hf_eq : f = i - a) :
    1 ≤ (p ^ a * (m - p ^ f)) % p ^ i := by
  -- Use Nat.mul_mod_mul_left: (p^a · x) % (p^a · p^(i-a)) = p^a · (x % p^(i-a)).
  -- Need x % p^(i-a) ≥ 1, i.e., p^(i-a) ∤ (m - p^f).
  -- For i = a + f exactly: (m - p^f) % p^f. Suppose p^f ∣ (m - p^f) → p ∣ m. Contradiction with hmp.
  -- For i = a + j with j ≤ f: similar by divisibility.
  sorry  -- ~15 LOC

-- main: witness saturates
lemma exists_witness_choose_saturates_log_succ
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 2 ≤ n) :
    ∃ k, k ≤ n ∧ (n + 1).factorization p + (Nat.choose n k).factorization p
                  = Nat.log p (n + 1) := by
  set e := Nat.log p (n + 1) with he_def
  set a := (n + 1).factorization p with ha_def
  refine ⟨(n + 1) - p ^ e, ?_, ?_⟩
  · -- bound k ≤ n
    have hpe_pos : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
    omega
  · -- saturation: v_p(C(n, k₀)) = e - a
    set k := (n + 1) - p ^ e with hk_def
    have hkn : k ≤ n := by
      have hpe_pos : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
      omega
    -- Apply Nat.factorization_choose with b = log p n + 1.
    have hb : Nat.log p n < Nat.log p n + 1 := Nat.lt_succ_self _
    rw [Nat.factorization_choose hp hkn hb]
    -- Goal: a + #{i ∈ Ico 1 (log p n + 1) | p^i ≤ k%p^i + (n-k)%p^i} = log p (n+1)
    -- Split the filter at position a+1, apply §2.1 + §2.2.
    sorry  -- ~25 LOC: case A vs case B split + apply helpers
```

**Total estimate**: 35–50 LOC (improving Iter 31 PREP §5's 40–60). Two small helper lemmas (~10 + ~15 LOC) plus main lemma body (~10 LOC after helpers).

**Sorries**: 3 in this skeleton (the two helpers and the main split). They are mechanical applications of residue lemmas already in Mathlib core (`Nat.add_mod`, `Nat.sub_mod`, `Nat.mul_mod_mul_left`, `Nat.mod_self`, `Nat.mod_eq_of_lt`); discharging is a straightforward exercise for the Iter 28b-2 ACT author and does not require any new Mathlib API.

## §5 — Mathlib API: residue lemmas pinned at v4.26.0

| Lemma | Provenance | Statement |
|---|---|---|
| `Nat.add_mod` | Lean core (`Nat/Basic.lean`) | `(a + b) % n = ((a % n) + (b % n)) % n` |
| `Nat.sub_mod` | Lean core | `(a - b) % n = ((a % n) + (n - b % n)) % n` (or via `Nat.ModEq`) — for $\mathbb{N}$, requires $b \le a$ to be clean |
| `Nat.mul_mod` | Lean core | `(a * b) % n = ((a % n) * (b % n)) % n` |
| `Nat.mul_mod_mul_left` | Lean core (`Init/Data/Nat/Mod`) | `(c * a) % (c * b) = c * (a % b)` for $c \ge 1$ |
| `Nat.mod_self` | Lean core | `n % n = 0` |
| `Nat.mod_eq_of_lt` | Lean core | `a < n → a % n = a` |
| `Nat.dvd_iff_mod_eq_zero` | Lean core | `0 < n → (n ∣ m ↔ m % n = 0)` |
| `Nat.pow_le_pow_right` | Mathlib `Algebra/Order/Group/Nat.lean` | `1 ≤ b → m ≤ n → b^m ≤ b^n` (already exercised in `BaselProblemOQ01OQ01OQ02OQ03.lean` at line 408) |
| `Nat.one_le_pow` | Mathlib | `0 < b → 1 ≤ b^n` |
| `Nat.factorization_choose` | **Mathlib v4.26.0 `Data/Nat/Choose/Factorization.lean:131`** | Carries form (load-bearing; see Iter 31 PREP §2) |
| `Nat.Prime.pos` | Mathlib `Data/Nat/Prime/Basic.lean` | Primes are positive |
| `Nat.Prime.one_lt` | Mathlib | Primes are > 1 |
| `Nat.Prime.coprime_iff_not_dvd` | Mathlib | $\gcd(m, p) = 1 \iff p \nmid m$ |

**Audit note**: All `Nat.*_mod` lemmas listed above are in Lean *core* (not Mathlib), so they are universally available without imports. The argument in §2 is mathematically independent of Mathlib's `Nat.digits` framework and **does not require** any of `Nat.digits`, `Nat.digits_pow_sub_one`, or analogous digit-based lemmas — sidestepping the digit-counting machinery cited in Iter 31 §3.4 as "needed".

## §6 — Why the residue route is cleaner than the digits route

Iter 31 PREP §3.4 proof sketch (paraphrased):

> ... $p^e - 1$ has the all-$(p-1)$ representation in base $p$ ... every nonzero digit of $k$ at a position $< e$ creates a carry ...

This requires a Lean lemma "the base-$p$ digits of $p^e - 1$ are all $p - 1$", which would be a 5–10 LOC induction on $e$. Then "carries from $k$'s nonzero digits" requires translating between `Nat.digits p (p^e - 1)` and `Nat.factorization_choose`'s residue form — at least 20–30 more LOC of `Nat.digits ↔ mod` plumbing.

The §2 residue route avoids this entirely. We never compute `Nat.digits`; we work in residue arithmetic directly, which is what `Nat.factorization_choose` already produces. This is **structurally simpler** and uses **only** lemmas already exercised in the existing 1469-LOC file.

**Comparison (LOC budget for witness saturation only)**:

| Route | Helpers | Main lemma | Total | Verification primitive |
|---|---|---|---|---|
| Iter 31 §3.4 (Nat.digits) | digits_pow_sub_one + digits→mod translator: ~30–40 | ~20–30 | 50–70 | `Nat.digits` |
| This PREP §2 (residues) | pow_sub_one_mod_pow + witness_mod_pow_lt: ~25 | ~10 | 35–50 | `Nat.mul_mod_mul_left` |

Saves 15–20 LOC and avoids `Nat.digits` plumbing (which is non-trivial in Mathlib v4.26.0 and would require additional imports).

## §7 — Race safety

### §7.1 Open-PR scan at 2026-05-13 08:14 UTC

```
$ gh pr list --repo rjwalters/lean-genius \
    --search "basel-problem-oq-01-oq-01-oq-02-oq-03 in:title" --state open
17619  Iter 17 — correction factor supported on small primes (p²≤n) (build pending)   2026-05-09 02:25 UTC
17551  Iter 15 — π(n) ≤ n-2 for n≥4 via erasing the smallest even composite           2026-05-09 00:02 UTC
```

Same two stale build-pending PRs as Iter 31 PREP. Both 4+ days old, on falsified pre-Iter-26 routes. **No active competition.**

### §7.2 Recent merges on this slug

```
2026-05-13 06:01:44 UTC  Iter 31 PREP (PR #18606)  — researcher-5  (+469 LOC)
2026-05-13 05:05:43 UTC  Iter 30 PREP (PR #18582)  — researcher-10
2026-05-13 03:07:38 UTC  Iter 29 PREP (PR #18485)  — researcher-1
2026-05-12 23:17:49 UTC  Iter 28 PREP (PR #18352)  — researcher-4
```

This PREP starts at ~08:15 UTC — **~2 h 15 min after Iter 31 PREP merge**, well outside the 30-min "hot zone". The slug is on a sustained PREP cadence (~2–4 h between merges in this 24h window).

### §7.3 Branch + file uniqueness

- **Branch**: `research/basel-iter32-prep-witness-residue-arithmetic-1778660079` (verified no remote collision via `git branch -r | grep iter32`).
- **File path**: `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-13-iter32-prep-witness-saturation-residue-arithmetic.md` — fresh path, no existing collision (only 2026-05-13 files in `sessions/` are Iter 30 and Iter 31 PREP).
- **Worktree-path discipline**: written via `Write` tool to fully-qualified worktree absolute path `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-4/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/...` per `feedback_write_tool_main_repo_absolute_path_trap.md`.
- **Pre-create race check**: `gh pr list --search "basel iter 32 in:title"` returned `[]`. No sibling Iter 32 PR.

### §7.4 Build risk: NONE

Pure documentation. No Lean file edits → no build runs → no `.lake` symlink-loop risk per `feedback_researcher_lake_symlink_loop_and_wipe.md`.

## §8 — Honesty / self-audit log

| Claim | Verified by | Outcome |
|---|---|---|
| `Nat.factorization_choose` at `Data/Nat/Choose/Factorization.lean:131` (v4.26.0) | `gh api .../contents/...?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` + grep `^theorem` | ✓ confirmed line 131 |
| `Nat.factorization_choose_le_log` at line 185 | Same | ✓ confirmed line 185 |
| §2.1 residue calc: $k \% p^i = 0$ for $i \le a$ | $p^i \mid p^a m$ and $p^i \mid p^e$, so $p^i \mid (p^a m - p^e) = k$ | ✓ pencil-paper |
| §2.1 residue calc: $(p^e - 1) \% p^i = p^i - 1$ for $i \le e$ | $p^e - 1 = (p^{e-i} - 1) p^i + (p^i - 1)$, both factors $\ge 0$ | ✓ pencil-paper |
| §2.2 sub-claim: $(m - p^f) \% p^j \ge 1$ for $f \ge 1$, $j \le f$ | Contradiction with $\gcd(m, p) = 1$ via $p \mid p^j \mid (m - p^f)$ ⟹ $p \mid m$ | ✓ pencil-paper |
| §2.2 sub-claim fails when $f = 0$ but range $(a, e]$ is empty | $e - a = f = 0$ | ✓ trivially |
| §2.3 filter never reaches $i > e$ | $\log_p n \le e$ (since $p^e \le n+1$ ⟹ $p^e \le n+1$, and $n+1 \le p^{e+1}$ ⟹ $\log_p n \le e$) | ✓ pencil-paper |
| §2.5 total: $|C| = e - a$ | §2.1 contributes 0, §2.2 contributes $e - a$ | ✓ |
| Iter 31 §3.4 "Why this works" was a sketch | Iter 31 PREP Honest Gap 2: "§3.4 ... is a sketch, not a rigorous Lean-ready proof" | ✓ verbatim |
| §6 LOC comparison is rough | Both routes' LOC are estimates, not measured. Comparison is qualitative. | ✓ flagged as estimate |

**Honest gap 1**: §4's Lean skeleton uses `sorry` for three sub-proofs:

- `pow_sub_one_mod_pow` (~10 LOC): residue arithmetic, pure `Nat.*_mod` algebra. No new Mathlib API.
- `witness_mod_pow_lt` (~15 LOC): case split on $i - a$ using `Nat.mul_mod_mul_left` + coprimality. No new Mathlib API.
- Main lemma's filter split (~25 LOC): apply helpers + `Finset.card_filter_eq` (or analogous count-by-cases).

All three are mechanical exercises in residue arithmetic + Finset cardinality. **None requires `Nat.digits` machinery, and none requires any Mathlib lemma not already in this file or in Lean core.**

**Honest gap 2**: §6's "saves 15–20 LOC" claim is a qualitative estimate. The actual LOC would be measured only by the Iter 28b-2 ACT author when discharging both routes side-by-side; we did not implement either.

**Honest gap 3**: This PREP closes Iter 31 Honest Gap 2 (the witness saturation rigor), but **not** Iter 31 Honest Gap 1 (the Iter 28b-1 weak-bound proof for arbitrary $k$, ~70 LOC). The full Iter 28b assembly remains incomplete; Iter 28b-1 is a separate ACT (different proof technique — digit-counting + carries-positions upper bound — but its conclusion is implied by an analogous residue argument applied to *every* $k$, not just our $k_0$).

**Honest gap 4**: This PREP does NOT prove `axiom hanson_bound`. It only refines the Iter 28b-2 sub-lemma proof skeleton. The full Hanson-bound discharge still requires Iter 28a (per-term integral identity), Iter 28b-1 (weak-bound for all $k$), Iter 28c (bridge dvd corollary), Iter 28d (post-bridge analytic argument). Even after a complete 28b-2, the parent axiom remains until all of those land.

**Honest gap 5**: No `lake build` was performed (per `CLAUDE.md` Docker-wrapper policy and `feedback_researcher_lake_symlink_loop_and_wipe.md`). Lean snippets in §4 are syntax-checked by eye, not by Lean.

## §9 — Updated "Done When" for Iter 28b-2

Iter 31 PREP §8 listed:

- [ ] Lean proof of `exists_witness_choose_saturates_log_succ` (Iter 28b-2 ACT, ~40–60 LOC).

This PREP refines:

- [x] Rigorous (pencil-paper) saturation proof of the witness $k_0 = (n+1) - p^e$ via residue arithmetic (§2).
- [x] Two-case split (Case A: $n+1 = p^e$; Case B: $n+1 \ne p^e$) made explicit (§3).
- [x] Drop-in Lean skeleton with three small `sorry`s (§4), 35–50 LOC.
- [x] Mathlib v4.26.0 API table for residue lemmas (§5).
- [x] Comparison vs Iter 31 §3.4's `Nat.digits` route (§6) — 15–20 LOC savings estimate.
- [ ] Discharge the three §4 `sorry`s (Iter 28b-2 ACT, 35–50 LOC estimate refined from 40–60).
- [ ] Lean proof of `factorization_succ_mul_choose_le_log_succ` (Iter 28b-1 ACT, ~80–120 LOC — separate from this PREP).
- [ ] Lean proof of `succ_mul_choose_dvd_lcmRange` (Iter 28c ACT bridge corollary, ~15 LOC).
- [ ] Iter 28a per-term integral identity (parallel work, ~60–100 LOC).
- [ ] Iter 28d post-bridge Hanson argument (~200 LOC).
- [ ] Final discharge of `axiom hanson_bound`.

## §10 — References

- **Iter 28 PREP**: `sessions/2026-05-12-iter28-prep-hanson-routes-survey.md` (PR #18352, researcher-4).
- **Iter 29 PREP**: `sessions/2026-05-12-iter29-prep-route-b-mathlib-api-audit.md` (PR #18485, researcher-1).
- **Iter 30 PREP**: `sessions/2026-05-13-iter30-prep-numerical-bridge-confirmation-N200.md` (PR #18582, researcher-10).
- **Iter 31 PREP**: `sessions/2026-05-13-iter31-prep-mathlib-api-audit-and-witness-correction.md` (PR #18606, researcher-5). **This PREP closes Iter 31 Honest Gap 2.**
- **Mathlib v4.26.0** at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
  - `Mathlib/Data/Nat/Choose/Factorization.lean:131` (`Nat.factorization_choose` — carries form).
  - `Mathlib/Data/Nat/Log.lean` (`Nat.log` API).
  - `Mathlib/Data/Nat/Factorization/Basic.lean` (`Nat.factorization` API).
- **Lean core** `Nat.*_mod` residue lemmas (universally available).
- **Parent file**: `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` (1469 LOC, 1 axiom = `hanson_bound`, 0 sorries).
- **Hanson, D.** (1972). "On the product of the primes". *Canad. Math. Bull.* 15, 33–37.
