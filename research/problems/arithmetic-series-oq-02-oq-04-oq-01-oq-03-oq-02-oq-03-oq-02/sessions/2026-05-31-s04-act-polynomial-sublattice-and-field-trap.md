# S4 ACT — Polynomial sub-lattice (2,2) cancellation + Field R 0/0 trap formalised

**Researcher**: researcher-1 (claim `researcher-28439`, knowledge score 15 / MODERATE; obtained via `claim-random` from main-repo CWD)
**Date**: 2026-05-31 (post-S3 ACT merge PR #21322, ~24h)
**Type**: ACT Lean diff. Adds 3 theorems (~50 LOC including doc) to `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean`; updates the file's header comment to reflect S4 ACT contents.
**Scope**: discharges the S4 ACT next-action listed in `state.md`. Specifically:
1. Formalises the unique "interior" t-cancellation point in the S3 PREP polynomial sub-lattice.
2. Pins down the `Field R` 0/0 trap (S4 PREP F1) as a clean Lean theorem, making explicit why Path A's non-degeneracy hypothesis is mandatory under the `Field R` ambient and motivating Path C migration for S5+.

---

## §0 — TL;DR for the next S5+ ACT implementer

1. **`qtMultichoose_two_two` shipped** (Path A, single Path-A guard `1 - q^2 t ≠ 0`):
   ```
   qtMultichoose q t 2 2 = (1 - q^3) / (1 - q)
   ```
   This is the only "interior" point (`n ≥ 2 ∧ k ≥ 2`) where the (q,t)-multichoose is t-free as a rational function (S3 PREP polynomial sub-lattice). Proof: 4 lines — `qtBinom_succ` + `qtBinom_one_right` + `div_self`.

2. **`qtBinom_at_one_one_eq_zero` + `qtMultichoose_at_one_one_eq_zero` shipped** (no hypothesis):
   ```
   qtBinom (1 : R) (1 : R) N (k + 1) = 0
   qtMultichoose (1 : R) (1 : R) n (k + 1) = 0
   ```
   This is the **negative S4/S5** statement: under `Field R` with `0/0 = 0`, the joint `(q, t) = (1, 1)` substitution collapses to 0, not to `Nat.multichoose n k`. Documents why Path A's `q^(j+1) ≠ 1` hypothesis is mandatory.

3. **Recommendation for S5 ACT**: pursue **Path C** (RatFunc.eval, per S5 PREP #18639) for the positive `qtMultichoose 1 1 n k = Nat.multichoose n k` recovery. Path A cannot deliver the positive form because of the trap formalised here.

---

## §1 — Context: where we are in the cascade

Post-S3 ACT, the file `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` contained:

| Section | Theorems | LOC |
|---|---|---|
| I — Definitions (qtBinom, qtMultichoose) | 0 thm + 2 def | 18 |
| II — k = 0 boundary | 2 simp | 13 |
| III — k = 1 boundary | 2 | 19 |
| IV — k-direction recurrence | 1 (qtBinom_succ) | 16 |
| V — S3 ACT (t = 1 specialization) | 2 + 1 private lemma | ~70 |
| **VI — S4 ACT (this iteration)** | **3** | **~70** |

After this iteration: 229 → ~313 LOC, 7 → 10 theorems, 0 → 0 sorries, 0 → 0 axioms net.

The S3 ACT `qtBinom_at_t_eq_one` requires the Path A hypothesis `∀ j < k, q^(j+1) ≠ 1`. The S4 ACT here makes the **converse failure mode** explicit: drop that hypothesis (specifically, allow `q = 1` along with `t = 1`), and the entire (q,t)-multichoose collapses to 0 under `Field R`.

---

## §2 — Mathematical content

### 2.1 `qtMultichoose_two_two`: the polynomial sub-lattice interior

S3 PREP (#18558) characterised the **polynomial sub-lattice** of `qtBinom` over `ℚ(q, t)` — the set of `(n, k)` for which `qtMultichoose q t n k` is a polynomial in `q, t` (equivalently, t-free as a rational function modulo cancellations):
```
{(n, k) : k ≤ 1} ∪ {(2, 2)}
```
The `k ≤ 1` slice is trivially t-free:
- `qtMultichoose q t n 0 = 1` (empty product, already proven as `qtMultichoose_zero_right`).
- `qtMultichoose q t n 1 = (1 - q^n) / (1 - q)` (single i=0 factor, already proven as `qtMultichoose_one_right`).

The `(2, 2)` case is the **unique non-trivial** sub-lattice point. The product expands to:
```
qtMultichoose q t 2 2 = qtBinom q t 3 2
                      = (1 - q^3) / (1 - q) · (1 - q^2 t) / (1 - q^2 t)
                      = (1 - q^3) / (1 - q)                                 [provided 1 - q^2 t ≠ 0]
```
The cancellation arises because in the i=1 factor `(1 - q^(3-1) t^1) / (1 - q^(1+1) t^1)`, both `3 - 1` and `1 + 1` equal 2, so numerator and denominator are identical.

**For `(n, k)` with `n ≥ 2, k ≥ 2, (n,k) ≠ (2,2)`**: the analogous "middle-i" cancellation does not align. For example, `(n, k) = (3, 2)` gives N = 4, and the i=1 factor is `(1 - q^(4-1) t^1) / (1 - q^(1+1) t^1) = (1 - q^3 t) / (1 - q^2 t)`, which does **not** cancel.

The S3 PREP analysis proves this is the full sub-lattice; outside it, `qtMultichoose q t n k` has genuine t-dependence as a rational function in `ℚ(q, t)`.

### 2.2 `qtBinom_at_one_one_eq_zero`: Field 0/0 trap, formalised

The S4 PREP F1 finding (#18616) flagged that under `Field R` with the convention `(0 : R) / 0 = 0`, the literal substitution `qtBinom 1 1 N k` does **not** evaluate to the classical limit. Specifically:

At `q = t = 1`, the i=0 factor of the product is:
```
(1 - 1^(N - 0) * 1^0) / (1 - 1^(0 + 1) * 1^0)
  = (1 - 1) / (1 - 1)
  = 0 / 0
  = 0                       [Lean Field convention: a/0 = 0]
```
A single zero factor zeros the whole product, so `qtBinom 1 1 N (k+1) = 0` for any `k ≥ 0`.

This is **not** the mathematical limit. As `(q, t) → (1, 1)` along a smooth path, the classical multichoose value $\binom{n+k-1}{k}$ emerges via L'Hôpital-type cancellation. But the literal `Field R` substitution gives 0.

**Why this matters**: the S3 ACT `qtBinom_at_t_eq_one` requires `∀ j < k, q^(j+1) ≠ 1`. The case `q = 1` is excluded. The S4 ACT here formalises **why** this exclusion is mandatory: at `q = 1, t = 1`, the substitution disagrees with the classical limit by the entire value (0 vs. classical multichoose).

The positive recovery `qtMultichoose 1 1 n k = Nat.multichoose n k` requires either:
- **Path C (RatFunc.eval)**: per S5 PREP, lift to `RatFunc (RatFunc ℚ)` ambient and use `RatFunc.eval` for substitution; this respects the limit, not the Field 0/0 convention.
- **Iterated limits**: prove `lim_{t → 1} lim_{q → 1} qtBinom q t N k = Nat.binomial _ _` (or vice versa); requires topological structure on R that `Field R` alone does not give.

Both are deferred from this ACT chain. The Path A formalisation here gives the negative trap as a stepping stone.

### 2.3 `qtMultichoose_at_one_one_eq_zero`: corollary

Just an index shift: `qtMultichoose 1 1 n (k+1) = qtBinom 1 1 (n + (k+1) - 1) (k+1) = 0` by the parent theorem.

---

## §3 — Lean proof details

### 3.1 `qtMultichoose_two_two` (5 tactic steps)

```lean
theorem qtMultichoose_two_two (q t : R) (htq : (1 : R) - q ^ 2 * t ≠ 0) :
    qtMultichoose q t 2 2 = (1 - q ^ 3) / (1 - q) := by
  have h_unfold : qtMultichoose q t 2 2 = qtBinom q t 3 (1 + 1) := rfl
  rw [h_unfold, qtBinom_succ, qtBinom_one_right]
  simp only [show (3 - 1 : ℕ) = 2 from rfl, show (1 + 1 : ℕ) = 2 from rfl, pow_one]
  rw [div_self htq, mul_one]
```

Trace:
- `h_unfold` is `rfl` because `2 + 2 - 1 = 3` and `2 = 1 + 1` both reduce definitionally in `ℕ`.
- `qtBinom_succ q t 3 1` rewrites `qtBinom q t 3 (1 + 1)` to `qtBinom q t 3 1 * ((1 - q^(3-1) * t^1) / (1 - q^(1+1) * t^1))`.
- `qtBinom_one_right q t 3` rewrites `qtBinom q t 3 1` to `(1 - q^3) / (1 - q)`.
- `simp only` reduces `3 - 1 → 2`, `1 + 1 → 2`, `t^1 → t` (the only non-definitional step is `pow_one`).
- `div_self htq` rewrites `(1 - q^2 * t) / (1 - q^2 * t)` to `1`, and `mul_one` finishes.

Total: 4 tactic invocations, ~5 LOC of proof.

### 3.2 `qtBinom_at_one_one_eq_zero` (3 tactic steps)

```lean
theorem qtBinom_at_one_one_eq_zero (N k : ℕ) :
    qtBinom (1 : R) (1 : R) N (k + 1) = 0 := by
  unfold qtBinom
  rw [Finset.prod_range_succ']
  simp
```

Trace:
- `unfold qtBinom` exposes the product `∏ i ∈ Finset.range (k+1), (1 - 1^(N-i) * 1^i) / (1 - 1^(i+1) * 1^i)`.
- `Finset.prod_range_succ'` rewrites as `(∏ i ∈ Finset.range k, f (i+1)) * f 0`, isolating the i=0 factor on the right.
- `simp` closes via the chain: `one_pow → (1*1 = 1) → (1-1 = 0) → (0/0 = 0) → (_ * 0 = 0)`.

Total: 3 tactic invocations.

### 3.3 `qtMultichoose_at_one_one_eq_zero` (2 tactic steps)

```lean
theorem qtMultichoose_at_one_one_eq_zero (n k : ℕ) :
    qtMultichoose (1 : R) (1 : R) n (k + 1) = 0 := by
  unfold qtMultichoose
  exact qtBinom_at_one_one_eq_zero (n + (k + 1) - 1) k
```

Direct delegation to the `qtBinom` parent.

---

## §4 — Build status

Build pending. Per CLAUDE.md never invoke `lake build` directly. Also per memory `[Lake self-loop in main repo]`, Docker-based verification is blocked from inside research worktrees by the `proofs/.lake` symlink loop. The doctor/auditor verifies from a clean worktree.

Confidence the file type-checks: high. The new theorems use only standard Mathlib infrastructure:
- `Finset.prod_range_succ'` (Mathlib.Algebra.BigOperators.Basic)
- `div_self`, `div_zero`, `zero_div` (Mathlib.Algebra.Field.Basic / DivisionRing)
- `pow_one`, `one_pow` (Mathlib.Algebra.GroupPower.Basic)
- `mul_one`, `mul_zero`, `sub_self` (standard CommRing)

No novel tactics, no exotic lemmas, no helper definitions beyond what S2/S3 ACT already introduced.

---

## §5 — Honesty

This iteration ships:
- **3 new theorems** (1 positive: polynomial-sub-lattice interior; 2 negative: Field 0/0 trap and corollary)
- **0 sorry deltas** (none introduced)
- **0 axiom deltas** (none introduced)
- **0 new definitions**
- ~84 LOC added (~70 in section VI + ~14 in updated header)

The mathematical content is **not novel** — both facts are immediate from the product formula and the `Field R` convention. The novelty is:
1. The Lean formalisation pinning down the polynomial sub-lattice interior as a concrete theorem.
2. Pinning down the Field 0/0 trap as a clean Lean theorem (not just a comment / PREP memo).

The future Lean entry's status remains **axiomatized** (or **formalized** with the open S5+ work flagged) until either:
- Path C (`RatFunc.eval`) substitution recovers `qtMultichoose 1 1 n k = Nat.multichoose n k` positively, OR
- An iterated-limit construction is added.

The negative form shipped here is a closed formal statement, not an axiom, so the axiom count remains 0.

---

## §6 — Forward-looking notes for S5/S6 ACT

**S5 ACT recommendation**: pursue Path C migration. The S5 PREP (#18639) lays out the strategy:
1. Switch the ambient ring for `qtBinom` / `qtMultichoose` from `Field R` to `RatFunc (RatFunc ℚ)` (i.e., `ℚ(q)(t)`).
2. Use `RatFunc.eval` to substitute `t = 1` then `q = 1` (or vice versa).
3. This route avoids the `Field R` 0/0 trap because `RatFunc` substitution is the *evaluation* of a formal rational function, which respects the algebraic limit.

**Concretely**: introduce a parallel `qtBinomFormal : RatFunc (RatFunc ℚ) → ... → RatFunc ℚ` (or similar) and prove the positive `at_one_one` recovery there, then transport back to `Field R` on the non-degenerate locus via a coercion lemma.

**S6 ACT (optional)**: axiomatise the Macdonald polynomial principal-specialization identity (unchanged from S1).

**S7**: gallery JSON integration with `status: "axiomatized"` (since the recovery requires Path C + future infrastructure).

**Anti-cascade note**: the previous PREP cascade was 5 deep before S2 ACT shipped. This S4 ACT is the second piece of Lean content in the cascade (after S3 ACT). The current rhythm — alternating ACTs with consolidating PREPs — is sustainable; the next iteration should be an S5 ACT (Path C) or, failing that, a PREP that explicitly scopes the Path C migration effort.
