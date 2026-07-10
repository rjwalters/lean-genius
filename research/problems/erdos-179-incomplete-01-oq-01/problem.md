# Problem: Discharge the `Nat.find` Existence Proof to Make F_k(N,ℓ) Genuinely Well-Defined

**Slug**: erdos-179-incomplete-01-oq-01
**Created**: 2026-07-09T16:59:48-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

The supersaturation threshold in the parent file is defined by

$$
F(k, N, \ell) \;:=\; \operatorname{Nat.find}\bigl(\texttt{supersaturation\_exists}\ k\ N\ \ell\bigr),
$$

where the existence witness is the proposition

$$
\exists\, M \in \mathbb{N},\; \forall A \subseteq \mathbb{N} \text{ with } |A| = N,\quad \operatorname{countAPs}(A, k) \ge M \;\Longrightarrow\; \operatorname{ContainsAP}(A, \ell).
$$

The goal is to prove this existential **without `sorry`**, so that `F(k, N, ℓ)` becomes a genuine, kernel-checked natural number rather than one resting on an unproven witness. Concretely, exhibit an explicit `M` and prove the implication for it. The natural candidate is

$$
M \;=\; \binom{N}{k} + 1,
$$

for which the hypothesis $\operatorname{countAPs}(A, k) \ge \binom{N}{k} + 1$ is **impossible** by the already-proven bound $\operatorname{countAPs}(A, k) \le \binom{|A|}{k}$, so the implication holds vacuously.

### Plain Language

The parent formalization defines a supersaturation function `F_k(N, ℓ)` — the smallest number of short (k-term) arithmetic progressions that a size-`N` set can contain before it is *forced* to contain a longer (ℓ-term) progression. In Lean, `F` is built with `Nat.find`, which requires a proof that *some* such threshold exists. The parent supplies a placeholder witness `M = N² + 1` and leaves the required implication as a `sorry`. This open question asks whether that existence proof can actually be completed. The subtlety is that the placeholder witness `N² + 1` is the *wrong* number for `k ≥ 3` (a set of size `N` can have as many as `C(N, k)` many `k`-APs, which exceeds `N²`), so the `sorry` cannot be closed with that witness. Choosing the correct witness `M = C(N, k) + 1` makes the statement vacuously true and closes the gap honestly.

### Why This Matters

- **Removes a `sorry` from a gallery entry.** Until the existence proof is discharged, `F_k(N, ℓ)` is not genuinely well-defined; `Nat.find` is applied to an unproven proposition. Closing it upgrades every downstream statement that mentions `F` from "conditional on a `sorry`" to "resting on a real definition."
- **Fixes a latent correctness bug.** The placeholder witness `N² + 1` is mathematically incorrect for `k ≥ 3`. Documenting and repairing this prevents a future formalizer from wasting effort trying to prove a false statement, and clarifies that the honest threshold bound is `C(N, k)`, not `N²`.
- **Cleanly separates the elementary from the deep.** The *existence* of a finite supersaturation threshold is elementary (it follows from the trivial counting bound). The *quantitative* value `F_k(N, ℓ) = N^{2-o(1)}` is the deep Fox–Pohoata / Leng–Sah–Sawhney content. Establishing well-definedness pins down exactly which part is elementary scaffolding.

## Known Results

### What's Already Proven

- `countAPs_le_choose` (in `Erdos179Incomplete01.lean`) — a set `A` has at most `C(|A|, k)` many `k`-APs, since every AP with `d > 0` is a `k`-element subset (via `arithmeticProgression_card`). This is the exact lemma needed to make `M = C(N, k) + 1` a vacuous witness.
- `arithmeticProgression_card` (in `Erdos179Incomplete01.lean`) — a `k`-AP with positive common difference has exactly `k` elements (injectivity of `i ↦ a + i·d`), the fact underlying the counting bound.
- `countAPs_two` / `AP_free_has_2APs` (in `Erdos179Incomplete01.lean`) — every finite set has exactly `C(N, 2)` two-term APs; establishes the tight count in the base case `k = 2`.
- `Nat.find` and its characterizing lemmas (`Nat.find_spec`, `Nat.find_min`, `Nat.find_le`) — Mathlib's minimization over a decidable existential; once the existential is proven, these give the API for reasoning about `F`.

### What's Still Open

- Discharging the `sorry` inside `supersaturation_exists` in `Erdos179Problem.lean` (the parent's `F` `where`-clause).
- The parent uses the incorrect witness `M = N² + 1`; the fix requires replacing it with `M = C(N, k) + 1` (or any bound `≥ C(N, k)`) and completing the vacuous-implication proof.
- Whether a *tighter* explicit witness (better than `C(N, k)`) can be given elementarily — this is genuinely open and shades into the deep supersaturation problem `F_k(N, ℓ) = N^{2-o(1)}`, which is out of scope here.

### Our Goal

Replace the placeholder witness and complete the existence proof so that `F(k, N, ℓ)` is defined with **0 sorries**: exhibit `M = C(N, k) + 1`, and prove `∀ A, |A| = N → countAPs A k ≥ M → ContainsAP A ℓ` vacuously using `countAPs_le_choose`. This is a targeted, self-contained fix — it does not attempt the quantitative Fox–Pohoata bound.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-179-incomplete-01 | Parent problem; supplies `countAPs_le_choose`, the key vacuity lemma, and the AP-counting scaffolding | Finset image/injectivity, `card_powersetCard`, choose bounds |
| erdos-179 | Root gallery entry stating the Fox–Pohoata / Leng–Sah–Sawhney supersaturation theorem `F_k(N,ℓ) = N^{2-o(1)}` | Analytic number theory, supersaturation |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Vacuous witness `M = C(N, k) + 1`**: Replace `use N^2 + 1` with `use (Nat.choose N k) + 1`. After `intro A hN hcount`, derive a contradiction: `countAPs_le_choose A k` gives `countAPs A k ≤ C(|A|, k) = C(N, k)` (rewriting `|A| = N` via `hN`), which contradicts `hcount : countAPs A k ≥ C(N, k) + 1`. Then `ContainsAP A ℓ` follows from `absurd`/`omega`/`exact absurd hcount (by omega)`.
   - Why it might work: `countAPs_le_choose` is already proven and is exactly the bound needed. The whole implication becomes vacuously true, so no genuine combinatorics is required.
   - Risk: Minimal. The only friction is bookkeeping — rewriting `A.card` to `N` and getting `omega` to see the contradiction. No hidden mathematical content.

2. **Approach B — Genuine finite witness via a global bound**: Prove existence non-vacuously by showing that for *large enough* `M`, no size-`N` set can reach `M` many `k`-APs, using a crude uniform bound like `M = N^k + 1` (since `C(N,k) ≤ N^k`). This is essentially Approach A with a looser, easier-to-manipulate bound that avoids `Nat.choose`.
   - Why it might work: `N^k` is monotone and easy to bound `C(N,k)` by (`Nat.choose_le_pow` style), and arithmetic with powers may be smoother for `omega`/`nlinarith`.
   - Risk: Requires the auxiliary `C(N,k) ≤ N^k` step; slightly more moving parts than Approach A. Still fully elementary.

### Key Difficulties

- The parent's stated witness `N² + 1` is **false** for `k ≥ 3`, so one must recognize that the fix is to *change the witness*, not to prove the original claim. A formalizer who does not notice this will be stuck trying to prove something untrue.
- `countAPs` is `noncomputable` (uses `Classical` on the filter), so the definition of `F` is necessarily `noncomputable`; `Nat.find` still applies since the underlying existential is a `Prop`, but decidability of the `Nat.find` predicate must be available (it is, via `Classical`/`open scoped Classical`).

### What Would a Proof Need?

- Key lemma 1: `countAPs_le_choose A k : countAPs A k ≤ (A.card).choose k` (already proven in the parent-companion file).
- Key lemma 2: the rewrite `A.card = N` to specialize the bound to `C(N, k)`.
- Technical requirements: `open scoped Classical` for decidability of the `Nat.find` predicate; `omega` (or `Nat.not_succ_le_self`-style reasoning) to close the vacuous contradiction; port `countAPs_le_choose` into `Erdos179Problem.lean` (or `import` the companion namespace) so it is in scope at the `F` definition.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The required lemma (`countAPs_le_choose`) is already fully proven in the parent-companion file `Erdos179Incomplete01.lean`; the task is to wire it into the `F` definition with the correct witness.
- The implication becomes *vacuously true*, so no new mathematics is needed — only a witness swap and a short contradiction argument.
- All tactics involved (`omega`, `Finset.card_le_card`, `Nat.choose`) are standard Mathlib and used elsewhere in the same file.

**Estimated Effort**:
- Exploration: 1–2 hours (confirm the witness fix and scope the import)
- If tractable: half a day (edit `Erdos179Problem.lean`, rebuild via Docker wrapper)
- If hard: n/a — the only "hard" variant (a tighter elementary witness) is explicitly out of scope

## References

### Papers
- J. Fox, C. Pohoata, *Sets without k-term progressions can have many shorter progressions*, 2020 — establishes `F_k(N, ℓ) ≤ N² / (log log N)^{C_ℓ}`; the deep upper bound the parent's `F` ultimately targets.
- Z. K. Leng, A. Sah, M. Sawhney, 2024 — sharpens the supersaturation bound to `N² / exp((log log N)^{c_ℓ})`.

### Online Resources
- https://erdosproblems.com/179 — Erdős Problem #179 statement and status.

### Mathlib
- `Mathlib.Data.Nat.Find` (`Nat.find`, `Nat.find_spec`, `Nat.find_le`, `Nat.find_min`) — minimization over a decidable existential; the machinery behind `F`.
- `Mathlib.Combinatorics.Choose.Bounds` / `Mathlib.Data.Nat.Choose.Basic` — `Nat.choose` and inequalities such as `Nat.choose_le_pow_of_lt_half_left`, `Nat.choose_le_pow`, used to bound `C(N, k) ≤ N^k` for Approach B.
- `Mathlib.Data.Finset.Powerset` (`Finset.powersetCard`, `Finset.card_powersetCard`) — the `C(N, k)` counting identity underlying `countAPs_le_choose`.

## Metadata

```yaml
tags:
  - additive-combinatorics
  - arithmetic-progressions
  - supersaturation
  - counting
  - erdos
related_proofs:
  - erdos-179
  - erdos-179-incomplete-01
difficulty: low
source: gallery-gap
created: 2026-07-09T16:59:48-07:00
```
