# Keystone — k-th Courant–Fischer min-max: complete proof design

**Author**: researcher-11, 2026-06-15 (iter 4)
**Status**: full mathematical proof + per-step Mathlib lemma map. **No Lean
compiled** (both backends down this session: Docker pool saturated at 3
concurrent `lean-build` containers on the 7.65 GiB VM; Aristotle MCP `prove` →
`Resource not found`). This document is robust to the missing compiler because
its content is the *argument*, not Lean syntax — the next backend-up session (or
Aristotle) transcribes it.

> Prior iterations (1–3, see `orient-min-max-scaffolding.md`) deliberately
> deferred this lemma: they flagged the k-th min-max as "the keystone, build it"
> but never worked out **how**. This document is that work. Steps 2 and 4 of the
> §6 roadmap (extreme cases, final assembly) are bookkeeping over confirmed
> Mathlib API; **this** lemma is the only genuine new-theory piece, so it is
> where design effort belongs.

## 0. Setup and conventions

Work in the **operator** setting (sorted eigenvalues come for free; see iter-3
correction in the scaffolding memo). Fix:

- `𝕜 = ℝ` or `ℂ` (`[RCLike 𝕜]`), `E` a finite-dimensional inner product space
  over `𝕜`, `n : ℕ` with `hn : Module.finrank 𝕜 E = n`, and `[Nontrivial E]`
  where needed (so `n ≥ 1`).
- `T : E →ₗ[𝕜] E`, `hT : T.IsSymmetric`.
- `μ : Fin n → ℝ := hT.eigenvalues hn`, the **decreasing** eigenvalue tuple
  (`LinearMap.IsSymmetric.eigenvalues_antitone : Antitone (hT.eigenvalues hn)`),
  with orthonormal eigenbasis `b := hT.eigenvectorBasis hn : OrthonormalBasis (Fin n) 𝕜 E`
  and the diagonalisation
  `hT.apply_eigenvectorBasis hn i : T (b i) = (μ i : 𝕜) • b i`.
- Rayleigh quotient `R : E → ℝ`, `R x := RCLike.re ⟪T x, x⟫ / ‖x‖ ^ 2`. (This is
  the `LinearMap`-level spelling; it agrees with
  `ContinuousLinearMap.rayleighQuotient (T : E →L[𝕜] E)` in finite dimensions —
  keep the proof on **one** spelling to avoid a CLM/LM coercion detour; prefer
  defining a local `R` and a one-line `rayleigh_eq` bridge lemma rather than
  threading `reApplyInnerSelf` through the whole proof.)

**Target (max–min form, the one used by interlacing's lower bound):**

```
μ k = ⨆ (S : Submodule 𝕜 E) (_ : finrank 𝕜 S = k+1), ⨅ (x : {x : E // x ∈ S ∧ x ≠ 0}), R x
```

i.e. `μ k = max over (k+1)-dim subspaces S of (min over nonzero x ∈ S of R x)`.

The dual **min–max form** `μ k = ⨅_{finrank S = n-k} ⨆_{x∈S\0} R x` is obtained by
applying the max–min form to `-T` (whose eigenvalues are `-μ` in reverse order)
**or** proved symmetrically. Interlacing uses *both*: max–min for the lower
bound `λ_k ≤ μ_k`, min–max for the upper bound `μ_k ≤ λ_{k+1}` (scaffolding §3).
Design the max–min form fully; the dual is a mechanical mirror.

## 1. Two reusable sublemmas (build these first, standalone)

### Sublemma A — Rayleigh bounds on a coordinate eigenspan

For a subset `I : Finset (Fin n)` and any `0 ≠ x ∈ span 𝕜 (b '' I)`:

```
(⨅ i ∈ I, μ i) ≤ R x ≤ (⨆ i ∈ I, μ i).
```

*Proof.* Write `x = ∑ i ∈ I, c i • b i` (membership in the span of an
orthonormal family; coefficients `c i = ⟪b i, x⟫` by `OrthonormalBasis.repr` /
`Orthonormal.inner_right_finsupp`). Two Parseval computations:

- `‖x‖^2 = ∑ i ∈ I, ‖c i‖^2` — `OrthonormalBasis.norm_sq_eq_sum` restricted to
  the support `I` (orthonormality kills cross terms:
  `Orthonormal.inner_left_fintype` / `orthonormal_iff_ite`).
- `RCLike.re ⟪T x, x⟫ = ∑ i ∈ I, μ i * ‖c i‖^2` — expand `T x = ∑ μ i • c i • b i`
  via `apply_eigenvectorBasis` and linearity (`map_sum`, `map_smul`), then the
  same orthonormality collapse. `μ i` real ⇒ `RCLike.re` passes through.

So `R x = (∑ i∈I μ i ‖c i‖²) / (∑ i∈I ‖c i‖²)` is a **convex combination** of the
`μ i, i ∈ I` (weights `‖c i‖² / ‖x‖² ≥ 0` summing to 1, denominator `> 0` since
`x ≠ 0`). A convex combination lies between the min and max of its support:
`Finset.inner_le_weight_...`-style bounds, or directly
`div_le_iff`/`le_div_iff` + `Finset.sum_le_sum` against the constant `⨆`/`⨅`.
∎

This sublemma is the workhorse; it instantly gives:
- `R (b i) = μ i` (take `I = {i}`), used for tightness/achievement.
- "On `span (b '' {0..k})`, `R ≥ μ k`" (min over that `I` is `μ k`, since `μ`
  decreasing ⇒ smallest index-value on `{0..k}` is `μ k`).
- "On `span (b '' {k..n-1})`, `R ≤ μ k`" (max over that `I` is `μ k`).

### Sublemma B — nontrivial intersection by dimension count

For submodules `V W : Submodule 𝕜 E` with `finrank V + finrank W > n`:

```
∃ x ∈ V ⊓ W, x ≠ 0.
```

*Proof.* `Submodule.finrank_sup_add_finrank_inf_eq V W` gives
`finrank (V ⊔ W) + finrank (V ⊓ W) = finrank V + finrank W`. Since
`finrank (V ⊔ W) ≤ finrank E = n` (`Submodule.finrank_le`), rearrange:
`finrank (V ⊓ W) ≥ finrank V + finrank W - n ≥ 1 > 0`. A submodule of positive
finrank is `≠ ⊥` (`Submodule.one_le_finrank_iff` / `finrank_pos_iff`), so it has
a nonzero element (`Submodule.exists_mem_ne_zero_of_ne_bot` /
`Submodule.ne_bot_iff`). ∎

This is the codimension count that the textbook proof hides in "two subspaces
whose dimensions sum to more than `n` must meet."

## 2. Proof of the max–min identity

Let `k : Fin n`. Abbreviate the inner objective `m S := ⨅_{0≠x∈S} R x` and the
witness subspace `Vlo := span 𝕜 (b '' {i | i ≤ k})` (dimension `k+1`, since `b`
is a basis ⇒ the image of an injective index set is independent ⇒
`finrank = card {i ≤ k} = k+1`; `finrank_span_eq_card` +
`OrthonormalBasis.linearIndependent`).

### (≥) `μ k ≤ ⨆_S m S`: exhibit the witness `Vlo`.

By Sublemma A applied with `I = {i | i ≤ k}`: every nonzero `x ∈ Vlo` has
`R x ≥ ⨅_{i ≤ k} μ i = μ k` (the min of a decreasing tuple over `{0..k}` is its
last value `μ k`; `Finset.le_inf'` / `ciInf` with `μ` antitone). Hence
`m Vlo = ⨅_{0≠x∈Vlo} R x ≥ μ k` (`le_ciInf`). And `m Vlo ≤ ⨆_S m S` because
`Vlo` is one admissible `(k+1)`-dim subspace (`le_ciSup` with the boundedness
from §3). Chain: `μ k ≤ m Vlo ≤ ⨆_S m S`.

*(Tightness, not needed for the inequality but confirms no slack: `b k ∈ Vlo`,
`b k ≠ 0`, `R (b k) = μ k`, so `m Vlo ≤ μ k` too ⇒ `m Vlo = μ k`.)*

### (≤) `⨆_S m S ≤ μ k`: every admissible `S` has `m S ≤ μ k`.

Fix any `S` with `finrank S = k+1`. Let `Vhi := span 𝕜 (b '' {i | k ≤ i})`,
of dimension `card {i | k ≤ i} = n - k`. Then
`finrank S + finrank Vhi = (k+1) + (n-k) = n+1 > n`, so **Sublemma B** yields
`0 ≠ x₀ ∈ S ⊓ Vhi`. Since `x₀ ∈ Vhi`, Sublemma A (with `I = {i | k ≤ i}`) gives
`R x₀ ≤ ⨆_{k ≤ i} μ i = μ k` (max of a decreasing tuple over `{k..n-1}` is its
first value `μ k`). Since `x₀ ∈ S` and `x₀ ≠ 0`, `m S = ⨅_{0≠x∈S} R x ≤ R x₀ ≤ μ k`
(`ciInf_le` with the lower bound from §3). As `S` was arbitrary,
`⨆_S m S ≤ μ k` (`ciSup_le`). ∎

Combining (≥) and (≤): `⨆_S m S = μ k`. □

## 3. Boundedness obligations (do not skip — `ciInf`/`ciSup` need them)

`⨅`/`⨆` over possibly-empty or unbounded families return junk in Lean unless
`BddBelow`/`BddAbove` (and nonempty) are discharged. Concretely:

- Inner `⨅_{0≠x∈S} R x`: `BddBelow` by `μ (n-1)` (global min eigenvalue;
  Sublemma A with `I = univ` ⇒ `R x ≥ μ (last)` for all `x ≠ 0`). Nonempty
  because `finrank S = k+1 ≥ 1 ⇒ S ≠ ⊥ ⇒ ∃ 0 ≠ x ∈ S`.
- Outer `⨆_S m S`: `BddAbove` by `μ 0` (global max; Sublemma A ⇒ `m S ≤ μ 0`).
  Nonempty because `Vlo` is an admissible subspace.

Package these as two `have` lemmas up front; they are reused at every `le_ciSup`
/ `ciInf_le` invocation above. **This is the single most common way a min-max
formalization silently breaks** — budget for it.

## 4. Mathlib lemma checklist (names to confirm at build time, pin v4.26.0)

| Step | Lemma(s) |
|------|----------|
| eigenbasis diagonalises | `LinearMap.IsSymmetric.apply_eigenvectorBasis` |
| eigenvalues decreasing | `LinearMap.IsSymmetric.eigenvalues_antitone` |
| repr in ON basis | `OrthonormalBasis.repr`, `Orthonormal.inner_right_finsupp` |
| Parseval norm | `OrthonormalBasis.norm_sq_eq_sum` (or `_eq_sum_inner_sq`) |
| intersection dim | `Submodule.finrank_sup_add_finrank_inf_eq`, `Submodule.finrank_le` |
| pos finrank ⇒ ≠⊥ | `Submodule.finrank_pos_iff` / `one_le_finrank_iff`, `Submodule.exists_mem_ne_zero_of_ne_bot` |
| span dim = card | `finrank_span_eq_card`, `OrthonormalBasis.linearIndependent` |
| convex-combo bound | `Finset.sum_le_sum` + `div_le_iff` / `le_div_iff` (or `inner_le_nnorm`-free direct) |
| ⨆/⨅ plumbing | `le_ciSup`, `ciSup_le`, `le_ciInf`, `ciInf_le`, `BddAbove`/`BddBelow` |

Names are stable across recent Mathlib but **were checked against master, not the
`v4.26.0` pin** — re-confirm `eigenvalues_antitone`, `apply_eigenvectorBasis`,
and `finrank_sup_add_finrank_inf_eq` at first build. If `eigenvalues_antitone` is
absent in the pin, it is derivable from `eigenvalues` being defined via
`Tuple.sort` (monotone-by-construction).

## 5. Why this unblocks the whole problem

With the max–min lemma (and its `-T` dual) in hand, scaffolding §3 reduces
one-step interlacing to **Sublemma B alone** (the `dim (S ∩ H_i) ≥ dim S - 1`
count) plus monotonicity of `⨅`/`⨆` under the subspace restriction `S ↦ S ⊓ H_i`
and the domain inclusion `H_i ⊆ E`. No further new theory. So the realistic
build-up order, once a backend returns, is:

1. Sublemma A + Sublemma B (standalone, ~Aristotle-friendly, no open math).
2. Boundedness `have`s (§3).
3. max–min identity (§2), then dual via `-T`.
4. Interlacing assembly (scaffolding §3) — now pure bookkeeping.

Each of 1–3 is an independent, **closed** (known-mathematics) target — exactly
the HARD-not-OPEN profile Aristotle handles well — so when the MCP backend
returns, submit Sublemma A and Sublemma B first; they are the leaf dependencies
and unblock everything above them.

## 6. Honesty notes

- Nothing here is machine-checked; no `.lean` shipped this session (both backends
  down). The argument is classical (Courant–Fischer); the contribution is the
  **per-step Mathlib mapping** and the explicit boundedness/intersection
  obligations that a naive transcription would miss.
- The convex-combination step (Sublemma A) is the one place where the cleanest
  Mathlib spelling is uncertain without a compiler; the fallback (manual
  `div`/`sum_le_sum`) is spelled out so it is not a blocker.
