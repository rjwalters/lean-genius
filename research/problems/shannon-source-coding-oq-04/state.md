# Research State: shannon-source-coding-oq-04

## Current State
**Phase**: SCOPED — sorry isolated, proof outline in hand
**Since**: 2026-04-27T17:55:00Z
**Iteration**: 2

## Current Focus

`proofs/Proofs/ShannonSourceCodingOQ04.lean` (429 lines, 0 axioms, 1 sorry).
The single sorry is at line 386 in `source_coding_achievability_mot` — the main
achievability theorem of the Shannon source coding theorem via the method of types.

**Definition of the local `shannonEntropy`** in this file is `H(p) = -∑ pᵢ log₂ pᵢ` and is
used inside the conclusion.

The supporting infrastructure is already proved:

| Lemma | Role |
|---|---|
| `type_class_size_eq_multinomial` | |T_f| = n!/∏(fᵢ!) (combinatorial identity) |
| `count_types_le` | distinct types ≤ (n+1)^k (polynomial in n) |
| `total_sequences_eq` | Total k^n sequences |
| `dominant_type_lower_bound` | Largest type class has ≥ k^n / (n+1)^k sequences |
| `type_class_size_le_entropy_pow` | |T_f| ≤ 2^{n H(Q)} (entropy upper bound) |

What remains for the sorry:

The conclusion `(typeClass n f hf).card ≤ 2 ^ code_length` with
`code_length ≤ n·H(p) + nε` must be exhibited together with the existence of
the type vector `f`. The intended construction is:
1. Choose `f` to be the dominant type (closest to `n·p` componentwise) — by
   `dominant_type_lower_bound`, the dominant type class has size ≥ k^n / (n+1)^k.
2. Bound that class size from above using `type_class_size_le_entropy_pow` for
   the dominant type's empirical distribution Q (which is ε-close to p for
   sufficiently large n by the standard Bernstein/Chernoff concentration).
3. Set `code_length = ⌈n·H(p) + nε⌉` so 2^{code_length} ≥ 2^{n·H(p)+nε} ≥ |T_f|
   for all sufficiently large n (by 2^{nε/2} eventually dominating the
   entropy-continuity error |H(Q) - H(p)| ≤ ε/2).

## Mathlib API Survey (Mathlib 4.26.0)

| Symbol | Use |
|---|---|
| `Mathlib.InformationTheory.KullbackLeibler.Basic` | KL divergence — useful for entropy continuity |
| `Mathlib.InformationTheory.KullbackLeibler.KLFun` | KL function and properties |
| `Mathlib.InformationTheory.Hamming` | Hamming distance (unrelated) |
| `Real.logb` | Used in `shannonEntropy` definition |
| `Real.exp_log` / `Real.rpow_logb` | Conversion between log and rpow |

Mathlib does **not** have a Shannon entropy function with the standard name (the
file's `shannonEntropy` is locally defined). It does have KL divergence, from which
H(p) = log(k) - D(p ‖ uniform) for finite alphabets — could be used as a bridge if
needed.

## Active Approach

**Direction: close the sorry directly using the lemmas already in the file.**

The proof is mostly bookkeeping: choose `code_length := Nat.ceil (n * shannonEntropy p + n * ε)`,
exhibit the dominant type vector, and chain `dominant_type_lower_bound` with
`type_class_size_le_entropy_pow`. The hardest sub-step is the **continuity-of-entropy**
argument: for any δ > 0, there is N such that |H(Q) - H(p)| ≤ δ whenever ‖Q - p‖_∞ ≤ 1/N.
This needs continuity of `shannonEntropy` (which is `x log x` integrable), but for the
discrete finite-alphabet case it is just continuity of a polynomial-in-rpow expression.

Estimated proof length: 50–80 lines of Lean.

## Blockers

**Disk space tight (2026-04-27): 90% capacity, ~1.4 GB free.** Closing the sorry
requires several Docker iteration cycles to debug log/rpow manipulation (Lean's
`Real.logb` lemmas are notoriously fiddly in proofs). Not safe this session per
researcher feedback memory.

## Next Action

For a future researcher session (disk > 5 GB free):

1. Read the file's `shannonEntropy` definition (around the imports) to confirm exact
   form (logb base 2 vs. nats).
2. Add a helper lemma `entropy_continuity_at_p`: for any δ > 0, ∃ N, ∀ Q with
   ‖Q - p‖_∞ ≤ 1/N, |H(Q) - H(p)| ≤ δ. ~20 lines using `Continuous.tendsto`.
3. Replace the sorry on line 386 by chaining `dominant_type_lower_bound` (existence
   of the dominant type) with `type_class_size_le_entropy_pow` (size bound), then
   bridge via the continuity lemma. ~40 lines.
4. Build with `./proofs/scripts/docker-build.sh Proofs.ShannonSourceCodingOQ04`.
5. Update `meta.json`: `sorries` 1 → 0, `status` `formalized` → `verified`,
   `badge` `wip` → `verified`.

This problem is **tractable in a single session** with disk headroom — the sorry is
isolated and all supporting lemmas are already proved.

## Attempt Counts
- Total attempts: 1 (sorry isolation + Mathlib survey, no code changes)
- Current approach attempts: 1
- Approaches tried: 1 (proof-outline scoping — concluded single-session feasible
  given Docker availability)
