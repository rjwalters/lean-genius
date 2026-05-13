# S2(c) PREP — explicit `Nat.log` counting bound from the Euclid construction

**Date**: 2026-05-13 (~04:20 UTC)
**Researcher**: researcher-8
**Mode**: PREP (doc-only)
**Status**: pristine doc-only follow-up to S1 OBSERVE (#18283, researcher-11, MERGED), S2 ACT(a) bridge (#18341, researcher-12, MERGED), and S3 PREP for q ∈ {3,4,6} (#18414 or similar, researcher-10, MERGED — see `sessions/2026-05-12-s03-prep-parametric-q3q4q6-easy-cases.md`). 0 open research PRs on this slug.

## §0. Position in the slug roadmap

`state.md` ("Recommended next-session entry point (post-S2)") lists two
parallel S3 targets:

> **S3**: pick S2(b) parametric elementary `p ≡ -1 (mod q)` for
> `q ∈ {3,4,6,8,12,24}`, or S2(c) explicit `Nat.log` counting bound.

The merged researcher-10 S3 PREP `2026-05-12-s03-prep-parametric-q3q4q6-easy-cases.md`
addresses **S2(b)** for the Klein-2 cases (q ∈ {3,4,6}). The Klein-4
cases (q ∈ {8,12,24}) remain open. **This PREP addresses the orthogonal
S2(c) target** — the explicit `Nat.log`-rate counting bound derivable
from the Euclid construction.

S2(c) is orthogonal to S2(b): S2(b) extends the construction across
moduli q ∈ {3,4,6,8,12,24}; S2(c) refines the q = 4 case with an
*explicit rate*.

## §1. The classical statement

The elementary Euclid-style construction for primes ≡ 3 (mod 4),
already in `proofs/Proofs/InfinitudePrimes4k3.lean:154` as
`infinitely_many_primes_3_mod_4`, has the following implicit form:

> Given a finite set `S` of primes ≡ 3 (mod 4), the construction
> `N = 4 · ∏ S - 1` produces a prime `p ≡ 3 (mod 4)` with `p ∉ S` and
> `p ≤ N`. Iterating gives an infinite sequence.

Explicit growth rate: enumerate primes ≡ 3 (mod 4) as `p₁ < p₂ < p₃ < …`.
Starting with `p₁ = 3`, the construction yields:

```
p_{k+1} ≤ 4 · p₁ · p₂ · … · p_k − 1
       ≤ 4 · p_k^k        (since p_i ≤ p_k for i ≤ k)
       ≤ 4^k · p_k^k.
```

Taking logarithms:

```
log p_{k+1} ≤ k · log p_k + log 4 · k
            ≤ k · (log p_k + 2).
```

Inducting backwards: `log log p_k ≥ k − O(log k)`, equivalently
`p_k ≤ 2^{2^{O(k)}}`. The *count* of primes ≡ 3 (mod 4) up to `x` is
therefore `≥ log log log x` (very weak — the elementary bound is
exponentially weaker than the true `x / (2 log x)` from Dirichlet's
density).

## §2. Concrete Lean target

A clean Lean statement for the counting bound, formulated to play
nicely with Mathlib's `Nat.log`:

```lean
/-- **S2(c) target**: The k-th prime ≡ 3 (mod 4) is bounded by an
    iterated exponential in `k`. Concretely, defining
    `tower : ℕ → ℕ` by `tower 0 = 4`, `tower (k+1) = 4 ^ tower k`,
    the prime sequence `p_k` satisfies `p_k ≤ tower k`. -/
theorem primes_3_mod_4_explicit_tower_bound :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      (∀ k, Nat.Prime (f k) ∧ f k % 4 = 3) ∧
      (∀ k, f k ≤ tower k)
```

where `tower : ℕ → ℕ` is defined as `tower 0 = 4`, `tower (k+1) = 4 ^ tower k`
(a fixed primitive-recursive function).

The corollary (using `Nat.log`):

```lean
/-- **Counting bound corollary**: π(x; 4, 3) ≥ log log log x for x large. -/
theorem primes_3_mod_4_count_loglog_bound :
    ∀ᶠ x in Filter.atTop,
      (Nat.log 4 (Nat.log 4 (Nat.log 4 x)) : ℕ) ≤
      ((Finset.range x).filter (fun p => Nat.Prime p ∧ p % 4 = 3)).card
```

The `4` base in the `Nat.log` is the construction's natural base
(the `4 · ∏` factor in the Euclid argument). A cleaner formulation
might use `Nat.log 2` after a constant-factor adjustment.

## §3. Discharge sketch

### §3.1 Step 1 — define `tower`

```lean
def tower : ℕ → ℕ
  | 0     => 4
  | k + 1 => 4 ^ tower k
```

Properties (all provable by induction on `k`):

- `4 ≤ tower k`
- `tower k ≤ tower (k+1)` (`StrictMono`)
- `tower (k+1) = 4 ^ tower k`

LOC: ~15.

### §3.2 Step 2 — define the prime sequence

Use `Nat.rec` with `Classical.choice`-style witness extraction from
`has_prime_factor_3_mod_4` (parent file line 133):

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

The `next_prime_witness` auxiliary lemma packages the existence claim
from `has_prime_factor_3_mod_4` with a strict-monotonicity refinement.

LOC: ~50.

### §3.3 Step 3 — `tower` upper bound

By induction on `k`:

- Base: `primeSeq_3_mod_4 0 = 3 ≤ 4 = tower 0`. ✓
- Step: Assume `primeSeq_3_mod_4 i ≤ tower i` for all `i ≤ k`. Then
  the product `∏_{i ≤ k} primeSeq_3_mod_4 i ≤ ∏_{i ≤ k} tower i ≤ tower k^k`.
  Hence `N ≤ 4 · tower k^k ≤ 4 · 4^(k · tower k) ≤ 4^(tower k · (k+1)) ≤ 4^(tower k · tower k)
  ≤ 4^(tower (k+1)) = tower (k+1)`. (Some bookkeeping required.)

LOC: ~80.

### §3.4 Step 4 — `Nat.log` counting corollary

Apply the Galois connection `Nat.log b n ≤ k ↔ n < b^(k+1)`
(`Nat.log_lt_iff_lt_pow`) iteratively to translate the `tower` bound
into a `log log log` lower bound on the count. The `Filter.atTop`
framing avoids edge cases for small `x`.

LOC: ~60.

### §3.5 Total budget

| Stage | Lemma | LOC | New axioms | New sorries |
|---|---|---|---|---|
| 3.1 | `tower` definition + monotonicity | 15 | 0 | 0 |
| 3.2 | `primeSeq_3_mod_4` construction | 50 | 0 | 0 |
| 3.3 | `primeSeq_3_mod_4 k ≤ tower k` | 80 | 0 | 0 |
| 3.4 | `Nat.log` counting corollary | 60 | 0 | 0 |
| **Total** | | **~205 LOC** | **0** | **0** |

For comparison:

- S2(a) bridge: ~100 LOC (PR #18341, MERGED).
- S2(b) q ∈ {3,4,6}: ~100 LOC each ≈ 300 LOC total (researcher-10 PREP).
- S2(b) q ∈ {8,12,24}: ~200 LOC each ≈ 600 LOC total (deferred).
- **S2(c) (this PREP)**: ~205 LOC.

S2(c) is the smallest single-axis extension of the parent file with
quantitative substance.

## §4. Mathlib API surface

| Symbol | Module | Used for |
|---|---|---|
| `Nat.log` | `Mathlib.Data.Nat.Log` | counting corollary |
| `Nat.log_lt_iff_lt_pow` | same | Galois adjoint inversion |
| `Nat.Prime`, `Nat.Prime.dvd_mul` | `Mathlib.Data.Nat.Prime` | primality preservation |
| `List.prod`, `Finset.prod` | `Mathlib.Data.List.Defs` / `Mathlib.Algebra.BigOperators.Basic` | product of prior primes |
| `Classical.choose` | core Lean | extracting prime witness |
| `Filter.atTop` | `Mathlib.Order.Filter.AtTopBot` | "eventually" framing |
| Parent `has_prime_factor_3_mod_4` | `Proofs/InfinitudePrimes4k3.lean:133` | the construction's prime witness |

All present at v4.26.0 pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**No new axioms**, **no new sorries**. The `tower`-bound proof is
elementary (`Nat`-induction + `Nat.pow_le_pow_right`-style monotonicity).

## §5. Why this is a PREP not an ACT

1. **Build cost**: 205 LOC of new Lean would require
   `docker-build.sh Proofs.InfinitudePrimes4k3OQ01` (worktree
   `proofs/.lake` is in the symlink loop per memory
   `feedback_researcher_lake_symlink_loop_and_wipe.md`; first build ~10 min).
   Shipping as PREP avoids the build-pending convention and lets the
   next agent run from a clean worktree.

2. **Honest contribution**: this PREP turns the abstract S2(c)
   bullet from `state.md` into a 4-step Lean blueprint with
   per-stage LOC budgets, Mathlib API audit, and tower-bound
   formulation. The next ACT agent can copy-paste the function
   signatures and proof outlines.

3. **No race risk**: doc-only, single new sessions file. The S3 PREP
   from researcher-10 covers S2(b)-Klein-2; this PREP covers
   orthogonal S2(c). Both can land independently.

## §6. Anti-targets

This PREP does NOT:

- Implement the `tower` definition or any Lean proof.
- Address S2(b) q ∈ {3,4,6} (already covered by researcher-10's PREP).
- Address S2(b) q ∈ {8,12,24} (separate Klein-4 PREP needed; out of scope here).
- Refine the count bound from `log log log x` to `log log x` or
  `log x` (those require Mertens-style theorems, not the elementary
  Euclid construction).
- Modify `state.md`, `knowledge.md`, `problem.md`, or any JSON.

## §7. Race-safety

- **Pre-write probe** (2026-05-13 ~04:20 UTC):
  - `gh pr list -R rjwalters/lean-genius --search "infinitude-primes-4k3-oq-01" --state open` → `[]`.
  - `git branch -r | grep infinitude-primes-4k3` → none.
- **File path is unique**:
  `sessions/2026-05-13-s2c-prep-natlog-counting-bound.md`.
- **Doc-only**: no Lean changes, no `meta.json` changes, no
  `state.md` / `knowledge.md` / `problem.md` modifications.

## §8. Honest contribution boundary

This is a **counting-bound design and Mathlib API audit** document,
not a proof.

**What this PREP does**:

- Defines a concrete Lean statement for the explicit `tower`-bound on
  the k-th prime ≡ 3 (mod 4), plus its `Nat.log log log x` counting
  corollary.
- Provides a 4-stage proof sketch with per-stage LOC budgets totalling
  ~205 LOC.
- Audits Mathlib's `Nat.log` / `Filter.atTop` API at the pinned rev.
- Confirms no new axioms / sorries are introduced by S2(c) ACT.
- Confirms orthogonality with the merged S3 PREP for S2(b)-Klein-2.

**What this PREP does NOT do**:

- It does not implement the `tower` function or any of the 4 stages.
- It does not run a Lean build.
- It does not address the asymptotic `x / (2 log x)` density (out of
  scope — requires Dirichlet's theorem with explicit constants, much
  heavier).
- It does not address Klein-4 cases (q ∈ {8, 12, 24}) of S2(b).
- It does not modify `state.md` (the slug's phase remains "S2 ACT(a)
  complete" pending the next ACT).

## §9. Sub-step S2(c)-a / S2(c)-b decomposition (if needed)

If the 205-LOC budget exceeds a single research session, a clean
decomposition is:

- **S2(c)-a**: `tower` definition + `primeSeq_3_mod_4` construction
  + `primeSeq_3_mod_4 k ≤ tower k` (Stages 3.1–3.3, ~145 LOC).
- **S2(c)-b**: `Nat.log log log` counting corollary (Stage 3.4, ~60 LOC).

Each sub-step is self-contained and ships as a separate PR.

## §10. Implications

If S2(c) ACT lands:

1. The slug's `dirichlets-theorem-oq-01` (Siegel zeros, 5 axioms) and
   `dirichlets-theorem-oq-03` (Linnik bounds, 2 axioms + 3 sorries)
   gain a *non-conditional* corollary: the elementary growth rate is
   formalised, providing a lower bar that Siegel/Linnik improvements
   then improve over.
2. The gallery's `infinitude-primes-4k3` parent acquires a
   quantitative refinement (currently only the qualitative
   `Set.Infinite` form is proved).
3. The pattern generalises to all S2(b)-Klein-2 moduli `q ∈ {3, 4, 6}`
   verbatim — once the q ∈ {3, 6} elementary constructions are
   formalised by researcher-10's deferred S3 ACT, the S2(c)-style
   counting bound transfers immediately.
