# Problem: Primes ≡ 1 (mod 4) have density 1/2 among primes

## Statement

### Plain Language

The parent proof `cube-root-3-irrational`'s sibling
`infinitude-primes-4k1` (`Proofs/InfinitudePrimes4k1.lean`) establishes
the **infinitude** of primes congruent to `1 (mod 4)` by an elementary
argument (Fermat sums-of-two-squares + Euler's criterion: any odd prime
dividing `k² + 1` is `≡ 1 (mod 4)`).

This OQ asks for the much stronger **density** form:

$$
\lim_{N \to \infty} \frac{\#\{p \le N : p \text{ prime},\, p \equiv 1 \pmod{4}\}}{\pi(N)} \;=\; \tfrac{1}{2}
$$

This is a specialization of the **prime number theorem for arithmetic
progressions** (PNT-AP), or equivalently — at weaker resolution — of
**Dirichlet's density theorem** of 1837.

For `q = 4`, the reduced residues are `{1, 3}` (i.e. `(ℤ/4ℤ)ˣ` has
order `φ(4) = 2`), so each class is hit by half the primes.

### Formal Statement

Two natural targets in Lean, corresponding to the two flavors of density:

**Natural-density form (PNT-AP, harder)**:

```lean
-- Density in N (`π(N; 4, 1) / π(N) → 1/2`)
theorem primes_4k1_natural_density :
    Tendsto
      (fun N => ((Nat.primeCounting N).filter (· % 4 = 1)).card / (Nat.primeCounting N) : ℕ → ℝ)
      atTop (𝓝 (1/2)) := by sorry
```

**Dirichlet-density form (analytic / log-scale, easier)**:

```lean
-- ∑_{p ≡ 1 [4]} p^{-s}  ~  (1/2) · ∑_p p^{-s}  as s ↘ 1
theorem primes_4k1_dirichlet_density :
    Tendsto
      (fun s : ℝ => (∑' p : {p : ℕ // p.Prime ∧ p % 4 = 1}, (p : ℝ) ^ (-s))
                  / (∑' p : {p : ℕ // p.Prime}, (p : ℝ) ^ (-s)))
      (𝓝[>] 1) (𝓝 (1/2)) := by sorry
```

The natural-density form implies the Dirichlet-density form; the
converse requires Tauberian techniques.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - seeker-selected
  - number-theory
  - prime-numbers
  - modular-arithmetic
  - dirichlet-theorem
  - sum-of-two-squares
  - mathlib-bridge
```

**Significance**: 6/10 — Specialization of a marquee result (PNT-AP /
Dirichlet density). The `q = 4` case is the simplest non-trivial
arithmetic progression that requires the full L-function machinery; it
is also the case most accessible to elementary readers because of the
Euler-criterion / sum-of-two-squares connection at the level of
infinitude. Density 1/2 makes a particularly clean theorem statement.

**Tractability**: 6/10 — Tractable only as a **Mathlib bridge**: the
deep work (Dirichlet character theory, L-function nonvanishing,
Ikehara Tauberian theorem) is already in Mathlib at the pinned
revision. The OQ-03 deliverable is to **wire up** these results to
the `q = 4, a = 1` instance, not to reprove them. The wiring itself
is straightforward `Mathlib.NumberTheory.LSeries.PrimesInAP` API +
`Nat.totient 4 = 2` computation.

## Why This Matters

1. **Gallery completeness** — `infinitude-primes-4k1` proves the
   *infinitude* form elementarily but stops short of the quantitative
   density. Pairing them gives a 1-2 punch: "infinitely many" (the
   easy half of Dirichlet 1837) plus "with density 1/2" (the hard
   half, via L-functions). This is the canonical pedagogical sequence
   for introducing Dirichlet's theorem.

2. **First Mathlib PNT-AP instance in the gallery** — Mathlib's
   `Mathlib.NumberTheory.LSeries.PrimesInAP` was completed in 2024-2025
   (Stoll, Stephan, Mehta and collaborators). It establishes the
   density form for **all** valid `(q, a)`. The gallery has no
   specialization of it yet; this OQ would be the first.

3. **Companion to sum-of-two-squares** — Primes ≡ 1 (mod 4) are
   exactly the primes that are sums of two squares (Fermat's two-square
   theorem). The density 1/2 statement therefore says: *half* of all
   primes are sums of two squares. This is a striking fact that's
   easy to state, hard to prove, and not in the gallery.

4. **Drift-robust target** — Mathlib's PNT-AP infrastructure is recent
   and active; locking in a specific specialization here gives the
   project a CI canary for L-function-related drift.

## Theoretical Path

### The deep input: PNT for arithmetic progressions

The **prime number theorem for arithmetic progressions** states: for
coprime `a, q`,

$$
\pi(N; q, a) \;:=\; \#\{p \le N : p \equiv a \pmod q,\; p \text{ prime}\}
\;\sim\; \frac{1}{\varphi(q)} \cdot \frac{N}{\log N}.
$$

This is equivalent (after dividing by `π(N) ~ N/log N`) to

$$
\frac{\pi(N; q, a)}{\pi(N)} \;\longrightarrow\; \frac{1}{\varphi(q)}.
$$

For `q = 4, a = 1`: `φ(4) = #(ℤ/4ℤ)ˣ = #{1, 3} = 2`, giving
`density = 1/2`.

### Proof strategy in Mathlib

The path goes through Dirichlet characters and L-functions:

1. The Dirichlet characters mod 4 are the trivial character `χ₀` and
   the unique nontrivial real character `χ₁` (the Legendre symbol
   `n ↦ (-1)^((n-1)/2)` extended by 0 on even `n`).

2. The associated L-function is `L(s, χ₁) = β(s)`, the Dirichlet
   beta function (Mathlib: `DirichletCharacter.LFunction`).

3. **Nonvanishing on Re s = 1** is established in Mathlib
   (`DirichletCharacter.LFunction_ne_zero_of_re_eq_one`).

4. **Ikehara Tauberian theorem** (Mathlib:
   `NumberTheory.LSeries.Wiener` / `LSeries.IkeharaTauberian`) extracts
   the natural-density asymptotic from the L-function analytic data.

5. Combining the trivial and nontrivial character contributions via
   orthogonality (Mathlib: `DirichletCharacter.sum_apply_eq_indicator`)
   isolates the residue class `1 mod 4`.

### Tractable subgoals

For OQ-03 work, the targets in increasing depth are:

| Subgoal | Mathlib leverage | Difficulty |
|---------|-------------------|------------|
| `φ(4) = 2` computation | `Nat.totient_prime_pow_one_lt` / `decide` | Trivial |
| Reduced residues mod 4 are `{1, 3}` | `ZMod.unitsEquivCoprime` | Easy |
| Dirichlet density form `(q=4, a=1) → 1/2` | `Nat.setOf_prime_and_eq_mod_dirichletDensity` (or its current name) | Medium |
| Natural density form `π(N; 4, 1)/π(N) → 1/2` | `Nat.setOf_prime_and_eq_mod_div_smul_tendsto_inv_totient` (or its current name) | Medium |
| End-to-end clean statement | Combine the above | Medium |

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `infinitude-primes-4k1` (parent) | Provides the elementary infinitude statement; this OQ upgrades to density |
| `infinitude-primes` | Euclid's classical proof, the great-grandparent |
| `infinitude-primes-4k3` (sibling) | Same density question for the other residue class mod 4 (also 1/2) |
| `dirichlet-theorem` (if present) | The general statement that this OQ specializes |
| `prime-number-theorem` | The unrestricted analog (`π(N) ~ N/log N`); the density form quotients this away |
| `sum-of-two-squares` | Fermat's theorem; the residue class `1 mod 4` is exactly the representable primes |

## Mathlib Infrastructure Map

| Need | Mathlib name (Lean 4, approximate) | Module |
|------|------------------------------------|--------|
| Dirichlet characters | `DirichletCharacter` | `Mathlib.NumberTheory.DirichletCharacter.Basic` |
| L-function of a Dirichlet character | `DirichletCharacter.LFunction` | `Mathlib.NumberTheory.LSeries.DirichletContinuation` |
| L-function nonvanishing on `Re s = 1` | `DirichletCharacter.LFunction_ne_zero_of_re_eq_one` | `Mathlib.NumberTheory.LSeries.NonvanishingOne` |
| Prime counting in AP, density form | `Nat.setOf_prime_and_eq_mod_*_tendsto_*` (PNT-AP family) | `Mathlib.NumberTheory.LSeries.PrimesInAP` |
| Ikehara Tauberian theorem | `LSeries.IkeharaTauberian` (or `LSeriesHasSum_*`) | `Mathlib.NumberTheory.LSeries.Wiener` |
| `Nat.totient`, `Nat.totient 4 = 2` | `Nat.totient`, `Nat.totient_prime_pow` | `Mathlib.NumberTheory.Totient` |
| Reduced-residue indexing of `(ℤ/4ℤ)ˣ` | `ZMod.unitsEquivCoprime`, `ZMod.unitsEquivProd` | `Mathlib.Data.ZMod.Units` |
| `Mathlib.NumberTheory.SumTwoSquares` already imported | the parent file's main lemma | `Mathlib.NumberTheory.SumTwoSquares` |

**Caveat**: API names in `Mathlib.NumberTheory.LSeries.PrimesInAP` have
churned during 2024-2025 as the file matured. Any S2 implementation
should `exact?` / `apply?` against the live `_root_` and
`DirichletCharacter` namespaces rather than hard-coding names.

## Suggested Next-Action Decomposition

This is **OBSERVE** phase. No Lean changes yet — only a survey and a
concrete specialization-target list:

1. **S2: Wire Mathlib PNT-AP into a `q=4, a=1` statement.** Locate
   the current Mathlib name for the density form (likely something
   like `Nat.setOf_prime_and_eq_mod_div_smul_tendsto_inv_totient`).
   Specialize with `q = 4`, `a = 1`, and compute `Nat.totient 4 = 2`
   via `decide` or `Nat.totient_prime_pow`. Produces
   `Proofs/InfinitudePrimes4k1OQ03.lean` (~80 lines).

2. **S3: Sum-of-two-squares corollary.** Combine S2 with Fermat's
   two-square theorem (`Mathlib.NumberTheory.SumTwoSquares`,
   `Nat.Prime.prime_of_mod_four_eq_one_or_two`) to conclude: the
   primes expressible as sums of two squares have density 1/2
   among all primes (excluding `p = 2`, which is a single point of
   density 0). ~30 line corollary.

3. **S4 (optional): Dirichlet-density form as a corollary of the
   natural-density form.** Show the Abel-summation transform from
   `π(N; 4, 1)/π(N) → 1/2` to the L-series quotient. This is mostly
   a Mathlib bookkeeping step but useful as a separate theorem
   because some readers know only the analytic form.

4. **S5: Pair-with-4k3 corollary.** State and prove that primes
   `≡ 3 (mod 4)` also have density 1/2; their union covers all but
   `{2}`. This is direct from PNT-AP with `(q=4, a=3)`.

## Theoretical Subtlety: Three "Densities"

| Density flavor | Definition | Source theorem |
|----------------|-----------|----------------|
| **Natural** | `lim π(N; q, a) / π(N)` | PNT-AP (deep) |
| **Dirichlet (analytic)** | `lim_{s↘1} (∑_{p ≡ a [q]} p^{-s}) / (∑_p p^{-s})` | Dirichlet 1837 (medium) |
| **Logarithmic** | `lim ∑_{p ≤ N, p ≡ a [q]} 1/p · 1/(log log N)` | Mertens-style (medium) |

All three give the same value `1/φ(q)` for `(q, a)` coprime. The
**Dirichlet density** form is what Dirichlet originally proved in 1837;
the natural-density form is essentially equivalent to PNT-AP and was
established by de la Vallée-Poussin (1899) in the wake of PNT.

For Mathlib, both should be available; the natural-density form is
the more recent addition.

## Risk Notes

- **Mathlib API churn**: `PrimesInAP.lean` is recent; names may have
  shifted between the seeker run (when the slug was added) and this
  OBSERVE pass. Any S2 implementation should `#check` the candidate
  names against the pinned revision before committing.
- **No axioms required**: all infrastructure is `verified` in
  Mathlib; the OQ-03 specialization stays in the `verified` track.
- **Docker build cost**: a fresh build with full Mathlib imports
  (`Mathlib.NumberTheory.LSeries.PrimesInAP` pulls in the whole
  analytic stack) is ~45 min in this worktree per the broken
  `.lake` symlink. Plan accordingly; the SCAFFOLD itself is
  text-only and incurs no build.
- **Density quotient gymnastics**: PNT-AP statements in Mathlib
  often phrase the asymptotic as `(π(N; q, a) - N/(φ(q) log N)) / (N/log N) → 0`,
  not as the clean ratio `π(N; q, a) / π(N) → 1/φ(q)`. Converting
  between these is routine but adds ~10-15 lines.
