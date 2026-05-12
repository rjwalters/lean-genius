# Knowledge — infinitude-primes-4k1-oq-03

## S1 (researcher-1, 2026-05-12) — OBSERVE survey

### Concrete numerical data

For `q = 4`, the reduced residue classes are exactly `{1, 3}`:

| residue `a mod 4` | `gcd(a, 4)` | reduced? | first few primes in class |
|------------------:|:-----------:|:--------:|:--------------------------|
| 0                 | 4           | no       | (none) |
| 1                 | 1           | yes      | 5, 13, 17, 29, 37, 41, 53, 61, 73, 89, … |
| 2                 | 2           | no       | 2 (only) |
| 3                 | 1           | yes      | 3, 7, 11, 19, 23, 31, 43, 47, 59, 67, … |

Counts of primes ≤ N in each class:

| `N`     | `π(N)` | `π(N; 4, 1)` | `π(N; 4, 3)` | ratio 4k+1 | ratio 4k+3 |
|--------:|-------:|-------------:|-------------:|:-----------|:-----------|
| 100     | 25     | 11           | 13           | 0.440      | 0.520      |
| 1000    | 168    | 80           | 87           | 0.476      | 0.518      |
| 10⁴     | 1229   | 609          | 619          | 0.495      | 0.504      |
| 10⁵     | 9592   | 4783         | 4808         | 0.499      | 0.501      |
| 10⁶     | 78498  | 39175        | 39322        | 0.499      | 0.501      |

The famous "Chebyshev bias" (Chebyshev 1853, Knapowski-Turán)
favours `4k+3` over `4k+1` for small `N`, but both ratios
converge to `1/2` as `N → ∞`. This is the natural-density form of
the OQ-03 target.

**Reference**: OEIS A002145 (primes ≡ 3 mod 4), A002144 (primes ≡ 1 mod 4).

### Density value derivation

For `(q, a)` coprime: density = `1/φ(q)`.

| `q` | `(ℤ/qℤ)ˣ` | `φ(q)` | density per class |
|----:|:----------|:------:|:------------------|
| 3   | {1, 2}    | 2      | 1/2               |
| 4   | {1, 3}    | 2      | 1/2               |
| 5   | {1, 2, 3, 4} | 4   | 1/4               |
| 6   | {1, 5}    | 2      | 1/2               |
| 8   | {1, 3, 5, 7} | 4   | 1/4               |
| 12  | {1, 5, 7, 11} | 4  | 1/4               |

For OQ-03: `q = 4, a = 1, φ(4) = 2`, density = **1/2**.

### Why no elementary proof

**Chebyshev (1853)** showed `π(N; 4, 1)/π(N) ∈ (1/2 - ε, 1/2 + ε)`
for any `ε > 0` and large `N` — but only with the constant of
proportionality depending on `ε` via Chebyshev's bounds. The *limit*
statement requires either:

- **Dirichlet's analytic method (1837)**: L-function nonvanishing at
  `s = 1`. Gives the *Dirichlet density* directly.

- **De la Vallée-Poussin (1899)**: Extension of PNT to APs. Gives
  the *natural density* form. Requires L-function nonvanishing on
  the full line `Re s = 1`.

No fully elementary proof is known for either density form.
**Mertens (1874)** proved the logarithmic density
`∑_{p ≤ N, p ≡ 1 [4]} 1/p ~ (1/2) log log N` semi-elementarily,
but the natural-density limit eluded all elementary attacks until
Selberg-Erdős's elementary PNT (1949) and its later extension to APs.

### Mathlib status (Lean 4, pinned revision)

**Already in Mathlib** (with high confidence, names approximate):

- `Mathlib.NumberTheory.DirichletCharacter.Basic` — full theory of
  Dirichlet characters, including the mod-4 instance.
- `Mathlib.NumberTheory.LSeries.DirichletContinuation` — L-functions
  of Dirichlet characters with analytic continuation.
- `Mathlib.NumberTheory.LSeries.NonvanishingOne` — nonvanishing of
  `L(s, χ)` on `Re s = 1` for nontrivial `χ`.
- `Mathlib.NumberTheory.LSeries.PrimesInAP` — the PNT-AP statements
  (added 2024-2025). Probably contains the natural-density form
  under a name like `Nat.setOf_prime_and_eq_mod_*_tendsto_*`.
- `Mathlib.NumberTheory.Totient` — `Nat.totient`, computation
  `Nat.totient 4 = 2` via `decide` or `Nat.totient_prime_pow`.
- `Mathlib.NumberTheory.SumTwoSquares` — Fermat two-square theorem
  (already imported by the parent `InfinitudePrimes4k1.lean`).

**Mathlib gaps** (best-guess; may already be filled at pinned revision):

- A *clean ratio form* `(π(N; q, a) : ℝ) / (π(N) : ℝ) → 1/φ(q)`. The
  Mathlib statement is more likely phrased via the inverse:
  `π(N; q, a) ~ (1/φ(q)) · (N / log N)` as an asymptotic equivalence.
  Translating between these is a 10-15 line ratio lemma.

- A `(q=4, a=1)` specialization. Mathlib's statements are typically
  parametric in `(q, a)`; the user must instantiate.

- A "primes representable as sums of two squares" density corollary
  (combining S2 + Fermat-2-square).

### Parent file (already verified)

`Proofs/InfinitudePrimes4k1.lean` (178 lines, 5 theorems, 0 sorries, 0 axioms)
proves:

- `prime_dvd_sq_add_one_mod_four` — key Euler-criterion lemma
- `exists_odd_prime_factor` — basic combinatorics
- `infinitely_many_primes_1_mod_4` — main result (existence form)
- `primes_1_mod_4_infinite` — `Set.Infinite` form
- `no_largest_prime_1_mod_4` — `¬∃ max` form

This OQ-03 sits *above* the parent: the parent gives
`Set.Infinite {p | p.Prime ∧ p % 4 = 1}`, while OQ-03 strengthens
to the asymptotic density form.

### Density vs Dirichlet density

For the OQ statement "density 1/2 among primes" both natural and
Dirichlet density give the same value, but they are *different
theorems* in Mathlib:

- **Dirichlet form (analytic):** Easier; follows from L-function
  nonvanishing at the single point `s = 1`.
  Statement involves a limit `s ↘ 1` of an L-series ratio.

- **Natural form:** Harder; equivalent to PNT-AP. Statement involves
  a direct ratio of prime-counting functions.

For a maximally clean gallery deliverable, the *natural-density* form
is the preferred target — it matches the human-language reading of
"density 1/2" and connects directly to the Chebyshev bias data above.

### S1 scope (this iteration)

This S1 is **survey-only** per the SCAFFOLD pattern (no Lean changes).
Produced:

- `problem.md` (~250 lines, theoretical content + Mathlib map +
  decomposition table)
- `state.md` (current file inventory + next-action plan)
- `knowledge.md` (this file: numerical data + Mathlib status)
- `src/data/research/problems/infinitude-primes-4k1-oq-03.json`
  updated: phase NEW → OBSERVE, focus + insights + nextSteps populated

No Lean files modified; no axiom/sorry deltas.

### Next-action sketch (for S2)

The cleanest S2 is to create `Proofs/InfinitudePrimes4k1OQ03.lean`
with the structure:

```lean
import Proofs.InfinitudePrimes4k1
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Totient

namespace InfinitudePrimes4k1OQ03

open Nat Filter Topology

-- The key auxiliary computation
lemma totient_four : Nat.totient 4 = 2 := by decide

-- Specialize Mathlib's PNT-AP to (q=4, a=1)
theorem primes_4k1_density :
    Tendsto
      (fun N : ℕ => ((Finset.range N).filter
        (fun p => p.Prime ∧ p % 4 = 1)).card / (N.primeCounting : ℝ))
      atTop (𝓝 (1/2)) := by
  -- Use Mathlib's `Nat.setOf_prime_and_eq_mod_*_tendsto_*` family
  have := Nat.[PNT_AP_API_NAME] (q := 4) (a := 1) (by decide : (1 : ZMod 4).IsUnit)
  -- Convert via totient_four; ratio gymnastics
  sorry  -- placeholder for the API wiring

end InfinitudePrimes4k1OQ03
```

The `sorry` is the wiring step against the (recently-stabilized)
PNT-AP API. Once the Mathlib name is confirmed (`exact?` /
`#check Nat.` autocomplete in a REPL), the proof is mechanical.

### Risks for S2

- **API name churn** in `Mathlib.NumberTheory.LSeries.PrimesInAP` —
  the precise name of the density-form theorem may have shifted.
  Plan a name-discovery step before writing the proof.
- **Ratio-form vs asymptotic-equivalent form**: Mathlib's statement
  may be `IsEquivalent` (~) rather than `Tendsto`. Conversion is
  routine but worth budgeting.
- **`primeCounting` namespace**: `Nat.primeCounting` vs
  `Nat.Prime.count` vs the new `Nat.nth Nat.Prime`-based form —
  several flavors exist; pick the one matching the PNT-AP signature.
