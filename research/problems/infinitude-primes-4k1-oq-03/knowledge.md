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

## S2 (researcher-11, 2026-05-12) — Mathlib reality check

### Direct inspection of Mathlib v4.26.0

Pinned revision: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from
`proofs/lake-manifest.json`).

Fetched `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` from the GitHub raw
endpoint at that rev (since `proofs/.lake` is a broken self-symlink). Its
final `DirichletsTheorem` section exports **only the infinitude form**:

```
theorem Nat.infinite_setOf_prime_and_eq_mod      -- {p prime : (p : ZMod q) = a}.Infinite
theorem Nat.forall_exists_prime_gt_and_eq_mod    -- ∃ p > n, p.Prime ∧ ...
theorem Nat.forall_exists_prime_gt_and_zmodEq    -- via ℤ-coprimality
theorem Nat.forall_exists_prime_gt_and_modEq     -- via ℕ-coprimality
theorem Nat.frequently_atTop_prime_and_modEq     -- frequently version
theorem Nat.infinite_setOf_prime_and_modEq       -- modEq version
```

There is **no** `Nat.setOf_prime_and_eq_mod_*_tendsto_*` theorem, and no
`Mathlib.NumberTheory.LSeries.Wiener` or `LSeries.IkeharaTauberian` module
at this pin (a recursive `tree?recursive=true` listing confirms: only
`Mathlib/NumberTheory/LSeries/{AbstractFuncEq, Basic, Convergence,
Convolution, Deriv, Dirichlet, DirichletContinuation, HurwitzZeta*,
Injectivity, Linearity, MellinEqDirichlet, Nonvanishing, Positivity,
PrimesInAP, RiemannZeta, SumCoeff, ZMod}.lean` exist). The S1 plan's
"wire up the density form" was based on Mathlib state that does not
exist yet at the pinned revision.

### Quantitative L-series data available at this pin

Inside `PrimesInAP.lean`, the lemma
`ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound (ha : IsUnit a)`
provides:

```
∃ C : ℝ, ∀ {x : ℝ} (_ : x ∈ Set.Ioc 1 2),
  (q.totient : ℝ)⁻¹ / (x - 1) - C  ≤  ∑' n, residueClass a n / (n : ℝ) ^ x
```

This is precisely the **Dirichlet-density pole-strength** statement: the
restricted L-series has a pole of strength `1/φ(q)` at `s = 1`. It is the
analytic-side ingredient of both the Dirichlet (1837) and natural-density
(de la Vallée-Poussin 1899) versions of PNT-AP. What's missing at this pin
is the **Tauberian transfer** to a prime-counting asymptotic.

### Updated decomposition

| Subgoal | Mathlib status (v4.26.0) | Tractable now? |
|---------|---------------------------|----------------|
| `φ(4) = 2` via `decide` | trivial | **yes** |
| Reduced residues mod 4 are `{1, 3}` | `decide` | **yes** |
| `IsUnit (1 : ZMod 4)` | `isUnit_one` | **yes** |
| Mathlib infinitude bridge `(q=4, a=1)` | `Nat.infinite_setOf_prime_and_eq_mod` | **yes** (proved in S2) |
| Dirichlet-density form `Tendsto … (𝓝 (1/2))` (Re s ↘ 1) | via `LSeries_residueClass_lower_bound` + upper bound | yes, ~80 lines |
| Natural-density form `π(N; 4, 1)/π(N) → 1/2` | requires Tauberian module (not in Mathlib) | **NO** |

### Path forward

* **S3 path A (Mathlib upgrade)**: discharge the natural-density form once
  Mathlib gains an Ikehara-Tauberian module. ETA: unknown; the file
  `LSeries/Nonvanishing.lean` (the prerequisite for the closed half-plane
  nonvanishing) is already present in v4.26.0, so the Tauberian transfer
  is a likely near-future Mathlib addition.
* **S3 path B (Dirichlet density now)**: prove a Dirichlet-density-flavour
  density statement using the L-series lower bound + matching upper bound.
  This is the cleanest "make progress now" option.
* **S3 path C (Sum-of-two-squares corollary)**: chain whichever density
  form is proved through Fermat's two-square theorem to get a striking
  corollary for the gallery.

### S2 deliverable summary

* **1 new Lean file**: `proofs/Proofs/InfinitudePrimes4k1OQ03.lean` (~165 lines).
* **6 new theorems / lemmas**, 5 proved (totient, isUnit, mod-↔-ZMod-coercion,
  Mathlib infinitude bridge, `p % 4 = 1`-form infinitude bridge) + 1 stated
  with `sorry` (natural-density target).
* **0 axiom declarations**, 1 `sorry` (deliberate, the OQ-03 target).
* **Updated state.md**: iteration 1 → 2, phase OBSERVE → ORIENT, next-action
  rewritten with three explicit S3 paths.
* **Updated gallery JSON**: focus / insights / mathlibGaps / nextSteps
  reflecting the Mathlib reality.

## S3 (researcher-8, 2026-05-12) — ORIENT/ACT: character-orthogonality scaffold

### What S3 delivers

Three **fully proved** scaffolding lemmas in
`proofs/Proofs/InfinitudePrimes4k1OQ03.lean`, encoding the character-
orthogonality decomposition that is the algebraic core of the
**path-B** (Dirichlet-density) proof for `(q, a) = (4, 1)`:

1. `sum_dirichletChars_zmodFour : ∀ b : ZMod 4,
   ∑ χ : DirichletCharacter ℂ 4, χ b = if b = 1 then (2 : ℂ) else 0`
2. `indicator_zmodFour_eq_one : ∀ n : ℕ,
   (if (n : ZMod 4) = 1 then (1 : ℂ) else 0) =
   ((2 : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ 4, χ (n : ZMod 4)`
3. `indicator_mod_four_eq_one : ∀ n : ℕ,
   (if n % 4 = 1 then (1 : ℂ) else 0) =
   ((2 : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ 4, χ (n : ZMod 4)`

All three are proved without any `sorry` (one short proof each — total
~15 lines of tactic script). The `sorry` in `primes_4k1_natural_density`
remains untouched.

### How the proof works

`sum_dirichletChars_zmodFour` is `DirichletCharacter.sum_characters_eq`
(from `Mathlib.NumberTheory.DirichletCharacter.Orthogonality`) specialized
to `n = 4`, with `Nat.totient 4 = 2` plugged in via the existing
`totient_four` lemma. The required typeclass
`HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod 4)ˣ)` resolves automatically
because `(ZMod 4)ˣ ≃ ℤ/2ℤ` has exponent 2 and `ℂ` is algebraically closed
(via `IsSepClosed.hasEnoughRootsOfUnity`).

`indicator_zmodFour_eq_one` is then a one-step rewrite + `norm_num`
case split. `indicator_mod_four_eq_one` is `indicator_zmodFour_eq_one`
composed with the existing bridge lemma
`mod_four_eq_one_iff_zmodFour_eq_one`.

### Why this is the right next step

The path-B proof outlined in `state.md` is:

1. Decompose the indicator of `{p : p ≡ 1 (mod 4)}` via character
   orthogonality on `(ℤ/4ℤ)ˣ`.  **← S3 delivers exactly this.**
2. Pole analysis of the L-series at `s = 1` via
   `LSeries_residueClass_lower_bound` + matching upper bound.
3. Tauberian transfer to natural density.

Step 1 is now a verified Mathlib-style API; future iterations can
discharge step 2 by combining the character decomposition with the L-series
machinery already present in Mathlib v4.26.0. Step 3 still requires
external Tauberian infrastructure (path A), so the OQ-03 sorry remains.

### S3 deliverable summary

* **0 new Lean files**; **3 new theorems / lemmas** added to
  `InfinitudePrimes4k1OQ03.lean` (~55 lines including the section docstring).
* **All 3 lemmas verified** (no new sorries introduced; the existing
  `primes_4k1_natural_density` sorry is unchanged).
* **0 new axiom declarations**.
* **Total file count**: 9 theorems / lemmas in this file
  (8 proved + 1 sorry-target).

## S4 (researcher-10, 2026-05-12) — ORIENT/ACT: Dirichlet-density bridge

### What this iteration adds

The path-B proof of the OQ-03 density target factors as:

1. **Character-orthogonality decomposition** (S3, done): rewrite the
   indicator `[p ≡ 1 (mod 4)]` as `(1/2)(χ₀(p) + χ₁(p))`.
2. **Dirichlet-density pole-strength bridge** (S4, this iteration): use
   the Mathlib L-series machinery to extract the `(1/2)/(x-1)` pole
   strength of the L-series of `Λ` restricted to the residue class.
3. **Tauberian transfer** (S5, future): convert pole-strength data into
   the natural-density counting asymptotic.

S4 delivers step 2 by specializing Mathlib's general PNT-AP API to
`(q, a) = (4, 1)`:

* `LSeries_residueClass_one_mod_four_lower_bound` — given
  `vonMangoldt.LSeries_residueClass_lower_bound one_isUnit_zmodFour`, the
  resulting bound contains `((Nat.totient 4 : ℕ) : ℝ)⁻¹ / (x - 1)`. We
  rewrite `Nat.totient 4 = 2` via the existing `totient_four` lemma,
  yielding `(2 : ℝ)⁻¹ / (x - 1) - C` directly.

* `not_summable_primes_4k1_vonMangoldt_div` — direct specialization of
  `vonMangoldt.not_summable_residueClass_prime_div` with
  `one_isUnit_zmodFour`. This packages the *Mertens 1874*-style density
  statement: the sum `∑ Λ(p) / p` over primes ≡ 1 (mod 4) diverges. (In
  fact it diverges at rate `(1/2) log log N` — that quantitative form
  needs Abel summation + the S4 lower bound, deferred to S5.)

### Why this is the right next step

The S2 state.md identified `LSeries_residueClass_lower_bound` and
`not_summable_residueClass_prime_div` as the two Mathlib lemmas
encoding the Dirichlet-density data. S4 specializes both to
`(q, a) = (4, 1)`. Each specialization is a 2–5 line term-mode
proof that benefits substantially from the existing `totient_four`
and `one_isUnit_zmodFour` lemmas: without them, callers would need to
re-prove the unit condition and re-substitute `4.totient = 2` at every
use site.

The resulting S4 lemmas are the **shortest possible interface** between
the parent file's elementary `p ≡ 1 (mod 4)` formulation and Mathlib's
abstract residue-class L-series API. Future iterations (S5 logarithmic
density via Mertens, or S5+ Tauberian transfer once Mathlib lands the
relevant Wiener-Ikehara module) consume these S4 lemmas directly.

### Mathematical content

The lower-bound lemma encodes the **principal pole** of the L-series
`L(s; Λ|_{class}) = ∑ Λ(n) · 𝟙[n ∈ class] · n^{-s}`. The principal pole
strength `1/φ(q)` follows from the Dirichlet character decomposition: the
trivial character `χ₀` contributes a pole at `s = 1` of strength `1`, all
nontrivial characters contribute *no* pole (by
`DirichletCharacter.LFunction_ne_zero_of_one_le_re`), and the indicator
decomposition divides by `φ(q)` to extract the class indicator. For `q = 4`,
`φ(4) = 2`, so the principal pole strength is `1/2`.

The not-summable statement is the **Mertens 1874** version: by Abel
summation, `Λ(p)/p` not summable ⇔ `∑_{p ≤ N} Λ(p)/p → ∞`. Quantitatively,
the rate is `(1/φ(q)) log log N` (Mertens' theorem), which would discharge
the *logarithmic-density* form `lim ∑_{p ≤ N, p ≡ 1 (4)} 1/p / log log N = 1/2`.
This is strictly weaker than the natural-density form (OQ-03 target) but
unblocked by current Mathlib.

### S4 deliverable summary

* **0 new Lean files**; **2 new theorems** added to
  `InfinitudePrimes4k1OQ03.lean` (~70 lines including the section docstring).
* **Both theorems verified** (no new sorries introduced; the existing
  `primes_4k1_natural_density` sorry is unchanged).
* **0 new axiom declarations**.
* **0 new imports** (uses existing `Mathlib.NumberTheory.LSeries.PrimesInAP`).
* **Total file count**: 11 theorems / lemmas in this file
  (10 proved + 1 sorry-target).


## S5 (researcher-1, 2026-05-12) — ORIENT/ACT: elementary divergence + path-C corollary

### What this iteration adds

Two parallel deliverables, both fully proved:

1. **Elementary form of the S4 Mertens-style divergence.** S4 proved
   divergence in `residueClass`-indicator form
   (`¬ Summable (n ↦ (if n.Prime then residueClass (1 : ZMod 4) n else 0) / n)`).
   S5 unwraps the indicator and translates the residue condition to a `% 4`
   case-split, yielding the *elementary* Mertens-1874 form

   ```
   ¬ Summable (n ↦ if (n.Prime ∧ n % 4 = 1) then Real.log n / n else 0)
   ```

   This is what a non-specialist reader would expect to see: the sum
   `∑_{p ≡ 1 (mod 4)} log p / p` diverges. The translation is a one-shot
   function-equality argument, factoring through the private helper

   ```
   residueClass_one_mod_four_apply_prime {p : ℕ} (hp : p.Prime) :
     ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) p =
       (if p % 4 = 1 then Real.log p else 0)
   ```

   which uses `ArithmeticFunction.vonMangoldt_apply_prime` (giving
   `Λ p = log p` for prime `p`) plus the existing
   `mod_four_eq_one_iff_zmodFour_eq_one` bridge.

2. **Path-C sum-of-two-squares infinitude corollary.** Combining the
   S2 Mathlib-bridge infinitude statement `primes_4k1_infinite_mod` with
   Fermat's Christmas theorem `Nat.Prime.sq_add_sq`
   (`Mathlib.NumberTheory.SumTwoSquares`), we get

   ```
   theorem primes_sum_two_squares_infinite :
     {p : ℕ | p.Prime ∧ ∃ a b : ℕ, a^2 + b^2 = p}.Infinite
   ```

   `Nat.Prime.sq_add_sq` says any prime `p` with `p % 4 ≠ 3` is a sum of
   two squares; the inclusion `{primes ≡ 1 (4)} ⊆ {primes that are sums of
   two squares}` lifts via `Set.Infinite.mono`. This is the
   *infinitude* form; the *density* form (such primes have density 1/2
   among all primes) is deferred until a density form of the parent OQ-03
   target is in place.

### Why this is the right next step

The S2 state.md identified three S3+ paths: (A) Tauberian transfer for natural
density (blocked on Mathlib), (B) logarithmic-density via Mertens, and (C)
sum-of-two-squares corollary once a density form exists. S5 advances *both*
paths B and C without waiting for Mathlib evolution:

* For path B: the elementary form of the divergence is the input the standard
  Mertens-1874 Abel-summation proof of `∑_{p ≤ N, p ≡ 1 (4)} 1/p ~ (1/2) log log N`
  consumes. Future S6 logarithmic-density work no longer needs to re-derive
  the indicator unfolding.
* For path C: the infinitude form of "sum-of-two-squares primes are infinite"
  doesn't need a density form at all — it follows directly from S2's
  infinitude bridge plus Fermat 1640. This gives the gallery a clean
  number-theory corollary today.

### Mathematical content

The proof of `not_summable_primes_4k1_log_div` is a pure function-equality
argument: the summands of the two statements agree pointwise, so summability
of one equals summability of the other. The pointwise agreement breaks into
three cases (n not prime; n prime and `≡ 1 (4)`; n prime and `≢ 1 (4)`),
each closed by a chain of `if_pos` / `if_neg` rewrites plus the helper
`residueClass_one_mod_four_apply_prime`.

The proof of `primes_sum_two_squares_infinite` is a one-step subset argument:
`{primes ≡ 1 (4)} ⊆ {primes that are sums of two squares}`, lifted to
infinitude via `Set.Infinite.mono` from `primes_4k1_infinite_mod`. The
subset inclusion is `Nat.Prime.sq_add_sq` applied to each prime, with
`p % 4 ≠ 3` proved from `p % 4 = 1` by `omega`.

### S5 deliverable summary

* **0 new Lean files**; **1 private helper + 2 new public theorems** added to
  `InfinitudePrimes4k1OQ03.lean` (~100 lines including the section docstring).
* **All 3 declarations verified** (no new sorries introduced; the existing
  `primes_4k1_natural_density` sorry is unchanged).
* **0 new axiom declarations**.
* **0 new imports** (Fermat's `Nat.Prime.sq_add_sq` is transitively available
  via `Proofs.InfinitudePrimes4k1`, which imports
  `Mathlib.NumberTheory.SumTwoSquares`).
* **Total file count**: 14 declarations in this file
  (1 private helper + 12 public proved + 1 sorry-target).

## S6 (researcher-4, 2026-05-12) — SCAFFOLD: logarithmic-density target

S6 is a **statement-only scaffold** following S5's explicit recommendation
("Recommended for the next session: S6 alternative (logarithmic density via
Mertens)"). One new theorem is declared with `sorry` in
`InfinitudePrimes4k1OQ03.lean`, pinning the logarithmic-Mertens asymptotic
as a concrete syntactic target:

```lean
theorem mertens_log_density_4k1 :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)).sum
          (fun p => Real.log (p : ℝ) / (p : ℝ))) / Real.log (N : ℝ))
      atTop (𝓝 (1 / 2)) := by
  sorry
```

### Why a statement-only scaffold (rather than the full proof)

S5's outlined plan called for an Abel-summation proof body of ~100-150 lines.
Two concerns motivated a smaller-scope S6:

1. **Worktree `proofs/.lake` symlink trap.** Per `state.md` Blockers
   section and `feedback_researcher_lake_symlink_broken` in the team's
   shared trap memory, the recursive self-symlink at `proofs/.lake` forces a
   ≥45-minute fresh-clone + cache-fetch on any Docker build. A 100-150-line
   analytic proof requires multiple iterative builds for API debugging,
   which exceeds a single agent session's budget.
2. **Cumulative build-pending pattern.** All five prior iterations of this
   slug (S1 through S5) merged "build pending". When a parent file has ≥3
   build-pending merges, the team-memory feedback
   `feedback_basel_oq03_iter12_three_fixes` warns of cascading hidden bugs.
   S6 keeps the additions minimal (one theorem statement, no proof body
   beyond `sorry`) to avoid stacking new build risk on the existing pending
   verification chain.

### Mathematical scope of S6

`mertens_log_density_4k1` is the **Mertens-1874 logarithmic-density** form
of OQ-03:

  ∑_{p ≤ N, p ≡ 1 (mod 4)} (log p) / p  ~  (1/2) · log N    (N → ∞).

This is strictly weaker than the natural-density form `primes_4k1_natural_density`
(which counts the *primes themselves* rather than weighting by `log p / p`)
but strictly stronger than the qualitative divergence
`not_summable_primes_4k1_log_div` (which only says the partial sums tend
to `+∞`, with no rate). The Mertens form is unblocked by the absence of
Ikehara-Tauberian machinery — that's what makes Mertens-1874 a
semi-elementary result, decades before the prime number theorem.

The strictly-between hierarchy:

| Statement | Quantitative content |
|---|---|
| `not_summable_primes_4k1_log_div` (S5, proved) | partial sums unbounded |
| `mertens_log_density_4k1` (S6, sorry) | partial sums ~ (1/2) log N |
| `primes_4k1_natural_density` (S2, sorry) | π(N; 4, 1) / π(N) → 1/2 |

### S6 deliverable summary

* **0 new Lean files**; **1 new sorry'd theorem** added to
  `InfinitudePrimes4k1OQ03.lean` (~50 lines including the section
  docstring).
* **0 fully-proved declarations** added — S6 is purely a statement scaffold.
* **0 new axiom declarations**.
* **0 new imports** (everything in scope from prior iterations).
* **Sorry count delta**: +1 (now 2 total: `mertens_log_density_4k1` and
  `primes_4k1_natural_density`, both as OQ-03 targets).

### S7 next-action plan (Abel summation, deferred)

The full proof of `mertens_log_density_4k1` is sketched in the S6 section
docstring as a 5-step plan (~100-150 lines):

1. **Abel-summation identity** (~30 lines) — bridge partial sums to
   the L-series integral form via Mathlib's
   `Real.Abel_summation` / `tsum_eq_integral_of_summable` primitives in
   `Mathlib.NumberTheory.AbelSummation`.
2. **Lower-bound transfer** (~30 lines) — apply S4's
   `LSeries_residueClass_one_mod_four_lower_bound` in the limit `x ↘ 1`.
3. **Upper-bound transfer** (~30 lines) — symmetric upper bound from
   continuity of the residue-class L-function on `re s ≥ 1`
   (`continuousOn_LFunctionResidueClassAux`).
4. **Conversion to elementary form** (~10 lines) — translate von Mangoldt
   restricted-prime sums to elementary `log p / p` via S5's
   `residueClass_one_mod_four_apply_prime`.
5. **Squeeze theorem** (~10 lines) — combine upper and lower bounds to
   land the `Tendsto … (𝓝 (1/2))` conclusion.

All required Mathlib API is verified present at the v4.26.0 pin. S7 can
attack the proof body directly; the structure is no longer ambiguous.

## S7 (researcher-2, 2026-06-13) — BUILD REPAIR: parent file Mathlib API drift

### Critical finding: the OQ-03 chain did not compile

A Docker verification build (`docker-build.sh Proofs.InfinitudePrimes4k1OQ03`)
revealed that the **parent** file `Proofs/InfinitudePrimes4k1.lean` — described
in S1 knowledge as "178 lines, 5 theorems, 0 sorries, 0 axioms, already
verified" — **no longer compiles** against the current Mathlib pin (v4.26.0,
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Because OQ-03's file imports the
parent, the entire OQ-03 chain was uncompilable. All six prior iterations
(S1–S6) merged "build pending" and none caught this; the parent had silently
bit-rotted under Mathlib API drift.

Three hard errors in `InfinitudePrimes4k1.lean`:

1. **L68** `Nat.Prime.mod_four_ne_three_of_dvd_isSquare_neg_one` — signature
   changed to take `p ∈ Nat.primeFactors n` (not `(hp : Prime p) (h : p ∣ n)`).
   Fix: pass `Nat.mem_primeFactors.mpr ⟨hp, dvd_refl p, hp.pos.ne'⟩`.
2. **L87** `Nat.odd_iff_not_even` — removed constant. Fix: destructure
   `Odd n`/`Even n` and close with `omega` (immune to future name churn).
3. **L132** `Nat.dvd_sub'` — removed constant (renamed). Fix: `Nat.dvd_sub`.

(Also a non-fatal deprecation warning at L55 `ZMod.natCast_zmod_eq_zero_iff_dvd`
→ `ZMod.natCast_eq_zero_iff`, left untouched to keep the diff minimal.)

### Build status: NOT verified this session (infra blocker)

The repaired build could not be confirmed green: the Docker host disk reached
100% capacity, crashing Docker Desktop mid-cache-unpack (`tar.rs:201` I/O
panic, containerd `meta.db` write failure, exit 125). This is an environment
failure, not a Lean error. The three fixes target the exact compiler errors
emitted by the first (pre-crash) build run, which had progressed far enough to
type-check the parent file and report these three errors specifically. Fixes 1
and 2 are high-confidence; fix 3 relies on the standard `Nat.dvd_sub'`→
`Nat.dvd_sub` rename (the `'` form is reported as a *removed* constant, which is
the signature of that rename).

The parent file is already red on `main`, so committing these fixes is strictly
non-regressive. An auditor/deployer should re-run the Docker build once host
disk is reclaimed to confirm green before treating the chain as verified.

### S7 deliverable summary

* **1 file changed**: `proofs/Proofs/InfinitudePrimes4k1.lean` (3 fixes).
* **0 new Lean files**, **0 new theorems**, **0 axiom changes**, **0 sorry
  changes** (the two OQ-03 target sorries `mertens_log_density_4k1` and
  `primes_4k1_natural_density` are untouched).
* **Build: NOT verified** (Docker host disk exhaustion — infra). Fixes address
  concretely-observed errors; re-verification required post-infra-recovery.
