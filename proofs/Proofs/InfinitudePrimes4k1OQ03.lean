import Proofs.InfinitudePrimes4k1
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Density 1/2 of Primes ≡ 1 (mod 4) — OQ-03

## What This File Aims to Establish

The parent file `Proofs/InfinitudePrimes4k1.lean` proves the *infinitude* of
primes `p ≡ 1 (mod 4)` by an elementary argument (Fermat sums-of-two-squares
+ Euler's criterion). This OQ asks for the strictly stronger statement:

$$
\lim_{N \to \infty} \frac{\#\{p \le N : p \text{ prime},\, p \equiv 1 \pmod 4\}}{\pi(N)}
  \;=\; \tfrac{1}{2}.
$$

This is the **natural-density** form of Dirichlet's theorem for `(q, a) = (4, 1)`
— a specialization of the prime number theorem for arithmetic progressions
(PNT-AP).

## Mathlib Status at v4.26.0 (S2, 2026-05-12)

A direct inspection of `Mathlib.NumberTheory.LSeries.PrimesInAP` at the pinned
revision `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) shows:

* **The infinitude form is available**, exported as `Nat.infinite_setOf_prime_and_eq_mod`.
* **The natural-density form is NOT available**. There is no
  `Mathlib.NumberTheory.LSeries.Wiener` or `Mathlib.NumberTheory.LSeries.IkeharaTauberian`
  module at this pin, and no theorem of the form
  `Nat.setOf_prime_and_eq_mod_div_smul_tendsto_inv_totient`.

The S1 OBSERVE plan (in `state.md`) assumed the density form was already in
Mathlib; this was over-optimistic. The closest quantitative lemma at this pin is
`ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`, which states
that the L-series of the von Mangoldt function restricted to a residue class
has a pole of strength `1/φ(q)` at `s = 1`. This is the **Dirichlet-density**
data, not the natural-density data.

## Scope of S2 (this iteration)

1. **Mathlib-bridge infinitude (verified).** Connect the parent file's
   elementary infinitude statement to Mathlib's general Dirichlet's theorem,
   specialized to `(q, a) = (4, 1)`. The result is identical in content but
   demonstrates the path from the gallery proof to Mathlib's analytic machinery.

2. **State the natural-density target (sorry).** Declare the OQ-03 deliverable
   as a Lean statement, marked `sorry`, so future iterations have a concrete
   syntactic target.

## Future Work (S3+)

* **S3a (Mathlib upgrade path).** When Mathlib gains an Ikehara-Tauberian
  module — e.g. `Mathlib.NumberTheory.LSeries.Wiener` — instantiate it for
  `(q, a) = (4, 1)` and discharge the `sorry`.
* **S3b (Dirichlet density side-step).** State and prove the *Dirichlet-density*
  form of the question via `LSeries_residueClass_lower_bound` + the matching
  upper bound; this is achievable at the current Mathlib pin and gives a
  formally weaker but pedagogically equivalent result.
* **S3c (Sum-of-two-squares corollary).** Combine the density form with
  Fermat's two-square theorem (`Mathlib.NumberTheory.SumTwoSquares`).

## Status
* Mathlib bridge to infinitude: **verified**.
* Natural-density theorem: **stated, with `sorry`** (OQ-03 target).
* No axiom declarations introduced.
-/

namespace InfinitudePrimes4k1OQ03

open Nat Filter Topology

/-! ## Auxiliary: `Nat.totient 4 = 2` and `1` is a unit mod 4 -/

/-- The reduced residues mod 4 are `{1, 3}`, so `φ(4) = 2`. -/
lemma totient_four : Nat.totient 4 = 2 := by decide

/-- `1` is a unit in `ZMod 4`. -/
lemma one_isUnit_zmodFour : IsUnit (1 : ZMod 4) := isUnit_one

/-! ## Translating between `p % 4 = 1` and `(p : ZMod 4) = 1` -/

/-- For natural-number `p`, the residue-class condition `p % 4 = 1` is
equivalent to `(p : ZMod 4) = 1`. -/
lemma mod_four_eq_one_iff_zmodFour_eq_one {p : ℕ} :
    p % 4 = 1 ↔ (p : ZMod 4) = 1 := by
  have h1 : (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) := by norm_cast
  rw [h1, ZMod.natCast_eq_natCast_iff, Nat.ModEq]
  constructor
  · intro h; omega
  · intro h; omega

/-! ## Mathlib bridge: infinitude form -/

/-- **Mathlib bridge (infinitude form).** There are infinitely many primes
`p` with `(p : ZMod 4) = 1`, i.e. `p ≡ 1 (mod 4)`. This is
`Nat.infinite_setOf_prime_and_eq_mod` from
`Mathlib.NumberTheory.LSeries.PrimesInAP`, specialized to `(q, a) = (4, 1)`.

This is **strictly weaker** than the elementary parent statement
`InfinitudePrimes4k1.primes_1_mod_4_infinite` in the sense that the parent
uses no analytic input; but it is *the* statement that connects this file to
Mathlib's L-series machinery, which is the only known route to the density
form. -/
theorem primes_4k1_infinite_mathlib :
    {p : ℕ | p.Prime ∧ (p : ZMod 4) = 1}.Infinite :=
  Nat.infinite_setOf_prime_and_eq_mod one_isUnit_zmodFour

/-- The same statement in the `p % 4 = 1` formulation used by the parent file. -/
theorem primes_4k1_infinite_mod :
    {p : ℕ | p.Prime ∧ p % 4 = 1}.Infinite := by
  have key := primes_4k1_infinite_mathlib
  have hset : {p : ℕ | p.Prime ∧ (p : ZMod 4) = 1} =
      {p : ℕ | p.Prime ∧ p % 4 = 1} := by
    ext p
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro _
    exact (mod_four_eq_one_iff_zmodFour_eq_one).symm
  exact hset ▸ key

/-! ## S3 ORIENT/ACT: character-orthogonality scaffold for q = 4

These lemmas form the algebraic core of the **S3 path B** (Dirichlet-density)
proof outlined in `state.md`. They translate the general Mathlib character-
orthogonality result `DirichletCharacter.sum_characters_eq` into the `q = 4`
case, expressing the indicator of `[p % 4 = 1]` as a sum over Dirichlet
characters mod 4. Concretely: the indicator decomposes as
`(1/2) · (χ₀(p) + χ₁(p))` where `χ₀` is the trivial character mod 4 and
`χ₁` is the unique nontrivial (real) character.

The `HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod 4)ˣ)` typeclass needed by
`sum_characters_eq` is satisfied automatically: `(ZMod 4)ˣ ≃ ℤ/2ℤ` has
exponent `2`, and `ℂ` contains primitive 2nd roots of unity (since `ℂ` is
algebraically closed; instance via `IsSepClosed.hasEnoughRootsOfUnity`). -/

/-- **Character orthogonality at `q = 4`.**
For any `b : ZMod 4`, the sum of the `Nat.totient 4 = 2` Dirichlet characters
mod `4` with values in `ℂ`, evaluated at `b`, equals `2` if `b = 1`, else `0`.

This is `DirichletCharacter.sum_characters_eq` specialized to `n = 4`,
with `Nat.totient 4 = 2` plugged in via `totient_four`. -/
lemma sum_dirichletChars_zmodFour (b : ZMod 4) :
    ∑ χ : DirichletCharacter ℂ 4, χ b = if b = 1 then (2 : ℂ) else 0 := by
  rw [DirichletCharacter.sum_characters_eq ℂ b]
  split_ifs with hb
  · norm_num [totient_four]
  · rfl

/-- **Indicator-as-character-sum (ZMod 4 form).**
The indicator of `(n : ZMod 4) = 1` (in `ℂ`) is half the sum of the two
Dirichlet characters mod 4 evaluated at `n`. This is the
**character-orthogonality decomposition** of the indicator function used in
the standard analytic proof of Dirichlet's theorem on `(q, a) = (4, 1)`. -/
lemma indicator_zmodFour_eq_one (n : ℕ) :
    (if (n : ZMod 4) = 1 then (1 : ℂ) else 0) =
      ((2 : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ 4, χ (n : ZMod 4) := by
  rw [sum_dirichletChars_zmodFour]
  split_ifs <;> norm_num

/-- **Indicator-as-character-sum (`% 4` form).**
The indicator of `n % 4 = 1` (in `ℂ`) is half the sum of the two Dirichlet
characters mod 4 evaluated at `n`. This is `indicator_zmodFour_eq_one`
translated through `mod_four_eq_one_iff_zmodFour_eq_one` to the residue-class
formulation used by the parent file `InfinitudePrimes4k1`. -/
lemma indicator_mod_four_eq_one (n : ℕ) :
    (if n % 4 = 1 then (1 : ℂ) else 0) =
      ((2 : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ 4, χ (n : ZMod 4) := by
  simp only [mod_four_eq_one_iff_zmodFour_eq_one]
  exact indicator_zmodFour_eq_one n

/-! ## S4 ORIENT/ACT: Dirichlet-density bridge (q = 4, a = 1)

These lemmas specialize the Mathlib L-series machinery to the case
`(q, a) = (4, 1)`, packaging the Dirichlet-density data that drives the
path-B proof outlined in `state.md`.

The Mathlib API used here (verified to exist at v4.26.0, pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

* `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`
  — for `a : ZMod q` a unit, gives `∃ C, (q.totient)⁻¹/(x-1) - C ≤
  ∑' n, residueClass a n / (n : ℝ)^x` for `x ∈ Ioc 1 2`. The
  `(q.totient)⁻¹/(x-1)` term is the **principal pole strength** of
  the L-series of the von Mangoldt function restricted to the residue
  class `a (mod q)`.
* `ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div`
  — for `a : ZMod q` a unit, the prime-restricted Dirichlet sum
  `∑ (if n.Prime then residueClass a n else 0) / n` is **not summable**.
  This is the Dirichlet-density-style divergence statement used in
  Mathlib's proof of Dirichlet's theorem.

For `q = 4`, `q.totient = 2` (already proved as `totient_four`). The
S4 lemmas below substitute this explicit value, yielding the concrete
`1/2` pole strength for primes `≡ 1 (mod 4)`. This is the Dirichlet
density of `1/φ(4) = 1/2` made syntactically explicit on top of
Mathlib's general API, and is the bridge into the path-B step 3
(Tauberian transfer) that will eventually discharge
`primes_4k1_natural_density`.
-/

open ArithmeticFunction

/-- **Dirichlet-density lower bound at `(q, a) = (4, 1)`.**
For `x ∈ Ioc 1 2`, the L-series sum of the von Mangoldt function restricted
to the residue class `(n : ZMod 4) = 1` is bounded below by
`(1/2) · (x - 1)⁻¹ - C` for some constant `C` (depending only on the closed
half-plane behaviour of the auxiliary residue-class L-function, which is
continuous on `re s ≥ 1` by `continuousOn_LFunctionResidueClassAux`).

This is `vonMangoldt.LSeries_residueClass_lower_bound` specialized to
`(q, a) = (4, 1)`, with the explicit constant `1/φ(4) = 1/2`. The bound
demonstrates that the L-series sum tends to `+∞` at rate `(1/2)/(x-1)` as
`x ↘ 1`, which is the Dirichlet-density-style pole-strength data for the
arithmetic progression `4k + 1`. -/
theorem LSeries_residueClass_one_mod_four_lower_bound :
    ∃ C : ℝ, ∀ {x : ℝ} (_ : x ∈ Set.Ioc 1 2),
      (2 : ℝ)⁻¹ / (x - 1) - C ≤
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ) ^ x := by
  obtain ⟨C, hC⟩ :=
    ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound one_isUnit_zmodFour
  refine ⟨C, fun {x} hx ↦ ?_⟩
  have h := hC hx
  have htot : ((Nat.totient 4 : ℕ) : ℝ) = (2 : ℝ) := by
    rw [totient_four]; norm_num
  rwa [htot] at h

/-- **Prime-restricted Dirichlet divergence at `(q, a) = (4, 1)`.**
The function `n ↦ Λ(n) / n` restricted to primes with `(n : ZMod 4) = 1`
(equivalently, primes `≡ 1 (mod 4)`) is **not summable**.

This is `vonMangoldt.not_summable_residueClass_prime_div` specialized to
`(q, a) = (4, 1)`. It is strictly stronger than the elementary infinitude
statement (`primes_4k1_infinite_mathlib`): the divergence of `∑ Λ(p)/p` over
primes ≡ 1 (mod 4) is the *Mertens-style* density statement that Mertens
(1874) proved semi-elementarily, but here delivered through the analytic
L-series route from Mathlib's PNT-AP machinery. -/
theorem not_summable_primes_4k1_vonMangoldt_div :
    ¬ Summable fun n : ℕ =>
      (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n else 0) / n :=
  ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div one_isUnit_zmodFour

/-! ## S5 ORIENT/ACT: elementary divergence + sum-of-two-squares corollary

These lemmas package the S4 divergence in a form a non-specialist reader can
parse without knowing about `residueClass` indicators, and add the
sum-of-two-squares infinitude corollary (path C from `state.md`) chaining
through Fermat's Christmas theorem `Nat.Prime.sq_add_sq`.

`residueClass_one_mod_four_apply_prime` is a private helper that unfolds
`ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4)` on prime arguments
to the elementary case-split `if p % 4 = 1 then log p else 0`. The unfolding
uses `vonMangoldt_apply_prime` (giving `Λ p = log p` for `p` prime) and the
`mod_four_eq_one_iff_zmodFour_eq_one` bridge.

`not_summable_primes_4k1_log_div` translates `not_summable_primes_4k1_vonMangoldt_div`
into the elementary form `¬ Summable (n ↦ if (n.Prime ∧ n % 4 = 1) then log n / n
else 0)`. This is the **Mertens-1874 qualitative divergence** in the formulation
a number-theory reader would expect; the quantitative `(1/2) log log N` rate
is left for a future iteration (Abel summation + the S4 lower bound).

`primes_sum_two_squares_infinite` is the **path C corollary**: combining
`primes_4k1_infinite_mod` with `Nat.Prime.sq_add_sq` (Fermat 1640, formalized
in `Mathlib.NumberTheory.SumTwoSquares`), the set of primes representable
as a sum of two squares is infinite. This is the elementary-density-free
flavour of the path-C result; the *density* form (sum-of-two-squares primes
have density 1/2) is deferred until a density form is in place.
-/

/-- **Helper: residueClass on primes unfolds to a `% 4` case-split.**
For prime `p`, `vonMangoldt.residueClass (1 : ZMod 4) p = if p % 4 = 1 then log p else 0`.
Combines `vonMangoldt_apply_prime` with `mod_four_eq_one_iff_zmodFour_eq_one`. -/
private lemma residueClass_one_mod_four_apply_prime {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) p =
      (if p % 4 = 1 then Real.log p else 0) := by
  unfold ArithmeticFunction.vonMangoldt.residueClass
  by_cases hmod : p % 4 = 1
  · have hzm : (p : ZMod 4) = 1 := mod_four_eq_one_iff_zmodFour_eq_one.mp hmod
    rw [if_pos hmod, Set.indicator_of_mem
          (show p ∈ {n : ℕ | (n : ZMod 4) = 1} from hzm)]
    exact ArithmeticFunction.vonMangoldt_apply_prime hp
  · have hzm : (p : ZMod 4) ≠ 1 := fun h =>
      hmod (mod_four_eq_one_iff_zmodFour_eq_one.mpr h)
    rw [if_neg hmod]
    exact Set.indicator_of_notMem
      (show p ∉ {n : ℕ | (n : ZMod 4) = 1} from hzm) _

/-- **Mertens-1874 qualitative divergence at `(q, a) = (4, 1)` — elementary form.**
The function `n ↦ log n / n` restricted to primes `≡ 1 (mod 4)` is **not summable**.

This is `not_summable_primes_4k1_vonMangoldt_div` translated through the
residueClass-on-primes unfolding `residueClass_one_mod_four_apply_prime`. The
elementary form avoids the `vonMangoldt.residueClass` indicator wrapper and
states the divergence in the formulation most readers expect: the
"Mertens-1874 divergence over primes in an arithmetic progression"
specialized to `(q, a) = (4, 1)`.

Quantitatively the Mertens rate is `∑_{p ≤ N, p ≡ 1 (4)} log p / p ~ (1/2) log N`
(prime number theorem for arithmetic progressions, restricted to primes), but
the asymptotic rate requires Abel summation on top of `LSeries_residueClass_lower_bound`
and is deferred to a future iteration. -/
theorem not_summable_primes_4k1_log_div :
    ¬ Summable fun n : ℕ =>
      (if n.Prime ∧ n % 4 = 1 then Real.log n / n else (0 : ℝ)) := by
  have heq : (fun n : ℕ =>
        (if n.Prime ∧ n % 4 = 1 then Real.log n / n else (0 : ℝ))) =
      (fun n : ℕ =>
        (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n
          else 0) / n) := by
    funext n
    by_cases hp : n.Prime
    · rw [if_pos hp, residueClass_one_mod_four_apply_prime hp]
      by_cases hmod : n % 4 = 1
      · rw [if_pos ⟨hp, hmod⟩, if_pos hmod]
      · rw [if_neg (fun ⟨_, h⟩ => hmod h), if_neg hmod, zero_div]
    · rw [if_neg (fun ⟨h, _⟩ => hp h), if_neg hp, zero_div]
  rw [heq]
  exact not_summable_primes_4k1_vonMangoldt_div

/-- **Path C corollary: primes that are sums of two squares are infinite.**
By Fermat's Christmas theorem (`Nat.Prime.sq_add_sq` in
`Mathlib.NumberTheory.SumTwoSquares`), every prime `p` with `p % 4 ≠ 3` is
representable as `a² + b²` for some `a, b : ℕ`. In particular every prime
`p ≡ 1 (mod 4)` is a sum of two squares; combined with `primes_4k1_infinite_mod`,
**the set of primes expressible as a sum of two squares is infinite**.

This is the *infinitude* form of the path-C result; the *density* form (such
sums-of-two-squares primes have density 1/2 among all primes) is deferred
until a natural-density or Dirichlet-density form of the OQ-03 target is
in place. The infinitude form is unblocked by current Mathlib and is a
clean elementary corollary of S2's Mathlib bridge plus Fermat's 1640
theorem. -/
theorem primes_sum_two_squares_infinite :
    {p : ℕ | p.Prime ∧ ∃ a b : ℕ, a ^ 2 + b ^ 2 = p}.Infinite := by
  apply primes_4k1_infinite_mod.mono
  rintro p ⟨hp, hmod⟩
  refine ⟨hp, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact Nat.Prime.sq_add_sq (by omega)

/-! ## S6 SCAFFOLD: logarithmic-density target (Mertens-1874 form)

The qualitative divergence in `not_summable_primes_4k1_log_div` (S5) extracts
*no rate* — it only says the partial sums of `log p / p` over primes
`p ≡ 1 (mod 4)` are unbounded. The Mertens-1874 quantitative statement
pins the rate at `(1/2) log N`, i.e. logarithmic density 1/2:

  ∑_{p ≤ N, p ≡ 1 (mod 4)} (log p) / p  ~  (1/2) · log N    (N → ∞).

This is the **logarithmic-density** form of OQ-03, strictly weaker than the
natural-density form but **unblocked by the current Mathlib pin**: the proof
follows by Abel summation on the S4 lower bound
`LSeries_residueClass_one_mod_four_lower_bound` together with the analogous
upper bound (a corollary of `vonMangoldt_LSeries_eq` plus the standard tail
estimate). The Ikehara-Tauberian machinery is **not** required for the
logarithmic form — that's what makes Mertens-1874 a semi-elementary result.

S6 (this iteration) is a **statement-only scaffold**: the target asymptotic
is declared with `sorry`, giving subsequent iterations a concrete syntactic
target. The proof (~100-150 lines, Abel summation in the limit `x ↘ 1`) is
deferred to S7+.
-/

/-- **S6 SCAFFOLD (logarithmic Mertens-density target, stated with `sorry`).**
The partial sums of `log p / p` over primes `p ≡ 1 (mod 4)` up to `N` grow
asymptotically like `(1/2) · log N`. Equivalently, the prime-residue-class
counting function has *logarithmic* density `1/2 = 1/φ(4)` in the Mertens
sense.

This is strictly *weaker* than `primes_4k1_natural_density`
(which would give natural density `1/2`) but strictly *stronger* than
`not_summable_primes_4k1_log_div` (S5, qualitative divergence only). It
captures Mertens-1874's precise rate, which the natural-density form
deepens to a counting asymptotic via the (currently missing) Tauberian
transfer.

**Proof outline (Abel summation, deferred to S7+):**

1. By Abel summation, for any `f : ℕ → ℝ` and `s > 1`,
   `∑_{n ≤ N} f n / n^s` and `∫_1^N (∑_{n ≤ t} f n) / t^(s+1) dt`
   are related by an explicit identity (Mathlib:
   `tsum_eq_integral_of_summable` / `Real.Abel_summation`).
2. Apply this with `f n = (vonMangoldt.residueClass 1 n) · (n.Prime indicator)`
   and `s = x` in the limit `x ↘ 1`, using S4's
   `LSeries_residueClass_one_mod_four_lower_bound`.
3. Convert the von Mangoldt restricted-prime sum to the elementary
   `(log p) / p` form via `residueClass_one_mod_four_apply_prime` and
   `vonMangoldt_apply_prime`.
4. The analogous upper bound (using `LSeries_residueClass` continuity on
   the half-plane `re s ≥ 1`) pins the `1/2 = 1/φ(4)` constant.

**Status (Mathlib v4.26.0):** unblocked. All required Mathlib API
(`Real.log`, `LSeries`, `vonMangoldt.LSeries_residueClass_lower_bound`,
`Asymptotics.IsEquivalent`, Abel summation) is present at the pinned
revision `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The remaining work is
analytic-number-theory bookkeeping rather than missing infrastructure. -/
theorem mertens_log_density_4k1 :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)).sum
          (fun p => Real.log (p : ℝ) / (p : ℝ))) / Real.log (N : ℝ))
      atTop (𝓝 (1 / 2)) := by
  sorry

/-! ## OQ-03 target: natural-density form -/

/-- **OQ-03 deliverable (stated, not yet proved).**
The natural density of primes `≡ 1 (mod 4)` among all primes is `1/2`.

This is the natural-density form of Dirichlet's theorem for `(q, a) = (4, 1)`;
equivalently, the prime number theorem for arithmetic progressions specialized
to `(q, a) = (4, 1)`.

**Status (Mathlib v4.26.0):** The proof is currently blocked on the lack of
an Ikehara-Tauberian module in Mathlib at the pinned revision. The L-series
infrastructure needed for the proof is *present*
(`DirichletCharacter.LFunction`, `LSeries_residueClass_lower_bound`,
`LFunction_ne_zero_of_one_le_re`), but the Tauberian transfer from the
L-series pole strength to the prime-counting asymptotic is not yet exposed.

**Proof outline (when Mathlib supports it):**

1. By Dirichlet character orthogonality on `(ℤ/4ℤ)ˣ`, the indicator function
   of `{p : p ≡ 1 (mod 4)}` decomposes as `(1/2)(χ₀(p) + χ₁(p))` where
   `χ₀` is the trivial character mod 4 and `χ₁` is the unique nontrivial
   real character.
2. Apply PNT-AP (Ikehara-Tauberian on the L-series) to extract the
   asymptotic `π(N; 4, 1) ~ (1/2) · π(N)`.
3. Divide and take limits.

Using `Set.indicator (fun _ => (1 : ℝ))` keeps the statement purely in terms of
finset cardinality on `Finset.range`, matching common Mathlib conventions for
prime-counting asymptotics.
-/
theorem primes_4k1_natural_density :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)).card : ℝ)
          / ((Finset.range (N + 1)).filter Nat.Prime).card)
      atTop (𝓝 (1 / 2)) := by
  sorry

/-! ## Sanity checks -/

#check primes_4k1_infinite_mathlib
#check primes_4k1_infinite_mod
#check sum_dirichletChars_zmodFour
#check indicator_zmodFour_eq_one
#check indicator_mod_four_eq_one
#check LSeries_residueClass_one_mod_four_lower_bound
#check not_summable_primes_4k1_vonMangoldt_div
#check not_summable_primes_4k1_log_div
#check primes_sum_two_squares_infinite
#check mertens_log_density_4k1
#check primes_4k1_natural_density

end InfinitudePrimes4k1OQ03
