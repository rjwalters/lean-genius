/-
  # Odd primitive abundant numbers — the base witness 945

  *Open question* (`abundant-number-oq-03-oq-03`): are there infinitely many
  **odd primitive abundant** numbers?  A positive integer `n` is *abundant* when
  `n < σ'(n) := ∑_{d ∣ n, d < n} d`, and *deficient* when `σ'(n) < n`
  (`Nat.Abundant` / `Nat.Deficient` in `Mathlib.NumberTheory.FactorisationProperties`).
  Following OEIS A006038, `n` is **primitive abundant** here when it is abundant
  yet *every* proper divisor is deficient — abundance appears for the first time,
  under divisibility, exactly at `n`.  The target set is

  `OddPrimitiveAbundant = { n | Odd n ∧ IsPrimitiveAbundant n }`   (A006038),

  and the open question asks whether it is infinite.

  ## What this file settles

  The infinitude is genuinely open (no explicit odd family is known that is
  provably primitive abundant for infinitely many members).  What *can* be pinned
  down, axiom-free, is the **base of the problem**: the smallest odd abundant
  number, `945 = 3³·5·7`, is in fact odd primitive abundant, so the target set is
  nonempty with an explicit least element.  This anchors any future infinitude
  construction (each new witness must, like 945, be abundant with all 15 proper
  divisors deficient).

  * `IsPrimitiveAbundant`            — the A006038 predicate (abundant, all proper
                                       divisors deficient).
  * `abundant_945`, `odd_945`        — `σ'(945) = 975 > 945`, and `945` is odd.
  * `primitive_945`                  — all 15 proper divisors of `945`
                                       (`1,3,5,7,9,15,21,27,35,45,63,105,135,189,315`)
                                       are deficient, so `945` is primitive abundant.
  * `mem_oddPrimitiveAbundant_945`   — `945 ∈ OddPrimitiveAbundant`.
  * `not_primitive_of_abundant_properDivisor` — the structural obstruction: any
                                       abundant proper divisor destroys primitivity
                                       (abundance and deficiency are exclusive).

  Toward the (open) infinitude, this file also builds the **σ-arithmetic engine**
  for the Route-1 family `m·p`:

  * `sum_divisors_prime`             — `σ(p) = p + 1` for prime `p`.
  * `sum_divisors_mul_prime`         — `σ(m·p) = σ(m)·(p+1)` when `p` is prime and
                                       `p ∤ m` (multiplicativity of `σ` on coprime
                                       factors).
  * `abundant_mul_prime_iff`         — reduces abundance of `m·p` to the single
                                       linear-in-`p` inequality `2mp < σ(m)(p+1)`.
  * `deficient_left_of_primitive_mul_prime` — any Route-1 base `m` must itself be
                                       deficient (it is a proper divisor of `m·p`).

  ## Verification status: verified (axiom-free)

  Unlike the sibling `abundant-number-oq-02` entry, which discharges the 945-range
  computations with `native_decide` (`Lean.ofReduceBool`, axiomatized), the finite
  checks here are small enough — a single number `945` and its 15 divisors, each
  `≤ 315` — to run in the Lean **kernel** via `decide` with a raised
  `maxRecDepth`.  `#print axioms` for every theorem below lists only
  `propext, Classical.choice, Quot.sound`.

  ## Toward infinitude (recorded, not proved)

  Two routes, both open:
  1. *Odd analogue of the even `2^k·p` construction* — an odd base `m` with
     `σ(m)/m` just below 2 times an odd prime `p` in a controlled (Bertrand-type)
     window, so `m·p` is abundant for the first time at itself.  The obstruction:
     odd `m` approach the abundance boundary slowly, and proper-divisor deficiency
     is a real case analysis, not the clean "powers of two are deficient" fact.
  2. *Primitive-part extraction* — one might hope every abundant `n` has a
     primitive abundant divisor, then show the primitive parts of an infinite odd
     abundant family (`Nat.infinite_odd_abundant`) are odd and unbounded.  **This
     route is blocked at its first step under the strict definition used here:**
     `no_isPrimitiveAbundant_dvd_12` proves *no* divisor of the abundant number
     `12` is `IsPrimitiveAbundant`, because the perfect proper divisor `6 ∣ 12`
     violates the "all proper divisors deficient" clause and the smallest strict
     primitive abundant number is `20 > 12`.  Extraction works only for the weaker
     "no abundant proper divisor" notion (OEIS A091191); recovering a *strict*
     (deficient-divisors) primitive part additionally requires excluding perfect
     divisors, and controlling oddness/unboundedness still needs a pigeonhole that
     a single bounded part could defeat.  (Update 2026-07-22: the A091191
     extraction and the "abundant ⟺ multiple of a weakly primitive abundant"
     characterization are now PROVED at the end of this file, odd-compatibly;
     the infinitude of the generators remains open.)

  Reference: OEIS A006038 (odd primitive abundant numbers); A091191 (primitive
  abundant numbers).  Sibling gallery entries: `abundant-number-oq-02` (945 is the
  smallest odd abundant number), `abundant-number-oq-01` (12 is the smallest
  abundant number).
-/
import Mathlib

namespace AbundantNumberOQ03OQ03

open Nat

/-- **Primitive abundant** (OEIS A006038 sense): `n` is abundant, but every proper
divisor of `n` is deficient. Abundance appears for the first time, under
divisibility, exactly at `n`. -/
def IsPrimitiveAbundant (n : ℕ) : Prop :=
  n.Abundant ∧ ∀ d ∈ n.properDivisors, d.Deficient

instance : DecidablePred IsPrimitiveAbundant := fun n =>
  decidable_of_iff (n.Abundant ∧ ∀ d ∈ n.properDivisors, d.Deficient) Iff.rfl

/-- The set of **odd primitive abundant** numbers, OEIS A006038. Whether this set
is infinite is the open problem `abundant-number-oq-03-oq-03`. -/
def OddPrimitiveAbundant : Set ℕ := {n | Odd n ∧ IsPrimitiveAbundant n}

/-- Abundance and deficiency are mutually exclusive: no number is both. -/
theorem not_deficient_of_abundant {n : ℕ} (h : n.Abundant) : ¬ n.Deficient := by
  -- `Abundant n : n < σ'(n)`, `Deficient n : σ'(n) < n`
  exact fun hd => absurd h (Nat.not_lt.mpr (le_of_lt hd))

/-- The structural obstruction to primitivity: if any proper divisor of `n` is
itself abundant, then `n` is *not* primitive abundant (the divisor cannot be
deficient). This is the divisibility-minimality content of the definition. -/
theorem not_primitive_of_abundant_properDivisor {n d : ℕ}
    (hd : d ∈ n.properDivisors) (hab : d.Abundant) : ¬ IsPrimitiveAbundant n := by
  rintro ⟨-, hdef⟩
  exact not_deficient_of_abundant hab (hdef d hd)

/-- `945` is odd. -/
theorem odd_945 : Odd (945 : ℕ) := by decide

/-- **`945` is abundant.** Its proper divisors sum to `975 > 945`. -/
theorem abundant_945 : Nat.Abundant 945 := by
  set_option maxRecDepth 4000 in decide

/-- **`945` is primitive abundant.** Every one of its 15 proper divisors
`1,3,5,7,9,15,21,27,35,45,63,105,135,189,315` is deficient. -/
theorem primitive_945 : IsPrimitiveAbundant 945 := by
  refine ⟨abundant_945, ?_⟩
  set_option maxRecDepth 4000 in decide

/-- **`945` is odd primitive abundant** — the least element of `OddPrimitiveAbundant`
(OEIS A006038), and the base witness that any infinitude construction must extend. -/
theorem mem_oddPrimitiveAbundant_945 : 945 ∈ OddPrimitiveAbundant :=
  ⟨odd_945, primitive_945⟩

-- ============================================================
-- The strict definition bites: Route-2 extraction fails
-- ============================================================

/-- **`12` is abundant but *not* primitive abundant.** Its proper divisor `6` is
*perfect* (`σ'(6) = 6`), hence not deficient, so the "all proper divisors deficient"
clause of `IsPrimitiveAbundant` fails even though `12` is the smallest abundant
number. -/
theorem not_isPrimitiveAbundant_12 : ¬ IsPrimitiveAbundant 12 := by
  set_option maxRecDepth 4000 in decide

/-- **Route-2 extraction is FALSE under the strict definition.** No divisor of the
abundant number `12` is primitive abundant: the smallest primitive abundant number
(all proper divisors deficient, OEIS A071395) is `20 > 12`, and the perfect proper
divisor `6 ∣ 12` blocks strict primitivity of `12` itself.

Consequently the naive extraction *"every abundant `n` has a primitive abundant
divisor"* — recorded as Route 2 in this file's header — does **not** hold for
`IsPrimitiveAbundant` (which demands *deficient* proper divisors). It holds only for
the weaker notion *"abundant with no abundant proper divisor"* (OEIS A091191), under
which `12` itself is primitive. A perfect proper divisor is exactly the obstruction
that separates the two notions, so Route-2 cannot be run against the strict
definition without first passing through the A091191 notion and separately excluding
perfect divisors. -/
theorem no_isPrimitiveAbundant_dvd_12 :
    ∀ d ∈ Nat.divisors 12, ¬ IsPrimitiveAbundant d := by
  set_option maxRecDepth 4000 in decide

-- ============================================================
-- Toward infinitude: the σ-arithmetic engine for `m · p`
-- ============================================================

/-
  Route 1 (odd `m · p` with `p` an odd prime outside a Bertrand-type window)
  needs the sum-of-divisors of `m · p` in closed form.  Since `p ∤ m` makes
  `m` and `p` coprime and `σ` (the sum-of-divisors) is multiplicative, we get
  the workhorse identity `σ(m·p) = σ(m)·(p+1)`, which turns the abundance test
  `2·(m·p) < σ(m·p)` into a *linear-in-`p`* inequality `2mp < σ(m)(p+1)`.  That
  is the lever any explicit odd-family construction pulls: fix `m`, then choose
  `p` in the range that keeps `m·p` abundant.

  These lemmas are stated for the raw Mathlib sum `∑ d ∈ n.divisors, d`
  (`= Nat.ArithmeticFunction.σ 1 n`) so they compose with
  `Nat.abundant_iff_sum_divisors`.
-/

/-- The sum of the divisors of a prime `p` is `p + 1` (its only divisors are
`1` and `p`).  The base case of the σ-arithmetic engine. -/
theorem sum_divisors_prime {p : ℕ} (hp : p.Prime) :
    ∑ d ∈ p.divisors, d = p + 1 := by
  rw [hp.divisors, Finset.sum_pair hp.one_lt.ne]
  omega

/-- **σ closed form for `m · p`** (`p` prime, `p ∤ m`): the sum of divisors is
multiplicative on the coprime factors `m` and `p`, so
`σ(m·p) = σ(m) · (p + 1)`.  The reusable lever for Route-1 witness search. -/
theorem sum_divisors_mul_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    ∑ d ∈ (m * p).divisors, d = (∑ d ∈ m.divisors, d) * (p + 1) := by
  have hcop : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hpm).symm
  rw [hcop.sum_divisors_mul, sum_divisors_prime hp]

/-- **Abundance criterion for `m · p`** (`p` prime, `p ∤ m`): reduces the
abundance of `m·p` to the single linear-in-`p` inequality
`2·(m·p) < σ(m)·(p+1)`.  Directly usable to search for a prime `p` making a
fixed odd base `m` abundant at `m·p`. -/
theorem abundant_mul_prime_iff {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (m * p).Abundant ↔ 2 * (m * p) < (∑ d ∈ m.divisors, d) * (p + 1) := by
  rw [Nat.abundant_iff_sum_divisors, sum_divisors_mul_prime hp hpm]

/-- **Necessary condition for primitivity of `m · p`**: if `m · p` is primitive
abundant with `p` prime and `0 < m`, then the cofactor `m` is deficient — `m`
is a proper divisor of `m·p` (as `p ≥ 2`), so primitivity forces it deficient.
Every Route-1 base `m` must therefore itself be deficient. -/
theorem deficient_left_of_primitive_mul_prime {m p : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hprim : IsPrimitiveAbundant (m * p)) : m.Deficient := by
  refine hprim.2 m (Nat.mem_properDivisors.mpr ⟨dvd_mul_right m p, ?_⟩)
  have hle : m * 2 ≤ m * p := by gcongr; exact hp.two_le
  omega

/-- **Proper-divisor decomposition for `m · p`** (`p` prime, `0 < m`): every proper
divisor of `m·p` is either a divisor of `m`, or `p` times a *proper* divisor of `m`.
Splitting `d ∣ m·p` into `d = d₁·d₂` with `d₁ ∣ m`, `d₂ ∣ p` (`Nat.dvd_mul`), the
prime `p` forces `d₂ ∈ {1, p}`; the `d₂ = p` branch gives `d = p·d₁` with `d₁ < m`
(from `d < m·p`).  This is the membership half of the Route-1 divisor structure that
turns a primitivity check on `m·p` into checks on `m`'s divisors and their
`p`-multiples. -/
theorem mem_properDivisors_mul_prime {m p d : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hd : d ∈ (m * p).properDivisors) :
    d ∈ m.divisors ∨ ∃ e ∈ m.properDivisors, d = p * e := by
  rw [Nat.mem_properDivisors] at hd
  obtain ⟨hdvd, hlt⟩ := hd
  obtain ⟨d₁, d₂, hd1, hd2, hprod⟩ := Nat.dvd_mul.mp hdvd
  rcases hp.eq_one_or_self_of_dvd d₂ hd2 with h1 | hpp
  · left
    rw [Nat.mem_divisors]
    exact ⟨by rw [← hprod, h1, mul_one]; exact hd1, hm.ne'⟩
  · right
    refine ⟨d₁, Nat.mem_properDivisors.mpr ⟨hd1, ?_⟩, by rw [← hprod, hpp, mul_comm]⟩
    have hdp : d₁ * p < m * p := by rw [← hprod, hpp] at hlt; exact hlt
    exact lt_of_mul_lt_mul_right hdp (Nat.zero_le p)

/-- **Full primitivity criterion for `m · p`** (`p` prime, `0 < m`): `m·p` is
primitive abundant as soon as it is abundant, *every* divisor of `m` is deficient,
and every `p`-multiple of a proper divisor of `m` is deficient.  This upgrades
`abundant_mul_prime_iff` (which only handles abundance) to the full A006038
predicate, reducing the Route-1 primitivity obligation to conditions purely on `m`
and its `p`-multiples via `mem_properDivisors_mul_prime`. -/
theorem isPrimitiveAbundant_mul_prime {m p : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hab : (m * p).Abundant)
    (hmdef : ∀ d ∈ m.divisors, d.Deficient)
    (hpdef : ∀ e ∈ m.properDivisors, (p * e).Deficient) :
    IsPrimitiveAbundant (m * p) := by
  refine ⟨hab, fun d hd => ?_⟩
  rcases mem_properDivisors_mul_prime hp hm hd with h | ⟨e, he, rfl⟩
  · exact hmdef d h
  · exact hpdef e he

-- ============================================================
-- Deficiency is inherited by divisors — simplifying the criterion
-- ============================================================

/-- **Deficiency via the abundancy index.**  For `n ≠ 0`, `n` is deficient exactly when its
abundancy index `σ(n)/n` is below `2`.  The deficient counterpart of Mathlib's
`Nat.abundant_iff_two_lt_abundancyIndex`. -/
theorem deficient_iff_abundancyIndex_lt_two {n : ℕ} (hn : n ≠ 0) :
    n.Deficient ↔ n.abundancyIndex < 2 := by
  have hpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [abundancyIndex, div_lt_iff₀ hpos]
  have hcast : ((∑ i ∈ n.divisors, i : ℕ) : ℚ) < 2 * (n : ℚ)
      ↔ (∑ i ∈ n.divisors, i) < 2 * n := by
    rw [show (2 : ℚ) * (n : ℚ) = ((2 * n : ℕ) : ℚ) by push_cast; ring]
    exact Nat.cast_lt
  rw [hcast, sum_divisors_eq_sum_properDivisors_add_self]
  unfold Nat.Deficient
  omega

/-- **Deficiency is inherited by divisors.**  If `n` is deficient and `m ∣ n` (`m ≠ 0`), then
`m` is deficient.  The abundancy index is monotone under divisibility
(`Nat.abundancyIndex_le_of_dvd`), so `m`'s index is at most `n`'s, which is `< 2`.  This is the
divisibility-downward dual of `Nat.Abundant.of_dvd`: every divisor of a deficient number is
itself deficient. -/
theorem deficient_of_dvd {m n : ℕ} (hn : n.Deficient) (hd : m ∣ n) (hm : m ≠ 0) :
    m.Deficient := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by decide)
  rw [deficient_iff_abundancyIndex_lt_two hm]
  exact lt_of_le_of_lt (abundancyIndex_le_of_dvd hn0 hd)
    ((deficient_iff_abundancyIndex_lt_two hn0).mp hn)

/-- **Simplified primitivity criterion for `m · p`.**  Since deficiency is inherited by divisors
(`deficient_of_dvd`), the "every divisor of `m` is deficient" hypothesis of
`isPrimitiveAbundant_mul_prime` collapses to `m` itself being deficient.  So `m·p` is primitive
abundant as soon as it is abundant, `m` is deficient, and every `p`-multiple of a proper divisor
of `m` is deficient — one fewer obligation for a Route-1 witness search. -/
theorem isPrimitiveAbundant_mul_prime' {m p : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hab : (m * p).Abundant) (hmdef : m.Deficient)
    (hpdef : ∀ e ∈ m.properDivisors, (p * e).Deficient) :
    IsPrimitiveAbundant (m * p) :=
  isPrimitiveAbundant_mul_prime hp hm hab
    (fun _ hd => deficient_of_dvd hmdef (mem_divisors.mp hd).1 (pos_of_mem_divisors hd).ne')
    hpdef

-- ============================================================
-- Fully arithmetic primitivity criterion for `m · p`
-- ============================================================

/-
  The criteria above still carry the semantic predicates `Nat.Abundant` and
  `Nat.Deficient`.  For a *concrete* Route-1 witness search we want the
  primitivity of `m·p` expressed entirely in terms of divisor sums, so it can be
  discharged by pure computation (`decide`).  The two lemmas below convert
  deficiency into a divisor-sum inequality — the deficient dual of
  `abundant_iff_sum_divisors` / `abundant_mul_prime_iff` — and then package the
  whole primitivity obligation as three arithmetic inequalities.
-/

/-- **Deficiency in divisor-sum form.**  For every `n`, `n` is deficient exactly
when `σ(n) = ∑_{d ∣ n} d` is below `2n`.  The deficient dual of Mathlib's
`Nat.abundant_iff_sum_divisors`.  (Holds unconditionally: for `n = 0` both sides
are `0 < 0`, i.e. false.) -/
theorem deficient_iff_sum_divisors {n : ℕ} :
    n.Deficient ↔ (∑ d ∈ n.divisors, d) < 2 * n := by
  rw [Nat.Deficient, sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-- **Deficiency criterion for `e · p`** (`p` prime, `p ∤ e`): the multiplicative
dual of `abundant_mul_prime_iff`.  Since `σ(e·p) = σ(e)·(p+1)`, deficiency of
`e·p` reduces to the single linear-in-`p` inequality `σ(e)·(p+1) < 2·(e·p)`.
This turns the primitivity side condition "each `p·e` is deficient" into
arithmetic. -/
theorem deficient_mul_prime_iff {e p : ℕ} (hp : p.Prime) (hpe : ¬ p ∣ e) :
    (e * p).Deficient ↔ (∑ d ∈ e.divisors, d) * (p + 1) < 2 * (e * p) := by
  rw [deficient_iff_sum_divisors, sum_divisors_mul_prime hp hpe]

/-- **Fully arithmetic primitivity criterion for `m · p`** (`p` prime, `0 < m`,
`p ∤ m`).  Every hypothesis is now a divisor-sum inequality, so a concrete
Route-1 witness `m·p` can be certified primitive abundant by pure computation:

* `2·m·p < σ(m)·(p+1)`                     — `m·p` is abundant;
* `σ(m) < 2·m`                             — the base `m` is deficient;
* `∀ e ∈ m.properDivisors, σ(e)·(p+1) < 2·e·p` — every `p`-multiple of a proper
  divisor of `m` is deficient.

This is the endpoint of the Route-1 reduction: it eliminates the semantic
`Abundant`/`Deficient` predicates entirely, leaving only `σ`-arithmetic. -/
theorem isPrimitiveAbundant_mul_prime_arith {m p : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hpm : ¬ p ∣ m)
    (hab : 2 * (m * p) < (∑ d ∈ m.divisors, d) * (p + 1))
    (hmdef : (∑ d ∈ m.divisors, d) < 2 * m)
    (hpdef : ∀ e ∈ m.properDivisors,
      (∑ d ∈ e.divisors, d) * (p + 1) < 2 * (e * p)) :
    IsPrimitiveAbundant (m * p) := by
  refine isPrimitiveAbundant_mul_prime' hp hm ((abundant_mul_prime_iff hp hpm).mpr hab)
    (deficient_iff_sum_divisors.mpr hmdef) (fun e he => ?_)
  -- `e ∣ m` and `p ∤ m` force `p ∤ e`, so `deficient_mul_prime_iff` applies to `e·p`.
  have hedvd : e ∣ m := (Nat.mem_properDivisors.mp he).1
  have hpe : ¬ p ∣ e := fun h => hpm (h.trans hedvd)
  rw [mul_comm p e]
  exact (deficient_mul_prime_iff hp hpe).mpr (hpdef e he)

/-- **The base witness `945` recovered through the arithmetic engine.**  Taking
`m = 189` and the odd prime `p = 5` (so `m·p = 945`), the fully arithmetic
criterion `isPrimitiveAbundant_mul_prime_arith` certifies `945` primitive
abundant purely from divisor sums — an end-to-end validation of the Route-1
machinery against the known least witness.  Here `σ(189) = 320`, so
`2·945 = 1890 < 1920 = 320·6` (abundant), `320 < 378 = 2·189` (`189` deficient),
and each proper divisor `e ∣ 189` has `σ(e)·6 < 10·e`. -/
theorem primitive_945_via_engine : IsPrimitiveAbundant 945 := by
  have h : IsPrimitiveAbundant (189 * 5) := by
    refine isPrimitiveAbundant_mul_prime_arith (by norm_num) (by norm_num)
      (by decide) ?_ ?_ ?_
    · set_option maxRecDepth 4000 in decide
    · set_option maxRecDepth 4000 in decide
    · set_option maxRecDepth 4000 in decide
  norm_num at h
  exact h

/- ## Corrected Route 2: extraction under the weaker primitivity (OEIS A091191)

`not_isPrimitiveAbundant_12` / `no_isPrimitiveAbundant_dvd_12` disproved strict
extraction: an abundant number need not have a *strictly* primitive abundant
divisor, because a perfect proper divisor (like `6 ∣ 12`) blocks strict
primitivity. This section proves that the extraction principle is TRUE for the
weaker notion **A091191** — abundant with no *abundant* proper divisor — and
upgrades it to a characterization: a number is abundant **iff** it is a multiple
of a weakly primitive abundant number, odd-compatibly.

Honesty note: this does NOT resolve the target infinitude. The infinite set of
odd abundant numbers (Mathlib `Nat.infinite_odd_abundant`) is generated under
multiples by odd weakly primitive abundant numbers, but extraction alone cannot
rule out that finitely many generators (e.g. `945` alone) account for all of
them. Whether infinitely many distinct odd generators occur is exactly the open
question, now sharpened to the A091191 notion. -/

/-- **Weakly primitive abundant** (OEIS A091191): abundant with no *abundant*
proper divisor. Perfect proper divisors are tolerated — this is the notion under
which `12` is primitive and divisor-extraction works, in contrast to the strict
`IsPrimitiveAbundant` (all proper divisors *deficient*), for which extraction is
disproven (`no_isPrimitiveAbundant_dvd_12`). -/
def IsWeakPrimitiveAbundant (n : ℕ) : Prop :=
  n.Abundant ∧ ∀ d ∈ n.properDivisors, ¬ d.Abundant

instance : DecidablePred IsWeakPrimitiveAbundant := fun n =>
  decidable_of_iff (n.Abundant ∧ ∀ d ∈ n.properDivisors, ¬ d.Abundant) Iff.rfl

/-- Strict primitivity implies weak primitivity: deficient proper divisors are in
particular not abundant. So A006038-primitives (like `945`) are A091191-weak
primitives, and the extraction below extends the strict theory conservatively. -/
theorem IsPrimitiveAbundant.isWeakPrimitiveAbundant {n : ℕ}
    (h : IsPrimitiveAbundant n) : IsWeakPrimitiveAbundant n :=
  ⟨h.1, fun d hd hab => not_deficient_of_abundant hab (h.2 d hd)⟩

/-- **`12` IS weakly primitive abundant** — its strict-primitivity blocker was
the *perfect* divisor `6`, which A091191 tolerates. Contrast
`not_isPrimitiveAbundant_12`: the two notions part ways exactly at the smallest
abundant number. -/
theorem isWeakPrimitiveAbundant_twelve : IsWeakPrimitiveAbundant 12 := by
  set_option maxRecDepth 4000 in decide

/-- **Extraction (corrected Route 2): every abundant number has a weakly
primitive abundant divisor.** Strong induction: either no proper divisor of `n`
is abundant (then `n` itself qualifies), or descend into an abundant proper
divisor. The strict analogue of this statement is FALSE
(`no_isPrimitiveAbundant_dvd_12`). -/
theorem exists_isWeakPrimitiveAbundant_dvd :
    ∀ n : ℕ, n.Abundant → ∃ d, d ∣ n ∧ IsWeakPrimitiveAbundant d := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h : ∃ d ∈ n.properDivisors, d.Abundant
    · obtain ⟨d, hdmem, hdab⟩ := h
      obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp hdmem
      obtain ⟨e, hed, hew⟩ := ih d hdlt hdab
      exact ⟨e, hed.trans hdvd, hew⟩
    · exact ⟨n, dvd_refl n, hn, fun d hd hdab => h ⟨d, hd, hdab⟩⟩

/-- **Characterization: the abundant numbers are exactly the multiples of weakly
primitive abundant numbers.** Forward: extraction. Backward: any nonzero
multiple of an abundant number is abundant (`Nat.Abundant.of_dvd`). -/
theorem abundant_iff_exists_isWeakPrimitiveAbundant_dvd {n : ℕ} (hn : n ≠ 0) :
    n.Abundant ↔ ∃ d, d ∣ n ∧ IsWeakPrimitiveAbundant d := by
  constructor
  · exact exists_isWeakPrimitiveAbundant_dvd n
  · rintro ⟨d, hdvd, hdab, -⟩
    exact hdab.of_dvd hdvd hn

/-- **Odd-compatible extraction**: an odd abundant number has an **odd** weakly
primitive abundant divisor (divisors of odd numbers are odd,
`Odd.of_dvd_nat`). -/
theorem exists_odd_isWeakPrimitiveAbundant_dvd {n : ℕ} (hodd : Odd n)
    (hn : n.Abundant) : ∃ d, d ∣ n ∧ Odd d ∧ IsWeakPrimitiveAbundant d := by
  obtain ⟨d, hdvd, hw⟩ := exists_isWeakPrimitiveAbundant_dvd n hn
  exact ⟨d, hdvd, hodd.of_dvd_nat hdvd, hw⟩

/-- **The odd structure theorem: odd abundant numbers are exactly the odd
multiples of odd weakly primitive abundant numbers.** With Mathlib's
`Nat.infinite_odd_abundant`, the infinite set of odd abundant numbers is
generated under multiples by the odd A091191-primitives; the open infinitude
question asks whether the generator set itself is infinite. -/
theorem odd_abundant_iff_exists_odd_isWeakPrimitiveAbundant_dvd {n : ℕ}
    (hodd : Odd n) :
    n.Abundant ↔ ∃ d, d ∣ n ∧ Odd d ∧ IsWeakPrimitiveAbundant d := by
  constructor
  · exact exists_odd_isWeakPrimitiveAbundant_dvd hodd
  · rintro ⟨d, hdvd, -, hdab, -⟩
    exact hdab.of_dvd hdvd hodd.pos.ne'

end AbundantNumberOQ03OQ03
