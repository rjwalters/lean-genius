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

/- ## INFINITUDE RESOLVED: products of consecutive primes — the first-crossing family

This section settles the target question **positively**: there are infinitely
many odd primitive abundant numbers (in the strict A006038 sense).

**The mechanism** (materially new versus both recorded routes): for a starting
index `a ≥ 1`, multiply consecutive primes `p_a, p_{a+1}, …` (nth-indexed, so
`p_a` is odd) until the product first becomes abundant. Divergence of `∑ 1/p`
(Mathlib's `not_summable_one_div_on_primes`) forces a first crossing `b`:

* the crossing product `N = p_a ⋯ p_{b-1}` is **abundant** (definition of
  crossing), and
* its predecessor `N/p_{b-1}` is **not** abundant; equality `σ = 2n` is
  impossible for a squarefree odd `n` (with `≥ 2` prime factors, `4 ∣ σ(n)`
  but `2n ≡ 2 [MOD 4]`), so the predecessor is strictly **deficient**, and so
  is every maximal divisor `N/p_i` (the computation only improves when the
  omitted prime is smaller: `p_i ≤ p_{b-1}`). Deficiency is divisor-inherited
  (`deficient_of_dvd`), so *every* proper divisor of `N` is deficient: `N` is
  **primitive abundant** — and odd, since all its prime factors are odd.

Distinct starting indices give witnesses with distinct least prime factors, so
the family is injective and the set is infinite. Unlike Route 1 (append ONE
prime to an odd deficient base with `σ(m)/m → 2⁻`, which needs an unknown odd
family), the base here *grows through* the boundary, and unlike Route 2
(extraction), no divisor of an existing family is taken — the witnesses are
built from scratch. No Bertrand window is needed anywhere. -/

open Finset

/-- **σ of a product of distinct `nth`-indexed primes** is the product of
`pᵢ + 1` — the squarefree closed form, generalizing `sum_divisors_mul_prime`
from one appended prime to any finite index set. -/
theorem sum_divisors_prod_nth (s : Finset ℕ) :
    ∑ d ∈ (∏ i ∈ s, Nat.nth Nat.Prime i).divisors, d
      = ∏ i ∈ s, (Nat.nth Nat.Prime i + 1) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    rw [Finset.prod_cons, Finset.prod_cons, mul_comm (Nat.nth Nat.Prime j)]
    have hnd : ¬ Nat.nth Nat.Prime j ∣ ∏ i ∈ s, Nat.nth Nat.Prime i := by
      intro hdvd
      obtain ⟨i, hi, hdvd'⟩ :=
        ((Nat.prime_nth_prime j).prime.dvd_finsetProd_iff _).mp hdvd
      have heq : Nat.nth Nat.Prime j = Nat.nth Nat.Prime i :=
        (Nat.prime_dvd_prime_iff_eq (Nat.prime_nth_prime j)
          (Nat.prime_nth_prime i)).mp hdvd'
      exact hj (Nat.nth_injective Nat.infinite_setOf_prime heq ▸ hi)
    rw [sum_divisors_mul_prime (Nat.prime_nth_prime j) hnd, ih,
      mul_comm (∏ i ∈ s, (Nat.nth Nat.Prime i + 1))]

/-- A product of `nth`-indexed primes with all indices `≥ 1` is **odd**:
`2 = p₀` is the only even prime, and it is excluded by the index bound. -/
theorem odd_prod_nth {s : Finset ℕ} (hs : ∀ i ∈ s, 1 ≤ i) :
    Odd (∏ i ∈ s, Nat.nth Nat.Prime i) := by
  have h2 : ¬ 2 ∣ ∏ i ∈ s, Nat.nth Nat.Prime i := by
    intro h
    obtain ⟨i, hi, h2i⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp h
    have heq : (2 : ℕ) = Nat.nth Nat.Prime i :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Nat.prime_nth_prime i)).mp h2i
    have h0 : Nat.nth Nat.Prime 0 = Nat.nth Nat.Prime i := by
      rw [Nat.nth_prime_zero_eq_two]; exact heq
    have := Nat.nth_injective Nat.infinite_setOf_prime h0
    have := hs i hi
    omega
  rcases Nat.even_or_odd (∏ i ∈ s, Nat.nth Nat.Prime i) with he | ho
  · exact absurd he.two_dvd h2
  · exact ho

/-- A product of `nth`-indexed primes is positive. -/
theorem prod_nth_pos (s : Finset ℕ) : 0 < ∏ i ∈ s, Nat.nth Nat.Prime i :=
  Finset.prod_pos fun i _ => (Nat.prime_nth_prime i).pos

/-- **No squarefree odd number with indices `≥ 1` is perfect**: for such a
product, `σ = 2·n` is impossible.  Zero factors: `σ(1) = 1 ≠ 2`.  One factor:
`p + 1 = 2p` forces `p = 1`, not prime.  Two or more factors: each `pᵢ + 1` is
even, so `4 ∣ σ(n)`, while `2·n ≡ 2 [MOD 4]` since `n` is odd. -/
theorem sum_divisors_prod_nth_ne_two_mul {s : Finset ℕ} (hs : ∀ i ∈ s, 1 ≤ i) :
    ∑ d ∈ (∏ i ∈ s, Nat.nth Nat.Prime i).divisors, d
      ≠ 2 * ∏ i ∈ s, Nat.nth Nat.Prime i := by
  rw [sum_divisors_prod_nth]
  intro h
  rcases Nat.lt_or_ge s.card 2 with hcard | hcard
  · interval_cases hc : s.card
    · rw [Finset.card_eq_zero] at hc
      subst hc
      simp at h
    · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hc
      have hp := (Nat.prime_nth_prime j).two_le
      simp only [Finset.prod_singleton] at h
      omega
  · -- ≥ 2 factors: 4 ∣ ∏ (pᵢ + 1) but 2·(odd) ≢ 0 [MOD 4]
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hcard
    have hoddj : Odd (Nat.nth Nat.Prime j) := by
      have := odd_prod_nth (s := {j}) (fun i hi => by
        simp only [Finset.mem_singleton] at hi; exact hi ▸ hs j hj)
      simpa using this
    have hoddk : Odd (Nat.nth Nat.Prime k) := by
      have := odd_prod_nth (s := {k}) (fun i hi => by
        simp only [Finset.mem_singleton] at hi; exact hi ▸ hs k hk)
      simpa using this
    have h4 : 4 ∣ ∏ i ∈ s, (Nat.nth Nat.Prime i + 1) := by
      have hsub : ({j, k} : Finset ℕ) ⊆ s := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hj
        · exact Finset.mem_singleton.mp hx ▸ hk
      have hpair : ∏ i ∈ ({j, k} : Finset ℕ), (Nat.nth Nat.Prime i + 1)
          = (Nat.nth Nat.Prime j + 1) * (Nat.nth Nat.Prime k + 1) :=
        Finset.prod_pair hjk
      have hdvd4 : 4 ∣ (Nat.nth Nat.Prime j + 1) * (Nat.nth Nat.Prime k + 1) := by
        obtain ⟨x, hx⟩ := hoddj
        obtain ⟨y, hy⟩ := hoddk
        exact ⟨(x + 1) * (y + 1), by rw [hx, hy]; ring⟩
      exact dvd_trans (hpair ▸ hdvd4)
        (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    rw [h] at h4
    obtain ⟨w, hw⟩ := odd_prod_nth hs
    omega

/-- **The crossing exists**: for every starting index `a` there is a `b` such
that the product of the consecutive primes `p_a ⋯ p_{b-1}` is abundant.  This
is the single analytic input, powered by the divergence of `∑ 1/p`
(`Nat.Primes.not_summable_one_div`): the partial sums of `1/pᵢ` over `[a, b)`
exceed `2`, so `σ(N)/N = ∏ (1 + 1/pᵢ) ≥ 1 + ∑ 1/pᵢ > 2` (Weierstrass). -/
theorem exists_crossing (a : ℕ) :
    ∃ b, 2 * ∏ i ∈ Finset.Ico a b, Nat.nth Nat.Prime i
      < ∑ d ∈ (∏ i ∈ Finset.Ico a b, Nat.nth Nat.Prime i).divisors, d := by
  -- Step 1: ∑ 1/pᵢ diverges (transport prime-reciprocal divergence along `nth`)
  have hnth : ¬ Summable (fun i : ℕ => (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)) := by
    intro hsum
    apply Nat.Primes.not_summable_one_div
    have e : ℕ ≃ Nat.Primes :=
      { toFun := fun i => ⟨Nat.nth Nat.Prime i, Nat.prime_nth_prime i⟩
        invFun := fun p => Nat.count Nat.Prime (p : ℕ)
        left_inv := fun i => Nat.count_nth_of_infinite Nat.infinite_setOf_prime i
        right_inv := fun p => Subtype.ext (Nat.nth_count p.2) }
    exact e.summable_iff.mp hsum
  have hnn : ∀ i, (0 : ℝ) ≤ 1 / (Nat.nth Nat.Prime i : ℝ) := fun i => by positivity
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp hnth
  -- Step 2: pick b with the tail sum over [a, b) exceeding 2
  obtain ⟨b, hb⟩ := (htend.eventually_ge_atTop
    ((∑ i ∈ Finset.range a, (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)) + 3)).exists
  have hab : a ≤ b := by
    by_contra hab
    push_neg at hab
    have hmono : ∑ i ∈ Finset.range b, (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)
        ≤ ∑ i ∈ Finset.range a, (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset.mpr hab.le) (fun i _ _ => hnn i)
    linarith
  have htail : (2 : ℝ) < ∑ i ∈ Finset.Ico a b, (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ) := by
    rw [Finset.sum_Ico_eq_sub _ hab]
    linarith
  -- Step 3: Weierstrass ∏(1 + xᵢ) ≥ 1 + ∑ xᵢ
  have hweier : ∀ (t : Finset ℕ),
      1 + ∑ i ∈ t, (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)
        ≤ ∏ i ∈ t, (1 + 1 / (Nat.nth Nat.Prime i : ℝ)) := by
    intro t
    induction t using Finset.cons_induction with
    | empty => simp
    | cons j t hjt ih =>
      rw [Finset.sum_cons, Finset.prod_cons]
      have hfj := hnn j
      have hsum : (0 : ℝ) ≤ ∑ i ∈ t, 1 / (Nat.nth Nat.Prime i : ℝ) :=
        Finset.sum_nonneg fun i _ => hnn i
      nlinarith [ih, mul_le_mul_of_nonneg_left ih
        (by linarith : (0 : ℝ) ≤ 1 + 1 / (Nat.nth Nat.Prime j : ℝ))]
  -- Step 4: convert the index product to σ-arithmetic and descend to ℕ
  refine ⟨b, ?_⟩
  rw [sum_divisors_prod_nth]
  have hposℝ : ∀ i, (0 : ℝ) < (Nat.nth Nat.Prime i : ℝ) := fun i => by
    exact_mod_cast (Nat.prime_nth_prime i).pos
  have hfactor : ∀ i ∈ Finset.Ico a b,
      (1 : ℝ) + 1 / (Nat.nth Nat.Prime i : ℝ)
        = ((Nat.nth Nat.Prime i : ℝ) + 1) / (Nat.nth Nat.Prime i : ℝ) := by
    intro i _
    rw [add_div, div_self (hposℝ i).ne']
  have hprodpos : (0 : ℝ) < ∏ i ∈ Finset.Ico a b, (Nat.nth Nat.Prime i : ℝ) :=
    Finset.prod_pos fun i _ => hposℝ i
  have hgt2 : (2 : ℝ) < (∏ i ∈ Finset.Ico a b, ((Nat.nth Nat.Prime i : ℝ) + 1))
      / ∏ i ∈ Finset.Ico a b, (Nat.nth Nat.Prime i : ℝ) := by
    rw [← Finset.prod_div_distrib]
    calc (2 : ℝ) < 1 + ∑ i ∈ Finset.Ico a b, (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ) := by
          linarith
      _ ≤ ∏ i ∈ Finset.Ico a b, (1 + 1 / (Nat.nth Nat.Prime i : ℝ)) := hweier _
      _ = ∏ i ∈ Finset.Ico a b,
            ((Nat.nth Nat.Prime i : ℝ) + 1) / (Nat.nth Nat.Prime i : ℝ) :=
          Finset.prod_congr rfl hfactor
  have hR : 2 * ∏ i ∈ Finset.Ico a b, (Nat.nth Nat.Prime i : ℝ)
      < ∏ i ∈ Finset.Ico a b, ((Nat.nth Nat.Prime i : ℝ) + 1) :=
    (lt_div_iff₀ hprodpos).mp hgt2
  exact_mod_cast hR

/-- The first index `b` at which the product of consecutive primes
`p_a ⋯ p_{b-1}` becomes abundant.  Noncomputable only through `Nat.nth`. -/
noncomputable def crossing (a : ℕ) : ℕ := Nat.find (exists_crossing a)

/-- **The odd primitive abundant witness for starting index `a`**: the product
of the consecutive primes `p_a, …, p_{crossing a − 1}`. -/
noncomputable def consecutivePrimeWitness (a : ℕ) : ℕ :=
  ∏ i ∈ Finset.Ico a (crossing a), Nat.nth Nat.Prime i

/-- The crossing lies strictly beyond the start: empty products are not
abundant (`σ(1) = 1`). -/
theorem lt_crossing (a : ℕ) : a < crossing a := by
  by_contra h
  push_neg at h
  have hspec := Nat.find_spec (exists_crossing a)
  rw [show crossing a = Nat.find (exists_crossing a) from rfl] at h
  rw [Finset.Ico_eq_empty (by omega : ¬ a < Nat.find (exists_crossing a))] at hspec
  simp [Nat.divisors_one] at hspec

/-- **Every maximal divisor `N / pᵢ` of the crossing product is deficient.**
For the omitted index `i = crossing − 1` this is exactly minimality of the
crossing (sharpened from `≤` to `<` by `sum_divisors_prod_nth_ne_two_mul`);
for smaller `i` the inequality only improves, because trading the omitted
prime `pᵢ` back in for `p_{crossing−1}` multiplies the σ-side by
`(p_c + 1)/(p_i + 1)` but the `2n`-side by `p_c/p_i ≥ (p_c+1)/(p_i+1)`. -/
theorem erase_prod_deficient {a : ℕ} (ha : 1 ≤ a) {i : ℕ}
    (hi : i ∈ Finset.Ico a (crossing a)) :
    (∏ j ∈ (Finset.Ico a (crossing a)).erase i, Nat.nth Nat.Prime j).Deficient := by
  rw [deficient_iff_sum_divisors, sum_divisors_prod_nth]
  obtain ⟨c, hc⟩ : ∃ c, crossing a = c + 1 :=
    ⟨crossing a - 1, by have := lt_crossing a; omega⟩
  have hac : a ≤ c := by have := lt_crossing a; omega
  -- predecessor is strictly deficient
  have hple : ¬ (2 * ∏ j ∈ Finset.Ico a c, Nat.nth Nat.Prime j
      < ∑ d ∈ (∏ j ∈ Finset.Ico a c, Nat.nth Nat.Prime j).divisors, d) :=
    Nat.find_min (exists_crossing a) (show c < crossing a by omega)
  have hpne := sum_divisors_prod_nth_ne_two_mul
    (s := Finset.Ico a c) (fun j hj => le_trans ha (Finset.mem_Ico.mp hj).1)
  rw [sum_divisors_prod_nth] at hple hpne
  have hpred : ∏ j ∈ Finset.Ico a c, (Nat.nth Nat.Prime j + 1)
      < 2 * ∏ j ∈ Finset.Ico a c, Nat.nth Nat.Prime j := by omega
  -- split on whether the omitted index is the top one
  rw [hc] at hi ⊢
  have hico : Finset.Ico a (c + 1) = insert c (Finset.Ico a c) :=
    Nat.Ico_succ_right_eq_insert_Ico hac
  rcases Finset.mem_Ico.mp hi with ⟨hai, hic1⟩
  rcases Nat.lt_or_ge i c with hilt | hige
  · -- i < c: erase i, keep the top prime p_c
    have herase : (Finset.Ico a (c + 1)).erase i
        = insert c ((Finset.Ico a c).erase i) := by
      rw [hico, Finset.erase_insert_of_ne (by omega : c ≠ i)]
    have hcnot : c ∉ (Finset.Ico a c).erase i := fun hmem =>
      absurd (Finset.mem_Ico.mp (Finset.mem_of_mem_erase hmem)).2 (lt_irrefl c)
    have himem : i ∈ Finset.Ico a c := Finset.mem_Ico.mpr ⟨hai, hilt⟩
    rw [herase, Finset.prod_insert hcnot, Finset.prod_insert hcnot]
    set A := ∏ j ∈ (Finset.Ico a c).erase i, (Nat.nth Nat.Prime j + 1) with hA
    set B := ∏ j ∈ (Finset.Ico a c).erase i, Nat.nth Nat.Prime j with hB
    set pi := Nat.nth Nat.Prime i with hpi
    set pc := Nat.nth Nat.Prime c with hpc
    -- hpred in split form: (pi + 1) * A < 2 * (pi * B)
    have hsplitσ : (pi + 1) * A = ∏ j ∈ Finset.Ico a c, (Nat.nth Nat.Prime j + 1) := by
      rw [hpi, hA]; exact Finset.mul_prod_erase _ _ himem
    have hsplitn : pi * B = ∏ j ∈ Finset.Ico a c, Nat.nth Nat.Prime j := by
      rw [hpi, hB]; exact Finset.mul_prod_erase _ _ himem
    have hpred' : (pi + 1) * A < 2 * (pi * B) := by
      rw [hsplitσ, hsplitn]; exact hpred
    have hpic : pi ≤ pc :=
      le_of_lt ((Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr hilt)
    -- goal: (pc + 1) * A < 2 * (pc * B)
    have hkey : pi * (pc + 1) ≤ pc * (pi + 1) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one, Nat.mul_comm pc pi]
      exact Nat.add_le_add_left hpic _
    refine Nat.lt_of_mul_lt_mul_left (a := pi + 1) ?_
    calc (pi + 1) * ((pc + 1) * A)
        = (pc + 1) * ((pi + 1) * A) := by ring
      _ < (pc + 1) * (2 * (pi * B)) :=
          mul_lt_mul_of_pos_left hpred' (by omega : 0 < pc + 1)
      _ = 2 * B * (pi * (pc + 1)) := by ring
      _ ≤ 2 * B * (pc * (pi + 1)) :=
          mul_le_mul_left' hkey (2 * B)
      _ = (pi + 1) * (2 * (pc * B)) := by ring
  · -- i = c: the erase IS the predecessor
    have hieq : i = c := by omega
    subst hieq
    have herase : (Finset.Ico a (i + 1)).erase i = Finset.Ico a i := by
      rw [hico, Finset.erase_insert (fun hmem =>
        absurd (Finset.mem_Ico.mp hmem).2 (lt_irrefl i))]
    rw [herase]
    exact hpred

/-- **The crossing product is odd primitive abundant** (for start `a ≥ 1`):
abundant by the crossing, odd because all its prime factors are odd, and every
proper divisor omits some prime `pᵢ`, hence divides the deficient maximal
divisor `N / pᵢ` and is deficient itself. -/
theorem consecutivePrimeWitness_mem {a : ℕ} (ha : 1 ≤ a) :
    consecutivePrimeWitness a ∈ OddPrimitiveAbundant := by
  have hodd : Odd (consecutivePrimeWitness a) :=
    odd_prod_nth fun i hi => le_trans ha (Finset.mem_Ico.mp hi).1
  refine ⟨hodd, ?_, ?_⟩
  · rw [Nat.abundant_iff_sum_divisors]
    exact Nat.find_spec (exists_crossing a)
  · intro d hd
    obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp hd
    have hNpos : 0 < consecutivePrimeWitness a := prod_nth_pos _
    have hdpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact absurd (Nat.eq_zero_of_zero_dvd hdvd) hNpos.ne'
      · exact h
    -- d omits some prime index i
    have homit : ∃ i ∈ Finset.Ico a (crossing a), ¬ Nat.nth Nat.Prime i ∣ d := by
      by_contra hall
      push_neg at hall
      have himg : ∏ p ∈ (Finset.Ico a (crossing a)).image (Nat.nth Nat.Prime), p
          = consecutivePrimeWitness a :=
        Finset.prod_image fun i _ j _ h =>
          Nat.nth_injective Nat.infinite_setOf_prime h
      have hNd : consecutivePrimeWitness a ∣ d := by
        rw [← himg]
        refine Finset.prod_primes_dvd d ?_ ?_
        · intro p hp
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
          exact (Nat.prime_nth_prime i).prime
        · intro p hp
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
          exact hall i hi
      exact absurd hdlt (not_lt.mpr (Nat.le_of_dvd hdpos hNd))
    obtain ⟨i, hi, hnd⟩ := homit
    -- d divides the deficient maximal divisor N / pᵢ
    have hsplit : Nat.nth Nat.Prime i
        * ∏ j ∈ (Finset.Ico a (crossing a)).erase i, Nat.nth Nat.Prime j
        = consecutivePrimeWitness a :=
      Finset.mul_prod_erase _ _ hi
    have hcop : Nat.Coprime d (Nat.nth Nat.Prime i) :=
      ((Nat.prime_nth_prime i).coprime_iff_not_dvd.mpr hnd).symm
    have hdM : d ∣ ∏ j ∈ (Finset.Ico a (crossing a)).erase i, Nat.nth Nat.Prime j := by
      refine hcop.dvd_of_dvd_mul_left ?_
      rw [hsplit]
      exact hdvd
    exact deficient_of_dvd (erase_prod_deficient ha hi) hdM hdpos.ne'

/-- **Distinct starts give distinct witnesses**: `p_a` divides the witness for
`a` but no witness for a later start (whose prime factors are all larger), and
`nth` is injective, so the family `k ↦ consecutivePrimeWitness (k + 1)` is
injective. -/
theorem consecutivePrimeWitness_injective :
    Function.Injective fun k : ℕ => consecutivePrimeWitness (k + 1) := by
  have key : ∀ {k l : ℕ}, k < l →
      consecutivePrimeWitness (k + 1) ≠ consecutivePrimeWitness (l + 1) := by
    intro k l hkl heq
    have hmem : k + 1 ∈ Finset.Ico (k + 1) (crossing (k + 1)) :=
      Finset.mem_Ico.mpr ⟨le_refl _, lt_crossing _⟩
    have hdvd : Nat.nth Nat.Prime (k + 1) ∣ consecutivePrimeWitness (k + 1) :=
      Finset.dvd_prod_of_mem _ hmem
    rw [heq] at hdvd
    obtain ⟨i, hi, hdvd'⟩ :=
      ((Nat.prime_nth_prime (k + 1)).prime.dvd_finsetProd_iff _).mp hdvd
    have heqp : Nat.nth Nat.Prime (k + 1) = Nat.nth Nat.Prime i :=
      (Nat.prime_dvd_prime_iff_eq (Nat.prime_nth_prime (k + 1))
        (Nat.prime_nth_prime i)).mp hdvd'
    have : k + 1 = i := Nat.nth_injective Nat.infinite_setOf_prime heqp
    have := (Finset.mem_Ico.mp hi).1
    omega
  intro k l h
  rcases lt_trichotomy k l with hlt | heq | hgt
  · exact absurd h (key hlt)
  · exact heq
  · exact absurd h.symm (key hgt)

/-- **MAIN RESULT — there are infinitely many odd primitive abundant numbers**
(OEIS A006038 is infinite).  This settles the target question of this entry
positively: the injective family `k ↦ p_{k+1} p_{k+2} ⋯ p_{crossing−1}` of
first-crossing consecutive-prime products consists entirely of odd primitive
abundant numbers. -/
theorem oddPrimitiveAbundant_infinite : OddPrimitiveAbundant.Infinite :=
  Set.infinite_of_injective_forall_mem consecutivePrimeWitness_injective
    fun k => consecutivePrimeWitness_mem (Nat.le_add_left 1 k)

/-- The headline restated without the named set: the odd primitive abundant
numbers — odd, abundant, every proper divisor deficient — form an infinite
set. -/
theorem infinitely_many_odd_primitive_abundant :
    {n : ℕ | Odd n ∧ n.Abundant ∧ ∀ d ∈ n.properDivisors, d.Deficient}.Infinite :=
  oddPrimitiveAbundant_infinite

end AbundantNumberOQ03OQ03
