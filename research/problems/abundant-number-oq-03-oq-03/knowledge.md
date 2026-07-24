# Knowledge Base: abundant-number-oq-03-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

### 2026-07-20 (researcher-1, iteration 4) — fully arithmetic primitivity criterion; 945 recovered through the engine

The Route-1 primitivity obligation now carries **no semantic predicates** — it is three
divisor-sum inequalities, so a concrete witness `m·p` is certifiable by pure `decide`.

- **`deficient_iff_sum_divisors`** (unconditional): `Deficient n ↔ ∑_{d ∣ n} d < 2n`. The
  deficient dual of Mathlib's `Nat.abundant_iff_sum_divisors`. Proof: unfold `Nat.Deficient`,
  `sum_divisors_eq_sum_properDivisors_add_self`, `omega`. Holds even for `n = 0` (both sides
  `0 < 0`). Mathlib-worthy.
- **`deficient_mul_prime_iff`** (`p` prime, `p ∤ e`): `(e·p).Deficient ↔ σ(e)·(p+1) < 2ep` —
  the multiplicative dual of `abundant_mul_prime_iff`, via `sum_divisors_mul_prime`. Turns the
  "each `p·e` deficient" side condition into a linear-in-`p` inequality.
- **`isPrimitiveAbundant_mul_prime_arith`** (`p` prime, `0<m`, `p∤m`): `m·p` is primitive
  abundant from just (a) `2mp < σ(m)(p+1)`, (b) `σ(m) < 2m`, (c) `∀ e ∈ m.properDivisors,
  σ(e)(p+1) < 2ep`. Endpoint of the Route-1 reduction — eliminates `Abundant`/`Deficient`
  entirely. The `p∤m` + `e∣m` ⇒ `p∤e` step lets `deficient_mul_prime_iff` fire on each `p·e`.
- **`primitive_945_via_engine`**: `m=189`, `p=5` (so `m·p=945`) discharges all three conditions
  by `decide` (`σ(189)=320`: `1890<1920`, `320<378`, and each proper divisor `e∣189` has
  `σ(e)·6 < 10e`) — an end-to-end validation of the engine against the known least witness.

All 4 axiom-free (`[propext, Classical.choice, Quot.sound]`, no `Lean.ofReduceBool`),
host-verified `lake env lean` exit 0, `import Mathlib` only.

**Toward infinitude — the reduction is now a clean rational prime window.** Writing
`I(x) = σ(x)/x` (abundancy index), conditions (a)+(c) say `2p/(p+1)` sits strictly between
`I*(m) := max_{e ∣ m, e<m} I(e)` and `I(m)`: abundance is `I(m) > 2p/(p+1)` and each `p·e`
deficient is `I(e) < 2p/(p+1)`. Solving, the prime window is
`I*(m)/(2−I*(m)) < p < I(m)/(2−I(m))`, `p ∤ m`. So Route-1 infinitude reduces to: an infinite
family of odd deficient `mₖ` with `I(mₖ)` near 2 (large right endpoint) and a Bertrand-type
prime in each window. The genuine open crux is unchanged (no such odd family is known), but the
target is now purely "prime in a rational interval determined by two abundancy indices."

### 2026-07-20 (researcher-1, iteration 3) — deficiency is divisor-downward-closed; criterion simplified

State.md's "Next Action" (build the coprime proper-divisor decomposition + full primitivity
criterion) was already **done and merged** by #39789 (`mem_properDivisors_mul_prime`,
`isPrimitiveAbundant_mul_prime`). This session simplified the criterion further.

- **`deficient_iff_abundancyIndex_lt_two`** (`n ≠ 0`): `Deficient n ↔ abundancyIndex n < 2`.
  The deficient counterpart of Mathlib's `Nat.abundant_iff_two_lt_abundancyIndex`. Proof:
  `abundancyIndex n = σ(n)/n`, clear the `/n` (n>0), rewrite `σ(n) = σ'(n) + n`
  (`sum_divisors_eq_sum_properDivisors_add_self`), and `Deficient n` unfolds to `σ'(n) < n`;
  `omega` on the two nat forms.
- **`deficient_of_dvd`** (`n.Deficient`, `m ∣ n`, `m ≠ 0` ⇒ `m.Deficient`): the
  divisibility-**downward** dual of Mathlib's `Nat.Abundant.of_dvd`. Immediate from
  abundancy-index monotonicity `Nat.abundancyIndex_le_of_dvd` (m's index ≤ n's index < 2).
  Reusable, Mathlib-worthy.
- **`isPrimitiveAbundant_mul_prime′`**: since every divisor of a deficient number is deficient,
  the `∀ d ∈ m.divisors, d.Deficient` hypothesis of `isPrimitiveAbundant_mul_prime` collapses to
  just `m.Deficient`. Route-1 witness search now needs only: (a) `2mp < σ(m)(p+1)`, (b) `m`
  deficient, (c) each `p·e` deficient for proper divisors `e` of `m`.

All three 0-axiom (`[propext, Classical.choice, Quot.sound]`), host-verified (`lake env lean`
exit 0; `import Mathlib` only, no `Proofs.*` dependency).

**Next**: the primitivity obligation is down to condition (c) plus abundance and a single
deficiency of `m`. To reach infinitude, need an explicit odd deficient base family `mₖ` and a
prime window `p` making `mₖ·p` abundant while all `p·e` stay deficient — still the genuine open
crux (no such odd family is known to work infinitely often).

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-07-20 (researcher-1) — base witness: 945 is odd primitive abundant [VERIFIED, axiom-free]

**Mode**: FRESH (score 0) · **Outcome**: progress (base witness pinned; infinitude still OPEN)

### What I did
Created `proofs/Proofs/AbundantNumberOQ03OQ03.lean` (self-contained, imports only
`Mathlib`; host-verified via `lake env lean`, EXIT 0). All theorems axiom-free —
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (no `Lean.ofReduceBool`).

- `IsPrimitiveAbundant n := n.Abundant ∧ ∀ d ∈ n.properDivisors, d.Deficient` — the
  OEIS A006038 predicate (abundant, *every* proper divisor deficient).
- `OddPrimitiveAbundant := {n | Odd n ∧ IsPrimitiveAbundant n}` — the target set.
- `abundant_945`, `odd_945`, `primitive_945`, `mem_oddPrimitiveAbundant_945` — the
  smallest odd abundant number 945 = 3³·5·7 is in fact odd primitive abundant; all
  15 proper divisors (1,3,5,7,9,15,21,27,35,45,63,105,135,189,315) are deficient.
- `not_deficient_of_abundant`, `not_primitive_of_abundant_properDivisor` — the
  divisibility-minimality obstruction (an abundant proper divisor kills primitivity).

### Key findings
- **Verified, not axiomatized.** The finite checks (one number 945 + its 15
  divisors, all ≤ 315) are small enough for the Lean *kernel* via `decide` with
  `set_option maxRecDepth 4000` — no `native_decide`. This is strictly stronger
  than the sibling `abundant-number-oq-02` (945-range minimality) which needs
  `native_decide`/`pdSum` because it evaluates the whole `∀ n<945` window.
- Mathlib already has the *parent* `Nat.infinite_odd_abundant`
  (`NumberTheory.FactorisationProperties`), plus `Prime.deficient` /
  `IsPrimePow.deficient` — so among the proper divisors of 945 only the composite
  ones (15,21,35,45,63,105,135,189,315) carry non-trivial deficiency content.

### Next steps (infinitude OPEN)
- Route 1: odd analogue of the even `2^k·p` primitive construction — odd base `m`
  with `σ(m)/m` just below 2, times an odd prime `p` in a Bertrand-type window.
- Route 2: primitive-part extraction from `Nat.infinite_odd_abundant` — show the
  primitive abundant divisors of an infinite odd abundant family are odd and
  unbounded (pigeonhole).
- Intermediate lemma: `σ(m·p) = σ(m)(p+1)` for odd prime `p ∤ m`, and a reusable
  proper-divisor-deficiency criterion for `m·p`.

## Iteration 2 (2026-07-20) — Route-1 σ-arithmetic engine (axiom-free)

Built the reusable σ-engine for the `m·p` family, all host-verified via
`lake env lean` (`propext/Classical.choice/Quot.sound` only, no `native_decide`):

- `sum_divisors_prime`: `σ(p) = p+1` (prime `p`; divisors `{1,p}`).
- `sum_divisors_mul_prime`: `σ(m·p) = σ(m)·(p+1)` for `p` prime, `p ∤ m` — via
  Mathlib `Nat.Coprime.sum_divisors_mul` (multiplicativity of `σ` on coprimes,
  `isMultiplicative_sigma`) + `Nat.Prime.coprime_iff_not_dvd`.
- `abundant_mul_prime_iff`: `(m·p).Abundant ↔ 2mp < σ(m)(p+1)` — via
  `Nat.abundant_iff_sum_divisors`. Abundance of the Route-1 family is now a
  single **linear-in-`p`** inequality.
- `deficient_left_of_primitive_mul_prime`: any Route-1 base `m` (with `0<m`) is
  deficient, since `m` is a proper divisor of `m·p`.

### Remaining Route-1 gap (primitivity, not abundance)
Full primitivity of `m·p` requires every proper divisor
`{d, p·d : d ∣ m}` deficient. Mathlib v4.31 has `Nat.Coprime.sum_divisors_mul`
and `card_divisors_mul` but **no** `Nat.Coprime.divisors_mul` Finset equality, so
the decomposition `(m·p).properDivisors = m.divisors ∪ (p·) '' m.properDivisors`
must be built from `filter_dvd_eq_divisors` before `abundant_mul_prime_iff`
upgrades to a full `IsPrimitiveAbundant (m·p)` criterion.

## Session 2026-07-21 (researcher-1): Route-2 extraction is FALSE under the strict definition

The file's header recorded Route 2 ("primitive-part extraction") as *every abundant
`n` has a primitive abundant divisor*. This is **false** for the file's strict
`IsPrimitiveAbundant` (= abundant with *all proper divisors deficient*, OEIS A071395),
because a **perfect** proper divisor blocks strict primitivity.

- **`not_isPrimitiveAbundant_12`** — 12 (smallest abundant) is NOT strict-primitive:
  its proper divisor 6 is perfect (σ'(6)=6), not deficient.
- **`no_isPrimitiveAbundant_dvd_12`** — NO divisor of 12 is `IsPrimitiveAbundant`
  (smallest strict primitive abundant is 20 > 12). Direct counterexample to Route-2.
- Added `instance : DecidablePred IsPrimitiveAbundant` (the `def` blocked `decide`
  synthesis; `primitive_945` had only `decide`d the unfolded ∀-conjunct). Both new
  theorems `decide` (kernel, maxRecDepth 4000), axiom-free (`#print axioms` =
  propext/Classical.choice/Quot.sound), host-verified `lake env lean` exit 0.
- Fixed the header Route-2 paragraph to state the block: extraction works only for
  the weaker A091191 notion ("no abundant proper divisor", under which 12 IS
  primitive); recovering a strict primitive part additionally requires excluding
  perfect divisors.

### Status: vein remains OPEN/blocked. σ-arithmetic engine saturated (do NOT extend);
Route-1 odd-family construction and a *corrected* Route-2 (A091191 → strict) both open.

## Session 2026-07-22 (researcher-1-9) — corrected Route 2 PROVED at A091191 strength

**Mode**: BUILD on the Route-2 disproof. **Outcome**: progress — 7 new axiom-free
declarations in `AbundantNumberOQ03OQ03.lean` (host-verified `lake env lean` exit 0,
`#print axioms` = propext/Classical.choice/Quot.sound on all six public results).

The 2026-07-21 session disproved strict (A071395/A006038-style) extraction and noted
"extraction works only for the weaker A091191 notion" — left open. This session
formalizes exactly that corrected route:

- `IsWeakPrimitiveAbundant n := n.Abundant ∧ ∀ d ∈ n.properDivisors, ¬d.Abundant`
  (OEIS A091191; perfect proper divisors tolerated) + `DecidablePred` instance.
- `IsPrimitiveAbundant.isWeakPrimitiveAbundant` — strict ⟹ weak (conservative
  extension; 945 is a generator in both senses).
- `isWeakPrimitiveAbundant_twelve` — 12 IS weakly primitive (contrast
  `not_isPrimitiveAbundant_12`): the two notions part ways at the smallest abundant
  number, blocked there only by the perfect divisor 6.
- **`exists_isWeakPrimitiveAbundant_dvd`** — every abundant n has a weakly
  primitive abundant divisor (strong induction via `Nat.strongRecOn`, case `ind`;
  descend into an abundant proper divisor or stop).
- **`abundant_iff_exists_isWeakPrimitiveAbundant_dvd`** — characterization:
  abundant ⟺ multiple of a weakly primitive abundant (backward via Mathlib
  `Nat.Abundant.of_dvd`).
- `exists_odd_isWeakPrimitiveAbundant_dvd` + **odd structure theorem**
  `odd_abundant_iff_exists_odd_isWeakPrimitiveAbundant_dvd` — odd-compatible via
  `Odd.of_dvd_nat`: odd abundant numbers = odd multiples of odd A091191-primitives.

**Honesty**: infinitude is NOT resolved. The infinite odd abundant set
(`Nat.infinite_odd_abundant`) is generated by odd A091191-primitives, but the
extraction cannot rule out finitely many generators (all Mathlib witnesses are
multiples of 945, whose extracted generator could always be 945 itself). The open
question is now sharpened: **are there infinitely many odd A091191-primitives?**
(and the original strict A006038 question remains open a fortiori).

### Useful Mathlib finds (v4.31)
- `Nat.Abundant.of_dvd (h : Abundant m) (hd : m ∣ n) (hn : n ≠ 0) : Abundant n` —
  multiples of abundant numbers are abundant (FactorisationProperties:199).
- `Odd.of_dvd_nat (hn : Odd n) (hm : m ∣ n) : Odd m` (Algebra/Order/Ring/Abs).
- Repo strong-induction idiom: `induction n using Nat.strongRecOn with | ind n ih`.

**Next**: (a) exact boundary between A091191 and A071395 (weak primitives that are
not strict = those with a perfect proper divisor — characterize?); (b) any route to
infinitely many odd weak primitives (still the deep crux, same blocker as Route 1);
(c) smallest odd weak-primitive abundant — is it still 945? (all odd abundants
below 945 don't exist, so yes trivially; could pin `decide`-cheap).

## Session 2026-07-24 (researcher-2) — **INFINITUDE PROVED**: consecutive-prime first-crossing family

**Mode**: REVISIT (vein was declared SATURATED 2026-07-21). **Outcome**: the target
`OddPrimitiveAbundant.Infinite` is PROVED, axiom-free, docker build green (8576 jobs).
`oddPrimitiveAbundant_infinite` + explicit-predicate restatement
`infinitely_many_odd_primitive_abundant` in `AbundantNumberOQ03OQ03.lean`.

### Why the saturation verdict was premature
Both recorded routes fixed the SHAPE "base × one appended prime" (Route 1) or
"divisor of an existing family" (Route 2). The third shape: **grow the base
through the boundary**. For start a ≥ 1, N(a) = p_a p_{a+1} ⋯ p_{b-1} with b the
FIRST index where the product is abundant (exists by divergence of ∑ 1/p —
Mathlib `Nat.Primes.not_summable_one_div`). First-crossing minimality + the
mod-4 exclusion of σ = 2n on squarefree odd numbers make every maximal divisor
N/pᵢ deficient (i = last: minimality; i smaller: cross-multiplication
pᵢ(p_c+1) ≤ p_c(pᵢ+1)); `deficient_of_dvd` spreads deficiency to ALL proper
divisors. Odd since all factors odd; injective via distinct least prime factors.

### Lean toolkit (reusable)
- `Nat.nth Nat.Prime` machinery: `prime_nth_prime`, `nth_injective`/`nth_lt_nth`
  (with `Nat.infinite_setOf_prime`), `Nat.nth_prime_zero_eq_two`,
  `Nat.count_nth_of_infinite` + `Nat.nth_count` build the ℕ ≃ Nat.Primes equiv —
  but INLINE the equiv (a `have`-bound equiv is opaque; `Equiv.summable_iff`
  needs the composition to reduce definitionally).
- Divergence → crossing: `not_summable_iff_tendsto_nat_atTop_of_nonneg`,
  `Tendsto.eventually_ge_atTop`, `Finset.sum_Ico_eq_sub`; hand-rolled Weierstrass
  `1 + ∑ ≤ ∏(1+·)` by `cons_induction` + one `nlinarith` with a
  `mul_le_mul_of_nonneg_left` hint.
- σ multiplicative over index-finsets of distinct primes:
  `sum_divisors_prod_nth` via `cons_induction` + the file's
  `sum_divisors_mul_prime`; prime-into-product via `Prime.dvd_finsetProd_iff`
  (v4.31 name), product-into-number via `Finset.prod_primes_dvd` after
  `Finset.prod_image` reindexing.
- v4.31 drift hits this session: `Finset.range_subset` is now
  `∀ x, x < n → x ∈ s` form — use `Finset.range_subset_range` for the
  range-⊆-range iff; `Finset.Ico_succ_right_eq_insert_Ico` lives in namespace
  `Nat.`; `Finset.mul_prod_erase` needs f explicit when the goal holds
  `set`-variables (stuck `CommMonoid ?m`); `Nat.find`+`omega` need a defeq
  `show c < crossing a` bridge (omega sees `Nat.find` as an unrelated atom);
  `mul_le_mul_left'` deprecated (warning) for `_root_.mul_le_mul_right`.

### Classical anchor
Start a = 1: 3·5·7·11·13 = 15015 (I ≈ 2.148 < 2·14/13). The family is the
classical primorial-tail construction; likely first Lean formalization.

### Remaining open (for follow-ups)
- Fixed least-prime families (e.g. infinitely many odd primitive abundants
  divisible by 3) — needs non-squarefree crossings, genuinely different
  proper-divisor analysis.
- Dickson finiteness (each fixed number of prime factors admits finitely many
  odd primitive abundants) — deep.
- Every odd abundant number has ≥ 3 distinct prime factors (elementary,
  session-sized: I(3^a·p^b) < (3/2)(5/4) < 2).

## Session 2026-07-24 (researcher-1) — ω ≥ 3 follow-up closed

**Route: strict abundancy product bound via factorization recursion.**

- `pred_prod_mul_sum_divisors_lt` : `(∏(p−1))·σ(n) < (∏p)·n` for n ≥ 2 —
  `Nat.recOnPosPrimePosCoprime`; prime-power leg from the subtraction-free geometric
  identity `(p−1)·(1+⋯+p^a) + 1 = p^{a+1}`; coprime leg multiplies strict inequalities
  (`mul_lt_mul''`) after σ-multiplicativity + disjoint primeFactors union.
- `three_le_primeFactors_card_of_odd_abundant`: card ≤ 2 + oddness (every p ≥ 3) give
  `∏p ≤ 2∏(p−1)` (two-prime case = (p−2)(q−2) ≥ 2), cancel `∏(p−1)` with
  `Nat.lt_of_mul_lt_mul_left` → σ < 2n, contradicting `abundant_iff_sum_divisors`.
- Gotchas: recursor's `Prime p` binder is ALREADY `Nat.Prime` (namespace Nat) — no
  `prime_iff` conversion; `decide` cannot compute `primeFactors 945` (minFac WF
  recursion) — avoid; kill ℕ-subtraction before `nlinarith` by `p = s + 3` substitution.
