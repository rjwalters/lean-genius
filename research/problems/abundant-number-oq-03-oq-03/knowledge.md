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
