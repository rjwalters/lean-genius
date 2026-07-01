# Problem: Idempotents of ℤ/mᵏ — Counting, Complementation, and the Boolean Algebra of Rank ω(m)

**Slug**: automorphic-number-oq-01-oq-02-oq-01
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent entry pins down the idempotents of `ZMod (10 ^ k)` — the automorphic residues
`n² ≡ n (mod 10^k)` — proving there are exactly four and that they split into two
complementary pairs `{0, 1}` and `{…5, …6}`. This problem removes the base `10` entirely
and describes the idempotent structure of `ZMod (m ^ k)` for **arbitrary** `m ≥ 2`.

Let `m ≥ 2` and `k ≥ 1`. The claim is that the number of idempotents of the ring
`ZMod (m ^ k)` depends only on the number of **distinct primes** of `m` (not on `k`):

$$
\#\{\, e \in \mathbb{Z}/m^k \mathbb{Z} : e^2 = e \,\} \;=\; 2^{\omega(m)},
\qquad \omega(m) = \#\{\text{distinct primes dividing } m\}.
$$

Concretely, the target Lean statement is:

```lean
theorem card_idempotents_eq_two_pow_omega (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) :
    Fintype.card {e : ZMod (m ^ k) // IsIdempotentElem e}
      = 2 ^ m.primeFactors.card
```

where `m.primeFactors.card = ω(m)` (Mathlib's `ArithmeticFunction.cardDistinctFactors`,
notation `ω`, satisfies `ω m = m.primeFactorsList.dedup.length = m.primeFactors.card`).

Two structural refinements accompany the count:

1. **Complementation involution (primary secondary goal).** The map `e ↦ 1 - e` sends
   idempotents to idempotents (`IsIdempotentElem.one_sub`), is an involution
   (`1 - (1 - e) = e`), and pairs the `2^ω(m)` idempotents by orthogonal complementation
   `e ↔ 1 - e` with `e + (1 - e) = 1` and `e · (1 - e) = 0`:

   ```lean
   theorem compl_involutive (m k : ℕ) :
       Function.Involutive
         (fun e : {e : ZMod (m ^ k) // IsIdempotentElem e} => eᶜ)
   ```

   (Mathlib already provides `HasCompl {a // IsIdempotentElem a}` with `↑aᶜ = 1 - ↑a` and
   `compl_compl`, so this refinement is largely a repackaging.)

2. **Boolean algebra of rank ω(m) (stretch goal).** The idempotents form a Boolean
   algebra under meet `a ∧ b := a · b`, join `a ∨ b := a + b − a·b`, and complement
   `¬a := 1 − a`; as a Boolean algebra it is isomorphic to the power set
   `𝒫(primeFactors m) ≅ (Bool)^{ω(m)}`, hence has rank `ω(m)` and `2^{ω(m)}` elements.

### Plain Language

An "automorphic" number is one whose square ends in the same digits as itself
(`76² = 5776`). Working base `10`, these are exactly the residues `e` mod `10^k` with
`e² = e` — the idempotents of the ring `ℤ/10^k`. There are always four of them, and the
parent entry showed they come in two complementary pairs. But `10 = 2·5` has two prime
factors, and *that* is the real reason there are `4 = 2²` of them. Replace `10` by any
`m`: the number of idempotents of `ℤ/mᵏ` is `2` raised to the number of *distinct primes*
of `m`. So `ℤ/12ᵏ` (with `12 = 2²·3`, two primes) also has `4` idempotents, `ℤ/30ᵏ`
(`30 = 2·3·5`, three primes) has `8`, and `ℤ/pᵏ` for a prime power has only the boring two
(`0` and `1`). The exponent `k` never matters. Moreover these idempotents form a Boolean
algebra — a "power set in disguise" — of the set of primes of `m`, and the pairing
`e ↔ 1 − e` is exactly set-complementation.

### Why This Matters

This is the *correct* level of generality for the automorphic-number phenomenon: the count
`2^ω(m)` and the complementary-pairing structure are consequences of the Chinese Remainder
Theorem and the fact that a finite local ring has only the two trivial idempotents, and
have nothing to do with the specific base `10`. Formalizing it converts the parent's
concrete `{0, 1, …5, …6}` computation into the structural statement it is a shadow of, and
exhibits the idempotents of `ZMod (m^k)` as the Boolean algebra `𝒫(primeFactors m)`. It
also exercises a reusable pattern — decompose a `ZMod` via CRT into a product of local
rings, then count/structure a ring-theoretic invariant factor by factor — that recurs
throughout elementary number theory (units, nilpotents, zero-divisors, idempotents).

## Known Results

### What's Already Proven

- **Complementary pairing mod 10^k** (`0` axioms) — gallery parent
  `automorphic-number-oq-01-oq-02`: the four idempotents of `ZMod (10^k)` are exactly
  `{0, 1, a, 1-a}`, orthogonal complements, with last-digit uniqueness. The `m = 10`
  case of this problem, done by hand.
- **The count is 2^ω(n)** — gallery entry `automorphic-number-oq-01` (first follow-up),
  which already frames the mod-`10^k` count `4` as `2^ω(10) = 2²`.
- **Idempotent algebra in a commutative ring** — Mathlib `Mathlib.Algebra.Ring.Idempotent`:
  `IsIdempotentElem.one_sub`, `one_sub_iff`, `mul_one_sub_self` (`a·(1-a)=0`),
  `HasCompl {a // IsIdempotentElem a}` with `coe_compl : ↑aᶜ = 1 - ↑a`, `compl_compl`,
  `zero_compl`, `one_compl`, and the Boolean-operation lemma `add_sub_mul`
  (`IsIdempotentElem (a + b - a*b)`).
- **CRT for ZMod** — `ZMod.chineseRemainder : m.Coprime n → ZMod (m*n) ≃+* ZMod m × ZMod n`.
- **Complete orthogonal idempotents and the product decomposition** —
  `Mathlib.RingTheory.Idempotents`: `CompleteOrthogonalIdempotents`, `bijective_pi`, and
  `pair_iffₛ : CompleteOrthogonalIdempotents ![x, y] ↔ x*y = 0 ∧ x + y = 1`.
- **ω is additive on coprime products** — `ArithmeticFunction.cardDistinctFactors_mul`,
  `cardDistinctFactors_apply_prime_pow (hp : p.Prime) (hk : k ≠ 0) : ω (p^k) = 1`.

### What's Still Open

- No Lean statement of `#{e : ZMod (m^k) // e² = e} = 2^ω(m)` for general `m`.
- No formal identification of the idempotents of `ZMod (m^k)` with subsets of
  `primeFactors m`, nor of the Boolean-algebra isomorphism to `𝒫(primeFactors m)`.
- No general "local ring / prime-power `ZMod` has only trivial idempotents" bridge wired
  to the count (the parent proves this only implicitly for `10^k` via its `4`-count).

### Our Goal

Prove `card_idempotents_eq_two_pow_omega` with `0` axioms: the idempotent count of
`ZMod (m^k)` is `2^ω(m)`, independent of `k`. Then upgrade to the complementation
involution `e ↦ 1 - e` (largely a repackaging of Mathlib's `HasCompl`/`compl_compl`), and,
as a stretch goal, the full Boolean-algebra isomorphism with `𝒫(primeFactors m)`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| automorphic-number-oq-01-oq-02 | Direct parent: the `m = 10` complementary-pairing case, done concretely | `IsNilpotent`, tripotent identity, `Finset.card`, `decide` |
| automorphic-number-oq-01 | First follow-up: frames the mod-`10^k` count as `2^ω(10)` | CRT count, `Nat.factorization` |
| automorphic-number | Base entry: automorphic numbers `n² ≡ n (mod 10^k)` as idempotents | `ZMod`, idempotency |

## Initial Thoughts

### Potential Approaches

1. **Approach A — CRT into local factors, count idempotents in the product (recommended).**
   Write `m^k = ∏_{p ∈ primeFactors m} p^{k·v_p(m)}`; the factors are pairwise coprime, so
   iterating `ZMod.chineseRemainder` gives a ring isomorphism
   `ZMod (m^k) ≃+* ∏_{p ∈ primeFactors m} ZMod (p^{k·v_p(m)})`. Idempotents transport
   across a ring isomorphism, and an idempotent of a product ring is exactly a tuple of
   idempotents of the factors (`IsIdempotentElem` in `R × S` ↔ a pair of idempotents —
   provable directly from `Prod.ext` / componentwise multiplication). Each factor
   `ZMod (p^a)` (with `a ≥ 1`) is a **local ring**, so its only idempotents are `0` and
   `1`. Hence idempotents of `ZMod (m^k)` correspond bijectively to functions
   `primeFactors m → {0,1}`, i.e. to `Finset.powerset (primeFactors m)`, giving the count
   `2^{ω(m)}` and, simultaneously, the Boolean structure and the `e ↦ 1-e` = set-complement
   pairing.
   - Why it might work: every ingredient exists in Mathlib — `ZMod.chineseRemainder`,
     `Fintype.card_congr` for the idempotent-subtype equivalence, `Finset.card_powerset`,
     and `cardDistinctFactors_apply_prime_pow`.
   - Risk: the CRT bookkeeping is over a `Finset` (`Finset.prod`), so the product-ring
     decomposition is an iterated / dependent product `∀ p ∈ s, ZMod (…)`; managing the
     coprimality side conditions and the dependent `Fintype.card` of the idempotent
     subtype of a `Π`-type is the main labor.

2. **Approach B — Prove the two-idempotent lemma for `ZMod (p^a)` first, then induct on
   `primeFactors m`.**
   Establish `Fintype.card {e : ZMod (p^a) // IsIdempotentElem e} = 2` for prime `p`,
   `a ≥ 1` (local ring), then peel one prime at a time using
   `ZMod.chineseRemainder` and the product rule
   `card_idem(R × S) = card_idem(R) · card_idem(S)`, accumulating the factor `2` per prime.
   `cardDistinctFactors_mul` gives `ω(m·m') = ω(m)+ω(m')` on coprime pieces, matching the
   doubling.
   - Why it might work: reduces the whole problem to a clean single-prime lemma plus a
     coprime-multiplicativity induction; avoids a global dependent product.
   - Risk: setting up the coprime factorization `m = ∏ p^{v_p(m)}` and threading the
     induction over `Finset` still needs care; the `Fintype.card` product lemma for the
     idempotent subtype of `R × S` must be proved from scratch.

### Key Difficulties

- **`ZMod (p^a)` has exactly two idempotents.** This needs a "local ring / no nontrivial
  idempotents" argument. Two routes: (i) `ZMod (p^a)` is local (`IsLocalRing`), and a
  local ring has only trivial idempotents; or (ii) reuse the parent's engine —
  the maximal ideal `(p)` is nil, two idempotents with nilpotent difference coincide, and
  modulo `p` the ring is the field `ZMod p` with only `0, 1`. A clean Lean lemma of the
  form `IsIdempotentElem e → e = 0 ∨ e = 1` for `ZMod (p^a)` is the crux.
- **Product-ring idempotents.** `IsIdempotentElem (x, y) ↔ IsIdempotentElem x ∧
  IsIdempotentElem y`, and the corresponding `Fintype.card` factorization
  `card {e : R×S // IsIdempotentElem e} = card{·:R//·} · card{·:S//·}`. Straightforward but
  must be built (via `Equiv` to a sigma/product of subtypes), then iterated over a `Finset`.
- **CRT indexing over `primeFactors`.** Assembling `ZMod (m^k) ≃+* Π p ∈ primeFactors m,
  ZMod (p^{k·v_p(m)})` from binary `ZMod.chineseRemainder` requires an induction on the
  prime factorization with pairwise-coprimality obligations (`Nat.Coprime.pow`,
  `Nat.coprime`-of-distinct-primes facts).
- **`k` must genuinely drop out.** The exponent `k·v_p(m) ≥ 1` keeps each factor a
  nontrivial local ring with exactly two idempotents; the count `2` per prime is
  independent of that exponent, which is why `k` never appears in `2^ω(m)` — this needs to
  be visible in the proof, not accidental.

### What Would a Proof Need?

- Key lemma 1: `∀ p a, p.Prime → 1 ≤ a → Fintype.card {e : ZMod (p^a) // IsIdempotentElem e}
  = 2` (local / prime-power ring has only trivial idempotents).
- Key lemma 2: idempotent-subtype cardinality is multiplicative across a ring product /
  `ZMod.chineseRemainder`, i.e. `card_idem (ZMod (m*n)) = card_idem (ZMod m) · card_idem
  (ZMod n)` for `m.Coprime n`.
- Key lemma 3: `m = ∏ p ∈ primeFactors m, p^{v_p(m)}` with pairwise coprime factors
  (`Nat.factorization` / `Nat.prod_primeFactors`), lifted to the `k`-th power.
- Assembly: fold lemmas 1–3 to get `2^{ω(m)}` via `Finset.card_powerset` /
  `cardDistinctFactors_mul`, then attach the `e ↦ 1-e` involution (`IsIdempotentElem.one_sub`,
  `compl_compl`) and, for the stretch goal, the Boolean-algebra isomorphism to
  `𝒫(primeFactors m)` using `add_sub_mul` for the join.

## Tractability Assessment

**Difficulty**: Moderate

**Justification**:
- The **count `2^ω(m)` is Moderate**: all the Mathlib pieces exist
  (`ZMod.chineseRemainder`, `Fintype.card_congr`, `Finset.card_powerset`,
  `cardDistinctFactors_apply_prime_pow` / `_mul`), and the parent already demonstrates the
  local-ring idempotent-uniqueness engine (`IsNilpotent`, tripotent identity) in the
  `10^k` case. The two genuinely new sub-lemmas are (i) `ZMod (p^a)` has exactly two
  idempotents and (ii) idempotent-count multiplicativity over a coprime product / CRT.
- The **CRT-over-`primeFactors` indexing is the main labor**: assembling the binary CRT
  isomorphism into a `Finset`-indexed product and computing the `Fintype.card` of the
  idempotent subtype of that dependent product is fiddly but standard.
- The **Boolean-algebra isomorphism to `𝒫(primeFactors m)` is a stretch goal**: Mathlib
  supplies the operations (`add_sub_mul`, `HasCompl`), but packaging them into a
  `BooleanAlgebra` instance and proving the iso to `Finset.powerset` is extra work beyond
  the count.
- Similar solved problems: the parent `automorphic-number-oq-01-oq-02` (hand proof for
  `m=10`) and Mathlib's `CompleteOrthogonalIdempotents.bijective_pi` (product-ring
  idempotent decomposition) show the technique is in reach.

**Estimated Effort**:
- Exploration: 1–2 days (fix the two-idempotent local-ring lemma and the CRT product form).
- If tractable (count + involution): 4–7 days for a `0`-axiom file.
- If hard (full Boolean-algebra iso to `𝒫(primeFactors m)`): +3–5 days.

## References

### Books
- Ireland, K. and Rosen, M., *A Classical Introduction to Modern Number Theory*, 2nd ed.,
  Springer GTM 84, 1990 — CRT for `ℤ/nℤ`, structure of `ℤ/p^kℤ` as a local ring, and
  idempotents / the number of solutions of `x² = x`.
- Atiyah, M. F. and Macdonald, I. G., *Introduction to Commutative Algebra*, 1969 —
  idempotents, local rings, and the product decomposition of a ring via a complete set of
  orthogonal idempotents.

### Mathlib
- `Mathlib.Data.ZMod.Basic` (`ZMod.chineseRemainder`, `ZMod.natCast_self`) — the CRT ring
  isomorphism `ZMod (m*n) ≃+* ZMod m × ZMod n` and the nilpotency of the residue.
- `Mathlib.Algebra.Ring.Idempotent` (`IsIdempotentElem`, `one_sub`, `mul_one_sub_self`,
  `HasCompl` on the idempotent subtype, `compl_compl`, `add_sub_mul`) — the complement and
  Boolean operations.
- `Mathlib.RingTheory.Idempotents` (`CompleteOrthogonalIdempotents`, `bijective_pi`,
  `pair_iffₛ`) — the product-ring idempotent decomposition machinery.
- `Mathlib.NumberTheory.ArithmeticFunction.Misc`
  (`ArithmeticFunction.cardDistinctFactors`, notation `ω`, `cardDistinctFactors_apply`,
  `cardDistinctFactors_apply_prime_pow`, `cardDistinctFactors_mul`) — `ω(m)` and its
  values on prime powers and coprime products.
- `Mathlib.Data.Nat.Factorization.Basic` (`Nat.factorization`, `Nat.primeFactors`,
  `Nat.prod_primeFactors`) — the coprime prime-power factorization `m = ∏ p^{v_p(m)}`.
- `Mathlib.Data.Finset.Powerset` (`Finset.card_powerset : (s.powerset).card = 2 ^ s.card`)
  — the final `2^{ω(m)}` count.

## Metadata

```yaml
tags:
  - number-theory
  - idempotents
  - zmod
  - chinese-remainder-theorem
  - boolean-algebra
  - automorphic-numbers
related_proofs:
  - automorphic-number-oq-01-oq-02
  - automorphic-number-oq-01
  - automorphic-number
difficulty: moderate
source: gallery-gap
created: 2026-06-30
```
