# Burnside pᵃqᵇ Theorem (abel-ruffini-oq-04-oq-02-oq-03-oq-01)

## Problem Summary

Pool title: *"Formalize Burnside pᵃqᵇ theorem via Mathlib character theory."*

**Burnside's theorem (1904):** every finite group of order `pᵃ · qᵇ` (with `p`, `q`
prime) is solvable. Equivalently, a finite simple group with at most two distinct
prime divisors is cyclic of prime order. This is one of the well-known "not yet in
Mathlib" results (it appears on tracking lists of missing classical theorems).

## Mathlib Status (v4.26.0) — Gap Analysis

What Mathlib **has** (the outer layers of the standard proof):

| Ingredient | Mathlib name |
|---|---|
| p-groups are nilpotent | `IsPGroup.isNilpotent` |
| nilpotent ⟹ solvable | `IsNilpotent.to_isSolvable` (instance) |
| prime-power order ⟹ p-group | `IsPGroup.of_card` |
| extension principle for solvability | `solvable_of_ker_le_range` |
| Lagrange / index arithmetic | `Subgroup.card_mul_index`, `index_mul_card`, `one_lt_index_of_ne_top` |
| abelian ⟹ solvable | `isSolvable_of_comm` |
| character of an `FDRep`, orthogonality | `FDRep.character`, `char_orthonormal` |

What Mathlib **lacks** (the character-theoretic core), and is the genuine blocker:

1. **Irreducible character degrees divide `|G|`.** Needs the algebraic-integer
   theory of `∑ χ(g)` over conjugacy classes and the class-sum/central-character
   machinery. Not present.
2. **Burnside's vanishing lemma.** If `gcd(|class of g|, χ(1)) = 1` for an irreducible
   `χ`, then `χ(g) = 0` or `ρ(g)` is scalar. Relies on an averaged-root-of-unity
   bound (`|χ(g)/χ(1)| ≤ 1` for an algebraic integer that is also an average of roots
   of unity ⟹ it is `0` or a root of unity). Not present.
3. **#irreducibles = #conjugacy classes** over `ℂ`. Mathlib has orthogonality of the
   characters that exist but not the completeness/count statement in a usable form.
4. Assembling 1–3 into: *a finite nonabelian group of order `pᵃqᵇ` has a proper
   nontrivial normal subgroup* (it is not simple).

Estimated cost to close the gap: **>1000 lines** of new representation theory
(class functions as an inner-product space, central characters, algebraic-integrality
of class sums, the vanishing lemma). This is a BLOCKED target for a single session.

## Approach Taken — Verified Reduction Scaffolding

Rather than axiomatize the whole theorem (pure scaffolding, discouraged), this session
delivers the **fully verified outer layers** and isolates the missing mathematics into
a single explicit hypothesis.

`proofs/Proofs/BurnsidePaQbSolvable.lean` (status: **verified**, 0 sorry, 0 axiom):

- `isSolvable_of_isPGroup`, `isSolvable_of_card_prime_pow` — the **base case**
  (`a=0` or `b=0` edge; leaves of the induction). Fully verified via Mathlib's
  nilpotency of p-groups.
- `solvable_of_normal_extension` — the **inductive engine**: `N ⊴ G` with `N` and
  `G ⧸ N` solvable ⟹ `G` solvable. Derived from `solvable_of_ker_le_range` with the
  subgroup inclusion and quotient projection (`ker_mk' = N`, `range_subtype = N`).
- `OrderTwoPrimes p q G` — predicate "every prime divisor of `|G|` is `p` or `q`",
  closed under subgroups/quotients (their orders divide `|G|`).
- `burnside_reduces_to_nonsimplicity` — **the reduction theorem, fully verified**:
  *given* that every finite nonabelian group with `OrderTwoPrimes p q` is not simple,
  every finite group of order `pᵃqᵇ` is solvable. Performs the strong induction on
  `|G|` and the extension assembly; the only unproved input is the non-simplicity
  hypothesis (= the character-theory core above).

Net effect: Burnside's theorem is reduced, with everything machine-checked, to the
single clean group-theoretic statement "*order `pᵃqᵇ` nonabelian ⟹ not simple*".

### Lean engineering notes
- Stated over `H : Type` (universe 0, not `Type*`) deliberately, so the induction
  hypothesis — quantified over all such `H` — applies to the subgroup `↥N` and the
  quotient `H ⧸ N`, which are again `Type`s.
- Strong induction done via `Nat.strong_induction_on` on `n = Nat.card H` with the
  statement reformulated as `∀ n, ∀ H, Nat.card H = n → …`; this avoids the
  ill-formed `induction (Nat.card H) generalizing H` (H occurs in the measure).
- Strict order drops `|N| < |H|` and `|H ⧸ N| < |H|` come from
  `Nat.lt_mul_iff_one_lt_right` plus `card_mul_index` / `index_mul_card`, using
  `one_lt_index_of_ne_top` (for `N ≠ ⊤`) and `one_lt_card_iff_ne_bot` (for `N ≠ ⊥`).

## Session 2026-06-26 (Session 1)

**Mode:** FRESH (EMPTY tier, genuinely fresh — verified no prior knowledge.md/meta.json).
**Outcome:** progress — verified scaffolding + reduction; character-theory core BLOCKED.

### Status classification
SURVEY / partially BLOCKED. The full theorem is not claimed. The verified deliverable
is real (prime-power solvability + extension principle + the non-simplicity reduction),
all `sorry`/`axiom`-free.

### Next Steps
1. Build the missing representation theory in Mathlib or a local file:
   class functions inner product → central characters → integrality of class sums →
   Burnside's vanishing lemma → non-simplicity of `pᵃqᵇ` groups.
2. Once `burnside_not_simple` is available, discharge the hypothesis of
   `burnside_reduces_to_nonsimplicity` to obtain the unconditional theorem.
3. Possible intermediate target submittable to Aristotle: the **algebraic-integer
   averaging lemma** ("an algebraic integer that is an average of `n` roots of unity
   and has all conjugates of absolute value `≤ 1` is `0` or a root of unity").
