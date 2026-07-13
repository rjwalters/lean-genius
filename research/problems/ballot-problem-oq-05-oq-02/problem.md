# Problem: The Reflection-Principle Form of the Ballot Number, BN(a,b) = C(a+b,b) − C(a+b,b−1)

**Slug**: ballot-problem-oq-05-oq-02
**Created**: 2026-07-09T16:43:21-07:00
**Status**: Active
**Source**: user-request

## Problem Statement

### Formal Statement

$$
\mathrm{BN}(a,b) \;=\; \binom{a+b}{b} - \binom{a+b}{b-1}
\qquad (a \ge 1),
$$

where $\mathrm{BN}(a,b) = \binom{a+b-1}{a-1} - \binom{a+b-1}{a}$ is the ballot number as defined and verified in the parent entry. Equivalently, the goal is to prove that the two closed forms agree:

$$
\binom{a+b-1}{a-1} - \binom{a+b-1}{a} \;=\; \binom{a+b}{b} - \binom{a+b}{b-1},
$$

and to place this reflection-principle identity in the same Lean file as the cycle-lemma derivation so that the two routes to the ballot number are reconciled side by side.

### Plain Language

The ballot number BN(a,b) counts the sequences of a up-steps and b down-steps whose every partial sum stays strictly positive — the number of ways candidate A (with a votes) can stay strictly ahead of candidate B (with b votes) throughout the count. The parent entry defines it in one manifestly-integral "reflection" shape, C(a+b−1,a−1) − C(a+b−1,a), and proves the defining relation BN(a,b)·(a+b) = (a−b)·C(a+b,a). This problem asks us to prove the *other* standard reflection form, C(a+b,b) − C(a+b,b−1), which is the shape that comes directly out of André's reflection principle (count all paths, subtract the reflected "bad" paths). The two expressions must be equal because they count the same thing, but that equality is a genuine binomial identity that has to be verified, not assumed. The second half of the task is expository: gather the reflection-principle derivation and the existing cycle-lemma derivation into a single Lean file so a reader can see both classical proofs of the ballot number and their point of contact.

### Why This Matters

The ballot number admits two famous elementary derivations — Dvoretzky–Motzkin's cycle lemma and André's reflection principle — and the mathematical folklore is that they produce "the same" closed form. In fact they produce two *different-looking* closed forms, C(a+b−1,a−1) − C(a+b−1,a) versus C(a+b,b) − C(a+b,b−1), and reconciling them is exactly the content of showing the two derivations agree. Formalizing that reconciliation turns a piece of combinatorial folklore into a machine-checked identity, and it completes the ballot family's arithmetic layer: the parent entry already ties the cycle-lemma aggregate to the probability (a−b)/(a+b) and to the Catalan numbers, and this entry adds the reflection route to the same anchor. It also exercises the pure binomial-shift API (Pascal's rule, symmetry C(n,k) = C(n,n−k)) that recurs throughout the ballot/Catalan strand.

## Known Results

### What's Already Proven

- `ballotNumber a b = C(a+b-1,a-1) - C(a+b-1,a)` and `ballotNumber_mul_add : BN(a,b)·(a+b) = (a-b)·C(a+b,a)` for `a ≥ 1` — parent entry `Proofs/BallotProblemOQ05.lean` (ballot-problem-oq-05), 0 sorries, 0 axioms.
- `ballotNumber_div : BN(a,b)/C(a+b,a) = (a-b)/(a+b)` over ℚ and `ballotNumber_catalan : BN(n+1,n) = catalan n` — parent entry `Proofs/BallotProblemOQ05.lean`.
- The Dvoretzky–Motzkin cycle lemma itself (per-sequence rotation count = a − b), 0-axiom — sibling entry `Proofs/BallotProblemOQ01.lean` (ballot-problem-oq-01).
- Binomial absorption `Nat.add_one_mul_choose_eq`, symmetry `Nat.choose_symm_diff`/`Nat.choose_symm`, and Pascal's rule `Nat.succ_sub_one`/`Nat.choose_succ_succ` are available in Mathlib.

### What's Still Open

- The equality `C(a+b-1,a-1) - C(a+b-1,a) = C(a+b,b) - C(a+b,b-1)` has not been formalized in this repository.
- The reflection-principle derivation and the cycle-lemma derivation of the ballot number have not been reconciled in a single Lean file.

### Our Goal

Prove `ballotNumber a b = C(a+b,b) - C(a+b,b-1)` for `a ≥ 1` (as a natural-number identity with truncated subtraction), reusing the parent's `ballotNumber` definition, and assemble the reflection form together with the existing cycle-lemma/aggregate results so both derivations of BN(a,b) live in one file. Casting to the probability and Catalan corollaries is out of scope beyond confirming consistency with the parent.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ballot-problem-oq-05 | Parent: defines `ballotNumber` in the C(a+b−1,a−1) − C(a+b−1,a) form and proves the defining relation, probability, and Catalan corollaries via the cycle-lemma aggregate | Binomial absorption identities, truncated ℕ subtraction, central-binomial/Catalan bridge |

## Initial Thoughts

### Potential Approaches

1. **Approach A — direct binomial rewriting via symmetry and Pascal**: Rewrite each term of C(a+b,b) − C(a+b,b−1) using the symmetry C(a+b,b) = C(a+b,a) and C(a+b,b−1) = C(a+b,a+1), then apply Pascal's rule C(a+b,a) = C(a+b−1,a−1) + C(a+b−1,a) and C(a+b,a+1) = C(a+b−1,a) + C(a+b−1,a+1) to reduce to the parent's form. Care is needed with truncated ℕ subtraction and the `b = 0` edge case.
   - Why it might work: it is a finite chain of standard Mathlib binomial lemmas (`Nat.choose_symm_diff`, `Nat.choose_succ_succ`), so no new mathematics is required.
   - Risk: ℕ subtraction does not distribute freely, so the identity may need to be proved first as an addition identity (C(a+b,b) + C(a+b,b−1)-complement rearrangement) and only then converted to the subtractive form under the hypothesis a ≥ b or with a case split.

2. **Approach B — go through the shared defining relation**: Prove that C(a+b,b) − C(a+b,b−1) also satisfies (·)·(a+b) = (a−b)·C(a+b,a) using the same absorption identities the parent used (`aux_up`, `aux_down`), then invoke uniqueness: since a+b > 0 for a ≥ 1, any two naturals with the same product against (a+b) are equal, giving the reflection form equals `ballotNumber`.
   - Why it might work: it reuses the parent's `ballotNumber_mul_add` verbatim and only requires establishing the analogous product identity for the new form, avoiding delicate subtraction juggling.
   - Risk: establishing the product identity for the b-indexed form still needs the absorption identity applied at the bottom index, so it duplicates some of the parent's `aux_down` reasoning; must confirm a+b ≠ 0 cancellation is clean over ℕ.

### Key Difficulties

- Truncated natural-number subtraction: identities of the form X − Y = Z − W over ℕ are only equivalent to X + W = Z + Y when the subtractions don't underflow, so the proof likely routes through an additive reformulation before recovering the subtractive statement.
- Edge cases: b = 0 (then C(a+b,b−1) = C(a,·) with the "−1" wrapping to a large index that must evaluate to 0) and a ≤ b (where the ballot number is 0) must be handled so the identity holds unconditionally, matching the parent's unconditional style.
- Index bookkeeping between the a-indexed reflection form (parent) and the b-indexed reflection form (this problem) requires consistent use of symmetry C(a+b,k) = C(a+b,a+b−k).

### What Would a Proof Need?

- Key lemma 1: the additive identity C(a+b,b) + C(a+b−1,a) = C(a+b,b−1) + C(a+b−1,a−1) (or its symmetric analogue), from which the subtractive form follows by `Nat.sub_eq_of_eq_add`-style reasoning.
- Key lemma 2: Pascal's rule and binomial symmetry specialised to the indices a−1, a, a+1 at level a+b (and level a+b−1), i.e. `Nat.choose_succ_succ` and `Nat.choose_symm_diff`.
- Technical requirements: reuse of the parent's `ballotNumber` definition and, for Approach B, its `ballotNumber_mul_add`; a cancellation lemma for a+b > 0 over ℕ; a single Lean file collecting both the reflection form and the cycle-lemma results with cross-references.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is a finite binomial identity provable from standard Mathlib lemmas (Pascal, symmetry, absorption), with no missing theory.
- The parent entry `ballot-problem-oq-05` already carried out closely analogous absorption/subtraction reasoning to 0 sorries, so a strong template exists.
- The main effort is careful handling of truncated ℕ subtraction and the b = 0 / a ≤ b edge cases, which is fiddly but routine.

**Estimated Effort**:
- Exploration: a few hours to fix the cleanest additive reformulation and edge-case handling.
- If tractable: 1–3 days to a green, 0-sorry file reconciling both forms.
- If hard: unlikely to exceed a week given the parent template.

## References

### Papers
- Renault, Marc, "Lost (and found) in translation: André's actual method and its application to the generalized ballot problem", American Mathematical Monthly 115(4), 2008, 358–363 — the reflection-principle derivation whose closed form is C(a+b,b) − C(a+b,b−1).
- Dvoretzky, Aryeh and Motzkin, Theodore, "A problem of arrangements", Duke Mathematical Journal 14(2), 1947, 305–313 — the cycle-lemma derivation being reconciled with reflection.

### Online Resources
- https://en.wikipedia.org/wiki/Bertrand%27s_ballot_problem — states both the reflection and cycle-lemma derivations and the closed forms of the ballot number.

### Mathlib
- `Mathlib.Data.Nat.Choose.Basic` — `Nat.choose_succ_succ` (Pascal's rule), `Nat.choose_symm`, `Nat.choose_symm_diff`, `Nat.succ_sub_one`.
- `Mathlib.Data.Nat.Choose.Central` — `Nat.centralBinom`, `Nat.succ_dvd_centralBinom` (for consistency with the parent's Catalan corollary).
- `Mathlib.Combinatorics.Catalan` — `catalan`, `catalan_eq_centralBinom_div`.

## Metadata

```yaml
tags:
  - probability
  - ballot-problem
  - cycle-lemma
  - combinatorics
  - catalan-numbers
  - binomial-coefficients
  - ballot-number
related_proofs:
  - ballot-problem-oq-05
difficulty: medium
source: open-question
created: 2026-07-09T16:43:21-07:00
```
