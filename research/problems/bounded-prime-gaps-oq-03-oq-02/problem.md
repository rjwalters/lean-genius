# Problem: Certified-computation replacement for `engelsma_lower_bound`

**Slug**: `bounded-prime-gaps-oq-03-oq-02`
**Parent**: `bounded-prime-gaps-oq-03` (Engelsma optimality of the 50-tuple diameter 246)
**Tier**: B (Significance 6 / Tractability 6)

## Statement

### Plain Language

`BoundedPrimeGapsOQ03.lean` introduces an axiom (`engelsma_lower_bound`) that records the
result of Thomas Engelsma's 2013 exhaustive computer search: **every admissible 50-tuple of
natural numbers has diameter at least 246.** This is the missing-half of the tight
identification "the narrowest admissible 50-tuple has diameter exactly 246."

**OQ-03-OQ-02 asks**: Can this axiom be replaced with a *machine-verified Lean computation*
— i.e., can we discharge it by `decide` / `native_decide` over a suitably encoded finite
search problem, eliminating the appeal to an unverified external program?

### Formal Statement

The axiom in `proofs/Proofs/BoundedPrimeGapsOQ03.lean` (line 134) is:

```lean
axiom engelsma_lower_bound :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, H.max' hne - H.min' hne ≥ 246
```

where `IsAdmissible H := ∀ p : ℕ, Nat.Prime p → (H.image (· % p)).card < p`
(from `BoundedPrimeGaps.lean` line 59).

The goal is to either replace this `axiom` by a `theorem ... := by native_decide` or by a
hand-written constructive proof using a verified search procedure.

$$
\forall H \subseteq \mathbb{N},\ \mathrm{IsAdmissible}(H) \,\land\, |H| \ge 50
\implies \max(H) - \min(H) \ge 246.
$$

By translation invariance, this is equivalent to the **finite** statement:

$$
\forall H \subseteq \{0, 1, \ldots, 245\},\ |H| = 50 \,\land\, 0 \in H
\implies \neg \mathrm{IsAdmissible}(H).
$$

## Classification

```yaml
tier: B
significance: 6      # closes a known axiom in an established result; doesn't open new mathematics
tractability: 6      # decidable in principle; native_decide feasibility is the real question
tags:
  - number-theory
  - primes
  - prime-gaps
  - sieve-theory
  - polymath
  - admissible-tuples
  - computer-search
  - decidability
  - native-decide
  - certified-computation
  - open-problem
  - research
  - seeker-selected
  - gallery-extracted
```

## Why This Matters

1. **Axiom elimination** — `BoundedPrimeGapsOQ03.lean` currently advertises 0 sorries but
   1 axiom. Replacing this axiom with a certified computation upgrades the file from
   `axiomatized` to `verified` (or at least removes the most quantitative external assumption).
2. **Pattern transferability** — The same template (admissible-tuple lower bounds via
   exhaustive search) recurs for `engelsma54Tuple`, the Sutherland narrow tuples, and
   future Polymath improvements. Establishing a *reusable* pattern matters more than the
   single bound.
3. **Mathlib contribution path** — A `Decidable (IsAdmissible H)` instance, together with
   a verified backtracking search, would be a natural Mathlib contribution under
   `Mathlib.NumberTheory.AdmissibleTuples` (currently nonexistent; admissibility lives only
   in this repository's gallery proofs).
4. **Methodology marker** — Demonstrates a non-trivial certified-computation result inside
   the gallery, parallel to Hales' Flyspeck (4-color, Kepler) but at a much smaller scale.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `bounded-prime-gaps` | Parent gallery entry; defines `IsAdmissible` and the Maynard-Tao framework |
| `bounded-prime-gaps-oq-03` | Contains the axiom; achievability side `admissible_50_tuple_diam_achieved` is proven via `native_decide` |
| `bounded-prime-gaps-oq-03-oq-01` | Sibling on the Engelsma 50-tuple; provides the `admissible_subset` lemma |
| `bounded-prime-gaps-oq-03-oq-01-oq-04` | Sibling exploration on the diameter-246 tuple optimality |
| `bounded-prime-gaps-sieve` | Sieve-theoretic lemmas; relevant for **Path C** (density / Selberg) below |
| `bounded-prime-gaps-tpc` | Twin Prime Conjecture machinery; example of `native_decide` on admissibility |

## Approach Menu

Three paths surveyed in S1 (see `knowledge.md` for full development):

- **Path A — `native_decide` on direct enumeration**: encode as `∀ H : Finset (Fin 246), …`
  and let Lean compile it. Search space $\binom{246}{50} \approx 1.7 \times 10^{54}$ —
  *infeasible* without pruning.
- **Path B — Verified backtracking with prime-residue pruning**: reify Engelsma's algorithm
  (constraint propagation on permitted residue classes mod small primes 2, 3, 5, 7, 11, …).
  Effective search after pruning ≈ $10^6$–$10^8$ leaves — *feasible* if we are careful
  about Lean's `decide` time budget, possibly via a kernel-friendly fuel-bounded encoding.
- **Path C — Sieve-theoretic sufficient condition**: use Selberg-type density bounds to
  prove a *weaker* diameter bound (say ≥ 240), then close the gap [240, 246] via a much
  smaller `native_decide`. *Speculative*: the density gap may be too narrow at H.card = 50
  for sieve methods to bite.

S1 recommends **Path B** as the only realistic target, with Path C as a fallback if the
search proves intractable in Lean's reduction model.
