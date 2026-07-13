# Knowledge Base: abel-ruffini-oq-04-oq-02-oq-02-oq-01

## Problem Understanding

Parent `abel-ruffini-oq-04-oq-02-oq-02` (Aₙ solvable iff n ≤ 4) proves A₄ solvable
indirectly. Open question: exhibit A₄'s composition series A₄ ▷ V₄ ▷ {e} explicitly
with A₄/V₄ ≅ ℤ/3ℤ and V₄ ≅ (ℤ/2ℤ)² identified.

## Result

The Lean file `AbelRuffiniOQ04OQ02OQ02OQ01.lean` (136L, 11 thm, 0 axioms) already
existed — added UNVERIFIED in #30747 (build host was down), repaired in #30783 — but
had no gallery entry of its own (only surfaced as an additionalFile companion of the
sibling `abel-ruffini-oq-04-oq-02-oq-01`). This session **verified** it (lake env lean
clean, #print axioms → only propext/Classical.choice/Quot.sound) and created its
dedicated gallery entry.

## Insights

- Prime-order quotient ⟹ cyclic ⟹ ℤ/nℤ: `isCyclic_of_prime_card` + `mulEquivOfPrimeCardEq`
  (no generator to exhibit).
- Order-4 exponent-2 ⟹ Klein four ⟹ (ℤ/2ℤ)²: `IsKleinFour.nonempty_mulEquiv`.
- `alternatingGroup.kleinFour` packages V₄ ◁ A₄ with normality, card, IsKleinFour,
  and `kleinFour_eq_commutator` (V₄ = [A₄,A₄], so the chain is the derived series).
- ℤ/nℤ rendered as `Multiplicative (ZMod n)` since the ambient groups are multiplicative.

## Dead Ends

None — the file was already complete; the gap was a missing gallery entry.
