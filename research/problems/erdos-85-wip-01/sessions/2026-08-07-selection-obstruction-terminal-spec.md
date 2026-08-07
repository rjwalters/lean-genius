# Goal #9 terminal spec: killing `SelectionObstructed` at the even boundary

Audit result (2026-08-07). The mixed prime-frequency dichotomy is COMPLETE
and unconditional up to `secondOrder_componentOrders_selectionObstructed`:
every exact-even-boundary graph's defect-component order family ℓ satisfies

`SelectionObstructed ℓ : ∀ p prime ≥ 7, (∃ even member p ∣ ℓ c) ∨ Even #{c : p ∣ ℓ c}`.

The remaining terminal is the arithmetic/structural impossibility of this
obstruction. Residual case map:

## Case A — some prime p > d divides some component order
The large-prime program closes this almost entirely:
- `all_component_orders_dvd_of_largePrime_dvd_one`: p divides EVERY order;
- `largePrime_dvd_card_of_dvd_component_order` + mass collapse: sector
  structure collapses (p ∣ #components etc.);
- `isSquare_d_sub_three_mod_largePrime_of_dvd_component_order`: d − 3 must be
  a QR mod p — `not_dvd_component_order_of_largePrime_nonresidue` kills all
  nonresidue primes;
- `exists_even_component_of_largePrime_dvd` handles the even-member branch.
Remaining sliver: residue primes p > d with all components p-divisible and
the obstruction satisfied — needs the sector-size cap (`PrimeSectorSize`:
each p-divisible component has ≥ p vertices, so #components ≤ (d(d−1)+3)/p)
against p ∣ #components ⟹ #components ∈ {0, p, 2p, …} and ≥ ... ⟹ for
p > √(d(d−1)+3) forces #components ∈ {0} — contradiction with "divides some
order". CHECK: this may already close Case A for p > √(d²−d+3) ≈ d; the gap
is only d < p ≤ d-ish boundary primes.

## Case B — all prime factors of all orders are < 7 ({2,3,5}-smooth families)
`SelectionObstructed` is VACUOUS here (no p ≥ 7 divides anything, count 0
even). This is the 3-primary/5-smooth escape. Killers available:
- order-five terminals (`five_dvd_orientedAnchorMass_forwardOriented`,
  `Erdos85OrientedFiveMass`) for 5-primary parts;
- the 3-primary terminals from the earlier program (goal #8's order-3 system);
- 2-primary parts are even components — the even-length machinery
  (orientation marking / reverse-block vanishing) applies with p replaced by
  the odd part.
MISSING: a composed statement `allSmooth ℓ → (boundary facts) → False`.
This is the genuine new work: likely a case split on the largest smooth
prime power present, feeding the respective mass identity.

## Case C — mixed: primes in [7, d] divide some orders, all obstructed
For each such p: either an even p-divisible member exists (route to the
even-member/orientation machinery at p) or the p-divisible count is even
(route to goal #9(b): `prime_dvd_pDivisibleAnchorMass_of_nonsquare` — the
even-sector mass identity kills even counts in the nonsquare branch; the
square branch needs the oriented square-branch convolution constancy
already in `Erdos85OrientedSquareBranch`).
MISSING: the assembly lemma routing each obstructed prime to its killer and
composing the finitely many windows. The window is finite per d
(π(d) − 3 primes), so for CONCRETE d (the exceptional-set analysis: d ∈
{4, 6, 8, 10, 12, 14, 16, 20, 22, …}) this is a finite per-d check; the
uniform-in-d statement needs only Cases A + B + the generic p ≤ d windows.

## Proposed first Lean deliverables
1. `selectionObstructed_smooth_or_exists_seven_le_prime_factor` — the A/B/C
   trichotomy as a clean case split (pure number theory over the family).
2. Case A closure: combine the four large-prime theorems + PrimeSectorSize
   into `false_of_largePrime_dvd_component_order` (residue sliver included).
3. Case B: `false_of_smooth_componentOrders` — compose 5-mass and 3-primary
   terminals (the hard one; may need new mass identities at p = 3, 5).
4. Case C assembly for the finite window.
