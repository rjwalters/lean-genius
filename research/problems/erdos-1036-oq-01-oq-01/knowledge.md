# Knowledge Base: erdos-1036-oq-01-oq-01

**Problem**: Eliminate the `numISCTrue` interface axioms in the gallery proof
`Erdos1036OQ01.lean` ("Optimal Constant in Shelah's Coloring Theorem") via a
Quotient construction — a Setoid on induced-subgraph pairs, a count on the
quotient, and the bound `cardinality ≤ 2^n`.

**Status**: ACT (S1, 2026-06-15, researcher-8). Wrote
`proofs/Proofs/Erdos1036OQ01OQ01.lean` discharging all three interface axioms as
definitions/theorems. BUILD-PENDING (Docker host down) and left UNREGISTERED in
`Proofs.lean`.

---

## Problem Understanding

The parent `Erdos1036OQ01.lean` carries 6 axioms. Three are a deliberate
*interface* placeholder for the "true ISC count":

- `axiom numISCTrue : SimpleGraph V → ℕ`
- `axiom numISCTrue_le_pow : numISCTrue G ≤ 2 ^ Fintype.card V`
- `axiom numISCTrue_pos : 0 < numISCTrue G`

with a comment that they "would be eliminated by ~200 lines of Quotient type
construction". The intended meaning (file docstring, line 13/44): `numISCTrue G`
is the number of **non-isomorphic induced subgraphs** of `G`, i.e. the number of
isomorphism classes of `{G[S] : S ⊆ V}`.

The other three axioms are genuinely deep and out of scope here:
`nonRamseyExistsTrue`, `shelah_isc` (Shelah's 1998 exponential lower bound), and
`optimalConstantTrue_eq_one` (the headline open conjecture).

---

## Insights

- **Faithful construction.** Put a setoid on `Finset V` by
  `S ~ T  ↔  Nonempty (G.induce ↑S ≃g G.induce ↑T)` (isomorphic induced
  subgraphs). Graph isomorphism is an equivalence relation (`Iso.refl`,
  `Iso.symm`, `Iso.trans`), so this is a genuine `Setoid (Finset V)`. Define
  `numISCTrue G := Nat.card (Quotient (iscSetoid G))`. The quotient's cardinality
  *is*, by construction, the number of isomorphism classes of induced subgraphs.

- **`Nat.card` beats `Fintype.card` here.** The ~200-line estimate comes from
  assuming a `Fintype`/`DecidableEq` instance on the quotient is needed — which
  would force *deciding graph isomorphism* (constructing `Fintype (G ≃g H)` and a
  `DecidableRel`). Using `Nat.card` needs **none** of that to *define* the count.
  The whole construction is ~50 lines.

- **The two bounds are one-liners.**
  - `≤ 2^n`: a quotient of a finite type is no larger than the type. Via a
    `classical` `DecidableRel`, `Fintype.card_quotient_le` gives
    `card (Quotient s) ≤ card (Finset V)`, and `Fintype.card_finset` gives
    `card (Finset V) = 2 ^ card V`. Bridge `Nat.card`↔`Fintype.card` with
    `Nat.card_eq_fintype_card`.
  - `> 0`: `⟦(∅ : Finset V)⟧` makes the quotient `Nonempty`; with the automatic
    `Finite (Quotient _)` instance, `Nat.card_pos` closes it.

- This discharges interface axioms 1–3 only (`numISCTrue`, `_le_pow`, `_pos`).
  Wiring it back into the parent would drop its `axiomCount` 6 → 3.

---

## Built items

- `proofs/Proofs/Erdos1036OQ01OQ01.lean` — `iscSetoid`, `numISCTrue`,
  `numISCTrue_le_pow`, `numISCTrue_pos`. **BUILD-PENDING / UNREGISTERED.**

---

## Mathlib gaps

- No prepackaged "number of induced-subgraph isomorphism classes" in Mathlib, but
  no real gap: it is `Setoid` + `Nat.card` + `Fintype.card_quotient_le`.

---

## Next steps

1. Docker-verify `Erdos1036OQ01OQ01.lean`. Names to confirm under a real build:
   `Fintype.card_quotient_le`, `Quotient.fintype` resolving as an instance under
   `classical`, `SimpleGraph.Iso.refl/.symm/.trans`, and the automatic
   `Finite (Quotient _)` instance.
2. On success: `import Proofs.Erdos1036OQ01OQ01` in `Proofs.lean`, then retarget
   the parent's three interface axioms at these theorems (axiomCount 6 → 3).
3. Optional: prove `G(n,1/2)` achieves `numISCTrue = 2^n` a.s. — input to the open
   `optimalConstantTrue_eq_one` conjecture.

---

## Dead Ends

- Building `Fintype (Quotient iscSetoid)` directly (the route the ~200-line
  estimate assumes) requires `DecidableRel` for graph isomorphism — avoidable, and
  avoided, by counting with `Nat.card`.

---

## Sessions

### Session 2026-06-15 (S1) — ACT, researcher-8

**Mode**: FRESH
**Outcome**: progress (build-pending) — first Lean written for this OQ.

#### What I did
- Read the parent `Erdos1036OQ01.lean`; identified the 3 interface axioms as the
  OQ target and the other 3 as out-of-scope deep axioms.
- Designed and wrote `Erdos1036OQ01OQ01.lean`: a setoid on `Finset V` by induced
  subgraph isomorphism, `numISCTrue := Nat.card (Quotient …)`, and the two bounds.
- Updated the knowledge JSON (phase OBSERVE → ACT).

#### Key findings
- The `Nat.card` framing removes the decidability-of-isomorphism obstacle that
  inflated the parent's size estimate (~200 → ~50 lines).

#### Files modified
- `proofs/Proofs/Erdos1036OQ01OQ01.lean` (new, build-pending, unregistered)
- `src/data/research/problems/erdos-1036-oq-01-oq-01.json`
- `research/problems/erdos-1036-oq-01-oq-01/knowledge.md`

#### Next steps
- Docker-verify, register in `Proofs.lean`, then wire into the parent to drop its
  axiomCount 6 → 3.
