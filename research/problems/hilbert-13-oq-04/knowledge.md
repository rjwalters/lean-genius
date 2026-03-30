# Knowledge Base: hilbert-13-oq-04

Kolmogorov-Arnold Generalization to Compact Metric Spaces

---

## Problem Understanding

The classical Kolmogorov-Arnold theorem (1957) states that every continuous function
f : [0,1]^n -> R can be written as a sum of 2n+1 compositions of univariate functions.
The natural question: for which spaces X does this hold?

**Key insight**: Covering dimension (Lebesgue) is the precise invariant. Sternfeld (1985)
proved the complete characterization: a compact metrizable space X has the superposition
property with 2n+1 maps iff dim(X) <= n.

**Key references**:
- Ostrand (1965): Compact metric spaces of dimension n have 2n+1 separating maps to [0,1]
- Sternfeld (1985): Full characterization linking covering dimension to superposition
- Engelking (1978): Dimension Theory textbook with full proofs

---

## Insights

- **Covering dimension is not in Mathlib** — this formalization introduces genuinely new
  infrastructure (covDimLE, covDimEq, OpenCover, etc.)
- The Sternfeld characterization is biconditional (iff), not just one direction
- Ostrand's separating maps are the technical bridge: dim(X) <= n gives 2n+1 maps g_q
  that jointly separate points, then outer functions Phi_q are constructed via Baire category
- The 2n+1 bound is sharp — uses cohomological obstructions on Menger compacta
- dim([0,1]^n) = n is a deep result: upper bound via coordinate decomposition, lower bound
  equivalent to Brouwer fixed point theorem / Lebesgue covering theorem

---

## Built Items (Session 1, 2026-03-30)

- `proofs/Proofs/Hilbert13GeneralSpaces.lean` (340 lines)
  - Definitions: covDimLE, covDimEq, OpenCover, coverOrderAt, IsRefinement, etc.
  - Proved: covDimLE_succ (monotonicity), unitCube_covDimEq, classical_KA_from_general,
    unitCube_superposition, unitCube_superposition_sharp
  - Axiomatized (6): unitCube_covDimLE, unitCube_covDim_lower_bound, ostrand_separating_maps,
    generalized_kolmogorov_arnold, sternfeld_characterization, superposition_2n_plus_1_sharp
  - 1 sorry: covDimLE_of_embedding (dimension monotonicity under continuous injection)
- `src/data/proofs/hilbert-13-oq-04/` — full gallery integration

---

## Dead Ends

(None yet — first session)
