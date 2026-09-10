# Scoped H5/H7 prior-coverage audit — 2026-09-10

Owner: codex-sol-3. This is a source-level inventory of the files listed in
`q7_h5_h7_prior_coverage_sources.json`, not an exhaustive repository audit.
Historical computation reports below were read, not rerun. Lean declarations
were inspected; this inventory does not claim fresh compilation of every
module. It authorizes no solver, spectrum-enumeration, or Phase B launch.

## Residual conventions

The older `orderFortyNineSeven_residualCharpoly` removes only
(x²-7)^(h-1). It has degree51-2h and includes the forced cubic
x³-7x²-7x+49-h. The current psi removes that cubic too and has degree48-2h.
Thus the old residual moments357-13h and4557-69h must not be substituted
for psi's moments294-13h and2058-97h. Their difference is exactly the
forced cubic's contribution.

## Inspected coverage

| source | established or reported scope | consequence for next work |
| --- | --- | --- |
| `Erdos85OrderFortyNineIntegralResidual.lean` | Monic integer old residual under actual graph hypotheses. | Integrality itself is banked; check the residual convention. |
| `Erdos85OrderFortyNineResidualRootMoments.lean` | Exact second/fourth old-residual moments. | Recomputing them is not a new filter. |
| `Erdos85OrderFortyNineResidualCoefficients.lean` | Exact old-residual second/fourth coefficients, including h5/h7 cases. | Distinguish old coefficients from current psi. |
| `Erdos85OrderFortyNineResidualMomentHighCountExclusion.lean` and arithmetic companion | Actual exclusions for h19/h21 via Perron/Cauchy inequalities. | These statements do not exclude h5/h7. |
| `H7_FIFTH_MOMENT_PIVOT_AUDIT.md` | Regular degree-five proof does not transfer to full nonregular A; tr(AD²) remains free. | The later block decomposition repairs the spectral-space issue, but an independent C4-sensitive overlap bound is still required. |
| `H7_BLOCK_SPECTRAL_DECOMPOSITION_AUDIT.md` | Exact H7 blocks, psi moments, variable fifth moment, Newton R congruence, non-excluding fourth-moment Hankel test. | Do not repeat the old degree-four scalar test. |
| `H7_FINITE_FIELD_RANK_AUDIT.md` | Full low C has six fixed zero modes; pinned linear system over F7 reported consistent with532 free dimensions. | Pure rank/linear equations do not give a graph exclusion. The new residual-lattice transfer has separate provenance. |
| `H7_CHARACTERISTIC_SQUARE_MODULE_AUDIT.md` | Characteristic-square multiplicity need not create another ordinary kernel vector; retained quadratic relaxation has minimal kernel. | Do not infer semisimplicity or another codeword from repeated factors. |
| `H7_R_MOD5_CONSUMER_AUDIT.md` | R=3T+1 mod5 is a Newton invariant; pinned support/degree data admit different residues and negative algebraic-defect entries in relaxations. | Need a new C4-sensitive restriction on R, rather than another evaluation from the same linear identities. |
| `H7_POLYNOMIAL_CALCULUS_AUDIT.md` | Degree<=3 visible subsystem reported satisfiable; full quartic basis has22.8 billion monomials. | Do not restart generic low-degree Macaulay search. A hand-derived sparse identity is a different route. |
| `Erdos85RootedFifthWalkDefectNeighborhood.lean` | General mixed-word diagonal equals twice the number of ambient edges in a defect neighborhood; later fifth-walk specializations assume regularity. | The graph-count interpretation can be reused nonregularly; the regular specialization cannot be imported unchanged. |
| `Erdos85ExteriorDefectDecomposition.lean` | Actual C4-free defect adjacency iff no common neighbor. | Supports a C4-sensitive local isolation argument. |
| `Erdos85SquareOrderLowTriangleDefectIdentity.lean` | Actual low triangle/defect/incidence relation at square order. | Supplies the local state count used in current triangle bounds. |
| `Erdos85OrderFortyNineDefectModSevenKernel.lean` | H3 high-difference vectors for the full shifted defect block. | Not by itself the new H5/H7 residual-C lattice theorem. |

## Current reviewed additions

The [H5/H7 worksheet](Q7_H5_H7_SQUEEZE_20260910.md) records independently
reviewed component connectivity/non-bipartiteness, strict residual intervals,
actual integer-kernel reduction and determinant divisibility, the correct
mixed-degree Ihara reduction, and weighted-projector parity. The full-Gram
square test is redundant; the H7 weighted parity test is redundant with Ihara.
The H5 mod-eight gate adds a restriction to the tested earlier coefficient
constraints, but its coefficient controls are not spectra or graph witnesses.

## Completed bounded consumer

The inspected H7 fifth-moment/R audits identify a specific unresolved input:
an independent bound on R=tr(CD²) using actual C4-freeness. For a root v,
the common C/D neighbors are isolated inside C[N_D(v)], by the no-common-
neighbor interpretation of a D edge. Combining that observation with the
reviewed local (t,triangle-count) states leaves at most five nonisolated
vertices. A finite small-graph edge bound and census-based dynamic program
can therefore bound R without launching a graph solver or enumerating full
spectra. This consumer is now completed in the [local overlap audit](Q7_LOCAL_DEFECT_OVERLAP_BOUND_20260910.md), review1603 PASS: it excludes exactly the H5/T2 triangle-count case T=4 among the tested H5/H7 rows. The [exact H7 moment measure](Q7_H7_FIFTH_MOMENT_RELAXATION_20260910.md), review1604 PASS, shows that the resulting continuous five-moment relaxation still admits T=10, R=96. It is not an integral spectrum or graph. Further progress needs an additional joint or integral constraint.

Before a broader connected-case campaign, reconcile this reviewed scoped
inventory with the operator's intended master inventory. The current graph
problem remains open.

Independent review1600 by codex-sol-2 passed the scoped fifteen-source inventory; historical computations were not rerun.
