# Final proof outline: Erdős 85 is false

Status: first complete top-down draft, 2026-08-17. This is a living map,
not a claim that the theorem is proved. A wrong `AXIOM` below is repairable;
an omitted branch is not. The labels mean:

- `PROVEN`: a uniform Lean theorem exists; the theorem name is given.
- `PROVEN-AT-49-ONLY`: proved for the `q = 7`, orders `48/49` instance.
- `AT-64-ONLY`: proved or exhaustively established only for `q = 8`, order 64.
- `PROVEN-COMPUTATIONALLY`: exhaustive computation with the stated finite
  scope; not a uniform mathematical theorem.
- `AXIOM`: a precise conjectural statement which would close its parent node.
- `GAP`: no adequate candidate statement is currently known.

The proposed verdict is that the minimum-degree threshold for forcing a
four-cycle has arbitrarily large one-step drops. The proof has two parallel
candidate families. The characteristic-two family currently has its existence
jaw uniformly and is missing its nonexistence jaw. The odd-prime family has a
complete first instance at `q = 7`, but no uniform existence construction and
no uniform square-order nonexistence theorem. **Either family alone is enough.**

## 0. Definitions and the root implication

Let `f(n) = minDegreeForC4 n`. A `C4FreeMinDegreeWitness n d` is a C4-free
graph on `n` vertices of minimum degree at least `d`.

1. **`PROVEN` — literal negation.**
   `erdos85Negation_iff_not_question` identifies `¬ Erdos85Question` with
   arbitrarily large strict drops `f(n+1) < f(n)`.

2. **`PROVEN` — one plane-order pincer gives one drop.**
   `PlaneOrderDropWitness q` consists of
   
   - a witness on `q² - 1` vertices with minimum degree `q`, and
   - nonexistence of such a witness on `q²` vertices.
   
   `PlaneOrderDropWitness.strict_drop` proves `f(q²) < f(q² - 1)`.

3. **`PROVEN` — cofinally many pincers refute Erdős 85.**
   `not_erdos85Question_of_cofinalPlaneOrderDropFamily` proves
   
   ```text
   (∀ N, ∃ q, N ≤ q²-1 ∧ PlaneOrderDropWitness q) -> ¬ Erdos85Question.
   ```

4. **Root remaining task.** Prove either Branch A or Branch B below for an
   unbounded set of `q`. Branch A is presently the shorter complete route.

## A. Characteristic-two / binary prime-power branch

Fix `q = 2^k`, `k ≥ 3`.

### A1. The `q² - 1` existence jaw

5. **`PROVEN` — uniform construction.** For every finite field `K` of
   characteristic two, deleting the absolute points and the nucleus from the
   orthogonal-polarity graph gives a C4-free graph on `q² - 1` vertices of
   minimum degree `q`:
   `Polarity.c4FreeMinDegreeWitness_even_delete_absolute_nucleus`.
   The first pincer instance is also concrete: commit `a7c0542252` provides
   the kernel-checked explicit theorem
   `c4FreeMinDegreeWitness_sixtyThree_eight`, an 8-regular C4-free graph on
   63 vertices.

6. **`PROVEN` — cofinality.** `cofinalEvenFieldSquareExclusion_of_binary`
   uses `GaloisField 2 k`; the orders `2^k` are cofinal. There is no remaining
   construction question on this jaw.

### A2. Normalize the `q²` nonexistence jaw

7. **`PROVEN` — energy-minimal tight core reduction.** For `d ≥ 1`,
   `squareOrderTightCoreExists_iff_witness` equates an arbitrary C4-free
   minimum-degree-`d` graph on `d²` vertices with a normalized core satisfying:
   
   - minimum degree at least `d`;
   - energy minimality;
   - every edge has a degree-`d` endpoint; and
   - every degree-balancing edge slide is saturated by a three-edge walk.

8. **`PROVEN` — exact sufficient target.**
   `binarySquareOrderTightCoreExclusion_iff` shows that it is enough, and is
   equivalent, to prove
   
   ```text
   BinarySquareOrderTightCoreExclusion :=
     ∀ k ≥ 3, ¬ SquareOrderTightCoreExists (2^k).
   ```
   
   `not_erdos85Question_of_binarySquareOrderTightCoreExclusion` is the final
   theorem once this statement is supplied.

### A3. Structural split of a normalized square-order core

The intended split uses the number and placement of vertices of degree above
`q`. This is the point where the order-49 and order-64 campaigns must be
generalized rather than merely replayed.

9. **`PROVEN` — general square-order skeleton.** The energy-minimality,
   tight-edge-cover, local saturation, high-root, clean-sector, defect-operator,
   and counting lemmas in the `Erdos85SquareOrder*`,
   `Erdos85HighRootZeroSlack`, `Erdos85NonregularDefectOperator`, and
   `Erdos85Branch*` modules apply to arbitrary `q` under their stated local
   hypotheses. Important reusable statements include
   `squareOrder_degree_eq_or_succ_of_tightEdgeCover`,
   `squareOrder_degree_succ_highRoot_structure`, and
   `false_of_squareOrder_clean_highRoot`.

10. **`PROVEN` — exhaustive parameterized sector split.**
    `squareOrder_regular_or_nonregularSectorProfile` proves that every
    tight-edge-cover square-order core is either regular or belongs to a
    scale-stable nonregular profile. In the latter sector all degrees are
    `q` or `q+1`; the high set is nonempty and independent; its incidence
    counts `k_x` satisfy exact first and second moments
    
    ```text
    Σ k_x = (q+1)h,       Σ k_x² = h(h+q),
    ```
    
    handshake parity, `2k_x ≤ q` at every low vertex, and
    `h² + (3q+1)h ≤ q³`. This replaces the earlier, unjustified suggestion
    of a finite orbit list independent of `q`: the known bound allows `h` to
    grow with `q`, so the honest split is parameterized.

### A4. Regular sector

11. **`PROVEN` — defect operator at the exact square order.** For a regular
    C4-free graph, the second-order defect relation is encoded by
    `A² = (q-1)I + J - D`, commutes with `A`, and supports the spectral and
    component machinery (`adjMatrix_sq_eq_sub_secondOrderDefect_of_regular`,
    `adjMatrix_comm_secondOrderDefect_of_regular`).

12. **`AXIOM A-REG` — binary square regular exclusion.** For every `k ≥ 3`,
    no `q`-regular C4-free graph exists on `q²` vertices for `q = 2^k`.
    A viable proof should use the defect spectrum/component quotient and the
    characteristic-two arithmetic, not a finite census.

13a. **`PROVEN` — uniform regular infrastructure.** The defect operator,
     commutation, Gram identities, and moment budgets used at order 64 are
     parameterized structural theorems. In a component decomposition they
     constrain the incidence blocks through identities of the form
     `A_H² + BB* = (q-1)I + J - D`.

     The characteristic-two input is now uniform at the square order, rather
     than an order-64 observation. The theorem
     `binarySquare_regular_exists_nontrivial_defect_kernel_vector` proves that
     for every positive even `q`, any `q`-regular C4-free graph on `q²`
     vertices has a vector `w` over `𝔽₂`, distinct from both `0` and `1`, with

     ```text
     Aw = 0,                 (I + J + D)w = 0.
     ```

     It follows from `A²=I+J+D` modulo two and the second-kernel-vector theorem
     for an even-dimensional alternating matrix killing `1`. This is a real
     uniform constraint on every binary regular core: the support of `w` has
     even `G`-neighborhood at every vertex while simultaneously satisfying the
     defect parity equation. The decoded graph-theoretic statement is the
     `PROVEN` theorem `binarySquare_regular_exists_coupled_parity_set`, which
     supplies a proper nonempty set `W` with both laws pointwise. It is not yet
     a contradiction; the next A-REG task is to combine this coupled proper
     parity set with defect components or the integral/complex Gram identities.

     There is also a stronger `PROVEN` characteristic-polynomial form.
     `adjMatrix_charpoly_odd_coeff_eq_zero_zmodTwo` proves that every
     odd-degree coefficient of an even-order adjacency characteristic
     polynomial vanishes over `𝔽₂`, and
     `adjMatrix_charpoly_isSquare_zmodTwo` packages the result as

     ```text
     χ_A(X) = p(X)²  in 𝔽₂[X].
     ```

     Squarehood for the defect polynomial needs no delicate transfer through
     `A²=I+J+D`: the defect graph is itself a simple graph on the same even
     vertex set. Accordingly `binarySquare_defect_charpoly_isSquare_zmodTwo`
     is `PROVEN` and gives `χ_D(X)=r(X)²` over `𝔽₂`. The next precise spectral
     layer is partly `PROVEN`: the generic UFD lemma
     `factorization_even_of_eq_sq` and its graph specialization
     `binarySquare_defect_charpoly_factorization_even_zmodTwo` show that every
     normalized mod-two polynomial factor has even valuation in `χ_D`.
     Component decomposition is now also `PROVEN`:
     `adjMatrix_charpoly_eq_prod_connectedComponents` gives the general
     characteristic-polynomial product, and
     `adjMatrix_charpoly_factorization_eq_sum_connectedComponents` turns each
     global valuation into the sum of component valuations. Consequently
     `binarySquare_sum_defectComponent_charpoly_factorization_even_zmodTwo`
     proves that component sum is even for every factor. This initially
     suggested seeking a graph-specific factor with odd component sum, but
     that proposed terminal is now **ruled out**, not merely open. In a regular
     square-order candidate the defect graph is `(q-1)`-regular; for even `q`
     this is odd-regular, so the handshaking lemma makes every connected defect
     component even-order. The `PROVEN` theorems
     `binarySquare_regular_defectComponent_card_even` and
     `binarySquare_regular_defectComponent_charpoly_isSquare_zmodTwo` show that
     every component polynomial is itself already a square modulo two. Hence
     every component valuation is even individually, independent of the Gram
     equations. No odd factor sum can be forced consistently. This
     characteristic-polynomial parity lane is useful infrastructure and a
     decisive negative audit, but it cannot be the A-REG terminal; the search
     must return to integral/complex Gram structure or a stronger
     characteristic-two invariant than ordinary factor multiplicity.

     The first return to the integral component quotient is now `PROVEN` and
     uniform.  `sum_componentNeighborCard_mul_eq_sum_ncard_mul_of_regular_comm`
     groups component-neighbor products for any regular commuting defect
     partition, while
     `sum_ncard_mul_componentQuotient_eq_of_ne_of_regular_comm` applies the
     C4-free cross-pair law.  Its square-order specialization
     `binarySquare_regular_componentQuotient_weightedGram_offDiagonal` gives,
     for distinct defect components `c,c'`,

     ```text
     sum_e |e| Q(e,c) Q(e,c') = |c| |c'|.
     ```

     This is graph-specific information unavailable from the component
     characteristic polynomials alone.  The diagonal equality is now also
     `PROVEN`.  The degree-independent transport theorem
     `componentQuotientMatrixReal_sq_apply_of_regular_comm` combines with
     detailed balance in
     `binarySquare_regular_componentQuotient_weightedGram_diagonal`; because
     `D` has degree `q-1`, it gives

     ```text
     sum_e |e| Q(e,c)^2 = |c|^2.
     ```

     Together with the off-diagonal identities this proves entrywise that the
     full weighted Gram matrix is `s s^T`, where `s_c=|c|`.  The rank-one and
     integrality consumers are now also `PROVEN`.
     `binarySquare_regular_componentQuotient_cross_mul` derives proportional
     quotient columns by expanding the weighted squared difference and using
     positivity of every component order.  Summing that proportionality over
     a quotient row gives the exact integral formula

     ```text
     q * Q(e,c) = |c|
     ```

     in `binarySquare_regular_mul_componentQuotient_eq_componentCard`, and
     `binarySquare_regular_dvd_defectComponent_card` concludes `q divides |c|`
     for every defect component.  Thus every quotient row is identical and
     the component orders are `q` times a partition of `q`.  This closes the
     former `A-REG-GRAM` gap but is not itself a contradiction.  The next
     `GAP A-REG-COMPONENTS` is to combine this rigid integral quotient with
     the internal `(q-1)`-regular defect graphs and the coupled proper parity
     set, or derive an additional local block constraint that rules out every
     partition of `q` when `q` is a power of two.

     The partition interpretation is itself now `PROVEN` rather than prose:
     `binarySquare_regular_exists_defectComponent_partition` supplies positive
     integers `m_c` with `|c|=q m_c` and `sum_c m_c=q`, while
     `binarySquare_regular_card_defectComponents_le` gives at most `q`
     components.  The graph-facing theorem
     `binarySquare_regular_mul_componentNeighborCard_eq_componentCard` says
     pointwise that every vertex has exactly `m_c` ambient neighbors in target
     component `c`.  The resulting limitation of the earlier mod-two kernel
     vector is now formal.  `defectComponentIndicatorZModTwo` is the
     characteristic-two component indicator, and
     `binarySquare_regular_adj_mulVec_defectComponentIndicatorZModTwo` proves
     that `A` sends it to the constant vector `m_c`.  Consequently
     `binarySquare_regular_defectComponentIndicator_mem_kernel_of_evenRow`
     puts every even part directly in `ker A`, while
     `binarySquare_regular_add_defectComponentIndicators_mem_kernel` does the
     same for any two parts of equal parity.  Thus disconnected
     component-constant combinations genuinely do account for many extra
     kernel vectors.  In particular the alternating-matrix second vector is
     automatic when there are at least three parts (two have equal parity),
     and for two even parts; only the connected case and the two-odd-part case
     necessarily demand within-component variation.  A successful parity
     terminal must address that split rather than merely reuse nullity greater
     than one.

     Smallest parts now have a uniform graph-level classification, also
     `PROVEN`.  If `m_c=1`, equivalently `|c|=q`, then
     `binarySquare_regular_sizeQ_defectComponent_adj` shows that the induced
     defect component is the clique `K_q`, because it is `(q-1)`-regular on
     `q` vertices.  At the same time
     `binarySquare_regular_card_componentNeighbors_sizeQ_eq_one` says every
     ambient vertex has exactly one `G`-neighbor in `c`.  Thus every unit part
     is a defect clique carrying perfect one-neighbor routing from all of
     `V`; this is the uniform replacement for the order-64 size-eight block
     lemmas.  Distinct vertices of such a unit block have disjoint ambient
     `G`-neighborhoods
     (`binarySquare_regular_sizeQ_component_commonNeighbors_card_zero`).

     The all-unit partition is now excluded for every binary exponent,
     uniformly and in Lean.  In the all-unit case the triangle-free-edge graph
     is 1-regular.  The local C4-free edge identity pairs every remaining edge
     at a vertex inside a triangle, so the ambient regular degree must be odd.
     This contradicts `q = 2^k` throughout the square-order range; the terminal
     is `binarySquare_regular_not_allUnit_of_two_pow`, via the stronger theorem
     `binarySquare_regular_not_allUnit_of_even`.  An earlier, weaker mod-three
     route remains available as
     `binarySquare_regular_not_allUnit_of_two_pow_odd`.  Hence
     `GAP A-REG-COMPONENTS` has been narrowed to mixed partitions only.
     In fact the parity argument is component-local: the `PROVEN` theorem
     `binarySquare_regular_no_sizeQ_defectComponent_of_even` excludes even one
     unit part.  Thus for binary `q`, every remaining normalized part satisfies
     `m_c ≥ 2`; in particular there are at most `q/2` defect components, as
     stated precisely by
     `binarySquare_regular_two_mul_card_defectComponents_le`.  The normalized
     part also has a direct internal meaning:
     `binarySquare_regular_degree_induce_defectComponent_eq_part` proves that
     `G` induced on the component is exactly `m_c`-regular.  Consequently the
     new smallest case `m_c=2` is a disjoint union of cycles on `2q` vertices,
     giving a uniform cycle/intertwiner target rather than an arbitrary
     `2q`-vertex block.  There is already a further `PROVEN` color restriction:
     `binarySquare_regular_triangleFree_degree_even` makes the triangle-free
     degree even at every vertex, while
     `binarySquare_regular_triangleFree_degree_le_part` bounds it by `m_c`.
     Thus on an `m_c=2` block every vertex has triangle-free degree exactly
     zero or two
     (`binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two`).
     The all-or-none propagation along internal ambient cycles is now itself
     `PROVEN`: `triangleFreeNeighbors_subset_componentNeighborFinset` records
     that triangle-free edges cannot leave their defect component, and
     `binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_adj`
     shows that the degree-two color status is identical across every internal
     `G`-edge.  Hence each cycle of `G[c]` is wholly triangle-free or wholly
     triangular.  Packaging these monochromatic cycles with the commuting
     defect block is the next precise subgoal.

13b. **`AT-64-ONLY` — finite component census.** For the first binary case,
     the 16-vertex defect subproblem was reduced to 12 two-factor partitions;
     quotient arguments kill eight, and R-classification plus exhaustive
     computation kills the four survivors. The `[10,6]` cell has Lean-replayed
     LRATs. Thus the seven-component cell is closed at order 64 modulo its
     graph-level assembly. None of these finite classifications proves A-REG
     for arbitrary `k`; certificate/semantic assembly remains paused.

### A5. Nonregular sectors

14. **`PROVEN` — uniform operator/counting layer.** The nonregular identity
    `adjMatrix_sq_eq_degreePredDiagonal_add_ones_sub_secondOrderDefect`, its
    commutator formula, tight-edge-cover regularity implications, local branch
    counting, saver/miss ledgers, and clean-high-root obstructions are structural
    and not tied to 49. The high-difference sector also forces
    `(X²-q)^(h-1)` to divide the adjacency characteristic polynomial. The
    scale-free residual theorem
    `exists_squareOrder_residualCharpoly_rootMoments` computes, after removing
    this factor,

    ```text
    p₂ = q³ + 2q + (1-2q)h,
    p₄ = 2q⁴ - q³ + 2q² + (4q+1-2q²)h.
    ```

    Thus real-rootedness/Newton terminals can now be posed uniformly rather
    than separately at orders 49 and 64. The pointwise defect-incidence package
    adds the stronger profile-sensitive laws

    ```text
    (D+I)k = h·1,              deg_D(y) + k(y) = q-1
    ```

    for every low vertex (`squareOrder_sum_highIncidence_over_defectNeighbors_add_self`
    and `squareOrder_defectDegree_add_highIncidence_eq_pred`). These laws now
    localize to every defect-closed low set `S`:

    ```text
    |S| h = Σ_{x∈S} k(x)(q-k(x)).
    ```

    This is `squareOrder_defectClosed_low_incidence_balance`. Since `2k≤q`
    makes `k↦k(q-k)` injective, the proved capstone
    `squareOrder_defectClosed_factorization_or_energy_crosses` gives an
    exhaustive component dichotomy:

    ```text
    h = c(q-c) for some c,
    or there are x,y in one component with
       k(x)(q-k(x)) < h < k(y)(q-k(y)).
    ```

    The first branch is therefore a precise Diophantine terminal, not merely
    an equitable-case heuristic. In the second branch the exact identity

    ```text
    h-k(x)(q-k(x)) = Σ_{z~_D x}(k(z)-k(x))
    ```

    is `squareOrder_highIncidence_energy_laplacian`; the theorem
    `squareOrder_highIncidence_exists_defectNeighbor_strict` proves that a
    below-energy vertex has a defect neighbor of strictly larger incidence,
    while an above-energy vertex has one of strictly smaller incidence. Thus
    the remaining open subbranch is specifically a heterogeneous component
    supporting this forced ascent/descent system. The global low sector also
    has the exact third-moment/Dirichlet budget

    ```text
    Σ_x Σ_{y~_D x}(k(x)-k(y))²
      = 2(h(q²-h)-Σ_x k(x)³),
    hence Σ_x k(x)³ ≤ h(q²-h).
    ```

    These are `squareOrder_lowIncidence_orientedDirichlet_eq_thirdMomentSlack`
    and `squareOrder_sum_low_highIncidence_cube_le`. This identity measures
    heterogeneous variation exactly, but does not by itself exclude the raw
    `q=8` moment profiles. The additional Gram input is now uniform and
    `PROVEN`: if `B` is the vertex-by-high-vertex incidence matrix, then

    ```text
    BᵀB = qI + J,
    ```

    so its columns are independent. After fixing any high base vertex, the
    other `h-1` column differences, and hence the corresponding full adjacency
    row differences, are jointly independent; every such row difference is a
    `-1` eigenvector of the defect adjacency matrix. These are
    `squareOrder_highIncidence_columns_linearIndependent`,
    `squareOrder_highIncidence_columnDifferences_linearIndependent`,
    `squareOrder_highRowDifferences_linearIndependent`, and
    `squareOrder_defect_mulVec_highRowDifference`. The rational, dimension-level
    statement is now explicit as
    `squareOrder_high_card_sub_one_le_finrank_defectShift_ker`:

    ```text
    h - 1 ≤ finrank_ℚ ker(A_D + I).
    ```

    Thus the missing terminal may assume a defect `-1` eigenspace of dimension
    at least `h-1`; the open work is to make that multiplicity incompatible
    with every surviving heterogeneous profile or to identify the further
    graph constraint needed. A second `PROVEN` spectral sector now comes
    directly from the incidence profile. If `ℓ` is the low-sector indicator,
    `k` the high-incidence vector, and `D` the defect adjacency matrix, then

    ```text
    Dℓ = (q-1)ℓ-k,
    Dk = hℓ-k,
    [D²-(q-2)D+(h-q+1)I]k = 0.
    ```

    These are `squareOrder_defect_mulVec_lowIndicatorRat`,
    `squareOrder_defect_mulVec_highIncidenceRat`, and
    `squareOrder_defect_incidence_quadratic`. The quotient polynomial is
    `X²-(q-2)X+(h-q+1)`, with discriminant `q²-4h`. The heterogeneous upgrade
    is also `PROVEN`: two low vertices with different incidences make `ℓ,k`
    linearly independent; their span is invariant with matrix

    ```text
    [ q-1   h ]
    [ -1   -1 ],
    ```

    and `squareOrder_defectIncidenceQuadratic_dvd_defectCharpoly` proves that
    the displayed quadratic divides the full rational defect characteristic
    polynomial. The `-1` sector is likewise upgraded from a finrank bound to
    the factor `(X+1)^(h-1)` by
    `squareOrder_defectMinusOneFactor_dvd_defectCharpoly`. Since

    ```text
    X²-(q-2)X+(h-q+1) = (X+1)(X-(q-1)) + h
    ```

    and `h>0`, the factors are coprime;
    `squareOrder_combinedDefectFactors_dvd_defectCharpoly` proves their product
    divides the full defect characteristic polynomial. The remaining work is
    not merely to construct the residual polynomial: the `q=8` census below
    shows that low-order residual trace/Cauchy bounds are too slack to be a
    terminal. Any useful spectral consumer must encode additional vertex-level
    structure.

15. **`PROVEN-AT-49-ONLY` — complete finite endpoint.** The checked 48-vertex
    construction `boza48_degreeSeven_witness` and the order-49 exclusion assemble
    to `minDegreeForC4_fortyNine_lt_fortyEight` and
    `consecutiveC4StarPlateauAt_fortyEight`. Thus `q = 7` is a genuine drop.
    This is one finite drop, not a refutation of eventual monotonicity.

16. **`PROVEN-AT-49-ONLY` — transported ingredients.** At order 49 the
    campaign proves degree stratification, high-neighborhood matching and
    partition laws, defect-incidence identities, perfect-code behavior in the
    one-high sector, and finite exclusions for the remaining strata. These show
    what a general sector theorem might look like, but several terminal steps
    are certificate-backed and 49-specific.

17. **`AT-64-ONLY` — what transported successfully.** At order 64 the following
    mechanisms remain meaningful and have been exercised:
    
    - the parity kill for appropriate degree/excess strata;
    - first- and second-layer counting and ownership partitions;
    - the defect-Laplacian/commutator route;
    - component-size and component-incidence constraints.

18. **`AT-64-ONLY` — what did not yet transport.** The order-49 canonical
    high-set orbit tables, fixed 40-vertex leaf graph, one-high perfect-code
    terminal, and its SAT family do not directly scale. The order-64 component
    analyses are incomplete as an exhaustive graph-level classification.

19. **`AXIOM A-NONREG` — uniform nonregular exclusion.** For every `k ≥ 3`,
    no nonregular `SquareOrderTightCoreExists (2^k)` exists. A satisfactory
    refinement must consume the parameterized profile from Node 10 and either
    derive a stronger bounded family of profiles or give an analytic terminal
    that works for all admissible `h` and incidence distributions.

20. **`GAP A-NONREG-TERMINALS`.** There is not yet a proposed scalable terminal
    for every high-vertex sector. The most concrete current candidate is to
    combine the exact Dirichlet/third-moment budget with the proved `h-1`
    multiplicity of the defect eigenvalue `-1` and the proved incidence
    charpoly factor of discriminant `q²-4h`. Their coprime product divisibility
    is now proved, but a `q=8` exact census gives strong negative evidence
    against a scalar terminal:

    - the moment equations leave 77 profiles across
      `h ∈ {2,4,6,8,10,12}` (respectively `1,4,12,29,22,9`);
    - exact weight-class defect-edge feasibility kills only seven
      (`h=8: 29→25`, `h=12: 9→6`);
    - all 77 survive the `-1` multiplicity plus defect trace-two/Cauchy budget;
      `BᵀB=qI+J` supplies no additional class-level equation.

    The subsequently proved branchwise incidence law is materially stronger
    than those scalar screens.  The reproducible discovery census
    `square_order_branch_profile_census.py` imposes only its necessary
    multiset-partition consequences at every occurring vertex weight and
    rejects 25 of the 77 profiles, leaving 52, distributed by
    `h=2,4,6,8,10,12` as `1,3,7,18,19,4`.  This is not yet a proof artifact:
    rejection by the relaxation is mathematically sound, but survivors need
    not be realizable and the finite calculation has not been reflected into
    a uniform Lean terminal.

    Claude's first exact vertex-level UNSAT exposed a uniform sub-obstruction,
    now `PROVEN` as
    `squareOrder_highIncidenceCount_add_le_card_high_add_one`: distinct
    vertices satisfy `k(u)+k(v)≤h+1`, since their high-neighbor sets intersect
    in at most one point.  Alone this rejects three arithmetic profiles
    (`77→74`, with `h=4:4→3` and `h=6:12→10`); all three were already among
    the 25 branch-partition rejections, so the combined frontier remains 51.
    The value is a short uniform proof replacing the scout's first finite
    UNSAT and a reusable template for extracting further overlap lemmas.

    Intersecting this branch relaxation with the independent aggregate defect
    weight-class equations (`square_order_combined_profile_census.py`) rejects
    one further profile, `h=12`, `(n₀,…,n₄)=(1,0,48,0,3)`, leaving 51 profiles
    distributed as `1,3,7,18,19,3`.  More revealingly, every one of the 52
    branch survivors admits an actual single-center transversal code, and the
    global pairwise-balanced high-incidence design rejects nothing new beyond
    the branch screen.  Therefore the missing obstruction must couple branch
    systems at different centers (or couple them to the same realized `D`),
    rather than strengthen one-center collision counting alone.

    The incidence quadratic is already forced by the same pointwise
    `(D+I)k=h1` system; its two roots consume only `q²-2q+2-2h` of the defect
    square trace, leaving a large residual budget at `q=8`. Thus the revised
    immediate GAP is **vertex-level structure**, not more low-order spectral
    bookkeeping: branch partitions, induced matching/miss constraints, or a
    new uniform relation coupling `D` back to common-neighbor ownership in
    `G`. The basic design interface for that coupling is now `PROVEN`:

    - `not_defectAdj_of_mem_squareOrderDefectOwnerBlock`: every original
      neighborhood is independent in `D`;
    - `not_defectAdj_iff_existsUnique_squareOrderDefectOwner`: every distinct
      `D`-nonedge pair lies in exactly one original neighborhood;
    - `squareOrder_card_defectOwnerBlock_eq_or_succ`: all owner blocks have
      size `q` or `q+1`.
    - `squareOrder_defectBranches_biUnion_eq_nonneighbors` and
      `squareOrder_defectBranches_pairwise_disjoint`: for every fixed `u`, the
      punctured branches `N_G(z)\{u}` indexed by `z∈N_G(u)` form an exact
      disjoint partition of `(V\{u})\N_D(u)`.
    - `squareOrder_card_largeDefectBranches_eq_highIncidence`: those branches
      have size `q-1` or `q`, and exactly `k(u)` of them have size `q`.
    - `card_neighbors_inter_squareOrderDefectBranch_le_one`: every vertex
      distinct from a branch owner has at most one original neighbor inside
      that branch, so non-owner vertices route as partial transversals.
    - `squareOrder_card_highNeighbors_inter_defectNonneighbors_eq`: if `u` is
      low, `v` is high, and `u,v` are nonadjacent in `G`, then `v` has exactly
      `q` neighbors in the branch union at `u`; together with the preceding
      one-per-branch cap and the `q` branches at a low owner, this is the
      aggregate perfect-transversal constraint (and the incidence theorem
      supplies the unique remaining neighbor on the `D`-neighbor side).
    - `squareOrder_card_highNeighbors_inter_defectBranch_eq_one` upgrades that
      count pointwise: under the same hypotheses, for every `z∈N_G(u)`, the
      high vertex `v` has exactly one neighbor in `N_G(z)\{u}`. Thus routing
      through the branch system at a low center is a literal perfect
      transversal.
    - `squareOrder_sum_highIncidence_over_defectBranch` refines the scalar
      equation branchwise: for low `u` and `z∈N_G(u)`, the sum of high-incidence
      weights `k(x)` over `x∈N_G(z)\{u}` is
      `h-k(u) + (if z is high then q else 0)`.  Hence every small branch has
      weight `h-k(u)` and every large branch has weight `h-k(u)+q`, a constraint
      invisible to the earlier weight-class defect-edge census.
    - `squareOrder_card_noncenterHighNeighbors_of_mem_defectBranch` identifies
      the pointwise code multiplicities: for `x∈N_G(z)\{u}`, exactly
      `k(x)-1_[z high]` high neighbors of `x` are nonadjacent to `u`.  The only
      high common neighbor of `x,u` that was removed is the owner `z`, when it
      is high.  This is the proved bridge from weighted branches to a family of
      transversal words with prescribed symbol multiplicities.
    - The first proved cross-center gluing laws are
      `mem_squareOrderDefectBranch_comm_of_adj_owner`,
      `card_inter_squareOrderDefectBranch_le_one_of_owner_ne`, and
      `card_inter_squareOrderDefectBranch_same_owner`: membership through one
      owner is reciprocal between centers; branches with different owners
      intersect in at most one point; branches with the same owner `z` at two
      distinct centers overlap in exactly `deg(z)-2` points.  Any next model
      must realize these shared-owner overlaps globally, not instantiate the
      local transversal codes independently.
    - `card_inter_squareOrderDefectBranch_eq_if_owner_ne` makes the
      different-owner case exact and couples it back to `D`: for centers
      `u,v` incident to distinct owners `z,w`, the two branches meet once iff
      `z,w` are nonadjacent in `D` and neither cross-edge `u-w` nor `v-z`
      exists; otherwise they are disjoint.  This is the first explicit
      cross-center equation involving both graphs and is the intended next
      input to the vertex-level scout.
    - `squareOrder_defectBranchGrid_biUnion_eq_inter_nonneighbors` and
      `squareOrder_sum_card_defectBranchGrid_eq` assemble the cells for two
      centers: their disjoint owner-pair grid covers exactly the intersection
      of the two defect-nonneighbor regions, and its double sum of cell sizes
      is exactly that region's cardinality.  Hence the same-owner
      `deg(z)-2` cells and the off-diagonal zero/one formula now feed a single
      exact two-center counting equation rather than isolated local facts.
    - `squareOrder_sum_card_defectBranchGrid_add_degrees` closes the other side
      of that equation:
      `Σ_{z∈N(u),w∈N(v)} |B_u(z)∩B_v(w)| + deg_D(u)+deg_D(v)+2`
      equals
      `|V| + |N_D(u)∩N_D(v)| + 2·1_[uv∈E(D)]` for `u≠v`.
      Thus every cell can be expanded by the proved owner formula while the
      total is expressed entirely through local data of `D`; this is the
      current strongest uniform cross-center constraint.
      For distinct low centers the normalized theorem
      `squareOrder_sum_card_defectBranchGrid_add_two_mul_degree` reads
      `cellSum + 2q = q² + |N_D(u)∩N_D(v)| + 2·1_[uv∈E(D)] + k(u)+k(v)`,
      eliminating both defect degrees through `deg_D+k=q-1`.  This is the
      form to impose directly in the surviving `q=8` vertex-level models.
    - `squareOrder_card_commonDefect_add_highIncidences_le` is the first
      obstruction extracted from this grid: for distinct low centers with
      `¬D.Adj u v`,
      `|N_D(u)∩N_D(v)| + k(u)+k(v) ≤ q`.  The proof isolates the unique common
      original owner, whose diagonal cell has size at most `q-1` and whose
      off-diagonal row and column vanish; the remaining `(q-1)²` cells have
      size at most one.  This exact two-center inequality is now an input to
      the `q=8` simultaneous `G/D` scout; its finite profile impact is not yet
      classified.
      The sharper theorem
      `squareOrder_card_commonDefect_add_highIncidences_le_pred_add_commonHigh`
      retains the owner type:
      `commonD+k(u)+k(v) ≤ q-1+|N_G(u)∩N_G(v)∩H|`.  Thus the budget is only
      `q-1` when the unique owner is low and rises to `q` exactly for a high
      owner; the preceding owner-free statement is a corollary.
      Its equality case is `PROVEN` as
      `squareOrder_maxHighIncidence_not_defectAdj_rigidity`: if two low
      vertices both attain `2k=q` and are nonadjacent in `D`, their defect
      neighborhoods are disjoint and their unique common original owner is
      high.  At `q=8`, every nonadjacent pair of `k=4` lows therefore has
      disjoint `D`-neighborhoods and shares exactly one high neighbor.
      `squareOrder_card_commonHigh_of_maxHighIncidence` completes the
      adjacency dictionary on this sector: for distinct maximal-incidence
      lows, the common-high count is `0` on a `D`-edge and `1` on a
      `D`-nonedge.  Hence at `q=8` the induced `D` graph on the `k=4` lows is
      exactly the disjointness graph of their four-subsets of the `h` highs;
      this supplies a much smaller coupled-design scout than the full graph.
      One level below, the `PROVEN` theorems
      `squareOrder_card_commonDefect_le_commonHigh_of_incidence_add_eq_pred`
      and `squareOrder_card_commonHigh_eq_one_of_incidence_add_eq_pred` say:
      for a low `D`-nonedge with `k(u)+k(v)=q-1`, `commonD≤commonHigh≤1`, and
      positive common defect degree forces the unique original owner to be
      high.  At `q=8` this is the coupled rule for every `k=4/k=3` pair.

    Thus the complement pairs of `D` admit a unique decomposition into a
    symmetric family of owner blocks. The next GAP is a classification or
    obstruction for this weighted symmetric neighborhood design, not merely
    for `D` alone. A vertex-level `q=8` model search is being used only to
    discover the first such obstruction, not as a certificate terminal. This
    is the largest mathematical hole in the binary branch. Generalizing
    certificate families is not a substitute for finding these statements.

### A6. Binary branch capstone

21. **`AXIOM A-CAPSTONE`.** Node 10 + A-REG + A-NONREG imply
    `BinarySquareOrderTightCoreExclusion`.

22. **`PROVEN` conditional finish.** From A-CAPSTONE,
    `not_erdos85Question_of_binarySquareOrderTightCoreExclusion` proves the
    desired negation of Erdős 85.

## B. Odd-prime / plane-order branch

This branch is strategically primary as a theory of where drops occur, but it
currently has two uniform jaws missing. Its `q = 7` instance is complete.

### B1. The `q² - 1` existence jaw

23. **`PROVEN-AT-49-ONLY`.** `boza48_degreeSeven_witness` gives a 7-regular
    C4-free graph on 48 vertices. Its known Cayley description on
    `Z24 semidirect Z2` has been exhaustively checked.

24. **`PROVEN-COMPUTATIONALLY` — Cayley route exhausted at 9 and 11.** The
    Cayley-Sidon campaign is exhaustive over all groups of orders 80 and 120:
    all 52 groups of order 80 and all symmetric 9-subsets at `q=9`; all 47
    groups of order 120 at `q=11`. No q-regular C4-free Cayley graph occurs.
    At `q=13`, the non-solvable candidate `PSL(2,7)` is exhausted, but not all
    groups of order 168. The mechanism is structural: a commuting generator
    pair creates a C4, while a symmetric odd-size generating set contains an
    involution and demands a large pairwise-noncommuting family. Artifacts are
    stored under `erdos85-cayley-sidon/`.

24a. **`AXIOM B-CAYLEY-DEAD`.** For every odd prime power `q ≥ 9`, no
     q-regular C4-free Cayley graph exists on `q²-1` vertices. This is proved
     computationally at `q=9,11`, partially tested at 13, and open uniformly.
     Even if proved, it excludes only Cayley constructions; B-EXIST would then
     require a genuinely non-vertex-transitive mechanism.

25. **`GAP B-EXIST`.** No precise uniform construction is currently known for
    C4-free minimum-degree-`q` graphs on `q² - 1` vertices for an unbounded set
    of odd prime powers. Candidate research directions are:
    
    - a geometric/incidence interpretation of the 48-vertex witness;
    - a non-Cayley lift or quotient of a polarity/incidence graph; or
    - a bipartite-incidence surgery with a proved degree-repair rule.

    The q=7 witness now supplies a precise non-Cayley construction candidate,
    recorded in `ODD_EXISTENCE_GEOMETRY.md`. Its defect graph has `q-1=6`
    components of order `q+1=8`, and the original graph is a matching lift of
    the quotient `J₆+P`: one matching inside each fiber, one between ordinary
    fiber pairs, and two between the pairs selected by a fixed-point-free
    involution `P`. This motivates **AXIOM B-NEAR-LATIN-LIFT**: collision-free
    lifts of this `(q-1)×(q+1)` form exist for an unbounded set of odd prime
    powers. General lifts are not Cayley, so the q=9/11 Cayley exhaustions do
    not test the axiom. The decisive smallest experiment is existence at q=9.

    Small orders sharply constrain the gap: existence is impossible at `q=3`
    and `q=5` because the required edge counts exceed `ex(8,C4)=11` and
    `ex(24,C4)=59`, respectively. The only known odd instance is `q=7`;
    nothing above 7 is known either way beyond Cayley-death at 9 and 11.

    Before this gap is replaced by an explicit construction statement, the
    odd branch cannot be a proof of infinitely many drops.

### B2. The `q²` nonexistence jaw

26. **`PROVEN-AT-49-ONLY`.** The `q = 7` endpoint is excluded and produces the
    drop at `48 -> 49` (Node 15).

27. **`AXIOM B-NONEXIST`.** For an unbounded set `Q` of odd prime powers,
    `¬ C4FreeMinDegreeWitness (q²) q` for every `q ∈ Q`.

28. **`PROVEN` partial uniform structure.** The normalization, parity,
    counting, defect-operator, clean-sector, branch-partition, and spectral
    lemmas used at 49 are formulated substantially more generally. They are
    necessary inputs to B-NONEXIST, not an assembly of it.

29. **`GAP B-CLASSIFY`.** The regular/parameterized-nonregular split is
    uniform, but there is no analytic terminal covering every resulting
    square-order profile for odd `q`; odd parity changes which profiles survive.

### B3. Odd branch capstone

30. **`AXIOM B-COFINAL`.** There is an unbounded set `Q` of odd prime powers
    on which both B-EXIST and B-NONEXIST hold.

31. **`PROVEN` conditional finish.** B-COFINAL instantiates
    `CofinalPlaneOrderDropFamily`, hence
    `not_erdos85Question_of_cofinalPlaneOrderDropFamily` proves the desired
    negation.

## C. Exact second-order boundary theory: supporting, not the root pincer

The long exact-boundary program concerns regular graphs on
`d(d-1)+3` vertices. It supplies powerful structural technology and may yield
terminals for A-REG/B-NONEXIST, but its order differs from the square-order
pincer. It must not silently be treated as the missing square-order theorem.

32. **`PROVEN` — exact-boundary defect structure.** At the regular exact
    boundary the defect graph is 2-regular, hence decomposes into cycles; cross
    component common-neighbor counting, quotient balance, Gram identities, and
    equal-size excess formulas are formalized.

33. **`PROVEN` — odd exact-boundary parity kill.** The odd-degree exact
    second-order boundary is excluded (`containsC4_of_odd_secondOrder` and the
    clean package `odd_secondOrder_boundary_package`). This explains why the
    tempting Boza congruence family cannot supply a pincer at that offset.

34. **`PROVEN` — even-boundary large-prime sector.** For even `d ∉ {4,12}`,
    `false_of_secondOrder_largePrime_sector` and
    `secondOrder_no_largePrime_dvd_component_order` exclude large-prime defect
    components and force all defect-cycle lengths to be `d`-smooth.

35. **`PROVEN` — minimum-layer dichotomy and descent.** The minimum-layer
    Gram/design equation and `secondOrder_minimumLayer_descent` produce a
    smaller regular C4-free graph at its own exact boundary. The extension
    theory gives the strict gap theorem `secondOrder_minimumLayer_strict_gap`;
    the saturated `d = 124` residual is killed by the hard-sector terminal.

36. **`AXIOM C-BOUNDARY`.** Complete the remaining exact even-boundary cases,
    including the known residual degrees/seeds and the unsaturated descent
    branches, by a uniform well-founded descent or explicit base terminals.

37. **`GAP C-TO-SQUARE`.** No theorem currently turns the exact-boundary
    classification into square-order nonexistence for all binary or odd prime
    powers. Such a bridge would be valuable only if stated precisely; order
    similarity alone is not a proof.

## D. Plateau-core route and why it is secondary to the pincer

38. **`PROVEN` — plateau equivalences.** The Ramsey inverse and plateau-core
    modules identify a one-step drop with a consecutive star-Ramsey plateau and
    with existence of a `C4PlateauCore`. These are exact reformulations.

39. **`PROVEN` — normalization/localization.** Plateau cores have a tight
    vertex cover, compact normal forms, componentwise nonextension, and several
    order/defect bounds. These results constrain arbitrary drops.

40. **`GAP D-GLOBAL`.** A classification of all sufficiently large plateau
    cores is not known. Proving their eventual absence would prove Erdős 85
    *positive*, contrary to the current pincer target; constructing cofinally
    many via Branch A or B proves it false. The outline therefore uses plateau
    cores as diagnostics and normalization tools, not as an unstated final step.

## E. Dependency tree and work allocation

The shortest current proof tree is:

```text
¬ Erdos85Question                                      [conditional root]
└── BinarySquareOrderTightCoreExclusion                 [AXIOM A-CAPSTONE]
    ├── q²-1 characteristic-two witnesses              [PROVEN]
    └── no square-order tight core for q = 2^k
        ├── regular / parameterized nonregular split     [PROVEN]
        ├── regular-sector exclusion                    [AXIOM A-REG]
        └── nonregular-sector exclusion                 [AXIOM A-NONREG]
            └── scalable terminals for every sector     [GAP]
```

The parallel odd-prime tree is:

```text
¬ Erdos85Question                                      [conditional root]
└── cofinal odd plane-order drop family                [AXIOM B-COFINAL]
    ├── q²-1 witnesses for unbounded odd q              [GAP B-EXIST]
    └── q² nonexistence for the same q                  [AXIOM B-NONEXIST]
        └── exhaustive uniform core classification      [GAP B-CLASSIFY]
```

According to the top-down rule, the next mathematical work should target, in
order:

1. `A-NONREG-TERMINALS`: strengthen or consume the parameterized incidence
   profile, using 49/64 only as experiments, until all admissible nonregular
   cores have analytic terminals.
2. `A-REG`: isolate and attack the regular binary square-order theorem.
3. In parallel, `B-EXIST`: turn the 48-vertex witness into a precise geometric
   construction conjecture or record a decisive obstruction.

Certificate generation, LRAT promotion, and graph-to-CNF semantic bridges are
paused until one of these parent nodes explicitly requires a finite endpoint.

## F. What the drop-family hypothesis predicts

41. **Observed finite pattern.** Among the tested odd plane orders, both jaws
    are present only at `q=7`, producing the proved drop `48 -> 49`. The
    existence jaw is impossible at `q=3,5`; hence the same mechanism cannot
    create drops at `8 -> 9` or `24 -> 25`. At `q=9,11`, the Cayley jaw is
    computationally absent, while general non-Cayley existence remains open.

42. **Falsifiable binary prediction.** The characteristic-two construction
    predicts drops at

    ```text
    (2^(2k)-1) -> 2^(2k),   k ≥ 3,
    ```

    beginning with `63 -> 64`, exactly when the square-order exclusion jaw is
    proved. A single C4-free minimum-degree-`2^k` graph on `2^(2k)` vertices
    would falsify that instance of A-REG/A-NONREG; infinitely many such
    counterexamples would refute the proposed binary route.

43. **Falsifiable odd-family question.** Either a genuinely non-Cayley family
    exists for unbounded odd `q`, or the isolated `q=7` witness is exceptional.
    The next decisive evidence is an explicit construction or full
    nonexistence result at `q=9`; further Cayley searches alone cannot decide
    this dichotomy.

## G. Completion checklist

The campaign may claim “Erdős 85 is false” only after all items in one column
below are proved and the final theorem is cold-built with an axiom audit:

| Binary route | Odd-prime route |
|---|---|
| Uniform `q²-1` witnesses — done | Uniform/cofinal `q²-1` witnesses — open |
| Parameterized square-core split — done | Parameterized square-core split — done |
| Regular square-core exclusion — open | Square-order nonexistence — open |
| Nonregular square-core exclusion — open | Same unbounded set on both jaws — open |
| `BinarySquareOrderTightCoreExclusion` | `CofinalPlaneOrderDropFamily` |
| `not_erdos85Question_of_binarySquareOrderTightCoreExclusion` | `not_erdos85Question_of_cofinalPlaneOrderDropFamily` |

The finite `48 -> 49` drop, exact-boundary case closures, and order-64 census
results are verified progress, but none alone checks every box in either
column.
