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
     triangular.  The cycle decomposition is exposed in the exact form needed
     by the older cycle APIs:
     `binarySquare_regular_sizeTwoPart_exists_cycle_of_internalComponent`
     produces a spanning simple closed walk for every connected piece of
     `G[c]` and proves its length is not four.  Packaging these monochromatic
     cycles with the defect block is now complete at the abstract matrix
     level: `binarySquare_regular_sizeTwoPart_commuting_regular_blocks`
     supplies simultaneously the internal ambient degree `2`, internal defect
     degree `q-1`, and exact integer adjacency commutation.  The remaining
     cycle-level equitable reduction is also `PROVEN` in
     `binarySquare_regular_sizeTwoPart_cycleQuotient`: the defect-over-cycle
     quotient has row sum `q-1`, satisfies detailed balance weighted by cycle
     lengths, and those lengths sum to `2q`.  Its support is genuinely
     irreducible, not merely assumed connected:
     `binarySquare_regular_sizeTwoPart_cycleQuotient_irreducible` lifts paths
     in the connected defect block to positive-entry paths in the quotient.
     The first graph-specific restriction beyond those abstract quotient laws
     is now formal too.  `not_secondOrderDefect_adj_of_commonNeighbor` forbids
     a defect edge whenever a common ambient neighbor is exhibited, and the
     cycle decomposition theorem records its consequence: every non-wrapping
     distance-two pair on an internal cycle is a defect nonedge.  The two
     basepoint-crossing cases are supplied by
     `not_secondOrderDefect_adj_cycle_wraparound_distanceTwo`.  Thus the full
     `±2` cyclic diagonals are absent from every diagonal defect block.  This
     now feeds a quantitative quotient inequality rather than remaining a
     pattern observation: for every internal cycle `a` of length at least five,
     `binarySquare_regular_sizeTwoPart_cycleQuotient_diagonal_le` proves
     `Q(a,a) ≤ |a|-3`.  Combining this with the row sum gives the `PROVEN`
     cross-mass inequality

     ```text
     q + 2 ≤ |a| + sum_{b≠a} Q(a,b),
     ```

     in `binarySquare_regular_sizeTwoPart_cycleQuotient_cross_mass`.

     More importantly, the order-64 pair-complement phenomenon is now uniform
     in `q`, not a finite-instance artifact.  The `PROVEN` theorem
     `binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj` says that for
     distinct `u,v` in a normalized size-two component `c`,

     ```text
     some ambient vertex has exactly {u,v} as its c-neighbors
       iff u and v are nonadjacent in D.
     ```

     Thus the `q²` ambient vertices select precisely the edges of the
     complement of the `(q-1)`-regular defect graph on `2q` vertices.  This is
     the scalable pair-design interpretation previously available only in the
     order-64 sixteen-block modules.  The selector is unique, not merely
     existent: `binarySquare_regular_sizeTwoPart_existsUnique_pair_iff_not_defectAdj`
     upgrades the equivalence using the exact-one common-neighbor law.  Hence
     the ambient vertices and complement edges form an exact bijective design;
     `binarySquare_regular_sizeTwoPart_componentNeighborFinset_injective`
     records the injective half directly as a reusable selector-map theorem.
     The range theorem
     `binarySquare_regular_sizeTwoPart_componentNeighborFinset_range` and the
     explicit equivalence
     `binarySquare_regular_sizeTwoPart_selector_equiv_nondefectPairs` package
     the full statement: ambient vertices are canonically equivalent to the
     non-defect two-element pairs in `c`.
     This is the concrete interface for decomposing the complement edges into
     regular layers indexed by source defect components.  The `PROVEN` theorem
     `binarySquare_regular_selector_incidence_from_component` supplies the
     degree calculation: a source component of order `q m` contributes exactly
     `m` selected pairs incident with each vertex of `c`.  Thus its selected
     pairs form a spanning `m`-regular layer, and the source-component layers
     partition the complement of `D[c]` through the selector bijection.
     There is also a Kneser-type constraint, now `PROVEN` in
     `componentNeighborFinset_disjoint_of_secondOrderDefect_adj`: endpoints of
     every defect edge have disjoint selectors in every target component.
     The size-two capstone
     `binarySquare_regular_sizeTwoPart_exists_selectorEquiv_maps_defectAdj_to_disjoint`
     packages this with the equivalence above, representing `D` on the
     complement edges of `D[c]` with defect adjacency mapping to pair
     disjointness.  Any surviving weighted cycle quotient must therefore lift
     to this simultaneous regular-factor/disjointness representation.
     In fact the simultaneous representation is exact, not one-way:
     `secondOrderDefect_adj_iff_componentNeighborFinset_disjoint_forall`
     proves for distinct ambient vertices `x,y` that

     ```text
     D.Adj x y  iff  their selectors are disjoint in every defect component.
     ```

     Thus, when size-two coordinates are present, `D` is recovered as the
     intersection of their Kneser-style disjointness relations together with
     the analogous relations from the remaining component coordinates.
     The complementary ownership law is also `PROVEN`:
     `not_secondOrderDefect_adj_iff_existsUnique_component_selector_inter_nonempty`
     says that every distinct non-defect pair has selector intersection in
     exactly one component coordinate.  This coordinate is precisely the
     defect component containing the pair's unique common ambient neighbor.
     Hence the simultaneous factor model is an exact owner-colored design:
     defect pairs are disjoint in all coordinates, while every other pair
     overlaps in one and only one coordinate.  This is the new local law to
     impose on the rectangular cycle intertwiners, beyond their row sums and
     weighted commutation identities.
     The owner coloring has uniform pointwise intersection numbers, not just a
     global pair count.  The `PROVEN` theorem
     `binarySquare_regular_crossComponent_ownerCoordinate_card` states that
     for `x` in source part `e`, a distinct target part `f`, and owner
     coordinate `c`, the number of vertices of `f` whose unique common
     neighbor with `x` lies in `c` is exactly

     ```text
     m_c m_f.
     ```

     This refines the weighted Gram product formula into a local orthogonal-
     array law.  In particular every cross-component row has the same owner
     distribution, determined solely by the normalized component parts.
     Its diagonal companion is `PROVEN` in
     `binarySquare_regular_sameComponent_ownerCoordinate_card`: for `x∈e`,
     owner coordinate `c` routes exactly `m_c(m_e-1)` other vertices of `e`.
     The two theorems therefore give the complete pointwise table

     ```text
     # {y∈f, y≠x : owner(x,y)=c} = m_c (m_f - delta(e,f)).
     ```

     This is an integral association-scheme-style constraint on every
     component partition, valid uniformly in `q`.
     The relation is now promoted to a first-class graph:
     `componentOwnerGraph G D c` joins exactly the pairs owned by `c`.
     `not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj`
     states that the owner graphs edge-partition the complement of `D`, and
     `binarySquare_regular_componentOwnerGraph_degree` proves that the graph
     for a normalized part `m_c` is exactly `m_c(q-1)`-regular.  This exposes
     adjacency matrices and spectra of the owner-color classes as the next
     uniform obstruction layer.  That layer is now algebraically connected to
     the original operator: `defectComponentDiagonalMatrix` is the diagonal
     projector `P_c`,
     `adjMatrix_mul_defectComponentDiagonalMatrix_mul_adjMatrix_apply` proves
     the component Gram-entry formula, and the `PROVEN` identity

     ```text
     Adj(Owner(c)) = A P_c A - m_c I
     ```

     is `binarySquare_regular_componentOwnerGraph_adjMatrix_eq`.
     Because both `A` and `P_c` commute with `D`, the `PROVEN` theorem
     `binarySquare_regular_componentOwnerGraph_adjMatrix_comm_defect` gives
     `Adj(Owner(c)) D = D Adj(Owner(c))` for every component color.  Thus each
     owner graph preserves every defect-component eigenspace, providing a
     simultaneous integral spectral constraint beyond the scalar part table.
     The colors also resolve the whole complement operator exactly.  The
     `PROVEN` identity
     `sum_componentOwnerGraph_adjMatrix_eq_ones_sub_one_sub_secondOrderDefect`
     is

     ```text
     sum_c Adj(Owner(c)) = J - I - D.
     ```

     Hence `J-I-D` is decomposed into commuting-with-`D`, regular integral
     color operators of degrees `m_c(q-1)`, with the local intersection table
     above fixing their component quotients.  More precisely, the `PROVEN`
     theorem `binarySquare_regular_componentOwnerGraph_componentQuotient`
     computes the quotient of color `c` exactly:

     ```text
     Q_c(e,f) = m_c (m_f - delta_{ef}).
     ```

     Consequently its action on component-constant vectors is rank one minus
     `m_c I`: it has eigenvalue `m_c(q-1)` on the all-ones vector and
     eigenvalue `-m_c` on the codimension-one subspace
     `sum_f m_f v_f = 0`.  Thus the component quotient already realizes the
     lower spectral bound `-m_c`.  That bound is now `PROVEN`, not merely
     prospective: `binarySquare_regular_componentOwnerGraph_adjMatrix_add_posSemidef`
     proves over the integers that

     ```text
     Adj(Owner(c)) + m_c I = A P_c A >= 0.
     ```

     Hence every owner-color eigenvalue is at least `-m_c`, while the quotient
     supplies a full component-constant equality space.  Classifying the
     additional equality directions inside components is the next uniform
     obstruction layer.  The equality condition is also now explicit:
     `binarySquare_regular_componentOwnerGraph_shifted_quadratic_eq_sum_sq`
     writes the shifted quadratic form as

     ```text
     v^T(Adj(Owner(c)) + m_c I)v = sum_{z in c} (Av)_z^2,
     ```

     and `binarySquare_regular_componentOwnerGraph_shifted_quadratic_eq_zero_iff`
     proves that equality holds exactly when `(Av)_z=0` throughout component
     `c`.  Thus any extra `-m_c` eigendirection is forced into a concrete
     componentwise adjacency-kernel condition.  The whole quotient equality
     space has now been lifted integrally.  For coefficients `a_e`, define
     `v(x)=a_[x]_D`; `defectComponentLinearCombinationInt_apply` verifies this
     pointwise description, while
     `binarySquare_regular_adj_mulVec_defectComponentLinearCombinationInt`
     proves

     ```text
     Av = (sum_e Q(e0,e) a_e) 1.
     ```

     Hence every weighted-zero assignment lies in `ker A`, and the `PROVEN`
     theorem
     `binarySquare_regular_componentOwnerGraph_mulVec_linearCombinationInt`
     makes it a simultaneous eigenvector

     ```text
     Adj(Owner(c)) v = -m_c v
     ```

     for every color `c`.  The dimension statement is now `PROVEN` over
     `ℚ`, not merely inferred from the integral vectors.  The linear map
     `binarySquareComponentConstantKernelMap` embeds the kernel of one
     component-quotient row into `ker A`; its injectivity and the nonvanishing
     of that quotient row give

     ```text
     number of D-components - 1 <= dim_Q ker A
     ```

     in
     `binarySquare_regular_card_components_sub_one_le_finrank_adj_kernel`.
     The lower bound is now sharp.  The `PROVEN` representation theorem
     `binarySquare_regular_adj_kernel_vector_component_representation` shows
     conversely that every rational adjacency-kernel vector is constant on
     each defect component and that its representative coefficients
     annihilate the same quotient row.  The reverse injection
     `binarySquareAdjKernelToComponentRowKernel` therefore gives the capstone

     ```text
     dim_Q ker A = number of D-components - 1
     ```

     in
     `binarySquare_regular_finrank_adj_kernel_eq_card_components_sub_one`.
     Thus a four-component order-64 candidate has ambient adjacency nullity
     exactly three: the global spectral ledger has no additional zero-root
     multiplicity available beyond the component-constant directions.
     This kernel is not merely an ambient spectral statistic.  The rational
     owner identity is now `PROVEN` in
     `binarySquare_regular_componentOwnerGraph_adjMatrix_eq_rat`, and
     `binarySquare_regular_componentOwnerGraph_mulVec_of_adj_mulVec_eq_zero_rat`
     shows that every `v in ker A` satisfies

     ```text
     Adj(Owner(c)) v = -m_c v
     ```

     simultaneously for every owner color `c`.  The inclusion is packaged as
     `binarySquareAdjKernelToOwnerBottomKernel`; its injectivity combines with
     the component-nullity bound in
     `binarySquare_regular_card_components_sub_one_le_finrank_owner_bottom`.
     Hence every owner color has bottom-eigenvalue multiplicity at least
     `#components-1`, realized by one common subspace.  In the q=8 all-two
     branch, all four owner colors therefore share a common `-2` eigenspace
     of dimension at least three.  This is the precise simultaneous
     multiplicity constraint that the next finite spectral consumer may use.
     The common subspace is now known exactly, not only from below.  The
     `PROVEN` resolution

     ```text
     sum_c (Adj(Owner(c)) + m_c I) = A_G^2
     ```

     is `binarySquare_regular_sum_shifted_componentOwnerGraph_adjMatrix_eq_sq_rat`,
     and symmetry of `A_G` yields the `PROVEN` equivalence

     ```text
     A_G v = 0  iff  for every c, Adj(Owner(c)) v = -m_c v
     ```

     in `binarySquare_regular_adj_mulVec_eq_zero_iff_forall_owner_bottom_rat`.
     Thus in the q=8 all-two branch the intersection of the four `-2`
     eigenspaces has dimension exactly three.  This does **not** by itself
     eliminate any internal order-16 two-factor cycle partition: those cycle
     spectra belong to the diagonal induced graphs, not to the ambient
     adjacency kernel.  A valid finite consumer must couple the owner colors
     (or their ranges) rather than apply the nullity statistic to each
     diagonal cycle graph separately.

     Minimum defect components interact sharply with this bound.  The
     `PROVEN` theorem
     `binarySquare_regular_sizeQ_component_not_componentOwnerGraph_adj`
     says that every defect component of order exactly `q` is an independent
     set in every owner-color graph.  Since color `c` is
     `m_c(q-1)`-regular on `q^2` vertices and has least eigenvalue at least
     `-m_c`, Hoffman's ratio bound predicts

     ```text
     alpha(Owner(c)) <= q,
     ```

     and this is now `PROVEN`.  The reusable theorem
     `hoffman_card_bound_of_shifted_adjMatrix_posSemidef` establishes
     `(k+tau)|S| <= tau|V|` directly over integral adjacency matrices;
     `binarySquare_regular_componentOwnerGraph_indepSet_card_le` specializes
     it to `|S| <= q`.  Finally,
     `binarySquare_regular_sizeQ_component_isMaximumIndepSet_componentOwnerGraph`
     proves that every order-`q` defect component is a maximum coclique
     attaining equality simultaneously in every nonzero owner color.
     The equality partition itself is now `PROVEN`, not merely predicted:
     `binarySquare_regular_sizeQ_component_centeredIndicator_mulVec_eq_zero`
     puts the centered component indicator in the `-m_c` eigenspace, and
     `binarySquare_regular_sizeQ_component_ownerIndicator_mulVec` gives the
     entrywise equitable law

     ```text
     |N_{Owner(c)}(x) intersect e| = 0   if x is in e,
                                    m_c otherwise.
     ```

     Thus every order-`q` defect component is simultaneously an equitable
     Hoffman cell for every owner color.  The next GAP is to combine two or
     more of these simultaneous equitable partitions (or prove that every
     component has order `q`) to contradict the self-indexed owner design for
     `q >= 8`.
     The local cross-color factor interface needed for that combination is
     also `PROVEN`.  In `Erdos85HoffmanEqualityCross`,
     `componentOwnerGraph_componentNeighborFinset_disjoint` says that
     distinct owner colors have disjoint neighbor slices in every target
     defect component, while
     `binarySquare_regular_sizeQ_component_ownerNeighborSlice_card` says that
     an outside vertex has exactly `m_c` color-`c` neighbors in every
     order-`q` target component.  Consequently, between any two order-`q`
     components the owner colors restrict to edge-disjoint `m_c`-regular
     bipartite factors; every normalized-size-one color is a perfect
     matching.  The covering half is exact as well:
     `biUnion_componentOwnerGraph_componentNeighborFinset_eq_component`
     proves that from any vertex outside a target defect component, the union
     of all owner-color slices is the entire target component.  Combined with
     disjointness, the restrictions between distinct order-`q` components are
     therefore genuine edge-colorings of `K_{q,q}` by regular factors of
     degrees `(m_c)_c` (whose sum is `q`), not partial designs.  The remaining
     GAP is now the global classification or parity obstruction for this
     self-indexed simultaneous factorization, not its coverage, local
     regularity, or disjointness.
     The unit-color matching interface is also `PROVEN`:
     `binarySquare_regular_sizeQ_ownerColor_existsUnique_neighbor` gives a
     unique color-`c` neighbor in every order-`q` target whenever `m_c=1`, and
     `binarySquare_regular_sizeQ_ownerColor_existsUnique_crossComponent_neighbor`
     packages this across any ordered pair of distinct order-`q` components.
     Hence each unit color supplies an honest perfect matching (and therefore
     a canonical bijection) between every such pair.  This is now exposed as
     a literal Lean equivalence by the `PROVEN` theorem
     `binarySquare_regular_sizeQ_ownerColor_exists_matchingEquiv`, whose graph
     consists entirely of owner-color edges.  The remaining ODC gap is solely
     the compatibility of this family of component equivalences with its
     self-indexed diagonal cycle blocks.
     One compatibility law is now `PROVEN`: the theorems
     `ownerColor_matchingEquiv_pointwise_ne` and
     `ownerColor_matchingEquiv_ne` show that equivalences carried by distinct
     owner colors disagree at every source point (maximum Hamming distance)
     and are therefore distinct permutations.  Thus each pair of order-`q`
     components carries a sharply separated permutation code indexed by the
     unit owner colors.  The unresolved step must use compatibility across
     three or more component pairs and the diagonal cycle indexing; pairwise
     collision-freeness itself is closed.

     **Strategic scope correction (2026-08-17):** this unit-color/ODC lane is
     valid infrastructure but is *vacuous for binary A-REG*.  The earlier
     `PROVEN` theorem
     `binarySquare_regular_no_sizeQ_defectComponent_of_even` rules out
     `m_c=1` for every even `q`, and
     `binarySquare_regular_two_mul_card_defectComponents_le` gives
     `2 * #components <= q`.  It must therefore not be treated as the main
     route for `q=2^k`.  The corrected `q=8` frontier is packaged in
     `Erdos85OrderSixtyFourRegularPartition`:
     `orderSixtyFour_regular_defectComponent_partition_package` gives
     `m_c>=2`, `sum m_c=8`, and at most four components, while
     `orderSixtyFour_regular_four_defectComponents_all_orderSixteen` proves
     that the maximal four-component branch consists of four 16-vertex
     components.  The three-component census is now `PROVEN` in the
     trace-facing form
     `orderSixtyFour_regular_three_defectComponents_partition_secondMoment`:
     the normalized partition is `4+2+2` or `3+3+2`, equivalently
     `sum m_c^2` is `24` or `22`.  The two-component branch is likewise
     `PROVEN` by
     `orderSixtyFour_regular_two_defectComponents_partition_secondMoment`:
     its partition is `6+2`, `5+3`, or `4+4`, so `sum m_c^2` is respectively
     `40`, `34`, or `32`.  The endpoint strata now use the same interface:
     `orderSixtyFour_regular_four_defectComponents_partition_secondMoment`
     gives moment `16`, and
     `orderSixtyFour_regular_one_defectComponent_partition_secondMoment`
     gives moment `64`.  Thus every possible regular order-64 component count
     has a formal trace-facing moment classification.  The single consumer
     `orderSixtyFour_regular_defectComponent_partition_secondMoment_census`
     packages the complete ledger

     ```text
     sum m_c^2 in {16,22,24,32,34,40,64}.
     ```

     The quadratic centered-owner trace does **not** intersect this ledger.
     The `PROVEN` colorwise calibrations
     `binarySquare_regular_trace_centeredOwnerGram` and
     `binarySquare_regular_trace_centeredOwnerGram_sq` give

     ```text
     tr(C_c)   = m_c q^2(q-1),
     tr(C_c^2) = m_c q^4(q-1) = q^2 tr(C_c).
     ```

     Both are linear in `m_c`, so after summing they see only `sum m_c=q`,
     not `sum m_c^2`.  The global Frobenius resolution is therefore a
     calibration, not a partition obstruction.  Binary A-REG must consume the
     finite ledger through a genuinely nonlinear statistic (a controlled
     cubic/higher trace, rank/equality structure, or the self-indexed block
     geometry); claiming an intersection from the quadratic trace alone would
     be invalid.

     A stronger pairwise-owner identity is also `PROVEN` graph-facing.
     For distinct components `c,e`, put `M_c=A P_c A=O_c+m_c I`.  Orthogonal
     projectors, defect block-diagonality, and uniform component routing give
     the proposed formula

     ```text
     M_c M_e = m_c m_e J,
     hence O_c O_e = O_e O_c.
     ```

     `Erdos85BinarySquareOwnerCross` instantiates the abstract calculation:
     `binarySquare_regular_ownerGram_cross_product` proves the rank-one
     product, and `binarySquare_regular_ownerMatrices_comm` proves the owner
     colors commute.  `Erdos85BinarySquareCenteredOwnerCross` strengthens this
     further.  For `C_c = q M_c - m_c J`, the `PROVEN` theorem
     `binarySquare_regular_centeredOwnerGrams_mul_eq_zero` gives

     ```text
     C_c C_e = 0  for every c != e.
     ```

     Thus the nonconstant centered owner sectors of distinct coordinates are
     not merely commuting: they mutually annihilate integrally.  The live task
     is to combine this orthogonal-sector decomposition with the self-indexed
     diagonal cycle blocks and simultaneous equitable cells.
     For unit colors this matrix identity now has a `PROVEN` combinatorial
     consumer in `Erdos85UnitOwnerRoute`:
     `binarySquare_regular_unitOwnerColors_existsUnique_mixedRoute` states
     that for distinct unit colors `c,d` and every ordered vertex pair `x,z`
     there is exactly one `y` with

     ```text
     (x=y or Owner(c)(x,y)) and (y=z or Owner(d)(y,z)).
     ```

     In other words, the reflexive closures of the two color relations compose
     to the complete relation with multiplicity one.  This is the precise
     mixed permutation-composition law needed for a three-coordinate parity
     argument; the matrix-to-combinatorics bridge is no longer a GAP.
     Its first genuinely three-component consequence is also `PROVEN` as
     `unitOwnerColors_matchingCompositions_pointwise_ne_of_intermediate_ne`:
     for fixed distinct unit colors `c,d`, the `c`-then-`d` matching
     compositions through two different intermediate order-`q` components
     disagree at every source point.  Thus intermediate components themselves
     index a second maximum-distance permutation code.  The live parity task
     can now count/compare these composition codes against the color-indexed
     code and the diagonal cycle permutations.
     The sharp counting consumer is `PROVEN` as
     `binarySquare_regular_unitOwnerColors_intermediateFamily_card_le`:
     any injectively component-indexed family of such mixed routes into an
     order-`q` target has at most `q` members.  Evaluation at one source vertex
     is injective by unique-route rigidity.  Equality and near-equality cases
     are now the relevant frontier; the base cardinal bound is formalized.
     The equality case is `PROVEN` as
     `binarySquare_regular_unitOwnerColors_intermediateFamily_eval_bijective`:
     a `q`-member family evaluates bijectively onto the target at every source
     vertex.  Thus saturation forces an exact Latin/transversal law, not just
     cardinal equality.  The remaining task is to force saturation (or extract
     a contradiction from its deficit) using the normalized component
     partition and diagonal cycle data.
     The first such algebra-to-cycle bridge is now `PROVEN` in
     `Erdos85BinarySquareCenteredOwnerResolution`.  For the normalized
     component sizes `m_c`, the theorem
     `binarySquare_regular_sum_centeredOwnerGrams` proves

     ```text
     sum_c C_c = q ((q-1) I - D).
     ```

     Combining this resolution with pairwise annihilation,
     `binarySquare_regular_centeredOwnerGram_mul_defectResolution` gives the
     colorwise projector equation

     ```text
     C_c · q ((q-1) I - D) = C_c^2.
     ```

     Hence every owner sector is an actual algebraic summand of the defect
     cycle polynomial, rather than only a commuting auxiliary operator.  The
     additive square law is also `PROVEN`:
     `binarySquare_regular_sum_centeredOwnerGrams_sq` gives

     ```text
     sum_c C_c^2 = (q ((q-1) I - D))^2.
     ```

     This is the exact Parseval/Frobenius-mass interface for a trace or rank
     terminal: all nonconstant defect-operator mass splits additively among
     mutually annihilating owner colors.  Its right-hand side is evaluated
     exactly by the `PROVEN` theorem
     `binarySquare_regular_trace_defectResolution_sq`:

     ```text
     trace((q ((q-1) I - D))^2) = q^5 (q-1).
     ```

     Thus any colorwise rank/Frobenius estimate now has a fixed global budget,
     with no remaining trace computation hidden in the interface.
     The scalar budget has now been fully calibrated—and by itself is not a
     contradiction.  `Erdos85BinarySquareCenteredOwnerTrace` proves

     ```text
     trace(C_c)   = m_c q^2 (q-1),
     trace(C_c^2) = m_c q^4 (q-1).
     ```

     Summing the second formula and using `sum m_c = q` recovers exactly
     `q^5(q-1)`.  Therefore no argument based only on total Frobenius mass can
     distinguish `q=4` from `q>=8`; the terminal must use an equality-case
     rank statement, the distribution of eigenvalues within colors, or the
     self-indexed diagonal cycle blocks.  This rules out a tempting but
     genuinely tautological scalar lane.  The surviving equality datum is
     packaged by
     `binarySquare_regular_trace_centeredOwnerGram_sq_eq` as

     ```text
     trace(C_c^2) = q^2 trace(C_c).
     ```

     Positivity is now `PROVEN` in
     `Erdos85BinarySquareCenteredOwnerPositivity`.
     The reusable division-free theorem
     `centered_posSemidef_of_const_eigen` proves that `n M - r J` is PSD
     whenever `M` is PSD and `M 1 = r 1`; its graph specialization
     `binarySquare_regular_centeredOwnerGram_posSemidef` proves every `C_c`
     is PSD.  For a unit color (`m_c=1`), the complementary bound is also
     `PROVEN` in `Erdos85BinarySquareUnitOwnerSpectralInterval`:

     ```text
     q^2 I - C_c = q Lap(Owner(c)) + J >= 0.
     ```

     The proof includes the needed integer graph-Laplacian positivity theorem.
     Hence unit-color sectors satisfy the genuine spectral interval
     `0 <= C_c <= q^2 I`.  Together with the moment identity, this is exactly
     the equality-case mechanism forcing any eventual real spectral
     decomposition to live at the interval endpoints.

     The upper interval is now uniform in the normalized component size, not
     restricted to the unit case.  The `PROVEN` theorem
     `binarySquare_regular_centeredOwnerGram_upper_posSemidef` establishes

     ```text
     0 <= C_c <= m_c q^2 I,
     m_c q^2 I - C_c = q Lap(Owner(c)) + m_c J >= 0.
     ```

     This applies directly to every surviving binary part `m_c>=2`.  It also
     isolates why the unit endpoint argument does not automatically extend:
     the calibrated ratio `trace(C_c^2)/trace(C_c)` is `q^2`, strictly below
     the available upper endpoint `m_c q^2` when `m_c>1`.  The remaining
     non-unit terminal must therefore control the rank or distribution of the
     interior eigenvalues, rather than invoke endpoint equality unchanged.

     The rank side is now exact, not merely bounded.  The centered rectangular
     component-incidence block `B_c` satisfies the `PROVEN` row-Gram identity

     ```text
     B_c B_c^T = q C_c
     ```

     in
     `centeredDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_centeredOwnerGram`.
     Combining this with the component Laplacian factorization and its
     one-dimensional constant kernel gives the `PROVEN` theorem
     `binarySquare_regular_real_centeredOwnerGram_rank`:

     ```text
     rank(C_c) = |c|-1 = q m_c - 1.
     ```

     Consequently
     `binarySquare_regular_sum_real_centeredOwnerGram_rank` proves

     ```text
     sum_c rank(C_c) = q^2 - number of defect components.
     ```

     Since distinct centered owner sectors mutually annihilate, their ranges
     therefore saturate the entire complement of the component-constant
     directions.  There is no unused ambient rank slack.  The remaining
     non-unit terminal can work with a genuine direct-sum decomposition: it
     must constrain the internal spectrum on these exact `q m_c-1`
     dimensional summands or exploit their self-indexed row-Gram geometry.
     The spectral identification is also now explicit and `PROVEN` in
     `Erdos85BinarySquareCenteredOwnerSpectrumTransfer`.  Writing `L_c` for
     the induced defect-component Laplacian, the two Gram identities give

     ```text
     C_c B_c = q B_c L_c.
     ```

     Hence every nonzero eigenpair `L_c v = a v` transfers to the nonzero
     owner eigenpair `C_c(B_c v) = q a (B_c v)`, while every nonzero owner
     eigenpair `C_c w = a w` transfers through `B_c^T` to
     `(q L_c)(B_c^T w) = a (B_c^T w)`.  Thus the nonzero owner-sector spectrum
     is exactly `q` times the component-Laplacian spectrum, with no loss of
     eigenvectors in either direction.  This reduces the remaining interior
     spectral distribution problem to the spectra of the connected defect
     components themselves.
     For the binary-surviving normalized size-two parts, the first
     graph-specific refinement beyond this spectrally tautological transport
     is now `PROVEN` in
     `Erdos85BinarySquareSizeTwoOwnerLineGraph`.  The canonical bijection from
     ambient vertices to non-defect selector pairs is a graph isomorphism

     ```text
     Owner(c) ~= intersection graph of the selector pairs in c.
     ```

     Moreover, for distinct size-two coordinates `c,d`, the two isomorphisms
     are orthogonal: intersecting selector edges in coordinate `c` map to
     disjoint selector edges in coordinate `d`.  This is the precise
     line-graph/orthogonal-double-cover structure that ordinary spectra and
     trace moments forget, and exposes the perfect-matching compatibility
     problem as the next combinatorial terminal for the all-size-two branch.
     The promised matching statement is now itself `PROVEN` in
     `Erdos85BinarySquareSizeTwoStarPerfectMatching`.  For a point `u` in one
     defect coordinate `c`, index ambient vertices by the selector star at
     `u`.  In every distinct normalized size-two coordinate `d`, their
     `d`-selectors are pairwise disjoint two-element sets and every point of
     `d` occurs in exactly one of them.  Thus each `c`-star becomes an actual
     perfect matching of `d`, not merely a family of disjoint edges.  The
     exact page-overlap law is now also `PROVEN` in
     `Erdos85BinarySquareSizeTwoMatchingOverlap`: the matchings indexed by
     distinct source points `u,v` share a target edge iff `u,v` are adjacent
     in the selector complement (equivalently, are not defect-adjacent).
     This holds even for the self-coordinate cover and is precisely the ODC
     incidence axiom.  Finally,
     `Erdos85BinarySquareSizeTwoMatchingTwoFoldCover` proves the exact cover
     multiplicity: every target selector edge lies in precisely the two
     source matching pages indexed by the endpoints of its source selector.
     Thus perfect pages, page overlaps, and the two-fold edge cover—the full
     ODC axiom package—are all formal consequences of a size-two pair.
     Pairwise ODCs do exist at `q=8`, so the remaining all-size-two terminal
     must use three-way compatibility: the same ambient labels must furnish
     Cartesian selector cubes whose every two-coordinate projection is the
     corresponding rectangle partition.  This triple object is now `PROVEN`
     and first-class in `Erdos85BinarySquareThreeSelectorCubeLines`:
     `threeSelectorCube` attaches the Cartesian cube to each ambient label,
     distinct labels give pairwise disjoint cubes, and
     `binarySquare_regular_threeSizeTwoParts_cubeSupport_allAxisLines_exactlyTwo`
     proves that every axis-parallel line in their union has exactly two
     points.  The stronger self-indexing constraint, absent from an abstract
     cube system, is `PROVEN` in
     `Erdos85BinarySquareSizeTwoSelfIndexedBlock`:

     ```text
     B_c[c,c] = Adj(G[c]),       degree(G[c]) = 2.
     ```

     Thus the sixteen distinguished labels of an order-64 size-two coordinate
     encode its internal cycle 2-factor on the same sixteen ground points.
     The off-diagonal compatibility is likewise `PROVEN` in
     `Erdos85BinarySquareSizeTwoCrossIndexedBlocks`.  For two size-two
     coordinates,

     ```text
     B_cd = transpose(B_dc),
     every row and column of B_cd has exactly two ones.
     ```

     Hence every cross block is a 2-regular bipartite cycle system, and the
     reverse coordinate uses the same edges with orientation transposed.
     This is now a first-class graph theorem, not only matrix prose:
     `Erdos85BinarySquareSizeTwoCrossBipartiteCycles` defines the canonical
     graph on `c.supp ⊕ d.supp`, identifies its left and right degrees with
     the corresponding cross-neighbor finsets, and proves that it is
     2-regular and `IsCycles`.  Its connected components can therefore be
     consumed directly by the existing cycle-component classification API.
     `Erdos85BinarySquareSizeTwoCrossBipartiteParity` supplies the canonical
     left/right two-coloring and proves that every one of these connected
     cycle components has even order.  Thus every off-diagonal block carries
     an explicit partition of its `4q` bipartite vertices into even cycle
     lengths, rather than merely row/column degree data.  The girth refinement
     is `PROVEN` in `Erdos85BinarySquareSizeTwoCrossBipartiteGirth`: for
     distinct defect components the forgetful map from the bipartite block
     into the ambient vertex set is injective and edge-preserving, so ambient
     `C4`-freeness excludes cross-block four-cycles.  Every connected block
     cycle consequently has even order at least six.  Summing over connected
     components is `PROVEN` in
     `Erdos85BinarySquareSizeTwoCrossBipartiteComponentBound`:

     ```text
     6 * number_of_cross_cycles(c,d) <= 4q.
     ```

     In the order-64 all-two branch (`q=8`), every off-diagonal cross block
     therefore has at most five cycle components.  This supplies a finite
     cycle-partition search space for each of the six unordered coordinate
     pairs.  The needed half-cycle arithmetic is `PROVEN` in
     `Erdos85BinarySquareSizeTwoCrossBipartiteComponentBalance`: within each
     connected cross-block cycle, the source-side and target-side vertex
     finsets have equal cardinality.  The proof is an exact degree-sum double
     count on the induced component.  Hence every block component of order
     `2r` canonically contributes `r` vertices on each coordinate side.
     The local owner-cycle bridge is `PROVEN` in
     `Erdos85BinarySquareSizeTwoOwnerEdgeSubdivision`: an edge of `F_cd` is
     exactly a distinct source pair joined through a unique target vertex by
     a two-edge path in the cross-block graph.  Conversely every such
     subdivided cross path is an owner-factor edge.  In particular, owner
     edges preserve the connected-component label of their source-side
     embeddings in the cross graph.  This reduces the remaining full
     component correspondence to compression of alternating cross walks.
     That compression is now `PROVEN` in
     `Erdos85BinarySquareSizeTwoCrossOwnerReachability`.  Induction on a
     cross walk pairs successive left-right-left edges, discards immediate
     backtracks, and replaces every other pair by the corresponding owner
     edge.  Consequently

     ```text
     Reachable(F_cd, x, y)
       iff Reachable(Cross_cd, inl x, inl y),
     ```

     equivalently the owner-factor connected-component partition is exactly
     the restriction of the cross-block component partition to either
     coordinate side.  The cycle-length correspondence is therefore
     combinatorial, not merely a consequence of cospectrality.  This quotient
     statement is packaged as an actual equivalence in
     `Erdos85BinarySquareSizeTwoCrossOwnerComponentEquiv`.  The canonical map
     sends an `F_cd` component to the cross component containing its left-side
     vertices; reachability reflection makes it injective, while degree two
     ensures every cross component meets that side and makes it surjective.
     Consequently, at `q=8` every restricted owner factor between distinct
     binary coordinates has at most five cycle components as well.  The exact
     order correspondence is `PROVEN` in
     `Erdos85BinarySquareSizeTwoCrossOwnerComponentSize`: source-side
     membership in a mapped cross component is equivalent to owner-component
     membership, its left cardinality is the owner-component order, and side
     balance gives

     ```text
     |CrossComponent(a)| = 2 * |a|.
     ```

     Thus an owner cycle of length `r` corresponds canonically to the
     bipartite cross cycle of length `2r`.  Finally,
     `Erdos85BinarySquareSizeTwoPairedOwnerComponentEquiv` defines the graph
     isomorphism `Cross_cd ≃ Cross_dc` obtained by swapping the two sides and
     composes its component equivalence with the two owner/cross equivalences.
     This gives a canonical bijection

     ```text
     ConnectedComponent(F_cd) ≃ ConnectedComponent(F_dc)
     ```

     which preserves each component order.  Hence paired restricted owner
     factors have identical cycle-length multisets by an explicit
     combinatorial correspondence, strictly strengthening the earlier
     characteristic-polynomial equality.
     Pairwise classification is not the end of the block constraints.  The
     first simultaneous identity is `PROVEN` in
     `Erdos85BinarySquareCrossBlockResolution`: resolving the ambient row
     coordinate by its defect component gives, for distinct `c,e`,

     ```text
     sum_d transpose(B_dc) B_de = J.
     ```

     Thus the cross blocks through every intermediate coordinate jointly
     resolve the unique-common-neighbor design.  In the all-two q=8 branch
     this is a genuine constraint coupling all four coordinates, rather than
     six independent paired cycle systems.  Its entrywise strengthening is
     `PROVEN` in `Erdos85BinarySquareCrossBlockUniqueRouting`.  For every
     `x∈c,z∈e` with `c≠e`, there is a unique intermediate defect component
     containing their unique common neighbor.  Writing this component as
     `route(x,z)`, each resolved summand satisfies

     ```text
     (transpose(B_dc) B_de)[x,z] = 1  if d = route(x,z),
                                  0  otherwise.
     ```

     Hence the simultaneous Gram resolution is literally a partition of the
     all-ones matrix by component-valued routing labels, suitable for a finite
     four-coordinate classification.  The first regularity law for that
     classification is `PROVEN` in
     `Erdos85BinarySquareSizeTwoRoutingRegularity`.  When `c,d,e` are
     size-two components, fixing either endpoint and the intermediate label
     `d` leaves exactly four choices for the other endpoint:

     ```text
     |{z in e : route(x,z)=d}| = 4,
     |{x in c : route(x,z)=d}| = 4.
     ```

     Thus every routing table between two coordinates has each intermediate
     color occurring exactly four times in every row and every column.  At
     q=8 in the all-two branch this turns the four component labels into a
     four-color decomposition of the 16-by-16 endpoint array by 4-regular
     bipartite relations, rather than merely an unconstrained entrywise
     partition of `J`.  These ordered routing tables are not independent:
     `Erdos85BinarySquareCrossRoutingSymmetry` proves

     ```text
     route_ce(x,z) = route_ec(z,x).
     ```

     It packages each intermediate color as a zero-one matrix `R_ce(d)`,
     identifies it exactly with the Gram summand
     `transpose(B_dc) B_de`, and proves
     `transpose(R_ce(d)) = R_ec(d)`.  Thus endpoint reversal transposes every
     color class without permuting its component label.  The actual maximal
     order-64 branch is packaged in
     `Erdos85OrderSixtyFourFourComponentRoutingArray`: after choosing the
     canonical cardinality equivalence from the four defect components to
     `Fin 4`, each distinct component pair carries a `Fin 4`-valued routing
     array.  Its Lean interface simultaneously states reversal symmetry and
     exact four-per-color row and column fibers.  This is the finite
     four-coordinate object that the remaining classification must rule out.
     `Erdos85OrderSixtyFourFourComponentRoutingMatrices` retains the stronger
     algebraic certificate: its four zero-one matrices `R(k)` have constant
     row and column sum four, pairwise disjoint supports, sum to `J`, transpose
     under endpoint reversal, and factor exactly as

     ```text
     R_ce(k) = transpose(B_(E.symm k),c) B_(E.symm k),e.
     ```

     Hence a future finite classification cannot accidentally admit balanced
     four-color arrays that do not arise from the underlying 2-regular
     cross-incidence blocks.  The first genuinely ternary closure law is
     `PROVEN` in
     `Erdos85OrderSixtyFourRoutingMonochromaticTriangleMultiplicity`, using
     the routing-color composition identity.  For three pairwise distinct
     endpoint components `c,e,f`, if `route_cf(x,w)=k`, then

     ```text
     2 ≤ |{z in e : route_ce(x,z)=k and route_ef(z,w)=k}| ≤ 4.
     ```

     Thus every colored endpoint edge extends through every third coordinate
     to at least two monochromatic routing triangles.  This rules out many
     balanced four-color arrays that satisfy only the binary line-sum laws.
     `Erdos85BinarySquareRoutingTriangleLift` identifies the geometry hidden
     behind each such monochromatic triangle.  Its three unique pairwise
     ambient common neighbors lie in the routing-color component and satisfy
     a sharp dichotomy: either all three are one shared center, or they are
     pairwise distinct and form a rainbow owner triangle.  In the latter
     case the three owner-edge colors are exactly the three endpoint defect
     components.  Consequently the finite routing classification must also
     support this star-versus-rainbow lift for every monochromatic triangle.
     The star side is quantitatively rigid by
     `Erdos85BinarySquareRoutingStarCompletions`: for a direct routing edge
     `x,w` of color `d`, its unique common neighbor `y∈d` has exactly two
     neighbors in every third size-two component `e`, and both are
     automatically color-`d` completions on the two new sides.  Thus every
     direct colored edge has a canonical two-element star-completion core;
     any third or fourth completion allowed by the preceding `2..4` bound
     must come from the rainbow-owner alternative.  This separation is made
     canonical in `Erdos85BinarySquareRoutingCompletionDichotomy`: a third
     endpoint belongs to the star core iff its canonical pairwise common
     neighbor equals the direct edge's center.  Every monochromatic
     completion either satisfies that equality (and all three centers
     coincide) or its three named centers are pairwise distinct and carry
     the three endpoint-colored owner edges; the two alternatives are proved
     disjoint.  `Erdos85OrderSixtyFourRoutingRainbowExcess` completes the
     local accounting.  For every direct color-`k` edge it defines the
     rainbow-excess finset and proves

     ```text
     number of monochromatic completions = 2 + rainbow excess,
     rainbow excess ≤ 2.
     ```

     The only freedom left per direct edge and third coordinate is therefore
     zero, one, or two explicitly witnessed rainbow owner triangles beyond
     the forced two-star core.  This excess is attached to the undirected
     direct edge, not its orientation:
     `Erdos85OrderSixtyFourRoutingRainbowExcessSymmetry` proves that the
     canonical common neighbor is invariant under endpoint reversal and that
     reversing the direct edge leaves the rainbow-excess finset through a
     fixed third component literally equal (hence with the same cardinality).
     A global numerical budget for this geometry is `PROVEN` in
     `Erdos85BinarySquareMixedOwnerCubicTrace`.  The shifted rank-one product
     of two distinct owner matrices implies, for three pairwise-distinct
     owner coordinates of normalized sizes `m_a,m_b,m_c`,

     ```text
     trace(O_a O_b O_c) = q²(q-1)m_a m_b m_c.
     ```

     Hence in the order-64 all-two branch every ordered triple of distinct
     owner colors has mixed cubic trace exactly `3584`.
     `Erdos85BinarySquareMixedOwnerTriangleCensus` makes this budget fully
     combinatorial: it proves for arbitrary finite simple graphs that the
     mixed cubic trace is the cardinality of the finset of ordered cyclic
     triples carrying the three prescribed edge colors.  Consequently, in
     the order-64 four-component branch this finset has cardinality `3584`
     for each ordered triple of distinct owner colors (and in particular is
     nonempty).  The remaining work can therefore decompose a concrete
     global exactly-colored triangle finset by defect-component membership
     and identify its same-component summands with the local routing-rainbow
     census.  The first half of that decomposition is now `PROVEN` in
     `Erdos85BinarySquareMixedOwnerComponentSplit`: the global finset is the
     disjoint cardinal sum of same-defect-component and cross-component
     triples, so their order-64 cardinalities add to `3584`; the
     same-component part is in turn the sum of its uniquely indexed defect-
     component fibers.  A fixed fiber is nonempty iff its component supports
     the corresponding `routingOwnerRainbow`.  The remaining quantitative
     structure includes `Erdos85BinarySquareMixedOwnerFiberSymmetry`: explicit
     vertex-rotation and reversal bijections prove that every fixed-component
     fiber has the same cardinality after cyclically rotating or transposing
     its owner colors, hence after any permutation generated by those moves.
     `Erdos85BinarySquareMixedOwnerFiberBound` then supplies the first sharp
     quantitative separation.  A generic sigma-finset count bounds a
     three-color cyclic-triple census by `|V| k_A k_B`; restricting to a
     16-vertex defect component and its 2-regular owner factors bounds every
     component fiber by `64`, hence the whole same-component term by `256`.
     Since the global count is `3584`, at least `3328` exactly colored triples
     are cross-component.  Thus local routing rainbows are necessarily a
     small minority of the global cubic trace.  This separation is pointwise,
     not merely averaged: `Erdos85BinarySquareMixedOwnerRootedCensus` expands
     the distinct-owner product identity on each diagonal and proves that
     every vertex roots exactly `56` ordered `a-b-c` triangles.  At most four
     can keep both other vertices in the root's defect component, so every
     root has at least `52` cross-component colored triangles.  The remaining
     bookkeeping refinement is `PROVEN` in
     `Erdos85BinarySquareMixedOwnerRootedComponentPatterns`.  It assigns every
     rooted triangle one of five exhaustive tags: wholly local; only the
     middle vertex leaves; only the closing vertex leaves; both leave into
     the same external component; or all three vertices occupy distinct
     components.  The five fiber cardinalities sum to `56` at every root,
     and the local fiber is the earlier size-at-most-four finset.  Therefore
     one of the four nonlocal patterns occurs at least `13` times at every
     root.  `Erdos85BinarySquareMixedOwnerRootedPatternBounds` begins the
     sharp pattern analysis.  It proves that an edge of a third owner color
     has exactly four two-step middle vertices in any prescribed ordered pair
     of the other distinct colors.  Combining this with the local degree-two
     owner factors bounds each “only one vertex leaves” pattern by `8`.
     Hence at every root either the “both leave together” pattern or the
     all-three-distinct pattern has size at least `18`.
     `Erdos85BinarySquareMixedOwnerRootedAllDistinct` closes the remaining
     numerical leaf.  Each owner color has exactly two neighbors inside a
     vertex's defect component and twelve outside it.  Therefore the
     “both-leave-together” pattern injects into twelve external first-color
     neighbors times two same-component second-color choices and has size at
     most `24`.  Combining all four upper bounds with the exact total `56`
     forces at least `12` prescribed-color triangles through three pairwise-
     distinct defect components at every root.  The translation into routing
     language is now `PROVEN` in
     `Erdos85BinarySquareMixedOwnerRootedRoutingCycles`.  Across distinct
     defect components, an edge has owner `a` exactly when its unique common-
     neighbor route is the component `a`.  Consequently the all-three-
     distinct pattern finset is literally the finset of ordered endpoint
     pairs whose three routes are `a,b,c`, and every root supports at least
     `12` such prescribed routing cycles.  Summing the rooted fibers in
     `Erdos85BinarySquareMixedOwnerRoutingCycleCensus` gives a global sigma-
     finset of at least `64 * 12 = 768` prescribed rooted routing-cycle
     incidences for every ordered triple of distinct colors.  In the branch
     with no same-component owner rainbow,
     `Erdos85BinarySquareMixedOwnerNoRainbowMiddleConcentration` combines the
     sharper sixteen-cycle root bound with the three possible external middle
     components: at every root, some one external component carries at least
     six prescribed routing cycles.  Routing-row regularity leaves only four
     possible route-`a` middle vertices in that component, so
     `Erdos85BinarySquareMixedOwnerNoRainbowMiddleCollision` further forces
     two of those cycles to share the same owner-`a` middle vertex.
     `Erdos85BinarySquareMixedOwnerNoRainbowFork` unpacks the cardinal
     statement into distinct closing vertices `z₁,z₂`: both are owner-`b`
     neighbors of the shared middle `y`, both are owner-`c` neighbors of the
     root `x`, and each triangle `x-y-zᵢ` occupies three distinct defect
     components.  `Erdos85BinarySquareMixedOwnerNoRainbowAmbientFork` lifts
     the two `b`-edges and two `c`-edges to ambient common neighbors.  The two
     `b`-side centers and the two `c`-side centers cannot both coincide:
     otherwise the distinct closing vertices `z₁,z₂` would share one common
     neighbor in component `b` and another in component `c`, contradicting
     `C₄`-freeness.  Since every component selector has cardinality two,
     `Erdos85BinarySquareMixedOwnerNoRainbowAmbientExhaustion` upgrades this:
     either the separated `b`-centers exhaust the component-`b` neighbor
     selector of `y`, or the separated `c`-centers exhaust the component-`c`
     neighbor selector of `x`.  The exact two-lift side has also been pushed to an
     explicit overlap split.  `Erdos85OrderSixtyFourRoutingCycleLiftSeparation`
     shows that each cycle's closing owner-`c` route has exactly two
     monochromatic `c,c` lifts through the middle component, both different
     from the original owner-`a` middle.  For the two closing vertices,
     `Erdos85OrderSixtyFourRoutingLiftPairDichotomy` places both two-point
     lift fibers inside the same four-point route-`c` row and proves that
     either they share a `c`-hub, or they are disjoint and together saturate
     that row.  `Erdos85BinarySquareSeparatedCentersDisjointSelectors` gives
     the direct bridge from ambient separation to this split: distinct
     centers already sharing `x` (respectively `y`) have disjoint selectors
     into every component not containing that shared neighbor.  Hence on the
     side selected by ambient-center separation,
     `Erdos85OrderSixtyFourDistinctCentersSaturateRoutingRow` now proves that
     the corresponding exact lift fibers cannot take either the equal-center
     or owner-adjacent/shared-hub branch and must saturate their four-point
     routing row.  `Erdos85OrderSixtyFourRoutingForkSaturation` performs the
     paired propagation.  For distinct fork closings, the canonical `b`-
     centers and canonical `c`-centers cannot both coincide (the two colors
     lie in distinct components); whichever pair separates forces saturation
     of its corresponding four-point row.  Thus every forced fork saturates
     either the `b`-side row from `y` through the root component or the
     `c`-side row from `x` through the middle component.  A subsequent audit
     shows that this terminal is structural rather than contradictory:
     `Erdos85BinarySquareRoutingRowStarDecomposition` proves that every
     fixed-color routing row is exactly the union of the target-component
     neighbor rows indexed by the corresponding intermediate-component
     neighbors of its root, and that the indexed star rows are pairwise
     disjoint.  Consequently, when those two selectors have sizes two and
     two, their saturation of the four-point routing row is automatic; it
     supplies no exceptional pressure by itself.  The remaining structural
     gap must therefore relate two different color decompositions of these
     rows, or impose a global compatibility condition across roots.  A local
     contradiction from saturation alone is not a valid remaining target.
     The first cross-root replacement is `PROVEN` in
     `Erdos85BinarySquareCrossRootCenterPairs`.  For two roots joined by a
     second-order-defect edge and any remote target component, send each
     target vertex to the ordered pair of its canonical ambient centers with
     the two roots.  This center-pair map is injective: coincident centers
     would give the defect-adjacent roots a common neighbor, while two target
     vertices with the same distinct center pair would give an ambient
     four-cycle.  Each coordinate fiber is exactly the corresponding
     component selector and hence has cardinality two in the normalized
     size-two branch.  Thus every defect edge and remote component canonically
     produces a simple 2-regular bipartite transition graph between the two
     eight-center root neighborhoods.  The remaining global obstruction can
     now be posed as compatibility of these transition cycle covers around a
     defect-component cycle, rather than as local row saturation.  Distinct
     remote target components give edge-disjoint transition graphs: a center
     pair reused by vertices in two components would again form a four-cycle.
     Hence the three remote sixteen-vertex components occupy exactly `48`
     distinct edges of the common `8 × 8` center grid, leaving a canonical
     sixteen-edge complement.  This `48+16=64` packing law is also `PROVEN`
     in `Erdos85BinarySquareCrossRootCenterPairs`; identifying the complement
     is now `PROVEN` in `Erdos85BinarySquareCenterGridComplement`.  The fourth
     factor is exactly the disjoint union of (i) center pairs having a common
     neighbor back in the roots' own defect component and (ii) center pairs
     which are themselves second-order-defect edges.  Their cardinalities
     therefore sum to `16` at order 64.  The next finite structural target is
     to determine that internal split and propagate the resulting graph-
     native four-factor grid decomposition around the defect cycle.  The
     operator side of that split is `PROVEN` in
     `Erdos85BinarySquareCenterGridOperator`: for a defect edge `x-y`,

     ```text
     (A D A)_{xy} = 14 - (D²)_{xy}.
     ```

     The combinatorial encoding is now also `PROVEN`: `A D A` counts exactly
     the defect-pair part of the center grid.  Writing
     `λ=(D²)_{xy}` for the number of common defect neighbors of the roots,
     `Erdos85BinarySquareCenterGridOperator` therefore gives the exact split

     ```text
     defect pairs       = 14 - λ,
     source-common pairs = 2 + λ.
     ```

     Thus propagation has been reduced to adjacent-codegrees in the
     7-regular sixteen-vertex defect component, with no remaining matrix-to-
     combinatorics interface gap.  The source-common summand is not an
     arbitrary `2+λ`-edge subgraph: `PROVEN` in
     `Erdos85BinarySquareCenterGridComplement`, it is a matching between the
     two eight-center root neighborhoods (both coordinate projections are
     injective).  The proof uses the size-two source selector to make the
     source witness unique and then `C₄`-freeness to make the opposite center
     unique.  In particular it has at most eight edges.  The fourth 2-factor
     is therefore decomposed into a matching of size `2+λ` and a residual
     defect-edge graph of size `14-λ`; propagation must preserve this much
     sharper matching/residual structure.  The local degree assertion behind
     “fourth 2-factor” is now formal on the first coordinate in
     `Erdos85BinarySquareCrossRootCenterPairs`: each remote target factor has
     degree exactly two at every actual root center (its two-point selector
     fiber is transported through the injective center-pair map), so the three
     disjoint remote factors use degree six of the `K_{8,8}` grid and their
     complement has degree exactly two at every first center.  The symmetric
     image-fiber and complement theorems are now also `PROVEN`, so the fourth
     factor has degree two on both eight-vertex sides.  It is therefore a
     genuine spanning 2-regular bipartite graph (a disjoint union of even
     cycles), with its `2+λ` source-common edges distinguished as a matching.
     The classified component representatives suggest a second, nonedge
     attack through defect near-twins (`(D²)_{xy}=6`).  Its first graph-facing
     terminal is now `PROVEN` in `Erdos85BinarySquareCenterGridOperator`: for
     distinct `D`-nonadjacent `x,y` of codegree six, `x,y` have their unique
     ambient common neighbor, while there is exactly **one** `D`-edge between
     the two eight-vertex ambient neighborhoods.  Thus any representative
     with six such near-twin pairs must support six extremely sparse
     `1-of-64` neighborhood cuts.  The component localization is now also
     `PROVEN` there: the unique cross-neighborhood `D`-edge occupies one
     defect component, and every other component's two-by-two selector block
     is `D`-anticomplete.  After also excluding the component of the unique
     ambient common neighbor, every pair in each remaining selector block is
     distinct and has exactly one component-owner color.  Hence every
     nonexceptional component supplies a complete `K_{2,2}` block uniquely
     edge-colored by the four owner graphs.  The four-component cardinal
     consequence is `PROVEN` in
     `Erdos85OrderSixtyFourNearTwinOwnerBlocks`: deleting the bridge and
     overlap components leaves at least two distinct components, so every
     near-twin forces at least two such uniquely owner-colored `K_{2,2}`
     blocks.  The next obstruction target is to combine these forced blocks
     with the owner 2-factor budgets (or show that the six near-twin cuts
     cannot coexist).
     A complementary no-rainbow consequence is `PROVEN` in
     `Erdos85NearTwinOwnerFork`: an induced-component codegree-six nonedge
     forces two distinct complement-common vertices that close through the
     same non-base owner at both roots.  The global interface is now `PROVEN`
     in `Erdos85OrderSixtyFourNearTwinForkAdapter`: matrix codegree six puts
     the roots in one defect component, preserves their codegree after
     induction, and feeds the result directly to that repeated-owner-fork
     endpoint.  Thus the graph-facing near-twin hypothesis no longer has an
     ambient-to-component gap in the no-rainbow branch.
     This ambient-adjacency symmetry is another constraint not present in an
     arbitrary family of ODC pages or a bare line-sum-two tensor.
     Its row-Gram/owner consequence is `PROVEN` in
     `Erdos85BinarySquareSizeTwoOwnerFactorization`: every size-two owner
     color restricts to a 2-regular factor on every size-two ground
     component, and the restricted owner colors uniquely edge-partition the
     selector complement of that component.  In the order-64 all-two branch,
     each 8-regular selector complement is therefore canonically decomposed
     into the four 2-factors indexed by the four defect coordinates.
     The inherited girth restriction is `PROVEN` in
     `Erdos85BinarySquareSizeTwoCrossBlockNoRectangle`: distinct rows of a
     cross block overlap in at most one target point, so no cross block
     contains a `K_{2,2}` (ambient four-cycle).  Moreover the overlap is one
     exactly on the corresponding restricted owner-factor edge and zero
     otherwise.  Thus each owner 2-factor is precisely the simple row-Gram
     graph of a rectangle-free 2-regular bipartite cross block.
     The resulting spectral compatibility is `PROVEN` in
     `Erdos85BinarySquareSizeTwoCrossFactorCospectral`.  If `B_cd` is the
     cross-incidence matrix, then

     ```text
     B_cd B_cd^T = 2I + Adj(F_cd),
     B_cd^T B_cd = 2I + Adj(F_dc).
     ```

     Equal size-two component orders and the rectangular `AB/BA`
     characteristic-polynomial identity therefore imply that the paired
     restricted owner factors `F_cd` and `F_dc` are cospectral.  Thus the
     coordinate-indexed 2-factorizations on different components cannot be
     chosen independently even at the level of cycle-length multisets.
     A stronger module-level compatibility is `PROVEN` in
     `Erdos85BinarySquareSizeTwoCrossFactorIntertwining`:

     ```text
     Adj(F_cd) B_cd = B_cd Adj(F_dc).
     ```

     Hence the actual cross-incidence block, not merely an abstract spectral
     bijection, transports the paired factor actions.  This is the exact
     vertex-level intertwining constraint available to a simultaneous-block
     classification.  Its direct combinatorial form is `PROVEN` in
     `Erdos85BinarySquareSizeTwoCrossFactorPathBalance`: for every `x` in
     component `c` and `z` in component `d`, the number of intermediate
     vertices reached by an `F_cd` edge followed by a `B_cd` edge equals the
     number reached by a `B_cd` edge followed by an `F_dc` edge.  Thus the
     matrix intertwiner is available to a finite census as an exact local
     alternating-path count, with no spectral decoding step.
     It is therefore the
     compatibility/classification of these simultaneous two-fold
     perfect-matching covers for at least four connected-complement
     coordinates (at `q=8`).
     The abstract equality case is now `PROVEN` in
     `Erdos85BinarySquareEndpointRigidity`:
     `posSemidef_mul_self_eq_smul_of_upper_of_trace_sq_eq` gives
     `A^2 = r A`, and
     `eigenvalue_eq_zero_or_endpoint_of_posSemidef_of_upper_of_trace_sq_eq`
     gives `lambda = 0` or `lambda = r` for every nonzero real eigenvector.
     Thus the now-complete real-matrix package

     ```text
     0 <= C_c <= q^2 I,   trace(C_c^2) = q^2 trace(C_c)   (m_c=1)
     ```

     yields endpoint spectral rigidity.  The integer-to-real interface and
     its application to the actual unit sector are now `PROVEN` in
     `Erdos85BinarySquareUnitOwnerProjection`:
     `binarySquare_regular_unit_centeredOwnerGram_real_mul_self` proves
     `C_c^2 = q^2 C_c`, while
     `binarySquare_regular_unit_centeredOwnerGram_real_eigenvalue_eq_zero_or_sq`
     proves every real eigenvalue is `0` or `q^2`.  The proof reconstructs
     real Gram/centering positivity, the real Laplacian upper bound, and casts
     the exact integer trace moment.  Exact multiplicity/rank is now `PROVEN`
     in `Erdos85BinarySquareUnitOwnerRank`:
     `binarySquare_regular_unit_centeredOwnerGram_real_rank` gives
     `rank(C_c)=q-1`, and
     `binarySquare_regular_unit_centeredOwnerGram_real_range_finrank` exposes
     the same statement as `finrank(range(C_c))=q-1`.  It follows by
     normalizing `C_c/q^2` to an idempotent and applying the formal theorem
     that the trace of a projection equals the dimension of its range.  The
     first self-indexed feedback is now `PROVEN` in
     `Erdos85BinarySquareUnitOwnerCliqueFibers`.  Expanding the projection
     identity for `C_c=q(A_c+I)-J` gives

     ```text
     (A_c+I)^2 = q(A_c+I).
     ```

     The theorem `binarySquare_regular_unit_componentOwnerGraph_adj_trans`
     turns this into adjacency transitivity, so every unit owner graph is a
     union of `K_q` clique fibers.  The self component is a transversal:
     `binarySquare_regular_unit_selfComponent_closedOwnerNeighborhood_disjoint`
     proves that its distinct support vertices select pairwise disjoint closed
     owner neighborhoods, and
     `binarySquare_regular_unit_componentOwnerGraph_closedNeighborhood_card`
     proves each such fiber has order `q`.  Since the support has `q` vertices
     inside `q^2` total vertices, these are the exact `q×q` fiber coordinates.
     (This remains unit-color infrastructure, hence relevant to odd-q branches
     but vacuous in the even binary A-REG branch.)  The remaining task is to
     combine these clique-fiber transversals across colors/components, while
     the binary branch must consume its non-unit centered-component ranks.  The
     remaining classification must exploit the self-indexed diagonal block
     of each summand (or its rank/spectrum) to distinguish `q=4` from
     `q >= 8`.
     The remaining subgoal is no longer an interface gap: it is to classify or
     obstruct this connected weighted cycle quotient and its rectangular
     cycle intertwiners under the square-order common-neighbor laws.

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

19. **`PROVEN` — uniform even-parameter nonregular exclusion.**
    `squareOrder_regular_of_even` proves that every tight-edge-cover C4-free
    graph on `q²` vertices is `q`-regular when `q` is even. The key theorem
    `squareOrder_odd_of_exists_degree_succ` says a degree-`q+1` vertex forces
    `q` odd: its neighbors all have degree `q`, so its conflict degree is
    `(q+1)(q-1)=q²-1`; its conflict neighborhood exhausts the punctured vertex
    set, and its ordinary neighborhood is 1-regular. Hence `q+1` is even.
    This closes A-NONREG for all binary parameters without a census.

20. **`PROVEN` for the binary branch; diagnostic structure retained.** The
    former A-NONREG terminal campaign is no longer needed for even `q`, but its
    structure remains useful for odd square orders. It attempted to
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
      the `q=8` simultaneous `G/D` scout.
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
      The audited discovery model `square_order_coupled_design_scout.py`
      realizes the high-incidence blocks and `D` vertex by vertex and imposes
      all of these owner-sensitive pair bounds.  This relaxation is SAT for
      every one of the 11 combined-census survivors with `h≤6`, so these
      inequalities alone are not a terminal.  Its `--full-graph` mode restores
      the low-low adjacency matrix, exact low degrees, and every remaining
      C4/common-owner constraint.  For the unique `h=2` profile
      `(n₀,…,n₄)=(45,16,1,0,0)`, let `x` be the `k=2` vertex and let `S` be its
      six low original neighbors.  The defect equations force the sixteen
      `k=1` vertices into two high-incidence classes joined by a D-perfect
      matching, and split the `k=0` vertices into the five D-neighbors `T` of
      `x` and forty vertices `U`.  Every `S` vertex has no original edge to a
      `k=1` vertex; every `T` vertex has no neighbor in `S`; every `U` vertex
      has exactly one.  Counting `S-U` incidences gives
      `|S∩{k=1}|=2`, one from each high class.  Moreover `U∩S` is internally
      1-regular, so `|T∩S|∈{0,2,4}`.  These are the first global consequences
      extracted from the exact model and are candidates for a short uniform
      lemma.

      After canonically fixing the resulting `S×U` partition, the three exact
      Boolean cases lower reproducibly to 2.02M, 2.16M, and 2.28M clauses via
      `--write-dimacs`; Kissat reports UNSAT for all three.  Thus the `h=2`
      profile is eliminated computationally and the combined q=8 frontier is
      `51→50`.  This is audited discovery evidence, not a Lean theorem or
      certificate terminal.  The contradiction has now been extracted,
      however.  Fix one high vertex and let `A` be its `q` incidence-one
      neighbors (apart from the shared `k=2` point).  C4-freeness makes the
      `q(q-1)` low-neighbor incidences from `A` hit distinct low vertices.  The
      `q-2` points of `S` have no neighbor in `A`, so they exhaust the misses;
      every low point outside `S` has exactly one neighbor in `A`.  Since
      `S∩A={p}`, the graph induced on `A\{p}` is one-regular.  Its order is
      `q-1`, odd for even `q`, contradicting handshaking.

      The endpoint is `PROVEN` abstractly in Lean as
      `false_of_even_highRoot_saturation`, with the reusable parity lemma
      `even_card_of_card_neighbors_inter_eq_one`, in
      `Erdos85SquareOrderTwoHighTerminal`.  The scout confirms that after the
      saturation/one-regular structure is imposed, all three cases are Z3
      UNSAT in about eight seconds even with every remaining owner implication
      and all D constraints removed.  The remaining `GAP` for a fully formal
      h=2 exclusion is now only the profile-to-terminal bridge: derive the
      distinct-incidence saturation and `S∩A={p}` hypotheses from the proved
      square-order owner counts.  This is a short structural application, not
      a finite classification or certificate task.

    Thus the complement pairs of `D` admit a unique decomposition into a
    symmetric family of owner blocks. The next GAP is a classification or
    obstruction for this weighted symmetric neighborhood design, not merely
    for `D` alone. A vertex-level `q=8` model search is being used only to
    discover the first such obstruction, not as a certificate terminal. The
    new parity theorem bypasses this classification in the binary branch;
    these statements remain diagnostic rather than required terminals.

### A6. Binary branch capstone

21. **`AXIOM A-CAPSTONE`.** Node 10 + A-REG + the proved A-NONREG imply
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
        └── nonregular-sector exclusion                 [PROVEN]
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

1. `A-REG`: isolate and attack the regular binary square-order theorem; it is
   now the only open square-order sector in the binary branch.
2. In parallel, `B-EXIST`: turn the 48-vertex witness into a precise geometric
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
