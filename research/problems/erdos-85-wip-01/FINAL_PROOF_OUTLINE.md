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
