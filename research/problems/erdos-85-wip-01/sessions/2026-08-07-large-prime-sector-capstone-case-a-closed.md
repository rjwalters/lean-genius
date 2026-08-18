# 2026-08-07 (afternoon): The large-prime sector capstone — Case A closed

**Participants**: claude (Fable), codex — live squad-room collaboration.
**Branches**: `feature/erdos85-freqpair` (claude, relay/union),
`feature/erdos85-assembly` (codex). All results Docker-verified
(`docker-build.sh`), sorry-free, `#print axioms` exactly
`[propext, Classical.choice, Quot.sound]` unless stated. No `native_decide`
anywhere in the new chain.

## Headline

**The entire large-prime sector of the exact even boundary is closed.**

- `false_of_secondOrder_largePrime_sector`
  (`Erdos85LargePrimeSectorCapstone.lean`): there is no `C4`-free graph of
  even minimum degree `d ∉ {4, 12}` on `d(d−1) + 3 = N·p` vertices when a
  prime `p > d` divides every second-order defect component order.
- `secondOrder_no_largePrime_dvd_component_order`: consequently (via sector
  closure: one `p`-divisible order spreads to all), **every defect-cycle
  length at the exact even boundary with `d ∉ {4, 12}` is `d`-smooth** —
  all its prime factors are at most `d`.

This closes Case A of the selection-obstruction program — square *and*
nonsquare branches, every normalized coefficient `a`, every leakage
pattern — with **no parity input, no convolution, no L-quantization, and
no square/nonsquare split**. The morning's L=2/double-cover/bouquet
machinery and the planned hcountOdd discharge are superseded on this
critical path (they remain valid theorems; several feed Cases B/C).

## The proof spine (one day, red-teamed in-room before formalization)

1. **Cross-pair count** (`Erdos85CrossComponentPairCount.lean`): vertices in
   distinct defect components have exactly one common neighbor (zero-common
   would make the pair defect-adjacent, hence same component; two-common
   makes a `C4`). Summed: `Σ_z |N(z)∩c|·|N(z)∩c'| = |c|·|c'|`.
2. **Weighted Gram identity** (`Erdos85QuotientGramIdentity.lean`):
   grouping by the middle vertex's component, `Σ_e |e|·Q(e,c)·Q(e,c') =
   |c|·|c'|` for all distinct components — the counting spine, valid at
   every exact even boundary.
3. **Minimum-layer cross-pair identity**
   (`Erdos85MinimumLayerCrossPairIdentity.lean`, hall-free): summing the
   Gram identity over ordered distinct pairs of minimum-layer components
   and splitting the middle component over `M` vs strictly larger:
   `Σ_{e∈M} [(d−L_e)² − (d−L_e) − (w−3)] = |M|(|M|−1)·w`. Larger
   components vanish from the pair sum because they see the minimum layer
   at most once (`secondOrder_largerComponent_minLayerRow_le_one`, built on
   codex's cyclic-cover source uniqueness
   `secondOrder_minimum_largerTarget_source_unique`), and the equal-size
   excess identity evaluates the `M`-block.
4. **Leakage bound** (`secondOrder_minLayer_leakage_add_le`): normalized
   balance (`a·Q(e,f) = m_f` on positive edges, codex's interface) +
   source uniqueness give `a·ΣL + u·a ≤ N`.
5. **Assembly squeeze** (`minimum_sector_assembly_squeeze`,
   `Erdos85MinimumSectorAssemblyArithmetic.lean`): pure integer arithmetic —
   identity + leakage + boundary `d²−d+3 = Np` + window `p ≥ d+1` + any
   non-minimum mass force `u = a = 1`.
6. **Lone-unit diagonal collapse** (`false_of_secondOrder_lone_unit_minimum`,
   `Erdos85UnitMinimumLayerTerminal.lean`): a lone minimum of odd order
   `p ≥ 7` collapses the equal-size excess to its diagonal:
   `Q(c,c)(Q(c,c)−1) = p−3 ≥ 4` against the odd-cycle diagonal bound `≤ 2`.
7. **All-equal branch**: no larger mass means the equal-cycle boundary —
   `equalCycle_degree_eq_four_or_twelve` — excluded by `d ∉ {4, 12}`.

Codex's parallel contributions this session: source-uniqueness
generalization (`Erdos85DoubleCoverTargetUniqueness.lean`), the unit-layer
leakage dichotomy (`Erdos85SquareMinimumLeakage{,Arithmetic}.lean` — which
with the lone-unit kill closed the exact-square `a = 1` case first, as
`false_of_secondOrder_square_unit_minimum`), the assembly interface
(reverse-entry-one, normalized balance, partition sums), ℕ-normalizers, the
prime-free universal terminal
`secondOrder_minimumLayer_totalOrder_le_of_degree_ne_four_twelve`
(`d ∉ {4,12} ⟹ u·w ≤ 2d−1` at every exact even boundary — no prime
hypotheses at all), and the design arithmetic
(`minimumLayer_design_discriminant`: `(2s−1)² = 4uw − 11`;
`minimumLayer_card_odd_of_design`: `u` odd).

## The new frontier: the minimum-layer design equation (goal #16)

Inside the bounded branch `u·w ≤ 2d−1`, the restricted quotient matrix
`R = Q|M` satisfies (`Erdos85MinimumLayerGramMatrix.lean`):

- `R` symmetric (`componentQuotientMatrix_symm_of_ncard_eq` — balance
  cancellation between equal orders);
- `R_ij < w` off-diagonal (`componentQuotientMatrix_lt_ncard_of_ne` — a
  full bipartite block between two components gives `K_{2,2} = C4`),
  diagonal `≤ 2`;
- `R² = w·J + diag(S − 3)`
  (`secondOrder_minimumLayer_gramSquare_offDiag` / `_diag`).

Commutator `[R, R²] = 0` then forces the row sums constant
(`(s_i − s_j)(w − R_ij) = 0` with `w − R_ij > 0`), whence
`R² = wJ + (s−3)I`, `s² − s + 3 = u·w`, `(2s−1)² = 4uw − 11` — a
friendship-theorem-shaped spectral system (`±√(s−3)` eigenvalues, trace
`≤ 2u`). **Notably `u·w = s²−s+3` reproduces the plane-order form
`N = s²−s+3` of the `(p, N) = (s²+s+3, s²−s+3)` family: the minimum-layer
quotient recurses into the same quadratic-boundary geometry one level
down** — unforced confirmation of the plane-order self-similarity that
goal #15 (plane-order dichotomy mission) conjectures. Expectation: the
design equation *classifies* the bounded branch into plane-order data
rather than killing it outright; the kill needs second-level structure
(untouched larger mass, equal-cycle on the recursion). `fifteenRegular`
(`d = 4`: `u = 1, w = 3`) realizes the branch, so the `d ∈ {4,12}` guards
are necessary.

## Goal-board changes

- Goal #15 (plane-order dichotomy mission) added earlier today by operator
  directive.
- Goal #16 added: Cases B/C frontier (universal dichotomy consumer, bounded
  minimum sector, e=0 survivors `d ∈ {6,12,16}`, equal-cycle residuals).
- Goal #9 was marked done in error (crossed messages) and restored verbatim
  as goal #17 with a status annotation: superseded **for Case A only**;
  its `p ≤ d` reach stays open.

## Corrections during the session (methodology record)

- claude's initial `hleak` sum-manipulation draft and the first
  `minimum_sector_assembly_squeeze` build both failed on `Finset.mul_sum`
  rewrite shapes — restated pointwise with `linear_combination`.
- codex red-teamed the msg-978 proposal and confirmed exact bookkeeping
  (no slack term needed once source uniqueness is used); he corrected his
  own earlier a=1 closure claims twice (mass-two uniqueness ≠ unit-count
  bound) before the capstone made the point moot.
- codex caught a premature #9 board closure; restored as #17.

## Status of other lanes (unchanged today)

Remote BBBB sweep continuing (all UNSAT so far); local deep SAT lanes
grinding; 49-lab survivor hypotheses untouched by this session; the
f(48)=8 / f(49)≥7 unconditional results and the publication fact-check
([a]–[d] resolved, comment pending operator) are as recorded in the
previous session log.
