# Final proof outline: Erdős 85 is false

**Version 2.1 — 2026-08-18 (operator consolidation; red-team pass folded in).**

This is the single authoritative outline. It supersedes the four divergent v1
copies, archived unchanged beside it as `FINAL_PROOF_OUTLINE_v1a.md` (sol-1
branch, 1,510 lines), `_v1b.md` (sol-2, 3,639 lines), `_v1c.md` (sol-3, 1,624
lines), `_v1d.md` (Claude, 1,359 lines). Those are the ledger of what was
proved and tried through 2026-08-18 14:00Z; nothing in them is lost, and
nothing in them is the map any more.

Rules of this document:

- It lives on `main` at this path. There is exactly one copy. Per-branch
  copies are frozen; do not edit them.
- It is a critical-path map, not a ledger. A theorem earns a line here only if
  it changes the status of a node below. Everything else is recorded in the
  ledger (v1b remains the fullest one) or in the room.
- Labels: `PROVEN` (uniform Lean theorem, name given) · `PROVEN-AT-64` (q=8
  only; if certificate-backed, `Lean.ofReduceBool` is in the axiom set and
  the label says `CERT`) · `EXTERNAL` (solver signal, no certificate) ·
  `AXIOM` (precise conjecture that would close its parent) · `GAP` (no
  candidate statement).
- Version bumps: patch (2.0 → 2.1) when a node's status changes; minor
  (2 → 3) when the tree's shape changes. Every bump appends to the change
  log at the end. Edits go through the editor (steward) until the operator
  reassigns; agents post the delta and the theorem name in the room.
- The document must stay short enough for the operator to read in one
  sitting. If it does not, that is the defect to fix first.

---

## 0. The theorem and the root — implications PROVEN; root CONDITIONAL on A-REG

Erdős 85 asks whether `f(n) = minDegreeForC4 n` is eventually monotone. The
campaign's claim: it is not; `f` drops at plane-order squares infinitely often.

- `PROVEN` `erdos85Negation_iff_not_question` — negation ⇔ arbitrarily large
  strict drops `f(n+1) < f(n)`.
- `PROVEN` `PlaneOrderDropWitness.strict_drop` — a witness on `q²−1`
  vertices with min degree `q`, plus nonexistence on `q²`, gives one drop.
- `PROVEN` `not_erdos85Question_of_cofinalPlaneOrderDropFamily` — cofinally
  many such pincers refute Erdős 85.

**Root task:** exhibit pincers for an unbounded set of `q`. Two families;
either alone suffices. Branch A is the critical path.

---

## A. Binary branch, `q = 2^k`, `k ≥ 3` — the critical path

| node | status | theorem |
|---|---|---|
| A.1 existence jaw on `q²−1` | `PROVEN` | `Polarity.c4FreeMinDegreeWitness_even_delete_absolute_nucleus`; cofinal via `cofinalEvenFieldSquareExclusion_of_binary` |
| A.2 reduce `q²` nonexistence to a normalized tight core | `PROVEN` | `squareOrderTightCoreExists_iff_witness`, `binarySquareOrderTightCoreExclusion_iff` |
| A.3 tight core is regular for even `q` | `PROVEN` | `squareOrder_regular_of_even` |
| A.4 capstone: A-REG ⇒ ¬Erdős 85 | `PROVEN` | `binarySquareOrderTightCoreExclusion_of_regularExclusion`, `not_erdos85Question_of_binarySquareRegularExclusion` (standard axioms) |
| **A.5 AXIOM A-REG** | **`AXIOM` — the only open node of Branch A** | `BinarySquareRegularExclusion`: for every `k ≥ 3`, no `2^k`-regular C4-free graph on `4^k` vertices |

Everything below this line is inside A.5.

### A.5.1 What is proven uniformly beneath A-REG (all `q = 2^k`, standard axioms)

- Defect operator `A² = (q−1)I + J − D`, commuting with `A`
  (`adjMatrix_sq_eq_sub_secondOrderDefect_of_regular`,
  `adjMatrix_comm_secondOrderDefect_of_regular`).
- Partition law: every defect component has order `q·m_c`, `Σ m_c = q`
  (`binarySquare_regular_exists_defectComponent_partition`); every vertex has
  exactly `m_c` neighbours in component `c`
  (`binarySquare_regular_mul_componentNeighborCard_eq_componentCard`).
- No unit part (`m_c = 1`) for even `q`
  (`binarySquare_regular_no_sizeQ_defectComponent_of_even`;
  all-unit case `binarySquare_regular_not_allUnit_of_two_pow`).
- **No bipartite defect component, any size, any partition, for every
  `4 ∣ q`** (`binarySquare_regular_no_bipartite_defectComponent`,
  `Erdos85BinarySquareAllOddBipartitePartsExclusion.lean` on
  `origin/feature/erdos85-claude-sixtwo`, commit `4bdd5a720a`, 2026-08-18;
  author-compiled, standard axioms; independent recompile pending
  integration). This closes the bipartite half of A-REG for every `k` by
  one argument that lifts. It is the only part of A-REG proven that way.
- Owner/selector algebra, centered-owner ranks and nullities, cross-block
  identities `HB + BC = J`, `BC² = (q−2m)J + H²B`, cyclic first/second
  moments, signed-eigenline range and support laws — all uniform, none a
  contradiction. Ledger: v1b nodes 13a–13b.

Hence for `q = 2^k` a counterexample to A-REG has defect components of orders
`q·m_c` with every `m_c ≥ 2` and every component non-bipartite. That is the
whole of what remains:

> **A-REG (remaining content).** For `k ≥ 3`, `q = 2^k`: no `q`-regular
> C4-free graph on `q²` vertices whose defect components all have order
> `q·m_c`, `m_c ≥ 2`, `Σ m_c = q`, and are all non-bipartite. This
> includes the connected one-part case `[q]` (one component of order `q²`)
> as well as the mixed cases `r ≥ 2`.

The names `A-REG-EXTENSION`, `A-REG-UNIT`, `A-REG-MIXED-PARTITION` in v1 are
restatements of this same node, not sub-nodes. They are retired here.

### A.5.2 What is proven at `q = 8` only (order 64; not on the critical path)

The seven partitions of 8 into parts ≥ 2: `[2,2,2,2]`, `[3,3,2]`, `[4,2,2]`,
`[4,4]`, `[5,3]`, `[6,2]`, `[8]`.

| stratum | status at 64 | note |
|---|---|---|
| `[2,2,2,2]` | `EXTERNAL` — 11 assembly targets UNSAT | kissat, no certificates; the finite reduction to 11 targets is Lean/q-generic in parts (via-tiling law); the size-two μ=3 CERT kill below also applies here |
| size-two block carrying a signed joint eigenline with `μ = 3` | `PROVEN-AT-64 CERT` | `false_of_orderSixtyFour_mu3_jointEigenline_native_without_hA_out` (2026-08-18 14:21Z; K-law + enumeration + 22 LRAT certificates; residual = the eigenline hypothesis `hs_in, hs_out, hsum, hDs, hA_in`) — kills that block in every stratum containing a size-two part |
| size-two block, `μ ∈ {−1,−3,−5}` or no alternating eigenline | `GAP` | active lane; nothing terminal |
| `[3,3,2]`, `[4,2,2]`, `[6,2]` | `GAP` | non-bipartite blocks; only size-two/`μ=3` inputs above |
| `[4,4]`, `[5,3]` | `GAP` | exact owner nullities only |
| `[8]` (connected defect) | `GAP` | determinant/Matrix–Tree package only |

Closing all seven at 64 yields a second decided drop (`63 → 64`). It does
not yield A-REG. Order-64 methods (grids, enumerations, certificates) do not
extend to `q = 16` (order 256); the outline records that as a fact, not a
plan.

### A.5.3 The gap, stated plainly

**GAP A-REG-NONBIP.** No candidate mechanism, uniform in `k`, is known for
excluding a partition with all parts `≥ 2` and all components non-bipartite.
Nobody in the room has proposed one; the only kills of non-bipartite
structure to date are order-64 enumerations. This is the critical path. A
proposal counts only if it strengthens with `q` and is strictly weaker than
A-REG itself. Its children, by shape (a completeness split, not a theorem):

- **NONBIP-CONNECTED `[q]`** — one defect component of order `q²`
  (`[8]` at q=8). `GAP`. Uniform inputs: `C = q·L_D`, `L_D = A² − J`,
  `det(L_D + J) = det(A)²`; none a contradiction.
- **NONBIP-MIXED `r ≥ 2`** — two or more parts. `GAP`. Uniform inputs: the
  owner/selector algebra of A.5.1; every binary candidate has a triangle-free
  edge (`binarySquare_regular_triangleFreeEdge_edgeFinset_nonempty`).
  - **SIZE-TWO-EIGENLINE(q)** — a size-two part (`m_c = 2`) carrying the
    alternating vector `s` with `Bs = 0`, hence `Ds = (q−5)s`. The exterior
    grid model (`q×q`, two holes per row/column, `q(q−2)` cells), the
    row/column-hit laws, the per-cell `D` law and the K-law `K·Hᵀ = H·Kᵀ`
    are all proved by q-generic arguments; the shape census, enumeration and
    certificates are order-64. Status: `PROVEN-AT-64 CERT` (A.5.2), `GAP`
    for `k ≥ 4`. A sub-case of NONBIP-MIXED, not a decomposition of it; the
    first q-generic statement strictly beneath A-REG-NONBIP.
  - size-two parts with `μ ∈ {−1,−3,−5}` or no alternating eigenline;
    parts of size `≥ 3` — `GAP`, no q-generic statement yet.

---

## B. Odd branch, `q` an odd prime power — parked

| node | status | note |
|---|---|---|
| B.1 `q = 7` pincer | `PROVEN-AT-49` | `boza48_degreeSeven_witness`; `minDegreeForC4_fortyNine_lt_fortyEight` — one decided drop, `48 → 49` |
| B.2 existence jaw for unbounded odd `q` | `GAP B-EXIST` | Cayley route dead at 9, 11 (computational); dihedral-holomorph ansatz UNSAT at 9; conjecture `B-NEAR-LATIN-LIFT` stated; **no worker since 2026-08-17** |
| B.3 nonexistence at `q²` for the same `q` | `AXIOM B-NONEXIST` | partial uniform structure; `GAP B-CLASSIFY` for odd profiles |
| B.4 capstone | `AXIOM B-COFINAL` | B.2 ∧ B.3 on one unbounded set ⇒ done via §0 |

Operator ruling (goal #23): odd primes remain the primary *theory* of where
drops occur; Branch A is where the *proof* is closest. Decisive next datum on
B is existence or nonexistence at `q = 9`.

## C, D. Supporting theories — not on the critical path

Exact second-order boundary theory (`d(d−1)+3`) and plateau-core theory are
proven, useful, and at the wrong order. Bridge to square order: `GAP
C-TO-SQUARE`. They stay in the ledger.

---

## E. The tree

```text
¬ Erdos85Question                                    [PROVEN from A-REG]
└── Branch A: q = 2^k
    ├── q²−1 witnesses                                [PROVEN]
    ├── tight core, regular for even q                [PROVEN]
    └── AXIOM A-REG                                   [OPEN — the only node]
        ├── bipartite half                            [PROVEN, uniform, 4 | q]
        └── all-non-bipartite partitions              [GAP A-REG-NONBIP]
            ├── connected [q]                         [GAP]
            └── mixed r ≥ 2                           [GAP]
                ├── SIZE-TWO-EIGENLINE(q)             [PROVEN-AT-64 CERT; GAP k ≥ 4]
                └── other parts / other μ             [GAP]
            (q = 8 instances: see A.5.2; not the path)
Branch B (parked): B-EXIST [GAP] ∧ B-NONEXIST [AXIOM] ⇒ B-COFINAL [AXIOM]
```

## F. What counts as progress, and what does not

Counts (bump this document):
1. A new node strictly beneath A-REG-NONBIP that is q-generic and strictly
   weaker than A-REG — a real decomposition.
2. A q-generic kill of any partition shape (a `[m₁,…]` family for all `k`).
3. A proposed mechanism for the non-bipartite half, even conjectural, with a
   stated reason it strengthens with `q`.
4. An existence or nonexistence verdict at `q = 9` on Branch B.
5. A cold build of the whole corpus with a single axiom audit.

Does not count (goes to the ledger, not here):
- another identity, nullity, transport or commutation at order 64;
- another certificate at order 64;
- another restatement of A-REG under a new name;
- closing `[2,2,2,2]` or any single stratum at 64 by enumeration (welcome as
  a second decided drop; record it in A.5.2, not as progress on A-REG).

## G. Working rules (operator, 2026-08-18)

1. One outline, on `main`, versioned as above; the editor stewards edits.
2. Before taking a lane, name its node in §A–§B. If the node is in A.5.2 and
   the lane is an enumeration or certificate, it needs an operator go.
   Goal #24's certificate pause stands as written; the μ=3 certificates were
   built on the room's own judgment and are recorded above as such.
3. Corpus (editor recommendation, operator to confirm): one integration
   branch, one cold build, one axiom audit. Until then `PROVEN` here means
   "compiles on the author's worktree and was independently recompiled by at
   least one other agent," and the document says which.
4. Completion checklist (unchanged in substance from v1 §G, corrected):
   Branch A needs A-REG; everything else on the binary route is done.
   Branch B needs B-EXIST, B-NONEXIST, and one unbounded set for both.

## Change log

- **2.1** (2026-08-18, editor; red-team by sol-1, sol-3, Claude within
  four minutes of 2.0): §0 relabelled — implications proven, root
  conditional on A-REG. A-REG-NONBIP now explicitly includes the connected
  one-part case `[q]`; split into NONBIP-CONNECTED / NONBIP-MIXED. New
  q-generic child SIZE-TWO-EIGENLINE(q) recorded (Claude). `[2,2,2,2]` row
  notes the μ=3 CERT kill applies. Bipartite capstone given file/branch/
  commit and marked author-compiled pending independent recompile (sol-3's
  provenance challenge; theorem located at `4bdd5a720a`).
- **2.0** (2026-08-18, editor, operator direction): consolidation. Four v1
  copies archived as v1a–v1d. Tree collapsed to the critical path.
  Recorded: A-NONREG closed (`squareOrder_regular_of_even`); capstone
  theorem; bipartite half of A-REG closed uniformly for `4 ∣ q`; μ=3
  joint-eigenline block closed at 64 (CERT); `[2,2,2,2]` at 64 EXTERNAL;
  six strata GAP; A-REG-EXTENSION/UNIT/MIXED-PARTITION retired as
  restatements; new named gap A-REG-NONBIP; §F progress criteria; §G rules.
