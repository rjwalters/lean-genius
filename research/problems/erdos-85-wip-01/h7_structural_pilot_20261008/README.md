# H7 t=0 structural cubes: extra-clause feasibility pilot (2026-10-08)

Question: do Lean-provable extra clauses make the 28 structural H7/T0 cubes
(`orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf F i`, 17,633 vars / 720,825 clauses)
solvable by SAT, so they can be certified with `cake_lpr`?

Status: **pilot / discovery evidence only.** No cube is closed. Nothing here is a certificate
for a whole cube. All computation ran on the e85 cloud builder (pinned CaDiCaL 3.0.1,
`cake_lpr` at `a36874a8`), ≤ 6 solver threads.

## Answer in one paragraph

No extra-clause family makes a cube fall to a single 30-minute solve. But one family changes
the picture: **high-side symmetry breaking (`hsb`)**. The completion semantics has a symmetry
group nobody had used: permute the seven high labels and swap the two singleton copies of any
label, *keeping every empty vertex fixed* (`S7 ⋉ (Z/2)^7`, order 645,120). It preserves C4-freeness,
the fixed high sector, the low degrees and the pinned empty mask, so it acts inside every cube.
Normalising the rows of the first three empty vertices against that group leaves a few thousand
to ~33k canonical row-triples per cube, and **every sampled leaf (60/60 over five cubes) was
UNSAT in 0–712 s**. That gives a cube-and-conquer route at an estimated ~70–480 CPU-hours per
cube. The implied facts (capacity, forbidden pair, |X| ≥ 35−4a) and the already-formalised
diagonal stabilizer lex-leader had no measurable effect.

## Inputs and identity

`gen_pilot.py` rebuilds each cube with the reviewed Python generator
(`sat49/check_h7_t0_canonical_compact.py` + 21 mask units) and asserts the bytes hash to the
frozen root hash in `h7-frontier-map-20260915/results.json`. Checked this way: F9_t0, F9_t1,
F8_t0, F7_t14, F6_t5 (`base_sha256` in `receipts/*.json`). The byte identity of the Python base
CNF with the Lean term was **not** re-run in this pilot (the Lean streaming emitter
`...CanonicalCnfEmit.lean` exists for that; the earlier path
`artifacts/erdos85-sat49/h7canon/cubes_compact/` no longer exists on the Mac).
Extra clauses are appended after the cube, matching
`orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf = cube ++ extra`.

## Per-fact impact (F9_t0, CaDiCaL 3.0.1, 1,800 s cap each)

| fact | clauses added | aux vars | 30-min result | adapter needed | impact |
|---|---:|---|---|---|---|
| `cap` singleton ≤ 2 empty nbrs, pair ≤ 1 | 931 | no | UNKNOWN (with fp, x35) | **sound under current adapter** (edge-only, entailed) | none: on 12 identical hsb3 leaves, mean 536k conflicts with vs 596k without (noise) |
| `fp` forbidden pair X ⊆ F | 525 | no | UNKNOWN | **sound under current adapter** | none; each clause is already a binary C4 clause after the 21 cube units |
| `x35` \|X\| ≥ 35−4a | 1,491 | yes | UNKNOWN | **needs orbit/existential adapter** (fresh auxiliaries) | none here; vacuous on F9 (bound −1), 3 on F8, 7/11 on F7/F6 (not measured there) |
| `dlex` diagonal Aut(mask) lex-leader (6 elements on F9_t0) | 25,835 | yes | UNKNOWN | **needs orbit-representative adapter** | none visible |
| `hsb1`/`hsb2`/`hsb3` high-side row normalisation | 3,706 / 11,439 / 134,917 | no | UNKNOWN | **needs orbit-representative adapter** | decisive when combined with cubing, see below |
| combo `cap,x35,dlex,hsb3` | — | yes | UNKNOWN | orbit adapter | — |

The first three rows hold in every completion graph, so they are semantic consequences of the
CNF and can only help as redundant clauses. They did not. Symmetry breaking is the only family
that removes models.

## Cubing on top of hsb3

`hsb3` forces the singleton/pair neighbourhoods ("rows") of empties 7, 8, 9 to be lex-minimal
(DIMACS edge order) along the stabilizer chain of the high-side group. The surviving row-triples
are the leaves. Each sampled leaf fixes those three rows by units on top of `cube ++ hsb3`.

| cube | leaves | sampled | UNSAT | mean s | max s | mean conflicts | est. CPU-h (leaves × mean) |
|---|---:|---:|---:|---:|---:|---:|---:|
| F9_t0 | 32,538 | 12 | 12 | 53.3 | 145 | 596k | ~480 |
| F9_t1 | 11,025 | 12 | 12 | 78.7 | 492 | 799k | ~240 |
| F8_t0 | 32,538 | 12 | 12 | 39.0 | 120 | 456k | ~350 |
| F7_t14 (C7) | 9,442 | 12 | 12 | 38.0 | 157 | 389k | ~100 |
| F6_t5 | 3,456 | 12 | 12 | 72.1 | 712 | 723k | ~70 |

Twelve samples from a heavy-tailed distribution: treat each estimate as good to a factor of
2–3. Extrapolated naively to 28 cubes this is of order 5,000–10,000 CPU-hours, the same scale
as the H1 census (≈3,500 CPU-hours).

Splitting deeper by hand is worse than letting CDCL work: extending F9_t0 leaves by random
compatible rows of empties 10–11 gives ~400 × ~50 sub-leaves at ~2k conflicts each (≈ 40M
conflicts per depth-3 leaf vs ≈ 0.6M measured). Depth 3 is about right for this row order.
Static `hsb4` generation was abandoned (> 13 min, > 4 GB in Python, millions of clauses).

## Certificate path (step 4)

Six F9_t0 hsb3 leaves were solved with binary LRAT streamed through a FIFO into `cake_lpr`:
6/6 `s VERIFIED UNSAT` (3–147 s wall including the check), `receipts/cert.tsv`.
These certify `cube ++ hsb3 ++ leaf-units` only, i.e. sampled leaves, not the cube.

The leaf cover can also be discharged on the SAT side: `gen_pilot.py --cover` emits
`cube ++ hsb3 ++ (one blocking clause per leaf)`; its UNSAT says every model of `cube ++ hsb3`
lies in a leaf. Both cover CNFs tried solved and verified in seconds (see "Cover CNF" below).

## Lean soundness: what exists, what is missing

Compiled on the builder in this pilot (axioms `propext`, `Classical.choice`, `Quot.sound` only):

* `proofs/Proofs/Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeOrbitExtraClauses.lean`
  * `SevenHighT0CanonicalExtraClausesOrbitSound F i extra`: every completion graph of the cube
    yields **some** model of `cube ++ extra` (the witness may be another graph of the orbit and
    may set auxiliaries freely).
  * `sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_orbitExtraUnsat`: orbit-sound + UNSAT ⇒
    semantic exclusion of the cube.
  * `sevenHighT0CanonicalExtraClausesOrbitSound_of_edgeOnly_representative`: for edge-only
    clauses it suffices to produce, for each completion `H`, a completion `H'` of the same cube
    whose edge valuation satisfies them.
  * `sevenHighT0CanonicalExtraClausesOrbitSound_of_sound`: the existing strong obligation
    implies the new one.
  * `cnf_unsat_of_case_split`: UNSAT of every leaf extension plus UNSAT of the cover CNF ⇒ UNSAT.
* `proofs/Proofs/Erdos85OrderFortyNineSevenHighT0CanonicalHighSymmetry.lean`
  * `sevenHighT0CanonicalHighRelabel σ flip H` (empties fixed, singleton `(w,c) ↦ (σ w, flip w c)`,
    pair `{a,b} ↦ {σa,σb}`).
  * `SevenHighT0CanonicalCompletionSemantics.highRelabel`: semantics invariant.
  * `sevenHighT0CanonicalEmptySemanticMask_highRelabel`: semantic empty mask unchanged.

The existing adapter `SevenHighT0CanonicalExtraClausesSound` quantifies over every base
valuation of every graph. It supports `cap` and `fp` only. It cannot support `hsb`/`dlex`
(true for one orbit representative) or `x35`/`dlex` auxiliaries (need an existential extension).

Still to prove for `hsb` (not started; estimate 400–600 lines, several builder iterations):

1. **Composition.** `highRelabel g' (highRelabel g H)` has the edge valuation of
   `highRelabel (g' * g) H` (needs the group law on `(σ, flip)` and
   `sevenHighT0PairIndexPerm (σ' * σ) = (…σ).trans (…σ')`).
2. **Lex-min representative.** Minimise `sevenHighT0CanonicalSemanticEdgeCode` over the finite
   set of `(σ, flip)`; same `Finset.exists_min_image` argument as
   `exists_stabilizerLex_relabel`. With (1): the minimiser `H'` satisfies
   `code H' ≤ code (highRelabel g H')` for all `g`.
3. **Code/prefix lemma.** If two valuations agree on edge ids `< p` and differ at `p` with
   `false < true`, the 861-bit MSB-first codes are strictly ordered.
4. **Row cardinality.** In any completion with the pinned mask, empty `e` has exactly
   `7 − deg_E(e)` singleton/pair neighbours (from `low_degree`, `high_empty`). The emitted
   clauses negate only the positive row literals, so this is what turns "contains these
   neighbours" into "the row is exactly this". (Alternative: emit full 35-literal row patterns;
   no cardinality lemma needed but weaker propagation.)
5. **Clause certificate.** Emit each `hsb` clause with a witness `g`; a Bool checker verifies
   that `g` fixes the prefix rows and maps the forbidden row to a lex-smaller one. Generic
   soundness: checker true ⇒ the clause holds for the lex-min `H'` (by 2–4). The clause list
   (25k–135k clauses per cube) is then checked by `native_decide`, as for the other H7 data.
6. Feed `H'` to `…OrbitSound_of_edgeOnly_representative`.

`dlex` already has its orbit-coverage lemma (`exists_stabilizerLex_relabel`) but would still need
(3), the auxiliary-variable encoding soundness, and showed no solver benefit; not recommended.

## Recommendation

1. Do not spend more on monolithic solves or on the implied facts.
2. If the 28 cubes are to be certified by SAT, the route is: `hsb3` + per-leaf CaDiCaL →
   `cake_lpr` streaming + SAT-side cover CNF, with the Lean obligations 1–6 above. Budget of
   order 5–10k CPU-hours (unmeasured for 23 of the 28 cubes) plus roughly a week of Lean work.
   This does not fit the "$0 beyond the running builder" constraint: the builder gives
   ~160 CPU-hours per day.
3. Before committing, two cheap improvements are worth measuring: (a) add the empty-side
   `Aut(mask)` acting on empties alone (independent of the high group; up to a further factor
   |Aut|, 6 on F9_t0) and (b) choose the row order per cube (F6_t5, whose first three empties
   have small rows, has 10× fewer leaves than F9_t0). Also run a 100–200 leaf sample per cube
   to firm up the estimates, since the tail (712 s leaf on F6_t5) dominates.
4. The reviewed structural closures (`H7_CLOSURE_20260915.md`) use the same normalisations
   ("arbitrary-high singleton", "maximum-high") by hand; `hsb` is their SAT counterpart, which is
   why it is the only fact with impact.

## Files

* `gen_pilot.py` — cube + extras generator (`--facts cap,fp,x35,dlex,hsbK`, `--sample-leaves`,
  `--probe-depth`, `--cover`).
* `pilot.sh` — builder-side driver (`gen`, `batch`, `leaves`, `cover`; `cert_one` streams LRAT
  into `cake_lpr`).
* `receipts/results.tsv` — every solve (name, cap, verdict, wall, conflicts).
* `receipts/cert.tsv` — `cake_lpr` verdicts.
* `receipts/*.json` — generator stats (base sha256, clause counts, leaf counts, sampled leaf ids,
  probe branching factors).
* `receipts/tools.txt` — solver/checker hashes.

## Receipts

Run on builder `i-04a61ff360a07bef2` via `e85-remote run erdos85/h7t0-formal-20261007 --host --full`.
Lean builds: jobs `20261008T032551-…-141516` (orbit adapter, 8782 jobs ok) and
`20261008T034051-…-153181` (high symmetry, 8767 jobs ok).

### Cover CNF

`cube ++ hsb3 ++ blocking clauses` was solved and `cake_lpr`-verified for two cubes:

| cube | blocking clauses | wall (solve + check) | cake_lpr |
|---|---:|---:|---|
| F6_t5 | 3,456 | 5 s | `s VERIFIED UNSAT` |
| F9_t0 | 32,538 | 14 s | `s VERIFIED UNSAT` |

So the cover step is cheap; the cost is entirely in the leaves.

## Caveats

* `hsb` soundness currently rests on the argument above and on codex's read-only review of the
  group action and generator (room messages 52576/52577). There is no satisfiable control
  instance that would catch an over-strong clause, and Lean obligations 1–6 are open.
* The timed leaves fix whole rows (positive and negative units). A certificate run should use
  positive-only leaf units so that they are exactly the negations of the blocking clauses.
* Per-cube cost estimates come from 12 leaves each; 23 of the 28 cubes were not sampled.

