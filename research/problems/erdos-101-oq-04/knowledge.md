
## Session 2026-07-10 (researcher-3) — two named surface points of the ternary conic (proofs machine-checked)

**Mode**: REVISIT (MODERATE) · **Outcome**: progress (2 theorems, 0 axioms). The quartic
four-point-line engine is saturated and has an open PR (#37106) adding the conic ⟺ four-point-line
characterization + `symmetric_triple_on_ternary_conic`. To stay orthogonal and non-colliding
(EOF placement vs #37106's insert-after-line-3088), I formalized the **two explicit surface-point
remarks** left in the `quartic_quadruple_family_criterion` docstring prose:

- `conic_slice_neg_eq_circle (p r) : Q(p,−p,r) = p²+r²` (`ring`) — the conic
  `Q=p²+q²+r²+pq+qr+rp` collapses to the circle on the slice `q=−p`; the algebraic core of
  "the symmetric family is the slice q=−p".
- `oblique_triple_on_ternary_conic : Q(−8/3,1/3,1) = 5` (`norm_num`, `=45/9`) — the oblique
  witness is a genuine conic point, the oblique twin of #37106's symmetric version.

**Verification.** Full-file `lake env lean` was NOT possible: this fresh worktree (recreated
after the worktree-eater deleted mine mid-session) has no `.lake`, and the file's dependency
`Proofs.Erdos101OQ01` olean is unbuilt in the main repo (docker down, `lake build` blocked). But
both lemmas reference **no local definitions** — only `ℝ`, `ring`, `norm_num` — so I verified them
**standalone** (`import Mathlib`) against the pinned Mathlib v4.26.0 oleans: exit 0, no errors,
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (axiom-free). In-file integration is
trivial (no name clashes, no local-context use). File `Erdos101OQ04.lean` 3194→3222 lines;
research-only (parent erdos-101 meta lists it as a bare additionalFile, no lineCount to sync).

**★Worktree-eater note.** My worktree was deleted mid-`lake env lean`; recovered via
`git worktree prune; git worktree add .loom/worktrees/researcher-3 -B <branch> origin/main`.
The recreated worktree has NO `.lake` → for verification, run standalone snippets from the MAIN
repo's `proofs/` (which retains Mathlib oleans) rather than the worktree.

## Session 2026-07-11 (researcher-2) - infinitely many distinct four-point lines

**Mode**: REVISIT (MODERATE) | **Outcome**: progress (PR #38258, axiom-free trio)

- Added companion `Erdos101OQ04Infinite.lean`: `quartic_four_point_lines_infinite` — the
  quartic carries INFINITELY MANY distinct four-point lines (symmetric circular slice
  `q=-p`; `symmetricAbs p := {p,-p,±sqrt(5-p^2)}` injective on (0,1), each a genuine line).
- Filled a real gap: mother file only had boundedness/sharpness of the fixed surface Q=5
  and 2 witnesses, never infinitude. No super-linear-growth claim (that stays OPEN).
- Gotchas: nlinarith can't prove `!=` (use `.ne`/`.ne'` or `exfalso;nlinarith[eq]`); don't
  `set s:=sqrt..` when later using Real.sq_sqrt (abstraction won't fold new occurrences).
- Next: turn infinitude into a per-n count with a joint no-five-collinear certificate.

## Session 2026-07-12 (researcher-3) — SATURATION ASSESSMENT, no code change (honest release)

**Mode**: REVISIT (RICH) · **Outcome**: nothing found — released without PR.

Surveyed the full OQ-04 corpus (mother `Erdos101OQ04.lean` 3536 L / 97 thm / **1 real sorry**
= `solymosi_stojakovic_lower_bound` line 362, the genuine OPEN Solymosi–Stojaković construction
at rate `n^{2−C/√log n}`; companions `Infinite` 0-sorry, `OQ01` 0-sorry, `Similarity` 0-sorry).
The other 8 "sorry" grep hits are all docstring prose, not code.

**Independent route attempted & found already-done.** Before reading others' favored-approach
notes, I independently derived the positive-definiteness of the governing ternary form
`Q = p²+q²+r²+pq+qr+rp` via the SOS decomposition `Q = ½((p²+q²+r²)+(p+q+r)²)`, intending to add
it as the structural reason the surface `Q=5` is bounded. **This is already fully formalized** in
the mother file (lines 3425–3534): `ternary_conic_eq_half_sum_of_squares`, `ternary_conic_nonneg`,
the sharp radius shell `ternary_conic_sq_sum_mem_Icc` (`[5/2,10]`) with BOTH endpoints attained
(`ternary_conic_sq_sum_range_sharp`), origin avoidance, and the eigenvalue (2, ½) interpretation.
The conic-algebra front is exhaustively saturated.

**Assessment.** Every tractable front is saturated (conic characterization + boundedness/shell +
sharpness + infinitude + similarity invariance + counting infrastructure + explicit witnesses).
The single remaining sorry IS the open problem — a >1000 LOC probabilistic construction, not
session-sized, not Aristotle-suitable. The 3536-line mother file is also under active-PR contention
(#37106, #38258), so a marginal cosmetic addition would be collision-prone enumeration theater.
Released the claim with no code change — the honest outcome. Next genuine progress requires the
actual Solymosi–Stojaković construction (Path A projected grid or Path B parabola), a research
frontier, not incremental scaffolding.

## Session 2026-07-13 (researcher-1) — exact collinearity bound for polynomial graphs

**Mode**: REVISIT (RICH, active multi-researcher). **Outcome**: progress — axiom-free,
build-verified (`LAKE_UNSAFE=1 ./bin/lake env lean`, EXIT 0, no warnings; `#print axioms`
on all three new results = `[propext, Classical.choice, Quot.sound]`).

### What I Did
Independent route (no collision with the active Grünbaum/Solymosi–Stojaković count sorries,
nor the Infinite/Rational/Similarity companions). The mother module's `noFiveCollinear_of_onPolyGraph`
is capped twice — at the fixed count *five* and at degree ≤ 4, both artefacts of the quartic
`y = x⁴ − 5x²`. New companion `Erdos101OQ04PolyDegree.lean` removes both, proving the **exact**
fact behind the quartic construction:
- `card_collinear_on_polyGraph_le` — for `deg Poly ≥ 2` and a non-vertical line `a–b`, any
  `Finset` of points lying on `y = Poly.eval x` and collinear with `a, b` has `card ≤ deg Poly`.
  Proof: the line meets the graph at the roots of `q = C(Δx)·Poly − C(Δy)·X − C(const)`;
  `deg q = deg Poly` (the `deg ≥ 2` hypothesis keeps the degree-≤1 correction from cancelling
  the top coefficient `(Δx)·leadingCoeff ≠ 0`), and the first-coordinate map injects the subset
  into `q.roots`, so `card ≤ #roots ≤ deg q = deg Poly`.
- `not_succ_natDegree_collinear_on_polyGraph` — the "no `deg+1` collinear" reading.
- `noFiveCollinear_of_onPolyGraph_via_card` — re-derives the mother module's five-collinear
  lemma from the exact bound at `d ≤ 4 < 5`, confirming subsumption.

### Key Findings
- The geometry has NO ceiling at five or at degree four: a quartic graph is no-five-collinear,
  a **quintic** graph is no-six-collinear, and generally a degree-`d` graph is
  no-`(d+1)`-collinear. This is the honest structural content — the degree-general version
  directly relevant to the higher-degree / higher-dimensional line-count theme of Erdős #101.
- Does NOT touch the open count sorries (`grunbaum_lower_bound_three_halves`,
  `solymosi_stojakovic_lower_bound`); those remain the analytic frontier.

### GOTCHA / process
- `collinear_self p q : collinear p p q` (NOT `collinear p q p`); for `collinear a b a`/`a b b`
  use `unfold collinear; ring`.
- `rcases hp with rfl | …` on `p = a` can substitute the WRONG variable (kills `a`, not `p`,
  when both are local); use `rcases hp with h | … <;> rw [h]` to stay direction-agnostic.

### Files Modified
- proofs/Proofs/Erdos101OQ04PolyDegree.lean (NEW, 155 lines, 3 thm, 0 axioms, 0 sorries)
- src/data/research/problems/erdos-101-oq-04.json (insights/builtItems)

### Next Steps (unchanged, hard)
- The open growth bounds Ω(n^{3/2}) and n^{2−o(1)} remain the frontier; the no-five-collinear
  certificate for a *growing* non-grid family is the bridge. This companion supplies the
  degree-general no-collinear principle any higher-degree witness would rely on.
