# Knowledge Base: erdos-507-wip-01 (Heilbronn's Triangle Problem — foundations)

Target file: `proofs/Proofs/Erdos507WIP01.lean`, foundational scaffolding for the
objects in `proofs/Proofs/Erdos507Problem.lean` (gallery `erdos-507`,
Heilbronn's triangle problem, **OPEN**: the exponent `β` with
`α(n) = n^{−β+o(1)}` satisfies only `7/6 ≤ β ≤ 2`). The deep `α(n)` bounds
(Komlós–Pintz–Szemerédi, Cohen–Pohoata–Zakharov) are untouched; this file builds
the elementary geometry of `triangleArea` and `minTriangleArea`/`heilbronn`.

## Session 2026-07-20 (researcher-1, iter 3) — concrete positive lower bound `heilbronn 3 ≥ 1/2`

**Mode**: continue a RICH node (24 declarations already on main).
**Outcome**: progress — 2 new public declarations, VERIFIED axiom-free
(`[propext, Classical.choice, Quot.sound]`, 0 sorry / 0 axiom / no
native_decide). Host-verified without Docker (parent is Mathlib-only):
`lake env lean` fresh-built `Erdos507Problem.olean`, compiled the child clean
(exit 0), `#print axioms` on both new results.

### What I added
- `heilbronn_three_ge_half : (1:ℝ)/2 ≤ heilbronn 3` — the unit right triangle
  `(0,0),(1,0),(0,1)` is a 3-point unit-disk config whose every ordering of its
  distinct vertices has `triangleArea = 1/2` (`triangleArea_unit` + the
  permutation lemmas), so `1/2` lies in the defining `sSup` set;
  `le_csSup (heilbronn_defining_bddAbove 3 _)`.
- `heilbronn_three_pos : 0 < heilbronn 3` — immediate from the above. Since
  `heilbronn 2 = 0` (no distinct triple below `n=3`, junk `sSup`), this shows
  Heilbronn is **not** monotone across the `2→3` boundary — the reason the
  monotonicity lemmas start at `n=3`.

### Key findings / reusable Lean recipe
- **`Finset.card_eq_three`** certifies a 3-point *real* config has card 3 without
  `decide` (`DecidableEq ℝ` is not computable): supply the three points + the
  three pairwise `≠` via `by simp [Prod.ext_iff]`, and `rfl` for the set equality.
- **Distinct-triple `∀`-bound over a 3-element `Finset`.** After
  `simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hr`,
  `rcases … <;> rcases … <;> rcases …` (27 cases) then
  `first | exact absurd rfl h<pair> | (unfold triangleArea; norm_num)`: the 21
  repeated-vertex cases die on the distinctness hyps, the 6 genuine permutations
  each compute to `1/2` — no need to invoke the permutation lemmas explicitly,
  `norm_num` evaluates each concrete `|·|/2`.
- The lower bound `1/2` is **not tight** (`heilbronn 3 = 3√3/4 ≈ 1.299` via the
  largest inscribed triangle); the tight value needs a max-inscribed-triangle
  upper bound, likely not session-sized.

### Next steps
- Tight `heilbronn 3 = 3√3/4` needs the max-inscribed-triangle bound (open here).
- Deep `α(n)` exponent bounds (KPS lower, CPZ upper) remain open, `7/6 ≤ β ≤ 2`.

## Session 2026-07-20 (researcher-1) — `heilbronn` monotonicity + config existence

**Mode**: continue a RICH node (18 declarations already on main).
**Outcome**: progress — 5 new declarations, VERIFIED axiom-free
(`[propext, Classical.choice, Quot.sound]`, 0 sorry / 0 axiom / no
native_decide). Host-verified without Docker (parent is Mathlib-only):
`lake exe cache get`, fresh-built `Erdos507Problem.olean`, `lake env lean` on the
child, `#print axioms` on all four public results.

### What I added
- `exists_unitDisk_config (n) : ∃ P, P.card = n ∧ IsInUnitDisk P` — a config of
  *every* cardinality exists in the disk, via the equally spaced chord points
  `(k/n, 0)`, `k = 0..n−1` (`(Finset.range n).image`, injective for `n ≥ 1`,
  membership `(k/n)² ≤ 1` since `0 ≤ k/n < 1`). Makes the `heilbronn` defining
  set nonempty.
- `heilbronn_defining_bddAbove (n) (3 ≤ n)` (private) — the `sSup` defining set
  is bounded above by `3` (the boundedness half of `heilbronn_le_three`, isolated
  for reuse).
- `heilbronn_nonneg (n) (3 ≤ n) : 0 ≤ heilbronn n` — `α = 0` is admissible (all
  areas `≥ 0`) and a config exists, so `0 ∈` the set; `le_csSup`.
- `heilbronn_succ_le (n) (3 ≤ n) : heilbronn (n+1) ≤ heilbronn n` — every
  `(n+1)`-witness restricts (delete one point via `Finset.erase`) to an
  `n`-witness with the same bound, so the `(n+1)`-set `⊆` the `n`-set;
  `csSup_le_csSup`.
- `heilbronn_antitone (3 ≤ m ≤ n) : heilbronn n ≤ heilbronn m` — full
  antitonicity on `{n ≥ 3}` by `Nat.le_induction` on `heilbronn_succ_le`.

### Key findings / reusable Lean recipe
- **`csSup_le_csSup (BddAbove t) (s.Nonempty) (s ⊆ t) : sSup s ≤ sSup t`** is the
  right tool for monotone `sSup`s of a *shrinking* defining set. The
  easy-to-miss side condition is `s.Nonempty` on the **smaller** (here `n+1`)
  set — supplied by `exists_unitDisk_config` + the always-admissible bound `0`.
- **The `n ≥ 3` hypothesis is forced by the junk value, not laziness.** For
  `n < 3` no distinct triple exists, the `∀`-bound condition is vacuous, the
  defining set is all of `ℝ` (unbounded above) and `heilbronn n` is the
  `sSup`-junk `0`. Since `heilbronn 3 > 0` (a genuine triangle has positive
  area) but `heilbronn 2 = 0`, monotonicity is **false** across the `2→3`
  boundary — state it from `3` onward.
- **Binder-annotation pitfall.** `fun k => ((k : ℝ)/n, 0)` inside a
  `Finset.range n` image: the ascription `(k : ℝ)` silently retypes the binder
  as `ℝ`, so `Finset.range n : Finset ℕ` no longer matches. Annotate the binder
  `fun k : ℕ => ((k : ℝ)/n, 0)` and cast in the body.
- **Dot notation fails on a `def`-Prop.** `IsInUnitDisk P` unfolds to
  `∀ p ∈ P, …` (a Pi type), so `hdisk.subset` resolves to `Function.subset`
  (nonexistent). Call the namespaced lemma directly: `IsInUnitDisk.subset hdisk …`.

### Next steps
- Sandwich corollary `0 ≤ heilbronn n ≤ 3` (`heilbronn_nonneg` +
  `heilbronn_le_three`).
- Concrete `heilbronn 3` lower witness (largest inscribed equilateral triangle),
  separating it from the junk `heilbronn 2 = 0`.
- The deep `α(n)` exponent bounds (KPS lower, CPZ upper) remain open — not
  session-sized; only `7/6 ≤ β ≤ 2` is known.

## Session 2026-07-20 (researcher-1) — `minTriangleArea` + `heilbronn` bound

**Mode**: continue a MODERATE node (14 lemmas already on main via #39642).
**Outcome**: progress — 4 new declarations, VERIFIED axiom-free
(`[propext, Classical.choice, Quot.sound]`, 0 sorry / 0 axiom / no native_decide).
Host-verified without Docker (parent is Mathlib-only): `lake exe cache get`, then
fresh-built `Erdos507Problem.olean` into `.lake/build/lib/lean/Proofs/`, then
`lake env lean` on the child; `#print axioms` on all three public results.

### What I added
`minTriangleArea P` is the nine-fold nested `⨅` over distinct triples
`p, q, r ∈ P` of `triangleArea p q r`. New declarations:
- `bddBelow_range_of_nonneg` (private) — a nonnegative real family is `BddBelow`
  (lower bound `0`); the recurring side condition for `ciInf_le`.
- `minTriangleArea_nonneg (P) : 0 ≤ minTriangleArea P` — every value is a
  nonnegative `triangleArea` and the empty-index junk value is `0`
  (`Real.sInf_empty`). Proof: `repeat' (Real.iInf_nonneg ⋯ | triangleArea_nonneg)`.
- `minTriangleArea_le (hp hq hr hpq hqr hpr) : minTriangleArea P ≤ triangleArea p q r`
  for distinct `p, q, r ∈ P` — descend the nine `⨅` binders with
  `ciInf_le_of_le`, discharging each `BddBelow` side goal by nonnegativity.
- `heilbronn_le_three (n) (hn : 3 ≤ n) : heilbronn n ≤ 3` — the `sSup` defining
  set is bounded above by `3`: any admissible bound `α` is `≤ triangleArea p q r`
  for some distinct triple (exists since `card = n ≥ 3`, `Finset.two_lt_card_iff`)
  and every unit-disk triangle has area `≤ 3` (`triangleArea_le_three`); close
  with `Real.sSup_le`.

### Key findings / reusable Lean recipe
- **Junk-value semantics over `ℝ`.** In a conditionally complete lattice an `⨅`
  over an empty index type is junk, but over `ℝ` it is `0` (`Real.sInf_empty`),
  so `minTriangleArea P ≥ 0` and `heilbronn n ≤ 3` hold *unconditionally* in the
  index (no nonemptiness hypothesis needed). The right toolkit is the
  `Real.*`-namespaced helpers `Real.iInf_nonneg`, `Real.le_iInf`, `Real.sSup_le`
  (each proved via the empty-set junk value), NOT the `[Nonempty ι]` `le_ciInf`.
- **Descending a deeply-nested `biInf`.** `ciInf_le_of_le (H : BddBelow (range f))
  (c) (h : f c ≤ a) : iInf f ≤ a`. Descend one binder at a time; the `BddBelow`
  side goal at every level is uniformly discharged by
  `bddBelow_range_of_nonneg` + `repeat' (apply Real.iInf_nonneg; intro)`.
- **Universe pitfall.** A local `have nn : ∀ {ι : Sort*} …` inside the proof
  triggers `AddConstAsyncResult.commitConst: constant has level params [u_1]`.
  Hoist the `BddBelow`-from-nonneg helper to a top-level (private) theorem so it
  is properly universe-polymorphic.
- `heilbronn n ≤ 3` needs `n ≥ 3`: for `n < 3` no distinct triple exists, the
  defining `∀`-condition is vacuous, so the set is all of `ℝ` (unbounded above)
  and `heilbronn n` is the `sSup`-junk value `0`. The bound `≤ 3` still holds
  there trivially, but the *proof* route (bounded-above) requires the triple, so
  the theorem is stated for `n ≥ 3`.

### Next steps (unchanged deep tail)
- Monotonicity `heilbronn (n+1) ≤ heilbronn n` (restrict a witness config).
- The deep `α(n)` exponent bounds remain open (KPS lower, CPZ upper) — not
  session-sized; only `7/6 ≤ β ≤ 2` is known in the literature.

## Prior session 2026-07-20 (#39642) — 14 foundational triangle-area lemmas
Shoelace `triangleArea` geometry: nonnegativity, full `S₃` permutation symmetry
(signed-area alternation), the three degenerate cases, collinearity ⟺ zero area,
explicit value `1/2`, unit-disk coordinate bounds `|p_i| ≤ 1`, and the uniform
bound `triangleArea ≤ 3`. All 0 sorry / 0 axiom.

## Session 2026-07-21 (researcher-1) — sharp lower bound heilbronn 3 ≥ 3√3/4

**Mode**: strengthen the crude `heilbronn 3 ≥ 1/2` witness. **Outcome**: progress —
the lower bound at `n = 3` is now **sharp** (equal to the conjectured exact value),
host-verified v4.31 (`lake env lean` exit 0, 0 warnings in the new block;
`#print axioms heilbronn_three_ge` = `[propext, Classical.choice, Quot.sound]`).

`heilbronn_three_ge : 3 * Real.sqrt 3 / 4 ≤ heilbronn 3`. Witness = the equilateral
triangle inscribed in the unit circle, `(1,0), (−1/2, √3/2), (−1/2, −√3/2)` — all three
vertices on the boundary of the unit disk (`(−1/2)² + (√3/2)² = 1/4 + 3/4 = 1`, via
`Real.sq_sqrt`), and every ordering of the vertices has `triangleArea = 3√3/4` (the largest
triangle inscribable in a radius-1 disk). So `3√3/4` is admissible for the `sSup` defining
`heilbronn 3` (`le_csSup` + `heilbronn_defining_bddAbove`), strengthening the right-triangle
bound `heilbronn 3 ≥ 1/2`.

**Recipe** (reusable for concrete-config `heilbronn` lower bounds):
- Compute the canonical-ordering area ONCE: `unfold triangleArea;
  rw [show <projected signed expr> = 3√3/2 from by ring]` (★`ring` sees through the
  `(a,b).1`/`.2` projections of literal pairs — no manual `Prod.fst` reduction needed),
  then `rw [abs_of_nonneg (by positivity)]; ring`.
- Discharge the other 5 ordered triples by permutation-invariance: `triangleArea_swap_left`,
  `triangleArea_swap_right`, `triangleArea_cyclic` inside a `first | …` combinator, each
  branch `rw [<perm chain>]; exact ge_of_eq hval` (any ordering reaches the canonical in
  ≤ 2 swap/cyclic rewrites; a failed `exact` rolls back the `rw`, so ordering is safe).
- Distinctness of the `Real.sqrt`-coordinate pair via `Prod.ext_iff` then `linarith` on the
  `.2` component against `Real.sqrt_pos`.

### Next
- **Matching upper bound `heilbronn 3 ≤ 3√3/4`** would pin `heilbronn 3 = 3√3/4` exactly.
  Requires "every triangle with vertices in the unit disk has area ≤ 3√3/4" — a genuine
  optimization (the current file only has the crude `triangleArea_le_three`, area ≤ 3). Not
  obviously session-sized; the sharp bound follows from the inscribed-equilateral being the
  area-maximizer, which needs a real argument.
- Deep `α(n)` exponent bounds (KPS lower, CPZ upper) remain open (literature: `7/6 ≤ β ≤ 2`).
