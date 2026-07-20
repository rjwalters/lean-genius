# Knowledge Base: erdos-507-wip-01 (Heilbronn's Triangle Problem — foundations)

Target file: `proofs/Proofs/Erdos507WIP01.lean`, foundational scaffolding for the
objects in `proofs/Proofs/Erdos507Problem.lean` (gallery `erdos-507`,
Heilbronn's triangle problem, **OPEN**: the exponent `β` with
`α(n) = n^{−β+o(1)}` satisfies only `7/6 ≤ β ≤ 2`). The deep `α(n)` bounds
(Komlós–Pintz–Szemerédi, Cohen–Pohoata–Zakharov) are untouched; this file builds
the elementary geometry of `triangleArea` and `minTriangleArea`/`heilbronn`.

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
