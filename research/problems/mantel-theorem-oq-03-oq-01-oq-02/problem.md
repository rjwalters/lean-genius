# Problem: Minimum Degree of the General Turán Graph `turanGraph n r` is Exactly `n − ⌈n/r⌉`

**Slug**: mantel-theorem-oq-03-oq-01-oq-02
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent entry `mantel-theorem-oq-03-oq-01` proved the $r = 2$ sharpness certificate
for Mantel's minimum-degree bound: the balanced complete bipartite graph
`turanGraph n 2` is triangle-free and has minimum degree exactly $\lfloor n/2\rfloor$.
This problem lifts that computation to **every** $r \ge 1$, certifying sharpness of the
Turán minimum-degree bound $(1 - 1/r)\,n$ for $K_{r+1}$-free graphs (the parent's third
open question).

Recall Mathlib's definition (`Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`):
$$
\texttt{turanGraph } n\ r \;:\; \text{SimpleGraph }(\mathrm{Fin}\,n),
\qquad
v \sim w \iff (v : \mathbb{N}) \bmod r \;\ne\; (w : \mathbb{N}) \bmod r .
$$
So `turanGraph n r` is the complete $r$-partite graph whose parts are the residue classes
$\{v : v \bmod r = j\}$ for $j = 0, \dots, r-1$ inside $\mathrm{Fin}\,n$. A vertex $v$ is
adjacent to **every** vertex outside its own residue class, hence
$$
\deg v \;=\; n \;-\; \bigl|\{\,k < n : k \bmod r = v \bmod r\,\}\bigr|
\;=\; n - c_r(v \bmod r, n),
$$
where $c_r(j, n) = \#\{k < n : k \bmod r = j\} = \lceil (n - j)/r\rceil$ is the size of the
$j$-th residue class. The class sizes decrease weakly in $j$, so the **largest** class is
$j = 0$ with size $\lceil n/r\rceil$; the minimum degree is attained there:
$$
\boxed{\;(\texttt{turanGraph } n\ r).\mathrm{minDegree} \;=\; n - \lceil n/r\rceil
\;=\; n - \tfrac{n + r - 1}{r}\ \ (\text{Nat division}).\;}
$$

**Target Lean theorem** (signature to formalize):

```lean
open SimpleGraph

/-- The exact per-vertex degree of the general Turán graph: `n` minus the size of the
own residue class of `v` modulo `r`. -/
theorem turanGraph_degree (n r : ℕ) (hr : 0 < r) (v : Fin n) :
    (turanGraph n r).degree v
      = n - Nat.count (fun k => k % r = v.val % r) n := by
  sorry

/-- **Sharpness, minimum degree, general `r`.** For `n ≥ 1` and `r ≥ 1`, the Turán graph
`turanGraph n r` has minimum degree exactly `n − ⌈n/r⌉`, attained on the residue class 0. -/
theorem turanGraph_minDegree (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    (turanGraph n r).minDegree = n - (n + r - 1) / r := by
  sorry

/-- **Sharpness certificate for the parent's third open question.** `turanGraph n r` is
`K_{r+1}`-free and its minimum degree `n − ⌈n/r⌉` witnesses that the `(1 − 1/r)·n`
minimum-degree bound for `K_{r+1}`-free graphs cannot be improved. -/
theorem turanGraph_minDegree_sharp (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    (turanGraph n r).CliqueFree (r + 1)
      ∧ (turanGraph n r).minDegree = n - (n + r - 1) / r :=
  ⟨turanGraph_cliqueFree hr, turanGraph_minDegree n r hn hr⟩
```

Here $(n + r - 1)/r$ is the `Nat`-division encoding of $\lceil n/r\rceil$. Specializing to
$r = 2$ recovers the parent: $n - \lceil n/2\rceil = \lfloor n/2\rfloor = n/2$, so
`turanGraph_minDegree n 2 hn (by norm_num)` reduces to the parent's `turanTwo_minDegree`.

### Plain Language

The Turán graph splits $n$ labelled vertices into $r$ groups as evenly as possible (group
$j$ is "everything with remainder $j$ when divided by $r$"), and joins two vertices exactly
when they are in different groups. Each vertex is therefore connected to everyone outside
its own group, so its degree is $n$ minus the size of its own group. The vertex with the
*fewest* neighbours lives in the *largest* group; because the groups are as balanced as the
division allows, the largest group has $\lceil n/r\rceil$ members, so the smallest degree in
the whole graph is $n - \lceil n/r\rceil$. The parent proved this for two groups
($r = 2$, the triangle-free / bipartite case); here we prove it for any number of groups,
which is exactly the extremal construction behind Turán's theorem.

### Why This Matters

Turán's theorem says a $K_{r+1}$-free graph on $n$ vertices has at most as many edges as
`turanGraph n r`. Its *local* companion — the minimum-degree version — states that a
$K_{r+1}$-free graph must contain a vertex of degree at most $(1 - 1/r)\,n$. Such an upper
bound is only meaningful once one exhibits a graph attaining it, and the natural witness is
the Turán graph itself. Computing `(turanGraph n r).minDegree = n − ⌈n/r⌉` supplies exactly
that witness for every $r$, closing the loop opened by the parent's third open question in
one uniform statement. It also produces, as a byproduct, the full minimum-degree data of the
extremal graph in Turán's theorem — a clean, reusable Mathlib-level fact — and demonstrates
that the parent's residue-counting technique scales from the parity ($r = 2$) case to
arbitrary moduli.

## Known Results

### What's Already Proven

- **Parent, $r = 2$ sharpness** — gallery entry `mantel-theorem-oq-03-oq-01`
  (`turanTwo_minDegree`, `turanTwo_sharp`): `turanGraph n 2` is triangle-free and has
  minimum degree exactly $\lfloor n/2\rfloor$, verified, $0$ axioms. This is the $r = 2$
  specialization of the present target.
- **Mantel minimum-degree corollary** — grandparent `mantel-theorem-oq-03`: every
  triangle-free graph on $n \ge 1$ vertices has a vertex of degree $\le \lfloor n/2\rfloor$.
- **Mantel's theorem** (edge bound $\lfloor n^2/4\rfloor$) — gallery entry `mantel-theorem`.
- **Turán graph API in Mathlib** — `SimpleGraph.turanGraph`, `turanGraph_adj`,
  `turanGraph_cliqueFree (hr : 0 < r) : (turanGraph n r).CliqueFree (r + 1)`,
  `turanGraph_eq_top`, and the exact edge-count `card_edgeFinset_turanGraph`
  (`Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`).
- **Reusable residue-counting lemmas from the parent** — `card_fin_filter_val`
  (bridging a `Fin n` filter to `Nat.count` over `range n`) and the closed forms
  `count_mod_two_eq_zero/one`. The $r = 2$ closed forms are the base cases of the general
  residue-class-size count needed here.

### What's Still Open

- No Lean statement of the general degree formula
  $\deg v = n - c_r(v \bmod r, n)$ for `turanGraph n r`.
- No Lean closed form for the residue-class size
  $c_r(j, n) = \#\{k < n : k \bmod r = j\} = \lceil (n - j)/r\rceil$, nor the monotonicity
  $c_r(0,n) \ge c_r(j,n)$ that pins the minimum-degree vertex to residue class $0$.
- No Lean statement `(turanGraph n r).minDegree = n − ⌈n/r⌉` for general $r$, and hence no
  formal certificate that the $K_{r+1}$-free minimum-degree bound $(1 - 1/r)\,n$ is sharp.

### Our Goal

Prove, with $0$ axioms, the three theorems above: the exact per-vertex degree
$\deg v = n - \mathrm{count}(\cdot \bmod r = v \bmod r)\,n$, the closed-form minimum degree
$n - \lceil n/r\rceil$, and the packaged sharpness certificate combining it with
`turanGraph_cliqueFree`. Confirm the $r = 2$ specialization reproduces the parent's
`turanTwo_minDegree`, and record the corollary that $n - \lceil n/r\rceil \le (1 - 1/r)\,n$
(with equality when $r \mid n$), certifying the parent's third open question.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| mantel-theorem-oq-03-oq-01 | Direct parent: the $r = 2$ case; this problem generalizes its `turanTwo_minDegree` to all $r$ | `turanGraph_cliqueFree`, `card_fin_filter_val`, `Nat.count` closed forms, `minDegree` antisymmetry |
| mantel-theorem-oq-03 | Grandparent: the triangle-free minimum-degree bound this construction shows is sharp | Degree double counting, `exists_degree_le_card_div_two` |
| mantel-theorem | The global edge bound $\lfloor n^2/4\rfloor$; `turanGraph n 2` is its extremal example | Extremal edge counting, complete bipartite witness |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Port the parent's residue-count architecture from mod 2 to mod r (recommended).**
   The parent computes $\deg v$ as a `Nat.count` over `range n` of a residue predicate via
   `card_fin_filter_val`, then evaluates the count in closed form by induction using
   `Nat.count_succ`. Reuse `card_fin_filter_val` verbatim; it is stated for a general
   `Q : ℕ → Prop`. The neighbour set of $v$ in `turanGraph n r` is
   $\{w : v \bmod r \ne w \bmod r\}$, so
   $\deg v = n - \#\{w : v \bmod r = w \bmod r\}$ (complement within `Fin n`), and the
   subtracted count is `Nat.count (fun k => k % r = v.val % r) n`.
   - Why it might work: the $r = 2$ file is a fully verified template; the only genuinely
     new lemma is the general residue-class-size count.
   - Risk: `Nat`-division / ceiling bookkeeping for $\lceil (n-j)/r\rceil$ is fiddlier than
     the two-way `omega` split that sufficed for parity.

2. **Approach B — General residue-class-size lemma, then minimize over $j$.**
   Prove a standalone lemma
   $\#\{k < n : k \bmod r = j\} = \lceil (n - j)/r\rceil$ for $j < r$ (e.g. by induction on
   $n$ with `Nat.count_succ`, or via a division argument), then show
   $j \mapsto \lceil (n-j)/r\rceil$ is antitone so the max class size is $\lceil n/r\rceil$ at
   $j = 0$. Feed both into the `minDegree` antisymmetry the parent used
   (`minDegree_le_degree` at vertex $0$ for the upper bound;
   `le_minDegree_of_forall_le_degree` with $n - \lceil n/r\rceil \le \deg v$ for the lower).
   - Why it might work: cleanly separates the arithmetic (class-size closed form) from the
     graph theory (minDegree antisymmetry).
   - Risk: needs an honest antitonicity proof and careful handling of $n < r$ (empty classes
     for $j \ge n$, where the graph is complete $K_n$ and every degree is $n - 1$; note
     $n - \lceil n/r\rceil = n - 1$ there, so the formula still holds).

### Key Difficulties

- **Ceiling / floor `Nat`-division bookkeeping.** The class size $\lceil (n-j)/r\rceil$ and
  the target $n - (n + r - 1)/r$ mix subtraction, ceiling division and the identity
  $\lceil n/r\rceil = (n + r - 1)/r$. `omega` handles linear `Nat` goals but not division in
  general; expect to introduce division lemmas of the form `Nat.add_div_right` /
  `Nat.succ_div` or an explicit `⌈a/b⌉ = (a + b - 1)/b` rewrite, then close residual linear
  goals with `omega`.
- **Identifying the minimizing vertex.** Unlike $r = 2$ (only two class sizes differing by
  at most one), for general $r$ one must prove the class-size function is antitone in $j$ to
  justify that residue $0$ minimizes the degree. Vertex $0 \in \mathrm{Fin}\,n$ (needs
  $n \ge 1$) is the concrete witness whose degree realizes the minimum.
- **Degenerate ranges.** For $n \le r$ some residue classes are empty; the graph is complete
  and every vertex has degree $n - 1$. The formula $n - \lceil n/r\rceil = n - 1$ must be
  checked to survive this regime rather than special-casing it.

### What Would a Proof Need?

- Key lemma 1: `card_fin_filter_val` (reuse from parent) to move the neighbour count to
  `Nat.count` over `range n`.
- Key lemma 2: the general residue-class-size closed form
  $\mathrm{count}(\cdot \bmod r = j)\,n = \lceil (n - j)/r\rceil$, by induction on $n$ with
  `Nat.count_succ` (a lemma of the form `count_mod_eq_size` — verify the exact name/shape in
  `Mathlib.Data.Nat.Count`, do not assume a ready-made one exists).
- Key lemma 3: antitonicity of class size in the residue $j$, giving max size
  $\lceil n/r\rceil$ at $j = 0$.
- Key lemma 4: `minDegree` antisymmetry via `minDegree_le_degree` and
  `le_minDegree_of_forall_le_degree` (`Mathlib.Combinatorics.SimpleGraph.Finite`), exactly
  as in `turanTwo_minDegree`.
- Technical requirements: `Nonempty (Fin n)` from $n \ge 1$; `turanGraph_adj` to unfold
  adjacency; `SimpleGraph.neighborFinset_eq_filter`; `Nat` ceiling-division lemmas plus
  `omega` for the arithmetic residue.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The **graph-theoretic scaffolding is a verified template**: `turanTwo_degree`,
  `turanTwo_minDegree` and `turanTwo_sharp` in the parent already exhibit the entire
  `card_fin_filter_val` → `Nat.count` → `minDegree`-antisymmetry pipeline. Generalizing the
  modulus from $2$ to $r$ keeps every structural step.
- The **only new mathematical content** is the closed-form size of a residue class mod $r$
  in $\mathrm{Fin}\,n$ and its antitonicity in the residue — an elementary `Nat.count`
  induction, but with real ceiling/floor `Nat`-division friction that the parity case dodged
  with a two-branch `omega`.
- Similar solved problems: the parent ($r = 2$) is $0$-axiom and verified; Mathlib already
  proves `card_edgeFinset_turanGraph` by the same residue-filtering style, confirming the
  approach is library-supported.
- Techniques available in Mathlib: `Nat.count_succ`, `Nat.count_eq_card_filter_range`,
  `turanGraph_cliqueFree`, `minDegree_le_degree`, `le_minDegree_of_forall_le_degree`,
  `omega`, and `Nat` division lemmas.

**Estimated Effort**:
- Exploration: 0.5–1 day (nail the residue-class-size closed form and its `Nat`-division
  normal form).
- If tractable: 1–2 days for a $0$-axiom file with all three target theorems plus the
  $r = 2$ specialization check.
- If hard: overrun would come entirely from the ceiling-division algebra, not the graph
  theory.

## References

### Papers
- Turán, P., *On an extremal problem in graph theory* (Hungarian),
  *Matematikai és Fizikai Lapok* **48** (1941), 436–452 — the theorem whose extremal graph
  is `turanGraph n r`.
- Mantel, W., *Problem 28*, *Wiskundige Opgaven* **10** (1907), 60–61 — the $r = 2$ base
  case (triangle-free edge bound).

### Online Resources
- https://en.wikipedia.org/wiki/Tur%C3%A1n_graph — the Turán graph $T(n,r)$, its part sizes,
  and its degree sequence.
- https://en.wikipedia.org/wiki/Tur%C3%A1n%27s_theorem — statement of Turán's theorem and the
  extremal graph.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan` — `SimpleGraph.turanGraph`,
  `turanGraph_adj`, `turanGraph_cliqueFree`, `turanGraph_eq_top`,
  `card_edgeFinset_turanGraph`.
- `Mathlib.Combinatorics.SimpleGraph.Finite` — `SimpleGraph.degree`,
  `SimpleGraph.neighborFinset_eq_filter`, `SimpleGraph.minDegree`,
  `SimpleGraph.minDegree_le_degree`, `SimpleGraph.le_minDegree_of_forall_le_degree`.
- `Mathlib.Data.Nat.Count` — `Nat.count`, `Nat.count_eq_card_filter_range`,
  `Nat.count_succ` (the residue-class-size induction engine).
- Parent file `Proofs/MantelTheoremOQ03OQ01.lean` — `card_fin_filter_val` and the
  `count_mod_two_eq_zero/one` closed forms to be generalized.

## Metadata

```yaml
tags:
  - graph-theory
  - combinatorics
  - extremal-graph-theory
  - turan-graph
  - turan-theorem
  - minimum-degree
  - sharpness
related_proofs:
  - mantel-theorem-oq-03-oq-01
  - mantel-theorem-oq-03
  - mantel-theorem
difficulty: medium
source: gallery-gap
created: 2026-06-30
```
