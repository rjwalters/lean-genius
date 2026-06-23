# Problem: Ramsey Numbers for k-Uniform Hypergraphs

## Statement

### Plain Language

The Erdős–Szekeres theorem on monotone subsequences is the *graph* Ramsey number
`R(r,s)` specialized to a total order: color the pair `(i,j)` (with `i<j`)
*red* if `a_i < a_j` and *blue* otherwise. The theorem states `R(r,s) ≤ (r-1)(s-1)+1`
for sequences. The natural higher-dimensional generalization asks:

> For each `k ≥ 2`, what is the asymptotic growth of the k-uniform hypergraph
> Ramsey number `R_k(s,t)` — the smallest `n` such that every 2-coloring of
> the k-element subsets of `{1,…,n}` contains a monochromatic clique of size
> `s` (red) or `t` (blue)?

Two refinements that directly extend Erdős–Szekeres:

* **Geometric ES_d(n).** The smallest `N` such that any `N` points in general
  position in `ℝ^d` contain `n` in *convex position* (i.e., the vertices of an
  `n`-element convex polytope). Erdős–Szekeres (1935) is the `d=2` case.
* **Order-type ES.** For an injective `f : Fin n → ℝ^d`, count the longest
  `(d+1)`-monotone chain (a substitute for monotonic subsequences when `d>1`).

### Formal Statement

Let `R_k : ℕ → ℕ → ℕ` denote the diagonal `k`-uniform hypergraph Ramsey number,
i.e. `R_k(s,t) = min { n | ∀ χ : [n]^{(k)} → {0,1}, ∃ S ⊆ [n], |S|=s ∧ χ ≡ 0 on [S]^{(k)},
                                              ∨ ∃ S ⊆ [n], |S|=t ∧ χ ≡ 1 on [S]^{(k)} }`.

The OQ-03 question packages two well-posed sub-goals:

$$
\boxed{
\begin{array}{rl}
\text{(OQ-03a)} & R_k(s,s) \text{ is finite for all } k \geq 2,\ s \geq k.\\[4pt]
\text{(OQ-03b)} & R_k(s,s) \text{ admits the Erdős–Rado upper bound}\\
 & R_k(s,s) \leq \mathrm{tower}_{k-1}(c_k \cdot s) \text{ for some } c_k > 0,\\[4pt]
\text{(OQ-03c)} & R_k(s,s) \geq \mathrm{tower}_{k-2}(c'_k \cdot s^2) \\
 & \text{(Erdős–Hajnal stepping-up; assumes } k \geq 4\text{).}
\end{array}
}
$$

Here `tower_0(x) = x` and `tower_{n+1}(x) = 2^{tower_n(x)}`.

For `k = 2` (graphs) the bound `R_2(s,s) ≤ \binom{2s-2}{s-1}` is the classical
Erdős–Szekeres bound; the existing `proofs/Proofs/ErdosSzekeres.lean` formalizes
the `(r-1)(s-1)+1` *sequence* refinement of this.

## Classification

```yaml
tier: B
significance: 7
tractability: 6
tags:
  - erdos
  - combinatorics
  - ramsey-theory
  - hypergraphs
  - pigeonhole
  - erdos-rado
  - stepping-up
  - wiedijk-100
  - seeker-selected
```

**Significance**: 7/10
**Tractability**: 6/10

OQ-03a alone is tractable in Lean modulo Mathlib's existing finite-Ramsey
machinery; OQ-03b is a clean induction once OQ-03a is set up; OQ-03c requires
the Erdős–Hajnal stepping-up construction, which is the harder half.

## Why This Matters

1. **Cornerstone of Ramsey theory.** Hypergraph Ramsey numbers control the
   "Hales–Jewett style" partition theorems — every monotone-subsequence
   refinement of pigeonhole has a hypergraph analogue.
2. **Open conjecture territory.** Even `R_3(s,s)` is one of the major open
   problems: the best bounds are `2^{c s} ≤ R_3(s,s) ≤ 2^{c s^2 \log s}`
   (Conlon–Fox–Sudakov 2010). Closing the gap would be a major advance.
3. **Geometric ES_d.** The geometric Erdős–Szekeres ES(n) ≤ \binom{2n-4}{n-2}+1
   (Tóth–Valtr 2005) and ES(n) ≥ 2^{n-2}+1 (Erdős–Szekeres conjecture, open in
   general; resolved up to constants by Suk 2017). Higher-dimensional ES_d(n)
   sits between these and the hypergraph Ramsey numbers.
4. **Reduction targets for `proofs/Proofs/ErdosSzekeres.lean`.**
   `erdos_szekeres_tight_axiom` (currently axiomatized) is precisely the
   lower-bound half of `R_2`. A clean `R_k` framework would let us discharge
   that axiom as a corollary of the `k=2` case of OQ-03c.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-szekeres` | Sequence version (k=2). 2 axioms (`erdos_szekeres_existence_axiom`, `erdos_szekeres_tight_axiom`); the `_tight_axiom` is the diagonal lower bound for `R_2`, which OQ-03c specializes when `k=2`. |
| `erdos-szekeres-oq-01` | Stub — related OQ on the original theorem. |
| `ramsey` (if/when added) | Standard graph Ramsey numbers `R_2(s,t)`, which `R_k` generalizes. Mathlib does not currently expose `R_k` for `k > 2`. |
| `pigeonhole` | Underlying tool for the `k = 2` base case of the Erdős–Rado induction. |

## Approach Sketch (for Lean formalization)

1. **Define `kColoring n k`** as `Finset (Fin n) → Bool` restricted to `k`-element
   subsets, i.e. functions `χ : { s : Finset (Fin n) // s.card = k } → Bool`.
2. **Define `RamseyK k s t n`** as the proposition "every `k`-coloring of
   `[n]^{(k)}` has a monochromatic `s`-clique or `t`-clique"; let
   `ramseyNumberK k s t` be the least such `n`.
3. **OQ-03a — finiteness.** Induct on `k`: the `k = 2` case is the standard
   Ramsey number, available as `SimpleGraph.ramseyNumber` in Mathlib. The
   inductive step uses Erdős–Rado's "neighborhood-tree" construction.
4. **OQ-03b — Erdős–Rado upper bound.** Tower-type induction on the same
   structure: each step multiplies `n` by `R_{k-1}(s,s)`, so we get
   `R_k(s,s) ≤ 2^{R_{k-1}(s-1,s-1) \cdot O(s)}`.
5. **OQ-03c — stepping-up.** Encode a `k`-coloring of `[2^N]^{(k)}` as a
   `(k+1)`-coloring of `[N]^{(k+1)}` via the binary-representation construction
   of Erdős–Hajnal. Needs careful index arithmetic in `Fin`.

Steps 1–3 are realistic for a few research sessions; step 4 is one session if
step 3 lands; step 5 is the harder half and may need its own OQ.
