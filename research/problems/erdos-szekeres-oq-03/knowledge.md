# Knowledge Base: erdos-szekeres-oq-03

Survey notes for the hypergraph-Ramsey generalization of Erdős–Szekeres.

---

## Problem Understanding

### The diagonal hypergraph Ramsey number `R_k(s,t)`

Fix `k ≥ 2`. The Ramsey number `R_k(s,t)` is the least `n` such that for every
2-coloring `χ : [n]^{(k)} → {0,1}` of the `k`-element subsets of `{1,…,n}`,
there is either an `s`-subset whose `k`-subsets are all `0`-colored, or a
`t`-subset whose `k`-subsets are all `1`-colored. The *diagonal* case is
`s = t`. We write `R_k(s) := R_k(s,s)`.

Special cases already in the gallery / Mathlib:

* `k = 2`, `s = t`: graph Ramsey `R(s,s)`. Mathlib defines it as
  `SimpleGraph.ramseyNumber` but the standard upper bound
  `R(s,s) ≤ \binom{2s-2}{s-1}` is not yet packaged as a clean theorem there.
* `k = 2`, *sequence* refinement (one order, one coloring): the classical
  Erdős–Szekeres `(r-1)(s-1)+1` bound, formalized in `Proofs/ErdosSzekeres.lean`.
* `k = 1`: `R_1(s,t) = s + t - 1` is the pigeonhole principle.

### Why hypergraph Ramsey is the "right" generalization

The Erdős–Szekeres theorem says: among `n` distinct real numbers, an
increasing subsequence of length `r` or a decreasing subsequence of length `s`
exists when `n ≥ (r-1)(s-1)+1`. Re-coloring the pair `(i,j)` by
`χ(i,j) = [a_i < a_j]` turns this into a *2-coloring of the 2-subsets of
`{1,…,n}`* — i.e., a graph 2-coloring. So Erdős–Szekeres is a special case of
the graph Ramsey theorem, with one direction of the bipartite duality squeezed
out by the linear order on `a_i`.

The hypergraph generalization replaces pairs `(i,j)` by `k`-subsets, and
"monotone subsequence" by "monochromatic clique." Geometrically: a `k`-subset
in convex position generalizes a 2-subset that is increasing.

---

## Classical Results (Literature)

### Existence (OQ-03a): Ramsey 1930

Frank Ramsey's original theorem (1930) shows `R_k(s,t)` is finite for all
`k, s, t`. Proof: induct on `s + t` for fixed `k`; the base case `s ≤ k` or
`t ≤ k` is trivial, and the induction step uses a single-vertex partition
argument:

> Take any vertex `v ∈ [n]`. For each `(k-1)`-subset `S ⊆ [n] \ {v}`, color it
> by the color of `S ∪ {v}`. By induction on `s + t`, the resulting
> `(k-1)`-coloring has either a `0`-monochromatic `(s-1)`-clique `T_0` (extend
> to an `s`-clique via `v`) or a `1`-monochromatic `(t-1)`-clique `T_1`
> (extend symmetrically).

The induction on `k` reduces the case `k+1` to the case `k` via the same
neighborhood trick. This is the "two-layer" induction that gives the
Erdős–Rado upper bound.

### Upper bound (OQ-03b): Erdős–Rado 1952

**Theorem (Erdős–Rado).** For `k ≥ 2` and `s ≥ k`,
`R_k(s,s) ≤ tower_{k-1}(c_k · s)` for an explicit constant `c_k`.

Recursive structure: `R_k(s,t) ≤ R_{k-1}(R_k(s-1,t), R_k(s,t-1)) + 1` (the
"two-step" neighborhood iteration). Unwinding this against the
`R_1(s,t) = s+t-1` base and `R_2(s,s) ≤ 2^{2s}` gives:

* `R_2(s,s) ≤ 4^s` (Erdős–Szekeres 1935; Mathlib's `ramseyNumber` agrees).
* `R_3(s,s) ≤ 2^{c s^2}` (Erdős–Rado).
* `R_4(s,s) ≤ 2^{2^{c s^2}}` (Erdős–Rado).
* In general, `R_k(s,s)` is bounded by a tower of height `k-1`.

### Lower bound (OQ-03c): Erdős–Hajnal stepping-up

**Lemma (Erdős–Hajnal 1972).** For `k ≥ 3`, if `R_{k-1}(s,s) > N` then
`R_k(2s-1, 2s-1) > 2^N`.

The construction: given a `(k-1)`-coloring `χ` of `[N]^{(k-1)}` with no
monochromatic `s`-clique, build a `k`-coloring `χ'` of `[2^N]^{(k)}` as
follows. View each `i ∈ [2^N]` as a 0/1 string of length `N`. For a `k`-subset
`{i_1 < i_2 < … < i_k}`, let `d_j` be the first position where `i_j` and
`i_{j+1}` differ. Color `{i_1,…,i_k}` by `χ({d_1, …, d_{k-1}})` if `d_1 <
… < d_{k-1}` or `d_1 > … > d_{k-1}`; otherwise color it by a parity
fix-up rule. One checks no monochromatic `(2s-1)`-clique exists in `χ'`.

For `k ≥ 4` this gives `R_k(s,s) ≥ tower_{k-2}(c'_k s^2)`. For `k = 3` the
best known lower bound `R_3(s,s) ≥ 2^{cs}` does *not* come from stepping-up
(stepping-up needs `k-1 ≥ 2`, i.e. `k ≥ 3`, but the resulting bound matches
the upper one tower lower).

### State of `R_3(s,s)`

This is the canonical open Ramsey-theoretic problem at the boundary of
"hard but reachable":

* Lower: `R_3(s,s) ≥ 2^{c s}` (Erdős–Hajnal 1972, refined by Conlon–Fox–Sudakov).
* Upper: `R_3(s,s) ≤ 2^{c s^2 \log s}` (Conlon–Fox–Sudakov 2010).
* **Conjecture.** Erdős conjectured `R_3(s,s) ≤ 2^{c s^2}` (matching the
  stepping-up lower bound up to constants). This would imply
  `R_3(s,s) = 2^{Θ(s^2)}`.

---

## Mathlib Status

* `SimpleGraph.ramseyNumber` (`Mathlib.Combinatorics.SimpleGraph.Ramsey`):
  defines `R(s,t)` for graphs. Some specialized bounds for off-diagonal cases
  exist but the diagonal `R(s,s) ≤ \binom{2s-2}{s-1}` bound is not yet in
  Mathlib as a clean theorem.
* `Finset.powersetCard k` and `Sym.card` give the right combinatorial
  primitives for `[n]^{(k)}`.
* `Nat.choose`, `Nat.iterate` (for `tower_k`) are present.
* No `RamseyK` / `hypergraphRamseyNumber` definition currently — this is the
  first piece of new infrastructure OQ-03 would add.

### Suggested API surface

```lean
namespace RamseyK
def IsMonochromatic {n k : ℕ} (χ : Finset (Fin n) → Bool)
    (S : Finset (Fin n)) (c : Bool) : Prop := ...

def IsRamsey (n k s t : ℕ) : Prop :=
  ∀ χ : Finset (Fin n) → Bool, ...

def ramseyNumber (k s t : ℕ) : ℕ := Nat.find ...

theorem ramsey_existence (k s t : ℕ) (hk : 2 ≤ k) (hs : k ≤ s) (ht : k ≤ t) :
    ∃ n, IsRamsey n k s t := ...

theorem erdos_rado_upper (k s : ℕ) (hk : 2 ≤ k) :
    ramseyNumber k s s ≤ tower (k - 1) (c_k * s) := ...
end RamseyK
```

This would also let us redefine `SimpleGraph.ramseyNumber` as `ramseyNumber 2`
modulo a small wrapper (long-term cleanup, not part of OQ-03).

---

## Insights

* **Reduction to `erdos_szekeres_tight_axiom`.** The `k = 2` diagonal lower
  bound `R_2(s,s) ≥ 2^{s/2}` (Erdős 1947) discharges
  `erdos_szekeres_tight_axiom` once OQ-03c is proved at `k = 2`. The
  probabilistic / random-graph argument is independently formalizable and
  would be a nicer reduction.
* **Tower function in Lean.** `Nat.iterate (· * 2) k 1 = 2^k`; the general
  tower is `fun s => Nat.iterate (2 ^ ·) (k-1) s`. Mathlib's existing
  `Nat.iterate` API suffices; no new tower definitions needed.
* **`Sym (Fin n) k` vs `Finset (Fin n)` filtered by `card = k`.** Both work
  for `[n]^{(k)}`; `Sym` is cleaner for combinatorial bijections but
  `Finset.powersetCard` is more idiomatic for "all `k`-subsets of a set."
  Recommend `Finset.powersetCard` because it composes with `Finset.card_*`
  lemmas.
* **Why this is *not* solved by a generic `Ramsey` formalization.** The
  existing `SimpleGraph.ramseyNumber` is graph-specific; the inductive
  structure of `R_k` requires `k`-uniform hypergraphs as a separate concept,
  and Mathlib does not have `Hypergraph` yet (only `SimpleGraph`).

---

## Dead Ends (none yet — first session)

---

## Next-Session Action Items

1. **Define `RamseyK.ramseyNumber k s t`** (Lean): smallest `n` such that every
   2-coloring of `(Finset.range n).powersetCard k` is monochromatic-witnessed.
2. **Prove `k = 1` case** as a sanity check: `ramseyNumber 1 s t = s + t - 1`
   via pigeonhole. ~30 lines.
3. **State `ramsey_existence`** as a theorem with `sorry`. The proof
   structure (two-layer induction on `k` and `s + t`) is standard and well-
   suited to an Aristotle companion if the base cases are clean.
4. **Document the reduction `erdos_szekeres_tight_axiom ⇐ ramseyNumber 2 s s ≥ \binom{2s-2}{s-1}`** in `ErdosSzekeres.lean`'s docstring (no
   code change, just a forward pointer).
