import Mathlib

/-
# Centered Hexagonal Sum = n³, the Combinatorial (Shell-Counting) Proof

## Open Question (centered-hexagonal-sum-oq-01-oq-02)

The parent entry `centered-hexagonal-sum-oq-01` proves the figurate identity

    ∑_{k=1}^{n} Hₖ = n³,        Hₖ = 3k(k−1)+1

*algebraically*, by telescoping / one-step induction closed with `ring`.  Its
docstring records the geometric intuition: `Hₖ = k³ − (k−1)³`, so the `n`
hexagonal numbers are the sizes of the `n` **cubic shells**

    C_k = {0,…,k−1}³ ∖ {0,…,k−2}³,      |C_k| = k³ − (k−1)³ = Hₖ.

This open question asks whether that picture can be promoted to a genuine
**counting proof** in Lean: exhibit the cubic shells as an explicit disjoint
decomposition of the full cube `{0,…,n−1}³` and read off `∑ Hₖ = n³` from
`Finset.card_biUnion`, turning the algebraic identity into a structural one.

## Result

A fully machine-checked, self-contained combinatorial proof.

* `cube n = range n ×ˢ range n ×ˢ range n` is the lattice cube, `card = n³`.
* `cubeShell k = cube (k+1) ∖ cube k` is the `k`-th cubic shell.
* **The mathematical heart** (`mem_cubeShell`): a lattice point `p` lies in
  `cubeShell k` **iff its ℓ∞-radius — the maximum of its three coordinates —
  equals `k`**.  So the shells are precisely the level sets of the Chebyshev
  (sup-norm) radius; this *is* the explicit shell-assignment map behind the
  identity.
* `card_cubeShell` : `|cubeShell k| = H_{k+1}`, the per-shell match.
* `cube_eq_biUnion` : the shells `C₁,…,Cₙ` disjointly reassemble the whole cube.
* `sum_centeredHex_range_bijective` : the headline `∑_{k<n} H_{k+1} = n³`,
  proved *entirely by counting* (`card_biUnion`), with no algebraic telescoping —
  the only `ring`/`omega` steps are the elementary per-shell cardinalities.

## Novelty

The parent proves the identity by algebra; this file proves the *same* identity
by a bijective/partition argument, the "proof from the book" for figurate-number
identities.  The reusable content is the shell-decomposition template
`∑ |shell_k| = |total|` via ℓ∞-level-sets, transferable to other
figurate/polytopic sums.  Mathlib has neither the centered-hexagonal identity nor
this Chebyshev-radius shell decomposition.

0 sorries, 0 axioms.
-/

namespace CenteredHexagonalSumOQ01OQ02

open Finset

/-- The `k`-th centered hexagonal number `Hₖ = 3k(k−1)+1` (OEIS A003215),
restated from the parent entry so this file is self-contained. -/
def centeredHex (k : ℕ) : ℕ := 3 * k * (k - 1) + 1

/-- Reindexed summand `H_{k+1} = 3(k+1)k + 1`: shifting the index turns the
truncated ℕ subtraction `(k+1) − 1` into the honest `k`. -/
theorem centeredHex_succ (k : ℕ) : centeredHex (k + 1) = 3 * (k + 1) * k + 1 := by
  simp [centeredHex]

/-- The lattice cube `{0,…,k−1}³ ⊆ ℕ³`, encoded as a `Finset (ℕ × ℕ × ℕ)`. -/
def cube (k : ℕ) : Finset (ℕ × ℕ × ℕ) := range k ×ˢ (range k ×ˢ range k)

/-- Membership in the cube: all three coordinates are `< k`. -/
theorem mem_cube {k : ℕ} {p : ℕ × ℕ × ℕ} :
    p ∈ cube k ↔ p.1 < k ∧ p.2.1 < k ∧ p.2.2 < k := by
  simp [cube, Finset.mem_product, Finset.mem_range]

/-- The cube has `k³` points. -/
theorem card_cube (k : ℕ) : (cube k).card = k ^ 3 := by
  simp only [cube, Finset.card_product, Finset.card_range]
  ring

/-- The cubes are nested: `{0,…,k−1}³ ⊆ {0,…,k}³`. -/
theorem cube_subset_succ (k : ℕ) : cube k ⊆ cube (k + 1) := by
  intro p hp
  rw [mem_cube] at hp ⊢
  omega

/-- The `k`-th **cubic shell** `C_k = {0,…,k}³ ∖ {0,…,k−1}³` (indexed so
`cubeShell k` has cardinality `H_{k+1}`, avoiding ℕ subtraction in the index). -/
def cubeShell (k : ℕ) : Finset (ℕ × ℕ × ℕ) := cube (k + 1) \ cube k

/-- **The combinatorial heart.**  A lattice point lies in `cubeShell k` iff its
**ℓ∞-radius** — the maximum of its three coordinates — equals `k`.  The cubic
shells are exactly the level sets of the sup-norm radius, which is the explicit
map assigning each point of the cube to its shell. -/
theorem mem_cubeShell {k : ℕ} {p : ℕ × ℕ × ℕ} :
    p ∈ cubeShell k ↔ max p.1 (max p.2.1 p.2.2) = k := by
  simp only [cubeShell, Finset.mem_sdiff, mem_cube]
  omega

/-- **Per-shell cardinality.**  `|cubeShell k| = H_{k+1} = 3(k+1)k + 1`, the
`(k+1)`-st centered hexagonal number.  Immediate from `card_sdiff` on the nested
cubes: `(k+1)³ − k³`. -/
theorem card_cubeShell (k : ℕ) : (cubeShell k).card = centeredHex (k + 1) := by
  rw [cubeShell, Finset.card_sdiff_of_subset (cube_subset_succ k), card_cube, card_cube,
    centeredHex_succ]
  have h : (k + 1) ^ 3 = k ^ 3 + (3 * (k + 1) * k + 1) := by ring
  omega

/-- **Disjointness.**  Distinct cubic shells are disjoint — a point's shell index
is its ℓ∞-radius, which is single-valued. -/
theorem cubeShell_disjoint {i j : ℕ} (h : i ≠ j) :
    Disjoint (cubeShell i) (cubeShell j) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rw [mem_cubeShell] at hpi hpj
  omega

/-- **Shell decomposition.**  The cubic shells `C₀,…,C_{n−1}` disjointly
reassemble the full cube `{0,…,n−1}³`: every point sits in the shell of its
ℓ∞-radius, and that radius is `< n` exactly when the point is in the cube. -/
theorem cube_eq_biUnion (n : ℕ) :
    cube n = (range n).biUnion cubeShell := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_range, mem_cubeShell, mem_cube]
  constructor
  · intro hp
    exact ⟨max p.1 (max p.2.1 p.2.2), by omega, by omega⟩
  · rintro ⟨k, hk, hp⟩
    omega

/-- **Centered hexagonal sum, combinatorial proof.**

`∑_{k<n} H_{k+1} = n³`.

Proved *by counting*: the left side sums the cardinalities of the disjoint cubic
shells (`card_cubeShell`), which by `card_biUnion` equals the cardinality of
their union — the full cube (`cube_eq_biUnion`) — namely `n³` (`card_cube`).  No
algebraic telescoping of the summand is used; the identity emerges purely from
the disjoint shell decomposition of the lattice cube. -/
theorem sum_centeredHex_range_bijective (n : ℕ) :
    ∑ k ∈ range n, centeredHex (k + 1) = n ^ 3 := by
  have hdisj : (↑(range n) : Set ℕ).PairwiseDisjoint cubeShell := by
    intro i _ j _ h; exact cubeShell_disjoint h
  calc ∑ k ∈ range n, centeredHex (k + 1)
      = ∑ k ∈ range n, (cubeShell k).card := by
        apply Finset.sum_congr rfl; intro k _; rw [card_cubeShell]
    _ = ((range n).biUnion cubeShell).card := (Finset.card_biUnion hdisj).symm
    _ = (cube n).card := by rw [← cube_eq_biUnion]
    _ = n ^ 3 := card_cube n

end CenteredHexagonalSumOQ01OQ02
