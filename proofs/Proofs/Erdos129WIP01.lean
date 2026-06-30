/-
# Erdős Problem 129 (leaf wip-01): Monotonicity of the Ramsey-avoidance property

Let `R(n; k, r)` denote the smallest `N` such that every `r`-coloring of the edges
of `K_N` admits a set of `n` vertices containing no monochromatic `K_k`
(Erdős–Gyárfás, "A variant of the classical Ramsey problem", 1997).

The parent entry `Erdos129Problem` sets up the predicate `HasRamseyAvoid N n k r`
("every `r`-coloring of `K_N` has an `n`-vertex monochromatic-`K_k`-free set") and
states the Erdős–Gyárfás exponential conjecture, but lists the *monotonicity*
properties of `R(n;k,r)` among the structural facts whose proofs "require embedding
arguments not yet in Mathlib".

This leaf supplies those embedding arguments and proves them from Mathlib alone:

* `hasRamseyAvoid_mono_N`  — **monotonicity in `N`**: enlarging the host complete
  graph preserves the avoidance property (`HasRamseyAvoid N n k r → N ≤ N' →
  HasRamseyAvoid N' n k r`). This is the genuinely non-trivial direction: given a
  coloring of `K_{N'}`, we pull it back along `Fin.castLE` to a coloring of `K_N`,
  use the hypothesis to find an avoiding set there, and push that set forward.
* `hasRamseyAvoid_antitone_n` — **antitonicity in `n`**: requiring fewer
  clique-free vertices is easier (`HasRamseyAvoid N n k r → m ≤ n →
  HasRamseyAvoid N m k r`), by passing to a sub-Finset.
* `hasRamseyAvoid_mono` — the combined statement.

Equivalently, in terms of `R`: `R(n;k,r)` is monotone non-decreasing in `n`
(antitonicity of the *property* in `n` is exactly monotonicity of the *threshold*),
and any `N ≥ R(n;k,r)` already witnesses the property — the content the parent
deferred.

The definitions mirror `Erdos129Problem.lean` so this file is self-contained.

*Reference:* [erdosproblems.com/129](https://www.erdosproblems.com/129)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open Finset

/- ## Setup (mirrors the parent `Erdos129Problem` definitions) -/

/-- An `r`-coloring of the edges of the complete graph on `Fin N`,
represented as a function on ordered pairs `i < j`. -/
def EdgeColoring (N : ℕ) (r : ℕ) : Type :=
    { p : Fin N × Fin N // p.1 < p.2 } → Fin r

/-- A set `S` of vertices avoids monochromatic `K_k` in color `c` if no `k`-element
subset of `S` has all of its edges colored `c` (witnessed by a non-`c` edge). -/
def AvoidsMono (N : ℕ) (r : ℕ) (coloring : EdgeColoring N r)
    (S : Finset (Fin N)) (k : ℕ) (c : Fin r) : Prop :=
    ∀ T : Finset (Fin N), T ⊆ S → T.card = k →
      ∃ e : { p : Fin N × Fin N // p.1 < p.2 },
        e.val.1 ∈ T ∧ e.val.2 ∈ T ∧ coloring e ≠ c

/-- A set `S` contains no monochromatic `K_k` in any color. -/
def NoMonoClique (N : ℕ) (r : ℕ) (coloring : EdgeColoring N r)
    (S : Finset (Fin N)) (k : ℕ) : Prop :=
    ∀ c : Fin r, AvoidsMono N r coloring S k c

/-- `HasRamseyAvoid N n k r` holds when every `r`-coloring of `K_N`
admits a set of `n` vertices with no monochromatic `K_k`. -/
def HasRamseyAvoid (N n k r : ℕ) : Prop :=
    ∀ coloring : EdgeColoring N r,
      ∃ S : Finset (Fin N), S.card ≥ n ∧ NoMonoClique N r coloring S k

/- ## Antitonicity in the number of required vertices -/

/-- `NoMonoClique` is downward closed in the vertex set: a subset of a
monochromatic-`K_k`-free set is itself monochromatic-`K_k`-free. -/
theorem noMonoClique_subset (N r : ℕ) (coloring : EdgeColoring N r)
    {S S' : Finset (Fin N)} (k : ℕ) (hsub : S' ⊆ S)
    (h : NoMonoClique N r coloring S k) :
    NoMonoClique N r coloring S' k := by
  intro c T hT hTk
  exact h c T (hT.trans hsub) hTk

/-- **Antitonicity in `n`.** Requiring fewer clique-free vertices is easier:
if `K_N` always has an `n`-vertex avoiding set, it always has an `m`-vertex one
for every `m ≤ n`. Equivalently, `R(n;k,r)` is non-decreasing in `n`. -/
theorem hasRamseyAvoid_antitone_n {N n k r : ℕ} (m : ℕ) (hm : m ≤ n)
    (h : HasRamseyAvoid N n k r) :
    HasRamseyAvoid N m k r := by
  intro coloring
  obtain ⟨S, hScard, hSavoid⟩ := h coloring
  obtain ⟨S', hS'sub, hS'card⟩ :=
    Finset.exists_subset_card_eq (s := S) (n := m) (by omega)
  exact ⟨S', by omega, noMonoClique_subset N r coloring k hS'sub hSavoid⟩

/- ## Monotonicity in the size of the host graph -/

/-- **Monotonicity in `N`.** Enlarging the complete graph preserves the
avoidance property: if every `r`-coloring of `K_N` has an `n`-vertex
monochromatic-`K_k`-free set, then so does every `r`-coloring of `K_{N'}`
for `N ≤ N'`.

The proof pulls an arbitrary coloring `χ'` of `K_{N'}` back along the order
embedding `Fin.castLE : Fin N ↪ Fin N'` to a coloring `χ` of `K_N`, applies the
hypothesis to obtain an avoiding set `S ⊆ Fin N`, and pushes `S` forward to
`S.map (Fin.castLEEmb _) ⊆ Fin N'`. Any `k`-subset upstairs is the image of a
`k`-subset downstairs, whose non-`c` witness edge maps to a non-`c` witness edge
upstairs. -/
theorem hasRamseyAvoid_mono_N {N N' n k r : ℕ} (hNN' : N ≤ N')
    (h : HasRamseyAvoid N n k r) :
    HasRamseyAvoid N' n k r := by
  intro χ'
  -- Pull `χ'` back to a coloring of `K_N` via the strictly monotone `castLE`.
  let χ : EdgeColoring N r := fun e =>
    χ' ⟨(Fin.castLE hNN' e.val.1, Fin.castLE hNN' e.val.2),
        (Fin.castLE_lt_castLE_iff hNN').mpr e.property⟩
  obtain ⟨S, hScard, hSavoid⟩ := h χ
  refine ⟨S.map (Fin.castLEEmb hNN'), ?_, ?_⟩
  · -- The image has the same cardinality.
    rw [Finset.card_map]; exact hScard
  · -- Image of an avoiding set is avoiding.
    intro c T' hT' hT'card
    -- Every `k`-subset `T'` upstairs is `T.map castLEEmb` for a `k`-subset `T` of `S`.
    obtain ⟨T, hTsub, hTeq⟩ := Finset.subset_map_iff.mp hT'
    have hTcard : T.card = k := by
      rw [hTeq, Finset.card_map] at hT'card; exact hT'card
    obtain ⟨e, he1, he2, hne⟩ := hSavoid c T hTsub hTcard
    -- The downstairs witness edge maps to an upstairs witness edge.
    refine ⟨⟨(Fin.castLE hNN' e.val.1, Fin.castLE hNN' e.val.2),
            (Fin.castLE_lt_castLE_iff hNN').mpr e.property⟩, ?_, ?_, ?_⟩
    · rw [hTeq]; exact Finset.mem_map_of_mem _ he1
    · rw [hTeq]; exact Finset.mem_map_of_mem _ he2
    · -- `χ'` of the mapped edge is, by construction, `χ e ≠ c`.
      exact hne

/-- **Combined monotonicity.** The avoidance property is preserved under
enlarging the host graph (`N ≤ N'`) and shrinking the required clique-free
set (`n' ≤ n`). -/
theorem hasRamseyAvoid_mono {N N' n n' k r : ℕ}
    (hN : N ≤ N') (hn : n' ≤ n) (h : HasRamseyAvoid N n k r) :
    HasRamseyAvoid N' n' k r :=
  hasRamseyAvoid_antitone_n n' hn (hasRamseyAvoid_mono_N hN h)
