import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01

/-
# The permutation descent statistic and the descent-free base case

The parent entry **geometric-series-oq-07-oq-01-oq-01-oq-01-oq-02** proved the explicit closed
form `A(n,k) = ∑_{i=0}^{k} (−1)ⁱ·C(n+1,i)·(k+1−i)ⁿ = ⟨n,k⟩` for the combinatorial Eulerian
numbers `⟨n,k⟩ = eulerian n k`, and its open question asked to (1) show `A(n,k) ≥ 0` and (2)
show `A(n,k)` equals the number of permutations of `{1,…,n}` with exactly `k` descents. Claim (1)
and the row palindromy are settled by the sibling **…-oq-02-oq-02** (non-negativity is immediate
since `A(n,k)` is the cast of a natural number; palindromy from the alternating sum). The descent
*moments* are computed analytically in the sibling **…-oq-03** through the Eulerian polynomial.

What none of those entries do — and what claim (2) literally asks for — is to define the descent
statistic on honest permutations `σ : Equiv.Perm (Fin (n+1))` and connect its distribution to the
Eulerian numbers. Mathlib has no permutation descent statistic (only Coxeter-group descents), so
this must be built from scratch. This entry takes the first concrete step: it defines

  `descentCount σ = |{i : Fin n | σ (i.succ) < σ (i.castSucc)}|`,

the number of positions where `σ` falls, and proves the **base rung** `k = 0` of the bijection:

  `descentCount_eq_zero_iff` :  `descentCount σ = 0 ↔ σ = 1`,
  `card_descentFree`         :  `|{σ : descentCount σ = 0}| = ⟨n+1, 0⟩  (= 1)`.

Combinatorially: a permutation has no descents iff it is increasing, and the increasing
permutation is unique — so the descent-free permutations are counted by `⟨n+1,0⟩ = 1`, the left
border of the Eulerian triangle. This is the first place in the gallery where the *abstract*
Eulerian number `⟨n+1,0⟩` is matched against an *actual* cardinality of a descent class.

## Method

A permutation with no descents satisfies `σ (i.castSucc) ≤ σ (i.succ)` for every adjacent pair;
injectivity upgrades this to a strict inequality, so `σ` is strictly monotone
(`Fin.strictMono_iff_lt_succ`). A strictly monotone self-equivalence of `Fin (n+1)` is an order
isomorphism, and `Fin (n+1) ≃o Fin (n+1)` is a subsingleton, forcing `σ = 1`
(`perm_eq_one_of_strictMono`). The converse is immediate. The cardinality then follows from
`Finset.card_eq_one`, the unique descent-free permutation being the identity, and
`eulerian_succ_zero` gives `⟨n+1,0⟩ = 1`.

The remaining columns `k ≥ 1` (the full `card_descent = eulerian` bijection, via the insertion
recurrence) stay open; they need the descent triangle recurrence on permutations, a substantial
further development.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ02OQ01

open Equiv Finset GeometricSeriesOQ07OQ01OQ01OQ01

/-! ## A strictly monotone permutation of `Fin n` is the identity -/

/-- A strictly monotone self-equivalence of `Fin n` is the identity. The monotone equivalence is
an `OrderIso`, and `Fin n ≃o Fin n` is a subsingleton (its only element is the identity). -/
private theorem perm_eq_one_of_strictMono {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : StrictMono σ) : σ = 1 := by
  have hmono : Monotone (σ : Fin n → Fin n) := hσ.monotone
  have hmono' : Monotone (σ.symm : Fin n → Fin n) := by
    intro a b hab
    by_contra h
    push_neg at h
    have h2 := hσ h
    simp only [Equiv.apply_symm_apply] at h2
    exact absurd hab (not_le.2 h2)
  let e : Fin n ≃o Fin n := σ.toOrderIso hmono hmono'
  have he : e = OrderIso.refl _ := Subsingleton.elim _ _
  have key : ∀ i, σ i = i := by
    intro i
    have hei : e i = i := by rw [he]; rfl
    simpa [e, Equiv.toOrderIso] using hei
  exact Equiv.ext key

/-! ## The descent statistic -/

/-- The **descent count** of a permutation `σ` of `Fin (n+1)`: the number of positions
`i : Fin n` at which `σ` falls, `σ (i.succ) < σ (i.castSucc)`. (For `n = 0` there are no adjacent
pairs, so every permutation of `Fin 1` is descent-free.) -/
def descentCount {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : ℕ :=
  (univ.filter (fun i : Fin n => σ i.succ < σ i.castSucc)).card

/-! ## The descent-free base case `k = 0` -/

/-- **Descent-free ⟺ identity.** A permutation of `Fin (n+1)` has no descents exactly when it is
the identity — the unique increasing arrangement. -/
theorem descentCount_eq_zero_iff {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    descentCount σ = 0 ↔ σ = 1 := by
  constructor
  · intro h0
    -- No descents: `σ (i.castSucc) ≤ σ (i.succ)`, upgraded to `<` by injectivity.
    have hempty : univ.filter (fun i : Fin n => σ i.succ < σ i.castSucc) = ∅ :=
      Finset.card_eq_zero.mp h0
    have hle : ∀ i : Fin n, σ i.castSucc < σ i.succ := by
      intro i
      have hnot : ¬ (σ i.succ < σ i.castSucc) := by
        have := Finset.filter_eq_empty_iff.mp hempty (mem_univ i)
        simpa using this
      rcases lt_trichotomy (σ i.castSucc) (σ i.succ) with hlt | heq | hgt
      · exact hlt
      · exact absurd (σ.injective heq) (Fin.castSucc_lt_succ (i := i)).ne
      · exact absurd hgt hnot
    exact perm_eq_one_of_strictMono σ (Fin.strictMono_iff_lt_succ.mpr hle)
  · intro h1
    subst h1
    -- The identity has no descents: `i.castSucc < i.succ`.
    have : univ.filter (fun i : Fin n => (1 : Equiv.Perm (Fin (n + 1))) i.succ
        < (1 : Equiv.Perm (Fin (n + 1))) i.castSucc) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _
      simp only [Equiv.Perm.one_apply]
      exact not_lt.mpr (Fin.castSucc_lt_succ (i := i)).le
    rw [descentCount, this, Finset.card_empty]

/-- **The descent-free base rung of the Eulerian bijection.** The permutations of `Fin (n+1)`
with no descents number exactly the Eulerian number `⟨n+1,0⟩ = 1`: the increasing permutation is
the unique descent-free one. This is the `k = 0` case of the open claim
`|{σ : descentCount σ = k}| = ⟨n+1,k⟩`. -/
theorem card_descentFree {n : ℕ} :
    (univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => descentCount σ = 0)).card
      = eulerian (n + 1) 0 := by
  rw [eulerian_succ_zero, Finset.card_eq_one]
  refine ⟨1, ?_⟩
  ext σ
  simp only [mem_filter, mem_univ, true_and, mem_singleton, descentCount_eq_zero_iff]

end GeometricSeriesOQ07OQ01OQ01OQ01OQ02OQ01
