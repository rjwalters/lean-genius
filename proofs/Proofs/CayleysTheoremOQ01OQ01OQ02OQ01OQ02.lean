/-
Proof: Infinite converse to Cayley — a free transitive `H ≤ Sym(α)` has `#H = #α`.
Research: cayleys-theorem-oq-01-oq-01-oq-02-oq-01-oq-02

Open question (from `cayleys-theorem-oq-01-oq-01-oq-02-oq-01`):
  The parent proves the *finite* converse to Cayley: a subgroup
  `H ≤ Sₙ = Equiv.Perm α` acting **freely** and **transitively** on a finite
  nonempty `α` is regular of order `n = |α|`, via the orbit bijection
  `regularEquiv : H ≃ α`.  Its order statement is phrased with `Nat.card`, which
  collapses to the vacuous `0 = 0` when `α` is infinite.  Here we record the
  genuine infinite generalisation.

The same orbit map `σ ↦ σ a` is a bijection `H ≃ α` for **arbitrary** nonempty
`α` — the parent's `regularEquiv` is built without any finiteness hypothesis.
Transporting cardinality across it gives the honest converse over any `α`:

* **Cardinal equality.**  `#H = #α` as `Cardinal`s, for arbitrary nonempty `α`.
  This subsumes the parent's finite order count and is non-vacuous when `α` is
  infinite (where `Nat.card` says nothing).
* **Infinitude transfer.**  `H` is infinite iff `α` is; in particular a free
  transitive subgroup of `Sym(α)` over an infinite `α` is itself infinite, of
  exactly the same cardinality.
* **Sharp transitivity** carries over unchanged from the parent (it was already
  proved for arbitrary `α`), so the full package — `#H = #α` together with
  unique-transitivity — holds verbatim in the infinite setting.

Everything reduces to one explicit bijection: no new mathematics beyond the
parent, only the correct cardinal invariant.  We reuse the parent's
`ActsTransitively` / `ActsFreely` / `IsRegular` predicates and its
`regularEquiv`, so no construction is duplicated.
-/

import Proofs.CayleysTheoremOQ01OQ01OQ02OQ01

namespace CayleyConverse

open Equiv

variable {α : Type*} {H : Subgroup (Equiv.Perm α)}

/-- **Infinite converse to Cayley.**  A free transitive subgroup `H ≤ Sym(α)`
over an arbitrary nonempty `α` has the *same cardinality* as `α`: `#H = #α`.

This is the genuine infinite generalisation of the parent's order count.  The
parent states `Nat.card H = Nat.card α`, which is the vacuous `0 = 0` when `α`
is infinite; the cardinal equality below is non-vacuous in that case and
specialises back to the finite count.  The proof transports cardinality across
the parent's orbit bijection `regularEquiv : H ≃ α`. -/
theorem cardinalMk_eq_of_free_transitive [Nonempty α]
    (htrans : ActsTransitively H) (hfree : ActsFreely H) :
    Cardinal.mk H = Cardinal.mk α :=
  Cardinal.mk_congr (regularEquiv htrans hfree (Classical.arbitrary α))

/-- **Infinitude transfer.**  For a free transitive subgroup, `H` is infinite
exactly when the underlying point set `α` is.  Immediate from the orbit
bijection `H ≃ α`. -/
theorem infinite_iff_of_free_transitive [Nonempty α]
    (htrans : ActsTransitively H) (hfree : ActsFreely H) :
    Infinite H ↔ Infinite α :=
  Equiv.infinite_iff (regularEquiv htrans hfree (Classical.arbitrary α))

/-- **An infinite regular subgroup is infinite.**  A free transitive subgroup of
`Sym(α)` over an infinite `α` is itself infinite (and, by
`cardinalMk_eq_of_free_transitive`, of the same cardinality as `α`). -/
theorem infinite_of_free_transitive [Infinite α]
    (htrans : ActsTransitively H) (hfree : ActsFreely H) :
    Infinite H :=
  haveI : Nonempty α := inferInstance
  (infinite_iff_of_free_transitive htrans hfree).mpr ‹Infinite α›

/-- **Infinite converse to Cayley, packaged.**  A regular (free transitive)
subgroup of `Sym(α)` over an *arbitrary* nonempty `α` has `#H = #α` and is
sharply transitive.  This is the parent's `regular_iff_card_and_sharp` with the
finite order count replaced by the cardinal equality that survives in the
infinite setting; the sharp-transitivity half is reused verbatim. -/
theorem regular_iff_cardinalMk_and_sharp [Nonempty α] (hreg : IsRegular H) :
    Cardinal.mk H = Cardinal.mk α ∧
      ∀ i j : α, ∃! σ : H, (σ : Equiv.Perm α) i = j :=
  ⟨cardinalMk_eq_of_free_transitive hreg.1 hreg.2,
    fun i j => existsUnique_of_free_transitive hreg.1 hreg.2 i j⟩

/-- **Consistency with the finite parent.**  For finite nonempty `α` the cardinal
equality `#H = #α` refines to the parent's `Nat.card H = Fintype.card α`, so the
infinite statement genuinely extends the finite one rather than replacing it. -/
theorem natCard_eq_of_cardinalMk [Fintype α] [Nonempty α]
    (htrans : ActsTransitively H) (hfree : ActsFreely H) :
    Nat.card H = Fintype.card α :=
  fintypeCard_eq_of_free_transitive htrans hfree

end CayleyConverse
