import Mathlib.Tactic
import Proofs.CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02

/-
# Fibre sizes of the power map on a finite abelian group are constant

## The question

The parent file `CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02` analysed the power
map `x ↦ xⁿ` on a finite **cyclic** group of order `m`: every non-empty fibre
has exactly `gcd(n, m)` elements, so the unordered multiset of fibre sizes is the
single value `gcd(n, m)` repeated `m / gcd(n, m)` times. From that multiset one
"recovers `gcd(n, m)` exactly". The open question asked whether, over a *product*
of cyclic groups, the fibre-size multiset becomes strictly more informative, and
which residues of `n` modulo the invariant factors it pins down.

## What this file proves

The premise of the open question — that the multiset gets richer on a product —
is **false**, and this file makes the reason precise.

* **Constant fibres (any finite abelian group).** Because `x ↦ xⁿ` is a group
  *endomorphism* of an abelian group, every non-empty fibre is a coset of the
  `n`-torsion subgroup, so they **all have the same size**, namely the number of
  solutions of `xⁿ = 1`. The fibre-size multiset therefore degenerates to a
  single value repeated `#(n-th powers)` times — on a product just as much as on
  a cyclic group (`card_fiber_pow_eq_card_torsion`).

* **Partition identity (any finite abelian group).** Counting the group through
  its fibres gives `#(n-th powers) · #{x : xⁿ = 1} = |G|`
  (`card_image_pow_mul_torsion`), strictly generalising the parent's cyclic
  identity `#(n-th powers) · gcd(n, m) = m`.

* **The single value, on a product of cyclics.** For `G = ∏ᵢ Gᵢ` with each `Gᵢ`
  finite cyclic, the `n`-torsion count multiplies over the factors:
  `#{x : xⁿ = 1} = ∏ᵢ gcd(n, |Gᵢ|)` (`card_torsion_pi_cyclic`). Hence the common
  fibre size on the product is `∏ᵢ gcd(n, |Gᵢ|)` and the number of `n`-th powers
  is `∏ᵢ |Gᵢ| / gcd(n, |Gᵢ|)` (`card_fiber_pow_pi_cyclic`,
  `card_image_pow_pi_cyclic`).

## Answer to the open question

The fibre-size multiset on a product of cyclic groups is **not** more
informative than its single value: it is the constant `∏ᵢ gcd(n, |Gᵢ|)`. That
number determines the product of the per-factor gcds, but — exactly as in the
cyclic case where `gcd(n, m)` does not determine `n mod m` — it pins down **no**
residue of `n` modulo any invariant factor. The genuine information content of
the map `x ↦ xⁿ` on a product is the *tuple* `(gcd(n, |Gᵢ|))ᵢ`, which the bare
fibre size collapses into a single product.

## Proof strategy

`card_fiber_pow_eq_card_torsion` is a translation bijection: left-multiplication
by a fixed preimage `a` (with `aⁿ = b`) carries the torsion set `{xⁿ = 1}` onto
the fibre `{xⁿ = b}`, using only `mul_pow` in the abelian group. The partition
identity then feeds this uniform count into `Finset.card_eq_sum_card_image`. The
product formula transports the torsion subtype across
`Equiv.subtypePiEquivPi` and reads each factor off the parent's cyclic count
`gcd(n, |Gᵢ|)` via `card_fiber_pow`.
-/

namespace CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02OQ02

open Finset

/-! ### Constant fibres on any finite abelian group -/

/-- **Uniform fibres (any finite abelian group).** Every non-empty fibre of the
power map `x ↦ xⁿ` has the same number of elements: the number of solutions of
`xⁿ = 1`. Indeed if `aⁿ = b` then `x ↦ a⁻¹ · x` is a bijection from the fibre
`{xⁿ = b}` onto the torsion set `{xⁿ = 1}`, because `(a⁻¹x)ⁿ = (aⁿ)⁻¹ · xⁿ`. No
cyclicity is used — only that `x ↦ xⁿ` is an endomorphism of the abelian group,
so its fibres are the cosets of the `n`-torsion subgroup. -/
theorem card_fiber_pow_eq_card_torsion {α : Type*} [CommGroup α] [Fintype α]
    [DecidableEq α] (n : ℕ) {b : α} (hb : ∃ a, a ^ n = b) :
    (univ.filter (fun x : α => x ^ n = b)).card
      = (univ.filter (fun x : α => x ^ n = 1)).card := by
  obtain ⟨a, rfl⟩ := hb
  refine Finset.card_bij' (fun x _ => a⁻¹ * x) (fun y _ => a * y) ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_filter] at hx
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [mul_pow, inv_pow, hx.2, inv_mul_cancel]
  · intro y hy
    rw [mem_filter] at hy
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [mul_pow, hy.2, mul_one]
  · intro x _
    simp only [mul_inv_cancel_left]
  · intro y _
    simp only [inv_mul_cancel_left]

/-- **Constant fibre value as the kernel cardinality.** The shared fibre size of
the previous theorem is exactly the order of the kernel of the power
homomorphism `powMonoidHom n`, i.e. the `n`-torsion subgroup. -/
theorem card_torsion_eq_card_ker {α : Type*} [CommGroup α] [Fintype α]
    [DecidableEq α] (n : ℕ) :
    (univ.filter (fun x : α => x ^ n = 1)).card
      = Fintype.card (powMonoidHom n : α →* α).ker := by
  rw [Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro x _
  simp only [MonoidHom.mem_ker, powMonoidHom_apply]

/-! ### The partition identity for any finite abelian group -/

/-- **Partition identity (any finite abelian group).** The power map `x ↦ xⁿ`
partitions the group into its fibres, every non-empty one having the same size
`#{x : xⁿ = 1}`. Counting the group two ways gives
`#(n-th powers) · #{x : xⁿ = 1} = |G|`. This generalises the parent's cyclic
identity `#(n-th powers) · gcd(n, m) = m`, replacing `gcd(n, m)` by the general
torsion count. -/
theorem card_image_pow_mul_torsion {α : Type*} [CommGroup α] [Fintype α]
    [DecidableEq α] (n : ℕ) :
    (univ.image (fun x : α => x ^ n)).card
        * (univ.filter (fun x : α => x ^ n = 1)).card
      = Fintype.card α := by
  have key : ∀ b ∈ univ.image (fun x : α => x ^ n),
      (univ.filter (fun a : α => a ^ n = b)).card
        = (univ.filter (fun x : α => x ^ n = 1)).card := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a, _, ha⟩ := hb
    exact card_fiber_pow_eq_card_torsion n ⟨a, ha⟩
  have hsum : Fintype.card α
      = ∑ b ∈ univ.image (fun x : α => x ^ n),
          (univ.filter (fun a : α => a ^ n = b)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_image _ _
  rw [hsum, Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul]

/-! ### The single fibre value on a product of cyclic groups -/

/-- **Torsion count is multiplicative over a product (general factors).** For a
finite product `∀ i, G i` of finite abelian groups, the number of solutions of
`xⁿ = 1` is the product over the factors of the per-factor torsion counts:
`xⁿ = 1` holds in the product iff `(xᵢ)ⁿ = 1` for every `i`. -/
theorem card_torsion_pi {ι : Type*} [DecidableEq ι] [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] (n : ℕ) :
    (univ.filter (fun x : (∀ i, G i) => x ^ n = 1)).card
      = ∏ i, (univ.filter (fun y : G i => y ^ n = 1)).card := by
  have e : {x : (∀ i, G i) // x ^ n = 1} ≃ ∀ i, {y : G i // y ^ n = 1} :=
    (Equiv.subtypeEquivRight (fun x => by
      rw [funext_iff]; simp only [Pi.pow_apply, Pi.one_apply])).trans
      Equiv.subtypePiEquivPi
  calc (univ.filter (fun x : (∀ i, G i) => x ^ n = 1)).card
      = Fintype.card {x : (∀ i, G i) // x ^ n = 1} := (Fintype.card_subtype _).symm
    _ = Fintype.card (∀ i, {y : G i // y ^ n = 1}) := Fintype.card_congr e
    _ = ∏ i, Fintype.card {y : G i // y ^ n = 1} := Fintype.card_pi
    _ = ∏ i, (univ.filter (fun y : G i => y ^ n = 1)).card :=
        Finset.prod_congr rfl (fun i _ => Fintype.card_subtype _)

/-- **Per-factor torsion count on a cyclic group.** On a finite cyclic group of
order `m`, the number of solutions of `xⁿ = 1` is `gcd(n, m)` (the kernel of the
power map), reading the parent's uniform fibre count over the basepoint `b = 1`. -/
theorem card_torsion_cyclic {α : Type*} [CommGroup α] [Fintype α] [DecidableEq α]
    [IsCyclic α] (n : ℕ) :
    (univ.filter (fun x : α => x ^ n = 1)).card = Nat.gcd n (Fintype.card α) :=
  CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02.card_fiber_pow ⟨1, one_pow n⟩

/-- **The fibre value on a product of cyclic groups (the answer).** For
`G = ∏ᵢ Gᵢ` with each `Gᵢ` finite cyclic of order `mᵢ`, the number of solutions
of `xⁿ = 1` — equivalently the common size of every non-empty fibre of
`x ↦ xⁿ` — is `∏ᵢ gcd(n, mᵢ)`. The fibre-size multiset is therefore the single
constant value `∏ᵢ gcd(n, mᵢ)`, not a richer object. -/
theorem card_torsion_pi_cyclic {ι : Type*} [DecidableEq ι] [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)]
    [∀ i, IsCyclic (G i)] (n : ℕ) :
    (univ.filter (fun x : (∀ i, G i) => x ^ n = 1)).card
      = ∏ i, Nat.gcd n (Fintype.card (G i)) := by
  rw [card_torsion_pi]
  exact Finset.prod_congr rfl (fun i _ => card_torsion_cyclic n)

/-- **Common fibre size on a product of cyclic groups.** Every non-empty fibre of
`x ↦ xⁿ` on `∏ᵢ Gᵢ` (each `Gᵢ` cyclic) has exactly `∏ᵢ gcd(n, |Gᵢ|)` elements. -/
theorem card_fiber_pow_pi_cyclic {ι : Type*} [DecidableEq ι] [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)]
    [∀ i, IsCyclic (G i)] (n : ℕ) {b : ∀ i, G i} (hb : ∃ a, a ^ n = b) :
    (univ.filter (fun x : (∀ i, G i) => x ^ n = b)).card
      = ∏ i, Nat.gcd n (Fintype.card (G i)) := by
  rw [card_fiber_pow_eq_card_torsion n hb, card_torsion_pi_cyclic]

/-- **Number of `n`-th powers on a product of cyclic groups.** Dividing the
partition identity by the common fibre size: the product `∏ᵢ Gᵢ` of finite cyclic
groups has exactly `(∏ᵢ |Gᵢ|) / (∏ᵢ gcd(n, |Gᵢ|)) = ∏ᵢ |Gᵢ| / gcd(n, |Gᵢ|)`
distinct `n`-th powers. -/
theorem card_image_pow_pi_cyclic {ι : Type*} [DecidableEq ι] [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)]
    [∀ i, IsCyclic (G i)] (n : ℕ) :
    (univ.image (fun x : (∀ i, G i) => x ^ n)).card
      = (∏ i, Fintype.card (G i)) / ∏ i, Nat.gcd n (Fintype.card (G i)) := by
  have h := card_image_pow_mul_torsion (α := (∀ i, G i)) n
  rw [card_torsion_pi_cyclic] at h
  rw [Fintype.card_pi] at h
  have hpos : 0 < ∏ i, Nat.gcd n (Fintype.card (G i)) :=
    Finset.prod_pos (fun i _ => Nat.gcd_pos_of_pos_right _ Fintype.card_pos)
  exact (Nat.div_eq_of_eq_mul_right hpos (by rw [mul_comm]; exact h.symm)).symm

end CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02OQ02
