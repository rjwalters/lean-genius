import Mathlib
import Proofs.Erdos70Problem

/-
# Erdős #70 — closure of the countable-ordinal class and conjecture specializations
# (erdos-70-wip-01)

## The Problem

**Erdős Problem #70** (OPEN). Does the continuum satisfy the partition relation
`𝔠 → (β, n)₂³` for *every* countable ordinal `β` and every `2 ≤ n < ω`?
`Erdos70Problem.lean` sets up `PartitionArrow`, `IsCountableOrdinal`, the
conjecture `erdos_70_conjecture` and the special cases `conjecture_omega` /
`conjecture_omega_squared`, and proves a handful of specific countability facts
(`omega0_countable`, `omega0_plus_n_countable`, `omega0_squared_countable`) plus
the two monotonicity directions of the arrow.

This file supplies the **general structural lemmas** those specific facts are
instances of: the countable ordinals are downward-closed and closed under `+`
and `*`; and it wires the open conjecture to its published special cases.

## Results (all in `namespace Erdos70`)

1. `IsCountableOrdinal.of_le` — countability is *downward closed*: `α ≤ β` and
   `β` countable ⟹ `α` countable. (`omega0_plus_n_countable` etc. become
   corollaries of this + closure below.)

2. `isCountableOrdinal_add` / `isCountableOrdinal_mul` — the countable ordinals
   are closed under ordinal addition and multiplication.

3. `erdos_70_conjecture_imp_omega` / `_imp_omega_squared` — the open conjecture
   specializes to its two flagship cases `𝔠 → (ω, n)` and `𝔠 → (ω², n)`, using
   the parent's countability witnesses.

4. `isCountableOrdinal_opow_nat` / `omega0_opow_omega0_countable` /
   `isCountableOrdinal_opow` — closure under exponentiation, from `α ^ (n:ℕ)`
   through the single limit power `ω^ω` up to the **general** statement that the
   countable ordinals are closed under `α ^ β` for arbitrary countable `α, β`
   (transfinite induction on the exponent + regularity of `ℵ₁`). Consequently the
   whole exponential tower `ω`, `ω^ω`, `ω^(ω^ω)`, … below `ε₀` is countable, and
   the conjecture specializes to every such `β` (`erdos_70_conjecture_imp_omega_tower`,
   `_imp_omega_tower_two`).

5. `omega0_opow_iSup_omegaTower` — **`ε₀` is an epsilon number** (`ω ^ ε₀ = ε₀`):
   the tower supremum is a fixed point of `ξ ↦ ω^ξ`, the defining property the
   development above only stated in prose.  Proved from normality of `ω^·`.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Built over the gallery defs.
-/

namespace Erdos70

/-- **Downward closure.** A sub-ordinal of a countable ordinal is countable. -/
theorem IsCountableOrdinal.of_le {α β : Ordinal} (hαβ : α ≤ β)
    (h : IsCountableOrdinal β) : IsCountableOrdinal α :=
  (Ordinal.card_le_card hαβ).trans h

/-- The countable ordinals are closed under ordinal addition. -/
theorem isCountableOrdinal_add {α β : Ordinal}
    (hα : IsCountableOrdinal α) (hβ : IsCountableOrdinal β) :
    IsCountableOrdinal (α + β) := by
  unfold IsCountableOrdinal at *
  rw [Ordinal.card_add]
  exact Cardinal.add_le_aleph0.mpr ⟨hα, hβ⟩

/-- The countable ordinals are closed under ordinal multiplication. -/
theorem isCountableOrdinal_mul {α β : Ordinal}
    (hα : IsCountableOrdinal α) (hβ : IsCountableOrdinal β) :
    IsCountableOrdinal (α * β) := by
  unfold IsCountableOrdinal at *
  rw [Ordinal.card_mul]
  calc α.card * β.card ≤ Cardinal.aleph0 * Cardinal.aleph0 :=
        mul_le_mul' hα hβ
    _ = Cardinal.aleph0 := Cardinal.aleph0_mul_aleph0

/-- **Closure under natural-number exponentiation.**  If `α` is a countable
ordinal then so is `α ^ n` for every `n : ℕ`.  Proof by induction on `n`:
`α ^ 0 = 1` is countable, and `α ^ (n+1) = α ^ n * α` is countable by
`IsCountableOrdinal.mul`.  This generalises the parent's `omega0_squared_countable`
(`ω * ω = ω ^ 2`) to all finite powers. -/
theorem isCountableOrdinal_opow_nat {α : Ordinal} (hα : IsCountableOrdinal α) :
    ∀ n : ℕ, IsCountableOrdinal (α ^ (n : Ordinal))
  | 0 => by simpa using one_countable
  | (n + 1) => by
      have hstep : α ^ ((n + 1 : ℕ) : Ordinal) = α ^ (n : Ordinal) * α := by
        rw [Nat.cast_add, Nat.cast_one, Ordinal.opow_add, Ordinal.opow_one]
      rw [hstep]
      exact (isCountableOrdinal_opow_nat hα n).mul hα

/-- Every finite power of `ω` is a countable ordinal: `ω ^ n` is countable for all
`n : ℕ`.  (`ω ^ 2 = ω · ω` recovers the parent's `omega0_squared_countable`.) -/
theorem omega0_opow_nat_countable (n : ℕ) :
    IsCountableOrdinal (Ordinal.omega0 ^ (n : Ordinal)) :=
  isCountableOrdinal_opow_nat omega0_countable n

/-- The open conjecture specializes to the flagship case `𝔠 → (ω, n)₂³`. -/
theorem erdos_70_conjecture_imp_omega (h : erdos_70_conjecture) (n : ℕ)
    (hn : 2 ≤ n) : conjecture_omega n :=
  h Ordinal.omega0 n omega0_countable hn

/-- The open conjecture specializes to `𝔠 → (ω², n)₂³`. -/
theorem erdos_70_conjecture_imp_omega_squared (h : erdos_70_conjecture) (n : ℕ)
    (hn : 2 ≤ n) : conjecture_omega_squared n :=
  h (Ordinal.omega0 * Ordinal.omega0) n omega0_squared_countable hn

/-! ## Countability of `ω^ω` (the tower case)

The finite-power closure `isCountableOrdinal_opow_nat` above stops at `ω^n` for
`n : ℕ`.  The genuinely new step is the *limit* exponent `ω^ω`, which the
parent's `conjecture_omega_tower` needs a witness for.  The clean route is to
bridge `IsCountableOrdinal` (`card ≤ ℵ₀`) to `< ω₁` and then use that a countable
supremum of countable ordinals stays below `ω₁` (`Ordinal.iSup_lt_omega_one`,
i.e. the regularity of `ℵ₁`): `ω^ω` is the supremum of the finite powers `ω^n`,
each of which is countable. -/

/-- **Bridge: `IsCountableOrdinal α ↔ α < ω₁`.**  A `card`-level restatement of
countability as being below the first uncountable ordinal, via
`Ordinal.lt_omega_iff_card_lt` and `Cardinal.lt_aleph_one_iff` (`c < ℵ₁ ↔ c ≤ ℵ₀`). -/
theorem isCountableOrdinal_iff_lt_omega_one {α : Ordinal} :
    IsCountableOrdinal α ↔ α < Ordinal.omega 1 := by
  unfold IsCountableOrdinal
  rw [Cardinal.lt_omega_iff_card_lt, Cardinal.lt_aleph_one_iff]

/-- **`ω^ω` is a countable ordinal.**  Writing `ω` as a successor-limit, ordinal
exponentiation gives `ω^ω = ⨆_{β < ω} ω^β`, and every `β < ω` is a finite `k`, so
`ω^β ≤ ω^k ≤ ⨆_{n} ω^n`.  That supremum is a *countable* supremum (indexed by `ℕ`)
of *countable* ordinals `ω^n` (`omega0_opow_nat_countable`), hence `< ω₁` by
`Ordinal.iSup_lt_omega_one`; so `ω^ω < ω₁` and is countable.  This supplies the
witness for the parent's `conjecture_omega_tower`, the `β = ω^ω` case of Erdős #70,
and completes the countability toolkit past all *finite* powers of `ω`. -/
theorem omega0_opow_omega0_countable :
    IsCountableOrdinal (Ordinal.omega0.{0} ^ Ordinal.omega0.{0}) := by
  have hS_lt : (⨆ n : ℕ, Ordinal.omega0.{0} ^ (n : Ordinal)) < Ordinal.omega 1 := by
    apply Ordinal.iSup_lt_omega_one
    intro n
    exact isCountableOrdinal_iff_lt_omega_one.mp (omega0_opow_nat_countable n)
  have hle : Ordinal.omega0.{0} ^ Ordinal.omega0.{0}
      ≤ ⨆ n : ℕ, Ordinal.omega0.{0} ^ (n : Ordinal) := by
    rw [Ordinal.opow_le_of_isSuccLimit Ordinal.omega0_ne_zero Ordinal.isSuccLimit_omega0]
    intro b' hb'
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hb'
    exact Ordinal.le_iSup (fun n : ℕ => Ordinal.omega0.{0} ^ (n : Ordinal)) k
  exact isCountableOrdinal_iff_lt_omega_one.mpr (lt_of_le_of_lt hle hS_lt)

/-- The open conjecture specializes to the tower case `𝔠 → (ω^ω, n)₂³`, using the
countability witness `omega0_opow_omega0_countable`. -/
theorem erdos_70_conjecture_imp_omega_tower (h : erdos_70_conjecture) (n : ℕ)
    (hn : 2 ≤ n) : conjecture_omega_tower n :=
  h (Ordinal.omega0 ^ Ordinal.omega0) n omega0_opow_omega0_countable hn

/-! ## General closure under ordinal exponentiation

`isCountableOrdinal_opow_nat` (above) closes the countable ordinals only under
exponentiation by a *natural number*, and `omega0_opow_omega0_countable` handles
the single limit exponent `ω^ω`.  The theorem below is the full statement: the
countable ordinals are closed under ordinal exponentiation `α ^ β` for **arbitrary**
countable base and exponent.  With it, every ordinal built from `ω` by finitely
many `+`, `*`, `^` steps — the whole tower `ω`, `ω^ω`, `ω^(ω^ω)`, … below `ε₀` —
is a countable ordinal, so the parent conjecture's hypothesis `IsCountableOrdinal β`
holds throughout that range.

The proof is transfinite induction on the exponent (`Ordinal.limitRecOn`):
* `β = 0`: `α ^ 0 = 1` is countable.
* `β = o + 1`: `α ^ (o+1) = α ^ o · α` (`opow_add_one`), countable by the mul-closure.
* `β` a succ-limit: for `α ≠ 0`, `α ^ β = ⨆_{x < β} α ^ x` (`opow_limit`); the index
  `Set.Iio β` is *countable* because `β` is (`mk_Iio_ordinal` + `lift_le_aleph0`), and
  each `α ^ x` is countable by the induction hypothesis, so the supremum stays below
  `ω₁` (`Ordinal.iSup_lt_omega_one`, regularity of `ℵ₁`).  The degenerate base `α = 0`
  gives `0 ^ β = 0` (`zero_opow`, since a limit exponent is nonzero). -/
theorem isCountableOrdinal_opow {α β : Ordinal} (hα : IsCountableOrdinal α) :
    IsCountableOrdinal β → IsCountableOrdinal (α ^ β) := by
  induction β using Ordinal.limitRecOn with
  | zero =>
    intro _
    rw [Ordinal.opow_zero]; exact one_countable
  | add_one o ih =>
    intro hβ
    have ho : IsCountableOrdinal o := hβ.of_le (self_le_add_right o 1)
    rw [Ordinal.opow_add_one]
    exact isCountableOrdinal_mul (ih ho) hα
  | limit o hlim ih =>
    intro hβ
    rcases eq_or_ne α 0 with rfl | hα0
    · have ho0 : o ≠ 0 := by
        have := hlim.ne_bot; simpa [Ordinal.bot_eq_zero] using this
      rw [Ordinal.zero_opow ho0]
      exact zero_countable
    · have hcount : Countable (Set.Iio o) := by
        rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]
        exact hβ
      rw [isCountableOrdinal_iff_lt_omega_one, Ordinal.opow_limit hα0 hlim]
      apply Ordinal.iSup_lt_omega_one
      rintro ⟨x, hx⟩
      exact isCountableOrdinal_iff_lt_omega_one.mp (ih x hx (hβ.of_le (le_of_lt hx)))

/-- **The second tower level `ω^(ω^ω)` is a countable ordinal.**  An immediate
consequence of the general closure `isCountableOrdinal_opow` applied twice to
`omega0_countable`; whereas `omega0_opow_omega0_countable` needed a bespoke
countable-supremum argument, every further tower level is now free.  Supplies the
`β = ω^(ω^ω)` countability witness for `erdos_70_conjecture`. -/
theorem omega0_opow_omega0_opow_omega0_countable :
    IsCountableOrdinal
      (Ordinal.omega0.{0} ^ (Ordinal.omega0.{0} ^ Ordinal.omega0.{0})) :=
  isCountableOrdinal_opow omega0_countable
    (isCountableOrdinal_opow omega0_countable omega0_countable)

/-- The open conjecture specializes to the second tower level `𝔠 → (ω^(ω^ω), n)₂³`,
using the countability witness `omega0_opow_omega0_opow_omega0_countable`. -/
theorem erdos_70_conjecture_imp_omega_tower_two (h : erdos_70_conjecture) (n : ℕ)
    (hn : 2 ≤ n) :
    PartitionArrow continuum_card
      (Ordinal.omega0 ^ (Ordinal.omega0 ^ Ordinal.omega0)) n :=
  h (Ordinal.omega0 ^ (Ordinal.omega0 ^ Ordinal.omega0)) n
    omega0_opow_omega0_opow_omega0_countable hn

/-! ## Capstone: `ε₀` is a countable ordinal

The tower witnesses above (`ω`, `ω^ω`, `ω^(ω^ω)`) each handle a *fixed finite* level.
The `ω`-tower `T 0 = ω`, `T (n+1) = ω ^ T n` runs through all of them, and its supremum
`⨆ₙ T n` is `ε₀`, the least fixed point of `ξ ↦ ω^ξ` (the least epsilon number).  Since
every level `T n` is countable (`isCountableOrdinal_opow`, by induction) and the index set
`ℕ` is countable, the supremum stays below `ω₁` (regularity of `ℵ₁`,
`Ordinal.iSup_lt_omega_one`).  So `ε₀` — the top of the whole exponential hierarchy over
`ω`, and the exact boundary the file's narrative points at — is itself a *countable*
ordinal, and the parent conjecture's hypothesis `IsCountableOrdinal β` holds all the way up
to and including it. -/

/-- The `ω`-tower `T 0 = ω`, `T (n+1) = ω ^ (T n)`: the sequence `ω, ω^ω, ω^(ω^ω), …`
whose supremum is `ε₀`. -/
noncomputable def omegaTower : ℕ → Ordinal
  | 0 => Ordinal.omega0
  | (n + 1) => Ordinal.omega0 ^ (omegaTower n)

/-- Every level of the `ω`-tower is a countable ordinal (induction on `n`, using the
general exponentiation closure `isCountableOrdinal_opow`). -/
theorem omegaTower_countable : ∀ n, IsCountableOrdinal (omegaTower n)
  | 0 => omega0_countable
  | (n + 1) => isCountableOrdinal_opow omega0_countable (omegaTower_countable n)

/-- **`ε₀` is a countable ordinal.**  `ε₀ = ⨆ₙ (ω`-tower `n)` is a countable (`ℕ`-indexed)
supremum of the countable ordinals `omegaTower_countable`, hence `< ω₁`
(`Ordinal.iSup_lt_omega_one`).  This is the capstone of the tower-closure development: the
supremum of the entire exponential hierarchy `ω, ω^ω, ω^(ω^ω), …` — the least epsilon
number — remains countable. -/
theorem iSup_omegaTower_countable :
    IsCountableOrdinal (⨆ n : ℕ, omegaTower n) := by
  rw [isCountableOrdinal_iff_lt_omega_one]
  apply Ordinal.iSup_lt_omega_one
  intro n
  exact isCountableOrdinal_iff_lt_omega_one.mp (omegaTower_countable n)

/-- **`ε₀` is an epsilon number: `ω ^ ε₀ = ε₀`.**  The supremum `ε₀ = ⨆ₙ (ω`-tower
`n)` is a *fixed point* of the base-`ω` exponential `ξ ↦ ω^ξ` — the defining property
of an epsilon number, which the development above only asserts in prose.  The proof
uses that `ω^·` is a normal function (`Ordinal.isNormal_opow Ordinal.one_lt_omega0`)
and hence commutes with the countable supremum (`IsNormal.map_iSup`):

  `ω ^ (⨆ₙ Tₙ) = ⨆ₙ ω^Tₙ = ⨆ₙ T_{n+1} = ⨆ₙ Tₙ`,

the last step because `ω^Tₙ = T_{n+1}` is by definition of the tower and shifting the
`ℕ`-index leaves the supremum unchanged (`≤` by the inflationary `x ≤ ω^x`, `≥` because
`{T_{n+1}}` is a subfamily of `{Tₙ}`).  Combined with `iSup_omegaTower_countable`, this
identifies `ε₀` as the *least countable* ordinal fixed by `ω^·` — the exact top of the
exponential hierarchy the file's narrative points at. -/
theorem omega0_opow_iSup_omegaTower :
    Ordinal.omega0 ^ (⨆ n : ℕ, omegaTower n) = ⨆ n : ℕ, omegaTower n := by
  have hN : Ordinal.IsNormal (Ordinal.omega0 ^ ·) :=
    Ordinal.isNormal_opow Ordinal.one_lt_omega0
  apply le_antisymm
  · -- `ω^ε₀ = ⨆ₙ ω^Tₙ = ⨆ₙ T_{n+1} ≤ ⨆ₘ Tₘ`
    rw [Order.IsNormal.map_iSup hN bddAbove_of_small]
    apply Ordinal.iSup_le
    intro n
    calc Ordinal.omega0 ^ (omegaTower n) = omegaTower (n + 1) := rfl
      _ ≤ ⨆ m : ℕ, omegaTower m := Ordinal.le_iSup omegaTower (n + 1)
  · -- `ε₀ = ⨆ₙ Tₙ ≤ ⨆ₙ ω^Tₙ = ω^ε₀`, using `Tₙ ≤ ω^Tₙ` and monotonicity of `ω^·`
    apply Ordinal.iSup_le
    intro n
    calc omegaTower n ≤ Ordinal.omega0 ^ (omegaTower n) := hN.le_apply
      _ ≤ Ordinal.omega0 ^ (⨆ m : ℕ, omegaTower m) :=
          Ordinal.opow_le_opow_right Ordinal.omega0_pos (Ordinal.le_iSup omegaTower n)

/-- The open conjecture specializes all the way to `ε₀`: `𝔠 → (ε₀, n)₂³`, using the
countability witness `iSup_omegaTower_countable`.  Every ordinal in the naturally-described
exponential hierarchy over `ω`, up to and including its `ε₀` limit, is a valid instance of
the parent conjecture. -/
theorem erdos_70_conjecture_imp_epsilon0 (h : erdos_70_conjecture) (n : ℕ)
    (hn : 2 ≤ n) :
    PartitionArrow continuum_card (⨆ k : ℕ, omegaTower k) n :=
  h (⨆ k : ℕ, omegaTower k) n iSup_omegaTower_countable hn

/-! ## The single missing ingredient: infinite Ramsey for 3-uniform 2-colourings

Every result above runs *from* the conjecture *to* a special case (it assumes
`erdos_70_conjecture` and specializes `β`).  This section runs the other way: it
identifies the *one* partition-calculus fact that would establish the whole
formalized conjecture at a stroke, uniformly in `β`, and proves the reduction.

That fact is the **infinite Ramsey theorem** for 2-colourings of 3-element
subsets: on any continuum-sized `S`, some colour class admits an *infinite*
homogeneous set.  It is a classical theorem but is **absent from Mathlib v4.31**
(there is no infinite Ramsey / hypergraph-partition development — see
`Mathlib.Combinatorics`, which stops at Hales–Jewett, Hindman, and finite
pigeonhole).  The reduction below shows it is the sole obstruction.

**Faithfulness caveat.**  Because the parent's `HasOrderTypeAtLeast` is the
*cardinality* surrogate `α.card ≤ #H` (an explicitly "simplified version", see
`Erdos70Problem.lean`), the colour-0 disjunct is met by any set of cardinality
`≥ ℵ₀`.  Consequently the *formalized* conjecture is **strictly weaker** than the
genuine partition relation `𝔠 → (β, n)₂³` of Erdős #70, which demands a colour-0
homogeneous set of true order type `β`.  The reduction proves the formalized
statement is in fact a *theorem modulo infinite Ramsey* — it does **not** settle
the real order-type problem, which remains open. -/

/-- **The missing ingredient.**  Infinite Ramsey for 2-colourings of 3-element
subsets of a continuum-sized set: some colour class has an *infinite* homogeneous
set.  A classical theorem, but not present in Mathlib v4.31; carried here as a
named hypothesis rather than an `axiom` so the reduction stays assumption-free. -/
def InfiniteRamsey3 : Prop :=
  ∀ (S : Type) [DecidableEq S] (_ : Cardinal.mk S = continuum_card) (c : Coloring S 3 2),
    ∃ (H : Set S) (i : Fin 2), H.Infinite ∧ IsHomogeneous H 3 c i

/-- **Reduction of the whole formalized conjecture to one Ramsey fact.**
`InfiniteRamsey3` implies `erdos_70_conjecture` — uniformly in every countable
`β` and every `2 ≤ n` — under the file's cardinality surrogate for order type.

Given a 2-colouring of the 3-subsets of a continuum-sized `S`, take the infinite
homogeneous set `H` supplied by `InfiniteRamsey3`.
* If its colour is `0`, `H` witnesses the left disjunct: it is homogeneous, and
  `β.card ≤ ℵ₀ ≤ #H` (`β` countable; `H` infinite), so `HasOrderTypeAtLeast S H β`.
* If its colour is `1`, any `n`-element finite subset of the infinite `H` witnesses
  the right disjunct (`Set.Infinite.exists_subset_card_eq`), homogeneous because a
  subset of an `IsHomogeneous` set is homogeneous. -/
theorem infiniteRamsey3_imp_conjecture (h : InfiniteRamsey3) : erdos_70_conjecture := by
  intro β n hβ _hn S _ hS c
  obtain ⟨H, i, hHinf, hHom⟩ := h S hS c
  fin_cases i
  · -- colour 0: the infinite homogeneous set meets the order-type (cardinality) side
    refine Or.inl ⟨H, ?_, hHom⟩
    have hcard : Cardinal.aleph0 ≤ Cardinal.mk H :=
      Cardinal.aleph0_le_mk_iff.mpr (Set.infinite_coe_iff.mpr hHinf)
    exact le_trans hβ hcard
  · -- colour 1: any n-subset of the infinite homogeneous set meets the size side
    obtain ⟨t, hts, htc⟩ := hHinf.exists_subset_card_eq n
    refine Or.inr ⟨t, htc.ge, ?_⟩
    intro s hs hsub
    exact hHom s hs (subset_trans (Finset.coe_subset.mpr hsub) hts)

/-- Contrapositive packaging: a genuine counterexample to the formalized conjecture
would refute infinite Ramsey for 3-uniform 2-colourings.  Since the latter is a
theorem, this reconfirms that the *formalized* conjecture (cardinality surrogate)
cannot have a counterexample — the open content lives entirely in the gap between
`HasOrderTypeAtLeast` and true order type. -/
theorem counterexample_imp_not_infiniteRamsey3
    (h : erdos_70_counterexample) : ¬ InfiniteRamsey3 :=
  fun hR => conjecture_xor_counterexample.mp (infiniteRamsey3_imp_conjecture hR) h

end Erdos70
