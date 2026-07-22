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

6. `infiniteRamsey3_holds` / `erdos_70_formalized_conjecture_holds` — the
   **infinite Ramsey theorem for 2-colourings of 3-element subsets** (absent from
   Mathlib v4.31), proved from scratch by the iterated-ultrafilter-majority
   argument over the hyperfilter on `ℕ`; consequently the *formalized* conjecture
   `erdos_70_conjecture` is an unconditional theorem.  **Faithfulness caveat**: the
   parent's `HasOrderTypeAtLeast` is a cardinality surrogate for order type, so
   this does NOT settle Erdős #70 itself — the genuine order-type partition
   relation `𝔠 → (β, n)₂³` remains open.

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
    Ordinal.omega0.{0} ^ (⨆ n : ℕ, omegaTower n) = ⨆ n : ℕ, omegaTower n := by
  have hN : Ordinal.IsNormal (Ordinal.omega0.{0} ^ ·) :=
    Ordinal.isNormal_opow Ordinal.one_lt_omega0
  apply le_antisymm
  · -- `ω^ε₀ = ⨆ₙ ω^Tₙ = ⨆ₙ T_{n+1} ≤ ⨆ₘ Tₘ`
    rw [hN.map_iSup omegaTower]
    apply Ordinal.iSup_le
    intro n
    calc Ordinal.omega0.{0} ^ (omegaTower n) = omegaTower (n + 1) := rfl
      _ ≤ ⨆ m : ℕ, omegaTower m := Ordinal.le_iSup omegaTower (n + 1)
  · -- `ε₀ = ⨆ₙ Tₙ ≤ ⨆ₙ ω^Tₙ = ω^ε₀`, using `Tₙ ≤ ω^Tₙ` and monotonicity of `ω^·`
    apply Ordinal.iSup_le
    intro n
    calc omegaTower n ≤ Ordinal.omega0.{0} ^ (omegaTower n) := hN.le_apply
      _ ≤ Ordinal.omega0.{0} ^ (⨆ m : ℕ, omegaTower m) :=
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
set.  A classical theorem, but not present in Mathlib v4.31; stated here as a
named proposition so the reduction below stays assumption-free — and **proved
outright** in the final section of this file (`infiniteRamsey3_holds`). -/
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

/-! ## `InfiniteRamsey3` is a theorem: infinite Ramsey for triples, proved

The section above isolated `InfiniteRamsey3` as the single missing ingredient and
proved the reduction `InfiniteRamsey3 → erdos_70_conjecture`.  This section supplies
the ingredient: a complete, assumption-free proof of the infinite Ramsey theorem for
2-colourings of 3-element subsets — a statement absent from Mathlib v4.31 — by the
classical iterated-ultrafilter-majority argument.

**Proof sketch.**  It suffices to work on `ℕ`: a continuum-sized `S` receives an
embedding `ℕ ↪ S`, colourings pull back along it, and infinite homogeneous sets push
forward.  Fix `U := hyperfilter ℕ`, the ultrafilter extending the cofinite filter,
and a 2-colouring `c` of the 3-subsets of `ℕ`.  Iterate the `U`-majority operation:

* `pairMaj x y` — the colour `z ↦ c {x, y, z}` takes on a `U`-large set of `z`;
* `pointMaj x` — the colour `y ↦ pairMaj x y` takes on a `U`-large set of `y`;
* `topMaj`     — the colour `pointMaj` takes on a `U`-large set.

Recursively pick `ramseySeq 0 < ramseySeq 1 < ⋯`, the `n`-th term being the least
member of the **good set** of the list `L` of earlier terms: `m` is *good for `L`*
when `pointMaj m = topMaj`, `m` exceeds every element of `L`, `pairMaj a m = topMaj`
for every `a ∈ L`, and `c {b, a, m} = topMaj` for every `b < a` in `L`.  Each clause
cuts out a `U`-large set of `m` — by the majority property `majColor_mem` plus the
invariant that all earlier terms were themselves chosen good — so the good set, a
finite intersection, lies in `U`, hence is nonempty.  Every 3-subset
`{ramseySeq p, ramseySeq q, ramseySeq r}` (`p < q < r`) of the range then has colour
`topMaj`, because its largest point was chosen good for a list containing the other
two.  Ordering every clause smaller-point-first means no symmetry lemmas for the
triple colour are ever needed. -/

section RamseyProof

open Filter

/-- The colour of the (unordered) triple `{x, y, z}` under a colouring of 3-subsets,
as a total function of the three points; junk value `0` when the points collide. -/
noncomputable def tripleColor (c : Coloring ℕ 3 2) (x y z : ℕ) : Fin 2 :=
  if h : ({x, y, z} : Finset ℕ).card = 3 then c ⟨{x, y, z}, h⟩ else 0

/-- Evaluation: on an honest 3-subset, `tripleColor` computes the colouring. -/
theorem tripleColor_eval (c : Coloring ℕ 3 2) {t : Finset ℕ} (ht : t.card = 3)
    {x y z : ℕ} (h : t = {x, y, z}) : c ⟨t, ht⟩ = tripleColor c x y z := by
  subst h
  rw [tripleColor, dif_pos ht]

open scoped Classical in
/-- The `U`-majority colour of a 2-valued function on `ℕ`, `U` = the hyperfilter
(the ultrafilter extending the cofinite filter). -/
noncomputable def majColor (f : ℕ → Fin 2) : Fin 2 :=
  if {n | f n = 0} ∈ hyperfilter ℕ then 0 else 1

/-- The defining property of the majority colour: it is attained on a `U`-large set. -/
theorem majColor_mem (f : ℕ → Fin 2) : {n | f n = majColor f} ∈ hyperfilter ℕ := by
  by_cases h : {n | f n = 0} ∈ hyperfilter ℕ
  · simp [majColor, h]
  · have h' : {n | f n = 0}ᶜ ∈ hyperfilter ℕ := Ultrafilter.compl_mem_iff_notMem.mpr h
    have hset : {n | f n = 0}ᶜ = {n | f n = 1} := by
      have h2 : ∀ x : Fin 2, ¬x = 0 ↔ x = 1 := by decide
      ext n
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      exact h2 (f n)
    rw [hset] at h'
    simpa [majColor, h] using h'

/-- Level-2 majority: the `U`-majority colour of `z ↦ c {x, y, z}`. -/
noncomputable def pairMaj (c : Coloring ℕ 3 2) (x y : ℕ) : Fin 2 :=
  majColor (fun z => tripleColor c x y z)

/-- Level-1 majority: the `U`-majority colour of `y ↦ pairMaj x y`. -/
noncomputable def pointMaj (c : Coloring ℕ 3 2) (x : ℕ) : Fin 2 :=
  majColor (fun y => pairMaj c x y)

/-- The top-level majority colour — the colour of the homogeneous set we build. -/
noncomputable def topMaj (c : Coloring ℕ 3 2) : Fin 2 :=
  majColor (fun x => pointMaj c x)

theorem pointMaj_large (c : Coloring ℕ 3 2) :
    {x | pointMaj c x = topMaj c} ∈ hyperfilter ℕ :=
  majColor_mem (fun x => pointMaj c x)

theorem pairMaj_large (c : Coloring ℕ 3 2) {x : ℕ} (hx : pointMaj c x = topMaj c) :
    {y | pairMaj c x y = topMaj c} ∈ hyperfilter ℕ := by
  have h := majColor_mem (fun y => pairMaj c x y)
  rwa [show majColor (fun y => pairMaj c x y) = topMaj c from hx] at h

theorem triple_large (c : Coloring ℕ 3 2) {x y : ℕ}
    (hxy : pairMaj c x y = topMaj c) :
    {z | tripleColor c x y z = topMaj c} ∈ hyperfilter ℕ := by
  have h := majColor_mem (fun z => tripleColor c x y z)
  rwa [show majColor (fun z => tripleColor c x y z) = topMaj c from hxy] at h

/-- Tails are `U`-large: `U` extends the cofinite filter. -/
theorem gt_large (a : ℕ) : {m | a < m} ∈ hyperfilter ℕ :=
  Nat.hyperfilter_le_atTop (Filter.Ioi_mem_atTop a)

/-- A conjunction of `U`-large conditions indexed by a finite list is `U`-large. -/
theorem list_forall_large {P : ℕ → ℕ → Prop} (L : List ℕ)
    (h : ∀ a ∈ L, {m | P a m} ∈ hyperfilter ℕ) :
    {m | ∀ a ∈ L, P a m} ∈ hyperfilter ℕ := by
  induction L with
  | nil =>
    have huniv : {m : ℕ | ∀ a ∈ ([] : List ℕ), P a m} = Set.univ := by
      ext m; simp
    rw [huniv]
    exact Filter.univ_mem
  | cons a L ih =>
    have h1 : {m | P a m} ∈ hyperfilter ℕ := h a (by simp)
    have h2 : {m | ∀ b ∈ L, P b m} ∈ hyperfilter ℕ :=
      ih fun b hb => h b (List.mem_cons_of_mem a hb)
    have hsub : {m | P a m} ∩ {m | ∀ b ∈ L, P b m} ⊆ {m | ∀ b ∈ a :: L, P b m} := by
      rintro m ⟨hm1, hm2⟩ b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hm1
      · exact hm2 b hb'
    exact Filter.mem_of_superset (Filter.inter_mem h1 h2) hsub

/-- The set of viable next elements after the finite prefix `L`: correct level-1
majority, larger than all of `L`, correct level-2 majority against each element of
`L`, and correct triple colour against each increasing pair from `L`. -/
def goodSet (c : Coloring ℕ 3 2) (L : List ℕ) : Set ℕ :=
  {m | pointMaj c m = topMaj c ∧ ∀ a ∈ L, a < m ∧ pairMaj c a m = topMaj c ∧
        ∀ b ∈ L, b < a → tripleColor c b a m = topMaj c}

/-- The good set is `U`-large, given the choice invariant for the prefix `L`. -/
theorem goodSet_mem (c : Coloring ℕ 3 2) {L : List ℕ}
    (h1 : ∀ a ∈ L, pointMaj c a = topMaj c)
    (h2 : ∀ a ∈ L, ∀ b ∈ L, b < a → pairMaj c b a = topMaj c) :
    goodSet c L ∈ hyperfilter ℕ := by
  have hA : {m | pointMaj c m = topMaj c} ∈ hyperfilter ℕ := pointMaj_large c
  have hB : {m | ∀ a ∈ L, a < m ∧ pairMaj c a m = topMaj c ∧
      ∀ b ∈ L, b < a → tripleColor c b a m = topMaj c} ∈ hyperfilter ℕ := by
    apply list_forall_large
    intro a ha
    have hBa1 : {m | a < m} ∈ hyperfilter ℕ := gt_large a
    have hBa2 : {m | pairMaj c a m = topMaj c} ∈ hyperfilter ℕ :=
      pairMaj_large c (h1 a ha)
    have hBa3 : {m | ∀ b ∈ L, b < a → tripleColor c b a m = topMaj c} ∈
        hyperfilter ℕ := by
      apply list_forall_large
      intro b hb
      by_cases hba : b < a
      · exact Filter.mem_of_superset (triple_large c (h2 a ha b hb hba))
          fun m hm _ => hm
      · exact Filter.mem_of_superset Filter.univ_mem
          fun m _ hba' => absurd hba' hba
    exact Filter.inter_mem hBa1 (Filter.inter_mem hBa2 hBa3)
  exact Filter.inter_mem hA hB

/-- The increasing prefix lists of the homogeneous sequence: each new term is the
least member of the good set of its predecessors. -/
noncomputable def ramseyPrefix (c : Coloring ℕ 3 2) : ℕ → List ℕ
  | 0 => []
  | n + 1 => ramseyPrefix c n ++ [sInf (goodSet c (ramseyPrefix c n))]

/-- The homogeneous sequence itself. -/
noncomputable def ramseySeq (c : Coloring ℕ 3 2) (n : ℕ) : ℕ :=
  sInf (goodSet c (ramseyPrefix c n))

theorem ramseyPrefix_succ (c : Coloring ℕ 3 2) (n : ℕ) :
    ramseyPrefix c (n + 1) = ramseyPrefix c n ++ [ramseySeq c n] := rfl

theorem mem_ramseyPrefix_iff (c : Coloring ℕ 3 2) {a : ℕ} {n : ℕ} :
    a ∈ ramseyPrefix c n ↔ ∃ k, k < n ∧ ramseySeq c k = a := by
  induction n with
  | zero => simp [ramseyPrefix]
  | succ n ih =>
    rw [ramseyPrefix_succ, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro (⟨k, hk, rfl⟩ | rfl)
      · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
      · exact ⟨n, Nat.lt_succ_self n, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · exact Or.inl ⟨k, hk', rfl⟩
      · exact Or.inr rfl

/-- The choice invariant: every prefix element has the majority level-1 colour, and
every increasing pair from the prefix has the majority level-2 colour. -/
def RamseyInv (c : Coloring ℕ 3 2) (L : List ℕ) : Prop :=
  (∀ a ∈ L, pointMaj c a = topMaj c) ∧
    ∀ a ∈ L, ∀ b ∈ L, b < a → pairMaj c b a = topMaj c

/-- Main induction: the invariant propagates, and every term really is chosen from
the good set of its predecessors (which is `U`-large, hence nonempty). -/
theorem ramsey_invariant (c : Coloring ℕ 3 2) (n : ℕ) :
    RamseyInv c (ramseyPrefix c n) ∧
      ramseySeq c n ∈ goodSet c (ramseyPrefix c n) := by
  induction n with
  | zero =>
    have hInv : RamseyInv c (ramseyPrefix c 0) := by
      constructor
      · intro a ha; simp [ramseyPrefix] at ha
      · intro a ha; simp [ramseyPrefix] at ha
    exact ⟨hInv,
      Nat.sInf_mem (Ultrafilter.nonempty_of_mem (goodSet_mem c hInv.1 hInv.2))⟩
  | succ n ih =>
    obtain ⟨hInv, hGood⟩ := ih
    have hg : pointMaj c (ramseySeq c n) = topMaj c ∧
        ∀ a ∈ ramseyPrefix c n, a < ramseySeq c n ∧
          pairMaj c a (ramseySeq c n) = topMaj c ∧
          ∀ b ∈ ramseyPrefix c n, b < a →
            tripleColor c b a (ramseySeq c n) = topMaj c := hGood
    have hInv' : RamseyInv c (ramseyPrefix c (n + 1)) := by
      constructor
      · intro a ha
        rw [ramseyPrefix_succ, List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hInv.1 a ha
        · exact hg.1
      · intro a ha b hb hba
        rw [ramseyPrefix_succ, List.mem_append, List.mem_singleton] at ha hb
        rcases ha with ha | rfl <;> rcases hb with hb | rfl
        · exact hInv.2 a ha b hb hba
        · exact absurd hba (not_lt.mpr (hg.2 a ha).1.le)
        · exact (hg.2 b hb).2.1
        · exact absurd hba (lt_irrefl _)
    exact ⟨hInv',
      Nat.sInf_mem (Ultrafilter.nonempty_of_mem (goodSet_mem c hInv'.1 hInv'.2))⟩

/-- Unpacked good-set membership of the `n`-th term. -/
theorem goodSet_spec (c : Coloring ℕ 3 2) (n : ℕ) :
    pointMaj c (ramseySeq c n) = topMaj c ∧
      ∀ a ∈ ramseyPrefix c n, a < ramseySeq c n ∧
        pairMaj c a (ramseySeq c n) = topMaj c ∧
        ∀ b ∈ ramseyPrefix c n, b < a →
          tripleColor c b a (ramseySeq c n) = topMaj c :=
  (ramsey_invariant c n).2

theorem ramseySeq_strictMono (c : Coloring ℕ 3 2) : StrictMono (ramseySeq c) := by
  intro j k hjk
  have hmem : ramseySeq c j ∈ ramseyPrefix c k :=
    (mem_ramseyPrefix_iff c).mpr ⟨j, hjk, rfl⟩
  exact ((goodSet_spec c k).2 (ramseySeq c j) hmem).1

/-- The heart of homogeneity: every increasing triple from the sequence has the
majority colour, because the largest point was chosen good for a prefix containing
the other two. -/
theorem ramseySeq_triple (c : Coloring ℕ 3 2) {p q r : ℕ}
    (hpq : p < q) (hqr : q < r) :
    tripleColor c (ramseySeq c p) (ramseySeq c q) (ramseySeq c r) = topMaj c := by
  have hp : ramseySeq c p ∈ ramseyPrefix c r :=
    (mem_ramseyPrefix_iff c).mpr ⟨p, hpq.trans hqr, rfl⟩
  have hq : ramseySeq c q ∈ ramseyPrefix c r :=
    (mem_ramseyPrefix_iff c).mpr ⟨q, hqr, rfl⟩
  exact ((goodSet_spec c r).2 (ramseySeq c q) hq).2.2 (ramseySeq c p) hp
    (ramseySeq_strictMono c hpq)

/-- Any 3-element finset of naturals lists as a strictly increasing triple. -/
theorem exists_sorted_triple {t : Finset ℕ} (ht : t.card = 3) :
    ∃ x y z : ℕ, x < y ∧ y < z ∧ t = {x, y, z} := by
  obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Finset.card_eq_three.mp ht
  rcases Nat.lt_or_ge a b with h1 | h1
  · rcases Nat.lt_or_ge b d with h2 | h2
    · exact ⟨a, b, d, h1, h2, rfl⟩
    · have h2' : d < b := lt_of_le_of_ne h2 (Ne.symm hbd)
      rcases Nat.lt_or_ge a d with h3 | h3
      · exact ⟨a, d, b, h3, h2', by ext w; simp; tauto⟩
      · have h3' : d < a := lt_of_le_of_ne h3 (Ne.symm had)
        exact ⟨d, a, b, h3', h1, by ext w; simp; tauto⟩
  · have h1' : b < a := lt_of_le_of_ne h1 (Ne.symm hab)
    rcases Nat.lt_or_ge a d with h2 | h2
    · exact ⟨b, a, d, h1', h2, by ext w; simp; tauto⟩
    · have h2' : d < a := lt_of_le_of_ne h2 (Ne.symm had)
      rcases Nat.lt_or_ge b d with h3 | h3
      · exact ⟨b, d, a, h3, h2', by ext w; simp; tauto⟩
      · have h3' : d < b := lt_of_le_of_ne h3 (Ne.symm hbd)
        exact ⟨d, b, a, h3', h1', by ext w; simp; tauto⟩

/-- **Infinite Ramsey for triples on `ℕ`**: any 2-colouring of the 3-subsets of `ℕ`
admits an infinite homogeneous set (namely the range of `ramseySeq`, with the
top-majority colour). -/
theorem ramsey3_nat (c : Coloring ℕ 3 2) :
    ∃ (H : Set ℕ) (i : Fin 2), H.Infinite ∧ IsHomogeneous H 3 c i := by
  refine ⟨Set.range (ramseySeq c), topMaj c, ?_, ?_⟩
  · exact Set.infinite_range_of_injective (ramseySeq_strictMono c).injective
  · intro t ht hsub
    obtain ⟨x, y, z, hxy, hyz, rfl⟩ := exists_sorted_triple ht
    have hx : x ∈ Set.range (ramseySeq c) := hsub (by simp)
    have hy : y ∈ Set.range (ramseySeq c) := hsub (by simp)
    have hz : z ∈ Set.range (ramseySeq c) := hsub (by simp)
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    obtain ⟨r, rfl⟩ := hz
    have hpq : p < q := (ramseySeq_strictMono c).lt_iff_lt.mp hxy
    have hqr : q < r := (ramseySeq_strictMono c).lt_iff_lt.mp hyz
    exact (tripleColor_eval c ht rfl).trans (ramseySeq_triple c hpq hqr)

/-- **The missing ingredient, delivered: `InfiniteRamsey3` is a theorem.**  Any
continuum-sized type embeds a copy of `ℕ`; pull the colouring back, run the
ultrafilter construction there, and push the infinite homogeneous set forward. -/
theorem infiniteRamsey3_holds : InfiniteRamsey3 := by
  intro S _ hS c
  have hinf : Infinite S := Cardinal.infinite_iff.mpr
    (by rw [hS]; exact Cardinal.aleph0_le_continuum)
  let f : ℕ ↪ S := Infinite.natEmbedding S
  obtain ⟨A, i, hAinf, hAhom⟩ :=
    ramsey3_nat (fun t => c ⟨t.1.map f, by rw [Finset.card_map]; exact t.2⟩)
  refine ⟨f '' A, i, hAinf.image f.injective.injOn, ?_⟩
  intro t ht hsub
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht
  have hx : x ∈ f '' A := hsub (by simp)
  have hy : y ∈ f '' A := hsub (by simp)
  have hz : z ∈ f '' A := hsub (by simp)
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨d, hd, rfl⟩ := hz
  have hab : a ≠ b := fun h => hxy (by rw [h])
  have had : a ≠ d := fun h => hxz (by rw [h])
  have hbd : b ≠ d := fun h => hyz (by rw [h])
  have hs3 : ({a, b, d} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, d, hab, had, hbd, rfl⟩
  have hmap : ({a, b, d} : Finset ℕ).map f = {f a, f b, f d} := by
    simp [Finset.map_insert, Finset.map_singleton]
  have hsubA : (↑({a, b, d} : Finset ℕ) : Set ℕ) ⊆ A := by
    intro w hw
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hkey := hAhom {a, b, d} hs3 hsubA
  have hmapcard : (({a, b, d} : Finset ℕ).map f).card = 3 := by
    rw [Finset.card_map]; exact hs3
  have hcast : (⟨{f a, f b, f d}, ht⟩ : {u : Finset S // u.card = 3}) =
      ⟨({a, b, d} : Finset ℕ).map f, hmapcard⟩ := Subtype.ext hmap.symm
  rw [hcast]
  exact hkey

/-- **The formalized conjecture is a theorem** — with the file's standing
faithfulness caveat.  Because the parent's `HasOrderTypeAtLeast` is the cardinality
surrogate `β.card ≤ #H`, this establishes the *formalized* statement
`erdos_70_conjecture`, not the genuine partition relation `𝔠 → (β, n)₂³` with true
order type `β`, which is Erdős Problem #70 and remains **open**.  What is proved:
for every countable `β` and every `n ≥ 2`, every 2-colouring of the 3-subsets of a
continuum-sized set admits either a colour-0 homogeneous set of cardinality
`≥ β.card` or a colour-1 homogeneous set of size `n` — an unconditional consequence
of the infinite Ramsey theorem for triples proved above. -/
theorem erdos_70_formalized_conjecture_holds : erdos_70_conjecture :=
  infiniteRamsey3_imp_conjecture infiniteRamsey3_holds

/-- The formalized counterexample predicate is refuted outright. -/
theorem no_erdos_70_counterexample : ¬ erdos_70_counterexample :=
  conjecture_xor_counterexample.mp erdos_70_formalized_conjecture_holds

/-- The flagship case `𝔠 → (ω, n)₂³` (cardinality surrogate), now unconditional. -/
theorem conjecture_omega_holds (n : ℕ) (hn : 2 ≤ n) : conjecture_omega n :=
  erdos_70_conjecture_imp_omega erdos_70_formalized_conjecture_holds n hn

/-- The case `𝔠 → (ω², n)₂³` (cardinality surrogate), now unconditional. -/
theorem conjecture_omega_squared_holds (n : ℕ) (hn : 2 ≤ n) :
    conjecture_omega_squared n :=
  erdos_70_conjecture_imp_omega_squared erdos_70_formalized_conjecture_holds n hn

/-- The `ε₀` case (cardinality surrogate), now unconditional. -/
theorem epsilon0_partitionArrow_holds (n : ℕ) (hn : 2 ≤ n) :
    PartitionArrow continuum_card (⨆ k : ℕ, omegaTower k) n :=
  erdos_70_conjecture_imp_epsilon0 erdos_70_formalized_conjecture_holds n hn

end RamseyProof

end Erdos70
