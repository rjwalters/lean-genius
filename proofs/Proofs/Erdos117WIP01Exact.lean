/-
  Erdős Problem #117 — Covering Groups by Abelian Subgroups: **h(3) = 3, exactly**.

  Companion to `Erdos117Problem.lean` and the `Erdos117WIP01*` ladder.  Prior
  companions pinned `h(0) = 0`, `h(1) = h(2) = 1`, and — conditionally on the
  covering set being nonempty — `h(n) ≥ 3` for `n ≥ 3` (witness `Q₈`).  Every
  `h(3)` statement so far carried the honest hypothesis
  `∃ k, CoversWithAbelian k 3`, because well-definedness of `h(3)` (a UNIFORM
  finite abelian-cover budget for *every* group with the 3-commuting property)
  was assessed as "classification-strength, not attempted here"
  (`Erdos117WIP01Three.lean` header).

  This file removes that hypothesis: the uniform budget is `3`, by an entirely
  elementary argument, and consequently

      **h(3) = 3** — the first nontrivial exact value on the Erdős #117 ladder,
      unconditional and axiom-free.

  The two-step mechanism (no classification, no Pyber, no symplectic forms):

  1. **Covering.**  If `a`, `b` do not commute, then `{a, b, ab}` is pairwise
     non-commuting, so in a group with the 3-commuting property every `g` must
     commute with one of `a`, `b`, `ab` — otherwise `{a, b, ab, g}` is a
     4-subset with no commuting pair.  Hence `G = C(a) ∪ C(b) ∪ C(ab)`.

  2. **Centralizers are abelian.**  If `u, v ∈ C(a)` fail to commute, a case
     analysis on which of `u`, `v`, `uv` the element `b` commutes with produces
     an explicit pairwise non-commuting 4-set in every case:

       | `b~u` | `b~v` | `b~uv` | forbidden 4-set          |
       |-------|-------|--------|--------------------------|
       |  yes  |  yes  |  (yes) | `{au, av, b, a(uv)}`     |
       |  yes  |  no   |   —    | `{au, b, v, uv}`         |
       |  no   |  yes  |   —    | symmetric (swap `u,v`)   |
       |  no   |  no   |  yes   | `{b, u, v, a(uv)}`       |
       |  no   |  no   |  no    | `{b, u, v, uv}`          |

     Distinctness of the four elements is automatic: non-commuting elements are
     distinct, so `no_four_clique` needs only the six non-commutation edges.

  Main results (all axiom-free — `#print axioms` = propext/Classical.choice/Quot.sound):

  * `no_four_clique`                   : the 3-commuting property forbids four
                                         pairwise non-commuting elements.
  * `centralizer_abelian_of_three`     : in a group with the 3-commuting property,
                                         the centralizer of either member of a
                                         non-commuting pair is abelian.
  * `exists_three_abelian_cover`       : **every** group (finite or not) with the
                                         3-commuting property is covered by 3
                                         abelian subgroups.
  * `coversWithAbelian_three_three`    : `CoversWithAbelian 3 3` — the covering
                                         set of `h(3)` is inhabited by `3`.
  * `coversWithAbelian_three_nonempty` : `h(3)` is well-defined (discharges the
                                         `hne` hypothesis of the `Three.lean`
                                         lower-bound results).
  * `abelianCoverNumber_le_three`      : `h(3) ≤ 3`.
  * `abelianCoverNumber_three`         : **`h(3) = 3`** (unconditional).
  * `abelianCoverNumber_two_lt_three_unconditional` : `h(2) < h(3)` — the
                                         ladder's first strict jump past `1`,
                                         now unconditional: `0, 1, 1, 3, …`.
  * `abelianCoverNumber_le_three_of_le` : `h(n) ≤ 3` for all `n ≤ 3`.

  Pyber's exponential bounds and the open exact growth base (Erdős #117 proper)
  are untouched.

  0 axioms, 0 sorries.
-/

import Mathlib
import Proofs.Erdos117Problem
import Proofs.Erdos117WIP01
import Proofs.Erdos117WIP01Mono
import Proofs.Erdos117WIP01Cover
import Proofs.Erdos117WIP01Two
import Proofs.Erdos117WIP01Three

/- The universe of the ambient groups (see `Erdos117WIP01Mono.lean`):
   `CoversWithAbelian`/`abelianCoverNumber` are universe-polymorphic, so every
   occurrence below is pinned to the same `u`.  The group-theoretic lemmas of
   sections 1–3 are universe-agnostic. -/
universe u

/- ## 1. Commutation kit

Seven cancellation micro-lemmas.  Everything below is pure `mul_assoc` +
`mul_left_cancel`/`mul_right_cancel` bookkeeping, packaged so each clique edge
in section 3 is a one-liner. -/

section CommKit

variable {G : Type*} [Group G]

/-- An element commuting with `x` and `y` commutes with `x * y`. -/
theorem comm_mul_of_comm {b x y : G} (hbx : b * x = x * b) (hby : b * y = y * b) :
    b * (x * y) = (x * y) * b := by
  calc b * (x * y) = (b * x) * y := (mul_assoc b x y).symm
    _ = (x * b) * y := by rw [hbx]
    _ = x * (b * y) := mul_assoc x b y
    _ = x * (y * b) := by rw [hby]
    _ = (x * y) * b := (mul_assoc x y b).symm

/-- If `b` commutes with `u`, and `a * u` commutes with `b`, then `a` commutes
    with `b` (cancel `u` on the right). -/
theorem comm_ab_of_comm_mul {a b u : G} (hbu : b * u = u * b)
    (h : (a * u) * b = b * (a * u)) : a * b = b * a := by
  have h1 : (a * b) * u = (b * a) * u := by
    calc (a * b) * u = a * (b * u) := mul_assoc a b u
      _ = a * (u * b) := by rw [hbu]
      _ = (a * u) * b := (mul_assoc a u b).symm
      _ = b * (a * u) := h
      _ = (b * a) * u := (mul_assoc b a u).symm
  exact mul_right_cancel h1

/-- Left-multiplication by a common commuting element reflects commutation:
    `(a*x)*(a*y) = a*(a*(x*y))` when `a` commutes with `x`. -/
theorem mul_mul_eq_of_comm {a x : G} (hax : a * x = x * a) (y : G) :
    (a * x) * (a * y) = a * (a * (x * y)) := by
  calc (a * x) * (a * y) = a * (x * (a * y)) := mul_assoc a x (a * y)
    _ = a * ((x * a) * y) := by rw [← mul_assoc x a y]
    _ = a * ((a * x) * y) := by rw [← hax]
    _ = a * (a * (x * y)) := by rw [mul_assoc a x y]

/-- If `a` commutes with `x` and `y`, and `a*x` commutes with `a*y`, then `x`
    commutes with `y` (cancel `a` twice on the left). -/
theorem comm_of_mul_mul {a x y : G} (hax : a * x = x * a) (hay : a * y = y * a)
    (h : (a * x) * (a * y) = (a * y) * (a * x)) : x * y = y * x := by
  have h1 : a * (a * (x * y)) = a * (a * (y * x)) := by
    rw [← mul_mul_eq_of_comm hax y, ← mul_mul_eq_of_comm hay x]
    exact h
  exact mul_left_cancel (mul_left_cancel h1)

/-- `x` commutes with `x * y` only if `x` commutes with `y`. -/
theorem comm_of_self_mul_left {x y : G} (h : x * (x * y) = (x * y) * x) :
    x * y = y * x :=
  mul_left_cancel (h.trans (mul_assoc x y x))

/-- `y` commutes with `x * y` only if `x` commutes with `y`. -/
theorem comm_of_self_mul_right {x y : G} (h : y * (x * y) = (x * y) * y) :
    x * y = y * x :=
  (mul_right_cancel ((mul_assoc y x y).trans h)).symm

/-- If `a` commutes with `v`, and `a*u` commutes with `v`, then `u` commutes
    with `v` (cancel `a` on the left). -/
theorem comm_of_mul_left_right {a u v : G} (hav : a * v = v * a)
    (h : (a * u) * v = v * (a * u)) : u * v = v * u := by
  have h1 : a * (u * v) = a * (v * u) := by
    calc a * (u * v) = (a * u) * v := (mul_assoc a u v).symm
      _ = v * (a * u) := h
      _ = (v * a) * u := (mul_assoc v a u).symm
      _ = (a * v) * u := by rw [← hav]
      _ = a * (v * u) := mul_assoc a v u
  exact mul_left_cancel h1

/-- If `a` commutes with `u`, and `u` commutes with `a*x`, then `u` commutes
    with `x` (cancel `a` on the left). -/
theorem comm_of_left_mul {a u x : G} (hau : a * u = u * a)
    (h : u * (a * x) = (a * x) * u) : u * x = x * u := by
  have h1 : a * (u * x) = a * (x * u) := by
    calc a * (u * x) = (a * u) * x := (mul_assoc a u x).symm
      _ = (u * a) * x := by rw [hau]
      _ = u * (a * x) := mul_assoc u a x
      _ = (a * x) * u := h
      _ = a * (x * u) := mul_assoc a x u
  exact mul_left_cancel h1

/-- If `b` commutes with `u` and with `u * v`, then `b` commutes with `v`
    (cancel `u` on the left). -/
theorem comm_right_of_comm_mul {b u v : G} (hbu : b * u = u * b)
    (h : b * (u * v) = (u * v) * b) : b * v = v * b := by
  have h1 : u * (b * v) = u * (v * b) := by
    calc u * (b * v) = (u * b) * v := (mul_assoc u b v).symm
      _ = (b * u) * v := by rw [← hbu]
      _ = b * (u * v) := mul_assoc b u v
      _ = (u * v) * b := h
      _ = u * (v * b) := mul_assoc u v b
  exact mul_left_cancel h1

end CommKit

/- ## 2. The 3-commuting property forbids 4-cliques -/

section NoFourClique

variable {G : Type*} [Group G]

/-- **No four pairwise non-commuting elements** exist in a group with the
    3-commuting property.  Distinctness is automatic (an element commutes with
    itself), so only the six non-commutation edges are required.  The 4-subset
    `{w, x, y, z}` then violates the defining property. -/
theorem no_four_clique (hprop : HasNCommutingProperty G 3) {w x y z : G}
    (cwx : w * x ≠ x * w) (cwy : w * y ≠ y * w) (cwz : w * z ≠ z * w)
    (cxy : x * y ≠ y * x) (cxz : x * z ≠ z * x) (cyz : y * z ≠ z * y) :
    False := by
  classical
  have hwx : w ≠ x := fun h => cwx (by rw [h])
  have hwy : w ≠ y := fun h => cwy (by rw [h])
  have hwz : w ≠ z := fun h => cwz (by rw [h])
  have hxy : x ≠ y := fun h => cxy (by rw [h])
  have hxz : x ≠ z := fun h => cxz (by rw [h])
  have hyz : y ≠ z := fun h => cyz (by rw [h])
  have hcard : ({w, x, y, z} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hwx, hwy, hwz]),
        Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz]),
        Finset.card_singleton]
  obtain ⟨p, q, hp, hq, hpq, hcomm⟩ :=
    hprop {w, x, y, z} (by rw [hcard]; norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    first
      | exact hpq rfl
      | exact cwx hcomm | exact cwy hcomm | exact cwz hcomm
      | exact cxy hcomm | exact cxz hcomm | exact cyz hcomm
      | exact cwx hcomm.symm | exact cwy hcomm.symm | exact cwz hcomm.symm
      | exact cxy hcomm.symm | exact cxz hcomm.symm | exact cyz hcomm.symm

end NoFourClique

/- ## 3. Centralizers of non-commuting elements are abelian -/

section CentralizerAbelian

variable {G : Type*} [Group G]

/-- Case `b~u`, `b~v`: the 4-set `{a*u, a*v, b, a*(u*v)}` is pairwise
    non-commuting. -/
private theorem centralizer_case_both (hprop : HasNCommutingProperty G 3)
    {a b u v : G} (hab : a * b ≠ b * a)
    (hau : a * u = u * a) (hav : a * v = v * a) (huv : u * v ≠ v * u)
    (hbu : b * u = u * b) (hbv : b * v = v * b) : False := by
  have hauv : a * (u * v) = (u * v) * a := comm_mul_of_comm hau hav
  have hbuv : b * (u * v) = (u * v) * b := comm_mul_of_comm hbu hbv
  refine no_four_clique hprop
    (w := a * u) (x := a * v) (y := b) (z := a * (u * v)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun h => huv (comm_of_mul_mul hau hav h)
  · exact fun h => hab (comm_ab_of_comm_mul hbu h)
  · exact fun h => huv (comm_of_self_mul_left (comm_of_mul_mul hau hauv h))
  · exact fun h => hab (comm_ab_of_comm_mul hbv h)
  · exact fun h => huv (comm_of_self_mul_right (comm_of_mul_mul hav hauv h))
  · exact fun h => hab (comm_ab_of_comm_mul hbuv h.symm)

/-- Case `b~u`, `¬ b~v`: the 4-set `{a*u, b, v, u*v}` is pairwise
    non-commuting. -/
private theorem centralizer_case_left (hprop : HasNCommutingProperty G 3)
    {a b u v : G} (hab : a * b ≠ b * a)
    (hau : a * u = u * a) (hav : a * v = v * a) (huv : u * v ≠ v * u)
    (hbu : b * u = u * b) (hbv : b * v ≠ v * b) : False := by
  have hauv : a * (u * v) = (u * v) * a := comm_mul_of_comm hau hav
  refine no_four_clique hprop
    (w := a * u) (x := b) (y := v) (z := u * v) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun h => hab (comm_ab_of_comm_mul hbu h)
  · exact fun h => huv (comm_of_mul_left_right hav h)
  · exact fun h => huv (comm_of_self_mul_left (comm_of_mul_left_right hauv h))
  · exact hbv
  · exact fun h => hbv (comm_right_of_comm_mul hbu h)
  · exact fun h => huv (comm_of_self_mul_right h)

/-- Case `¬ b~u`, `¬ b~v`, `b~uv`: the 4-set `{b, u, v, a*(u*v)}` is pairwise
    non-commuting. -/
private theorem centralizer_case_product (hprop : HasNCommutingProperty G 3)
    {a b u v : G} (hab : a * b ≠ b * a)
    (hau : a * u = u * a) (hav : a * v = v * a) (huv : u * v ≠ v * u)
    (hbu : b * u ≠ u * b) (hbv : b * v ≠ v * b)
    (hbuv : b * (u * v) = (u * v) * b) : False := by
  refine no_four_clique hprop
    (w := b) (x := u) (y := v) (z := a * (u * v)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact hbu
  · exact hbv
  · exact fun h => hab (comm_ab_of_comm_mul hbuv h.symm)
  · exact huv
  · exact fun h => huv (comm_of_self_mul_left (comm_of_left_mul hau h))
  · exact fun h => huv (comm_of_self_mul_right (comm_of_left_mul hav h))

/-- Case `¬ b~u`, `¬ b~v`, `¬ b~uv`: the 4-set `{b, u, v, u*v}` is pairwise
    non-commuting. -/
private theorem centralizer_case_none (hprop : HasNCommutingProperty G 3)
    {b u v : G} (huv : u * v ≠ v * u)
    (hbu : b * u ≠ u * b) (hbv : b * v ≠ v * b)
    (hbuv : b * (u * v) ≠ (u * v) * b) : False := by
  refine no_four_clique hprop
    (w := b) (x := u) (y := v) (z := u * v) ?_ ?_ ?_ ?_ ?_ ?_
  · exact hbu
  · exact hbv
  · exact hbuv
  · exact huv
  · exact fun h => huv (comm_of_self_mul_left h)
  · exact fun h => huv (comm_of_self_mul_right h)

/-- **Centralizers of non-commuting elements are abelian** in a group with the
    3-commuting property.  If `u, v ∈ C(a)` failed to commute, then splitting on
    which of `u`, `v`, `u*v` the witness `b` (with `a*b ≠ b*a`) commutes with
    yields four pairwise non-commuting elements in every case — impossible. -/
theorem centralizer_abelian_of_three (hprop : HasNCommutingProperty G 3)
    {a b : G} (hab : a * b ≠ b * a) :
    IsAbelianSubgroup G (Subgroup.centralizer {a}) := by
  intro u v hu hv
  by_contra huv
  have hau : a * u = u * a := (Subgroup.mem_centralizer_singleton_iff.mp hu).symm
  have hav : a * v = v * a := (Subgroup.mem_centralizer_singleton_iff.mp hv).symm
  by_cases hbu : b * u = u * b
  · by_cases hbv : b * v = v * b
    · exact centralizer_case_both hprop hab hau hav huv hbu hbv
    · exact centralizer_case_left hprop hab hau hav huv hbu hbv
  · by_cases hbv : b * v = v * b
    · -- symmetric to `centralizer_case_left` with the roles of `u`, `v` swapped
      exact centralizer_case_left hprop hab hav hau (fun h => huv h.symm) hbv hbu
    · by_cases hbuv : b * (u * v) = (u * v) * b
      · exact centralizer_case_product hprop hab hau hav huv hbu hbv hbuv
      · exact centralizer_case_none hprop huv hbu hbv hbuv

end CentralizerAbelian

/- ## 4. Three abelian subgroups cover -/

section Cover

variable {G : Type*} [Group G]

/-- **The uniform 3-cover.**  Every group with the 3-commuting property — finite
    or not — is covered by three abelian subgroups.  Abelian case: `⊤` three
    times.  Non-abelian case with `a*b ≠ b*a`: the centralizers
    `C(a), C(b), C(a*b)` are abelian (`centralizer_abelian_of_three`), and they
    cover because an element `g` commuting with none of `a`, `b`, `a*b` would
    complete `{a, b, a*b}` to four pairwise non-commuting elements. -/
theorem exists_three_abelian_cover (hprop : HasNCommutingProperty G 3) :
    ∃ H : Fin 3 → Subgroup G,
      (∀ i, IsAbelianSubgroup G (H i)) ∧ ∀ g : G, ∃ i, g ∈ H i := by
  by_cases habel : ∀ x y : G, x * y = y * x
  · exact ⟨fun _ => ⊤, fun _ x y _ _ => habel x y, fun g => ⟨0, trivial⟩⟩
  · obtain ⟨a, ha⟩ := not_forall.mp habel
    obtain ⟨b, hab⟩ := not_forall.mp ha
    have hab' : b * a ≠ a * b := fun h => hab h.symm
    have haab : a * (a * b) ≠ (a * b) * a := fun h => hab (comm_of_self_mul_left h)
    have hbab : b * (a * b) ≠ (a * b) * b := fun h => hab (comm_of_self_mul_right h)
    refine ⟨![Subgroup.centralizer {a}, Subgroup.centralizer {b},
        Subgroup.centralizer {a * b}], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact centralizer_abelian_of_three hprop hab
      · exact centralizer_abelian_of_three hprop hab'
      · exact centralizer_abelian_of_three hprop (fun h => haab h.symm)
    · intro g
      by_cases hga : g * a = a * g
      · exact ⟨0, show g ∈ Subgroup.centralizer {a} from
          Subgroup.mem_centralizer_singleton_iff.mpr hga⟩
      · by_cases hgb : g * b = b * g
        · exact ⟨1, show g ∈ Subgroup.centralizer {b} from
            Subgroup.mem_centralizer_singleton_iff.mpr hgb⟩
        · by_cases hgab : g * (a * b) = (a * b) * g
          · exact ⟨2, show g ∈ Subgroup.centralizer {a * b} from
              Subgroup.mem_centralizer_singleton_iff.mpr hgab⟩
          · exact (no_four_clique hprop hab haab (fun h => hga h.symm)
              hbab (fun h => hgb h.symm) (fun h => hgab h.symm)).elim

end Cover

/- ## 5. h(3) = 3 -/

/-- **`CoversWithAbelian 3 3`**: a budget of three abelian subgroups covers
    every finite group with the 3-commuting property — in every universe. -/
theorem coversWithAbelian_three_three : CoversWithAbelian.{u} 3 3 := by
  intro G _ _ hprop
  exact exists_three_abelian_cover hprop

/-- **`h(3)` is well-defined**: the covering set is nonempty.  This discharges
    the `hne` hypothesis carried by every `h(3)` lower-bound statement in
    `Erdos117WIP01Three.lean` — previously assessed there as requiring
    classification-strength input. -/
theorem coversWithAbelian_three_nonempty : ∃ k, CoversWithAbelian.{u} k 3 :=
  ⟨3, coversWithAbelian_three_three⟩

/-- **`h(3) ≤ 3`**: the upper half of the exact value. -/
theorem abelianCoverNumber_le_three : abelianCoverNumber.{u} 3 ≤ 3 := by
  rw [abelianCoverNumber_eq_sInf]
  exact Nat.sInf_le coversWithAbelian_three_three

/-- **`h(3) = 3`** — the first nontrivial exact value on the Erdős #117 ladder,
    unconditional.  Lower bound: `Q₈` (`three_le_abelianCoverNumber_three`, its
    nonemptiness hypothesis now discharged).  Upper bound: the uniform 3-cover
    by centralizers.  The known ladder is now exactly `0, 1, 1, 3, …`. -/
theorem abelianCoverNumber_three : abelianCoverNumber.{u} 3 = 3 :=
  le_antisymm abelianCoverNumber_le_three
    (three_le_abelianCoverNumber_three coversWithAbelian_three_nonempty)

/-- **`h(2) < h(3)`, unconditional** — the ladder's first strict jump past `1`,
    with the well-definedness hypothesis of the previous conditional version
    (`abelianCoverNumber_two_lt_three`) discharged. -/
theorem abelianCoverNumber_two_lt_three_unconditional :
    abelianCoverNumber.{u} 2 < abelianCoverNumber.{u} 3 := by
  rw [abelianCoverNumber_two, abelianCoverNumber_three]
  norm_num

/-- **`h(n) ≤ 3` for all `n ≤ 3`** — monotonicity is now usable at `m = 3`
    because well-definedness there is proved. -/
theorem abelianCoverNumber_le_three_of_le {n : ℕ} (hn : n ≤ 3) :
    abelianCoverNumber.{u} n ≤ 3 :=
  (abelianCoverNumber_mono hn coversWithAbelian_three_nonempty).trans_eq
    abelianCoverNumber_three

/- ## Axiom audit -/

#print axioms coversWithAbelian_three_three
#print axioms abelianCoverNumber_three
#print axioms abelianCoverNumber_two_lt_three_unconditional
