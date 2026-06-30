import Mathlib

/-
# Furstenberg's topological proof of the infinitude of primes

In 1955 Hillel Furstenberg gave a strikingly short topological proof that there
are infinitely many primes.  Equip `ℤ` with the **evenly spaced integer
topology**: a set `U` is open when, around every point `x ∈ U`, some full
two-sided arithmetic progression `x + dℤ` (`d > 0`) is contained in `U`.
Equivalently, the residue classes `R a d = {y | d ∣ (y − a)}` form a basis.

Two observations drive the proof:

* every nonempty open set is **infinite** (it contains an entire arithmetic
  progression), and
* each residue class `R a d` (`d > 0`) is **clopen**: it is open by definition,
  and its complement is open because being *outside* a residue class is also a
  congruence condition stable under shifting by multiples of `d`.

Now suppose there were only finitely many primes.  The set
`A = ⋃_{p prime} R 0 p` of integers admitting a prime factor would then be a
**finite union of closed sets, hence closed**, so its complement
`Aᶜ = {x | x.natAbs = 1} = {−1, 1}` would be **open**.  But `{−1, 1}` is a
nonempty *finite* open set — impossible, since nonempty opens are infinite.
Contradiction; therefore the primes are infinite.

## What is formalized

To avoid clashing with the standard `TopologicalSpace ℤ` instance, we work with
the open-set predicate `IsOpenAP` directly rather than registering a topology.
This is purely cosmetic: `IsOpenAP` satisfies the three topology axioms
(`isOpenAP_univ`, `isOpenAP_sInter` for finite intersections, `isOpenAP_sUnion`),
so it *is* a topology in the usual sense; we simply never need the typeclass.

* `IsOpenAP`, `IsClosedAP` — the topology.
* `isOpenAP_residue`, `isClosedAP_residue` — residue classes are clopen.
* `IsOpenAP.infinite_of_nonempty` — nonempty opens are infinite.
* `isClosedAP_biUnion` — finite unions of closed sets are closed.
* `infinitude_of_primes` — the topological proof: `{p : ℕ | p.Prime}.Infinite`.

The argument is genuinely self-contained: it does **not** invoke Mathlib's
`Nat.infinite_setOf_prime` (Euclid's theorem).  The only number-theoretic input
is `Nat.exists_prime_and_dvd` (every `n ≠ 1` has a prime factor), which is the
existence-of-prime-factors fact common to *all* proofs of infinitude.

No axioms, no `native_decide`, no sorries.
-/

namespace InfinitudePrimesOQ01

open Set

/-- The **evenly spaced integer topology** on `ℤ`, given by its open sets:
`U` is open when every point of `U` is surrounded by a full two-sided arithmetic
progression `x + dℤ` lying inside `U`. -/
def IsOpenAP (U : Set ℤ) : Prop :=
  ∀ x ∈ U, ∃ d : ℤ, 0 < d ∧ ∀ y : ℤ, d ∣ (y - x) → y ∈ U

/-- A set is **closed** when its complement is open. -/
def IsClosedAP (C : Set ℤ) : Prop := IsOpenAP Cᶜ

/-- The whole space is open. -/
theorem isOpenAP_univ : IsOpenAP (univ : Set ℤ) := by
  intro x _; exact ⟨1, one_pos, fun y _ => mem_univ y⟩

/-- The empty set is open (vacuously). -/
theorem isOpenAP_empty : IsOpenAP (∅ : Set ℤ) := by
  intro x hx; exact absurd hx (Set.notMem_empty x)

/-- Arbitrary unions of open sets are open. -/
theorem isOpenAP_sUnion {𝒮 : Set (Set ℤ)} (h : ∀ U ∈ 𝒮, IsOpenAP U) :
    IsOpenAP (⋃₀ 𝒮) := by
  rintro x ⟨U, hU𝒮, hxU⟩
  obtain ⟨d, hd, hsub⟩ := h U hU𝒮 x hxU
  exact ⟨d, hd, fun y hy => ⟨U, hU𝒮, hsub y hy⟩⟩

/-- Binary intersections of open sets are open: combine the two progression
spacings multiplicatively. -/
theorem isOpenAP_inter {U V : Set ℤ} (hU : IsOpenAP U) (hV : IsOpenAP V) :
    IsOpenAP (U ∩ V) := by
  rintro x ⟨hxU, hxV⟩
  obtain ⟨d₁, hd₁, h₁⟩ := hU x hxU
  obtain ⟨d₂, hd₂, h₂⟩ := hV x hxV
  refine ⟨d₁ * d₂, mul_pos hd₁ hd₂, fun y hy => ?_⟩
  exact ⟨h₁ y (dvd_trans (Dvd.intro d₂ rfl) hy),
         h₂ y (dvd_trans (Dvd.intro_left d₁ rfl) hy)⟩

/-- A **nonempty** open set is infinite: it contains a whole arithmetic
progression `x + dℤ`, which is an infinite subset. -/
theorem IsOpenAP.infinite_of_nonempty {U : Set ℤ} (hU : IsOpenAP U)
    (hne : U.Nonempty) : U.Infinite := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨d, hd, hsub⟩ := hU x hx
  -- The injection `n ↦ x + n * d` lands inside `U`.
  have hmaps : range (fun n : ℤ => x + n * d) ⊆ U := by
    rintro y ⟨n, rfl⟩
    exact hsub _ ⟨n, by ring⟩
  have hinj : Function.Injective (fun n : ℤ => x + n * d) := by
    intro a b hab
    have : a * d = b * d := by simpa using hab
    exact mul_right_cancel₀ (ne_of_gt hd) this
  exact (infinite_range_of_injective hinj).mono hmaps

/-- The **residue class** `R a d = {y | d ∣ (y − a)}` — an arithmetic
progression with common difference `d`. -/
def R (a d : ℤ) : Set ℤ := {y : ℤ | d ∣ (y - a)}

/-- For `d > 0` the residue class `R a d` is open. -/
theorem isOpenAP_residue (a : ℤ) {d : ℤ} (hd : 0 < d) : IsOpenAP (R a d) := by
  intro x hx
  refine ⟨d, hd, fun y hy => ?_⟩
  -- `d ∣ (y − x)` and `d ∣ (x − a)` give `d ∣ (y − a)`.
  have : d ∣ ((y - x) + (x - a)) := dvd_add hy hx
  simpa using this

/-- For `d > 0` the residue class `R a d` is closed: its complement is open,
because *not* being congruent to `a` mod `d` is also stable under shifting by
multiples of `d`. -/
theorem isClosedAP_residue (a : ℤ) {d : ℤ} (hd : 0 < d) : IsClosedAP (R a d) := by
  intro x hx
  refine ⟨d, hd, fun y hy => ?_⟩
  -- `x ∉ R a d` means `¬ d ∣ (x − a)`; if `y` were in `R a d` then
  -- `d ∣ (y − a)` and `d ∣ (y − x)` would force `d ∣ (x − a)`.
  simp only [R, mem_compl_iff, mem_setOf_eq] at hx ⊢
  intro hya
  exact hx (by simpa using dvd_sub hya hy)

/-- Binary unions of closed sets are closed. -/
theorem isClosedAP_union {C D : Set ℤ} (hC : IsClosedAP C) (hD : IsClosedAP D) :
    IsClosedAP (C ∪ D) := by
  have : (C ∪ D)ᶜ = Cᶜ ∩ Dᶜ := by simp [compl_union]
  rw [IsClosedAP, this]
  exact isOpenAP_inter hC hD

/-- The empty set is closed. -/
theorem isClosedAP_empty : IsClosedAP (∅ : Set ℤ) := by
  rw [IsClosedAP, compl_empty]; exact isOpenAP_univ

/-- A **finite union** of closed sets is closed. -/
theorem isClosedAP_biUnion {ι : Type*} {s : Finset ι} {C : ι → Set ℤ}
    (hC : ∀ i ∈ s, IsClosedAP (C i)) : IsClosedAP (⋃ i ∈ s, C i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isClosedAP_empty
  | @insert j t hjt ih =>
    have hstep : IsClosedAP (C j ∪ ⋃ i ∈ t, C i) :=
      isClosedAP_union (hC j (Finset.mem_insert_self j t))
        (ih (fun i hi => hC i (Finset.mem_insert_of_mem hi)))
    simpa [Finset.set_biUnion_insert] using hstep

/-- **Furstenberg's theorem.** There are infinitely many primes, proved by the
topological argument: if the prime set were finite, the integers with a prime
factor would form a closed set whose complement `{−1, 1}` would be a nonempty
finite open set — impossible. -/
theorem infinitude_of_primes : {p : ℕ | p.Prime}.Infinite := by
  intro hfin
  -- Work with the finite set of primes as a `Finset ℕ`.
  obtain ⟨P, hP⟩ := hfin.exists_finset
  -- `hP : x ∈ P ↔ x.Prime`
  -- `A` = integers divisible by some prime = integers with `natAbs ≠ 1`.
  set A : Set ℤ := ⋃ p ∈ P, R 0 (p : ℤ) with hA
  -- Each `R 0 p` (p prime, so `p ≥ 2 > 0`) is closed, hence the finite union is.
  have hAclosed : IsClosedAP A := by
    refine isClosedAP_biUnion (fun p hp => ?_)
    have hp2 : 2 ≤ p := (hP p |>.mp hp).two_le
    exact isClosedAP_residue 0 (by exact_mod_cast (lt_of_lt_of_le two_pos hp2))
  -- Identify the complement of `A` with `{x | x.natAbs = 1}`.
  have hcompl : Aᶜ = {x : ℤ | x.natAbs = 1} := by
    ext x
    simp only [hA, mem_compl_iff, mem_iUnion, R, mem_setOf_eq, sub_zero,
      not_exists]
    constructor
    · -- no prime divides `x`  ⟹  `x.natAbs = 1`
      intro hx
      by_contra hne
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
      have hqP : q ∈ P := (hP q).mpr hq
      have : (q : ℤ) ∣ x :=
        Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hqdvd)
      exact (hx q hqP) this
    · -- `x.natAbs = 1` (i.e. `x = ±1`)  ⟹  no prime divides `x`
      intro hx p hpP hpdvd
      have hp2 : 2 ≤ p := (hP p |>.mp hpP).two_le
      have hx1 : x.natAbs = 1 := hx
      have hdvd : p ∣ x.natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr hpdvd
        simpa using this
      rw [hx1] at hdvd
      have := Nat.le_of_dvd one_pos hdvd
      omega
  -- So `Aᶜ` is open (complement of a closed set) and nonempty (`1 ∈ Aᶜ`)…
  have hAcompl_open : IsOpenAP Aᶜ := hAclosed
  have hone : (1 : ℤ) ∈ Aᶜ := by rw [hcompl]; simp
  have hinf : (Aᶜ).Infinite := hAcompl_open.infinite_of_nonempty ⟨1, hone⟩
  -- …yet `Aᶜ = {−1, 1}` is finite.  Contradiction.
  have hfin2 : (Aᶜ).Finite := by
    rw [hcompl]
    have hsub : {x : ℤ | x.natAbs = 1} ⊆ ({1, -1} : Set ℤ) := by
      intro x hx
      rcases Int.natAbs_eq_iff.mp hx with h | h <;> simp [h]
    exact Set.Finite.subset ((Set.finite_singleton (-1 : ℤ)).insert 1) hsub
  exact hinf hfin2

end InfinitudePrimesOQ01
