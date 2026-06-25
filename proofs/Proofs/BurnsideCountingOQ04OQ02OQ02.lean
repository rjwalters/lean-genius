import Mathlib.Tactic
import Proofs.BurnsideCountingOQ04OQ02

/-
# Burnside Counting, OQ-04 → OQ-02 → OQ-02: the reflection half (odd `n`)

The parent file `BurnsideCountingOQ04OQ02OQ01` evaluated the **rotation half** of the dihedral
Burnside sum as the gcd-cycle sum `∑_i 2^{gcd(n,i)}`.  This file evaluates the **reflection
half**

      ∑_{i ∈ ZMod n} |Fix(sr i)|

for **both parities** of `n`, completing the closed form `b(n) = (rotations + reflections)/(2n)`.

## The reflection involution

A reflection `sr i` acts on positions by `p ↦ -i - p` (the parent's `posPerm_sr = subLeft (-i)`),
which is the **involution** `refl i`.  A colouring is fixed by `sr i` exactly when it is constant
on the `refl i`-orbits.  Counting the invariant `2`-colourings of *any* involution `σ` gives

      |{c : α → Fin 2 // c ∘ σ = c}|  =  2 ^ ((|α| + |Fix σ|) / 2)

(`card_invariant_colorings_involutive`): the orbits are fixed points (singletons) and transposed
pairs, so `|α| = |Fix σ| + 2·(pairs)` and the number of orbits is `(|α| + |Fix σ|)/2`.

## Odd `n`

The fixed points of `refl i` are the solutions of `2p = -i`.  For odd `n`, `2` is a unit in
`ZMod n`, so there is exactly **one** fixed point for every `i` (`reflFix_odd`); hence every
reflection fixes `2^{(n+1)/2}` colourings and

      ∑_{i ∈ ZMod n} |Fix(sr i)|  =  n · 2^{(n+1)/2}            (`reflection_sum_odd`).

For **even** `n`, doubling has the two-element kernel `{0, n/2}`, so `reflFix i ∈ {0, 2}`; since
`∑_i reflFix i = n` (each position is the unique fixed point of one axis), exactly `n/2` of the
reflections carry a fixed pair, giving

      ∑_{i ∈ ZMod n} |Fix(sr i)|  =  3 · (n/2) · 2^{n/2}            (`reflection_sum_even`).

The general per-reflection count `card_fixedBy_reflection` below applies uniformly and is the
single ingredient specialised by parity (`reflFix_odd` / `reflFix_even`).

`#print axioms` on the headlines confirms only `propext, Classical.choice, Quot.sound`.
-/

namespace BurnsideCountingOQ04OQ02OQ02

open Finset MulAction BurnsideCountingOQ04OQ02

variable {n : ℕ}

/-! ### Unfolding the reflection action -/

/-- The reflection `sr i` acts on a colouring by `(sr i • c) p = c (-i - p)`.  Reads off the
parent's `smul_apply` at `g = sr i`, where `ρ (sr i) = Equiv.subLeft (-i)`, an involution. -/
theorem reflection_smul_apply (i : ZMod n) (c : Coloring n) (p : ZMod n) :
    ((DihedralGroup.sr i : DihedralGroup n) • c) p = c (-i - p) := by
  rw [smul_apply]
  congr 1
  have hρ : (ρ (DihedralGroup.sr i) : Equiv.Perm (Pos n)) = Equiv.subLeft (-i) := rfl
  rw [hρ, Equiv.symm_apply_eq]
  show p = -i - (-i - p)
  ring

/-- A colouring is fixed by the reflection `sr i` iff it is symmetric about the axis:
`c (-i - p) = c p`. -/
theorem fixed_iff_symm (i : ZMod n) (c : Coloring n) :
    (DihedralGroup.sr i : DihedralGroup n) • c = c ↔ ∀ p, c (-i - p) = c p := by
  constructor
  · intro h p
    have := congrFun h p
    rwa [reflection_smul_apply] at this
  · intro h
    funext p
    rw [reflection_smul_apply]
    exact h p

/-! ### The reflection involution on positions -/

/-- The position involution induced by the reflection `sr i`: `refl i p = -i - p`. -/
def refl (i : ZMod n) : ZMod n → ZMod n := fun p => -i - p

/-- `refl i` is an involution: `-i - (-i - p) = p`. -/
theorem refl_involutive (i : ZMod n) : Function.Involutive (refl i) := by
  intro p
  show -i - (-i - p) = p
  ring

/-! ### Counting invariant 2-colourings of an arbitrary involution

The orbits of an involution `σ` are singletons (fixed points) and transposed pairs.  We index
`α` by `ℕ` and pick the smaller-indexed element of each orbit as its representative; an invariant
colouring is freely determined by its values on the representatives.  The representatives are
`{a : f a ≤ f (σ a)}`, whose size is `(|α| + |Fix σ|)/2` because the non-fixed points split
evenly (via `σ`) between `f a < f (σ a)` and `f (σ a) < f a`. -/

/-- **Invariant `2`-colourings of an involution.**  For an involution `σ` on a finite type,
the number of `2`-colourings constant on `σ`-orbits is `2^{(|α| + |Fix σ|)/2}`. -/
theorem card_invariant_colorings_involutive {α : Type*} [Fintype α] [DecidableEq α]
    (σ : α → α) (hσ : Function.Involutive σ) :
    Fintype.card {c : α → Fin 2 // ∀ a, c (σ a) = c a}
      = 2 ^ ((Fintype.card α + (univ.filter (fun a => σ a = a)).card) / 2) := by
  classical
  -- injective index function to ℕ
  let f : α → ℕ := fun a => (Fintype.equivFin α a).val
  have hf_inj : Function.Injective f := fun a b h => (Fintype.equivFin α).injective (Fin.ext h)
  -- the representative of each orbit (smaller index)
  let rep : α → α := fun a => if f a ≤ f (σ a) then a else σ a
  have hrep_def : ∀ a, rep a = if f a ≤ f (σ a) then a else σ a := fun _ => rfl
  set R : Finset α := univ.filter (fun a => f a ≤ f (σ a)) with hR
  have hrepR : ∀ a, rep a ∈ R := by
    intro a
    rw [hR, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    simp only [hrep_def]
    by_cases h : f a ≤ f (σ a)
    · rw [if_pos h]; exact h
    · rw [if_neg h, hσ a]; omega
  have hrep_symm : ∀ a, rep (σ a) = rep a := by
    intro a
    simp only [hrep_def, hσ a]
    rcases lt_trichotomy (f a) (f (σ a)) with h | h | h
    · rw [if_neg (show ¬ f (σ a) ≤ f a by omega), if_pos h.le]
    · have heq : a = σ a := hf_inj h
      rw [if_pos (le_of_eq h.symm), if_pos (le_of_eq h)]; exact heq.symm
    · rw [if_pos h.le, if_neg (show ¬ f a ≤ f (σ a) by omega)]
  have hrep_mem : ∀ a, a ∈ R → rep a = a := by
    intro a ha
    rw [hR, mem_filter] at ha
    rw [hrep_def, if_pos ha.2]
  have hrep_color : ∀ (c : {c : α → Fin 2 // ∀ a, c (σ a) = c a}) a, c.1 (rep a) = c.1 a := by
    intro c a
    rw [hrep_def]
    by_cases h : f a ≤ f (σ a)
    · rw [if_pos h]
    · rw [if_neg h]; exact c.2 a
  -- the bijection: invariant colourings ≃ functions on representatives
  have ecard : Fintype.card {c : α → Fin 2 // ∀ a, c (σ a) = c a}
      = Fintype.card (R → Fin 2) := by
    apply Fintype.card_congr
    refine
    { toFun := fun c r => c.1 r.1
      invFun := fun g => ⟨fun a => g ⟨rep a, hrepR a⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · intro a
      show g ⟨rep (σ a), hrepR (σ a)⟩ = g ⟨rep a, hrepR a⟩
      congr 1
      exact Subtype.ext (hrep_symm a)
    · intro c
      apply Subtype.ext
      funext a
      exact hrep_color c a
    · intro g
      funext r
      show g ⟨rep r.1, hrepR r.1⟩ = g r
      congr 1
      exact Subtype.ext (hrep_mem r.1 r.2)
  rw [ecard, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  congr 1
  -- count the representatives
  set Fix : Finset α := univ.filter (fun a => σ a = a) with hFix
  set L : Finset α := univ.filter (fun a => f a < f (σ a)) with hL
  set G : Finset α := univ.filter (fun a => f (σ a) < f a) with hG
  -- R = L ∪ Fix (disjoint)
  have hRLF : R.card = L.card + Fix.card := by
    have hdisj : Disjoint L Fix := by
      rw [hL, hFix, Finset.disjoint_filter]
      intro a _ h1 h2
      rw [h2] at h1
      exact absurd h1 (lt_irrefl _)
    have hpred : R = L ∪ Fix := by
      rw [hR, hL, hFix, ← Finset.filter_or]
      apply Finset.filter_congr
      intro a _
      constructor
      · intro h
        rcases lt_or_eq_of_le h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (hf_inj h').symm
      · rintro (h | h)
        · exact h.le
        · exact le_of_eq (congrArg f h).symm
    rw [hpred, Finset.card_union_of_disjoint hdisj]
  -- |R| + |G| = |α|
  have hRG : R.card + G.card = Fintype.card α := by
    have hGeq : G = univ.filter (fun a => ¬ f a ≤ f (σ a)) := by
      rw [hG]
      apply Finset.filter_congr
      intro a _
      exact not_le.symm
    rw [hR, hGeq, filter_card_add_filter_neg_card_eq_card, Finset.card_univ]
  -- |L| = |G| via σ
  have hLG : L.card = G.card := by
    rw [hL, hG]
    apply Finset.card_nbij' σ σ
    · intro a ha
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at ha ⊢
      rw [hσ a]; exact ha
    · intro a ha
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at ha ⊢
      rw [hσ a]; exact ha
    · intro a _; exact hσ a
    · intro a _; exact hσ a
  omega

/-! ### The per-reflection fixed-colouring count -/

/-- The number of positions fixed by `refl i`, i.e. solutions of `2p = -i`. -/
def reflFix [NeZero n] (i : ZMod n) : ℕ := (univ.filter (fun p : ZMod n => refl i p = p)).card

/-- **Per-reflection count.**  The number of colourings fixed by `sr i` is `2^{(n + reflFix i)/2}`:
they are the `2`-colourings invariant under the involution `refl i`. -/
theorem card_fixedBy_reflection [NeZero n] (i : ZMod n) :
    Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i))
      = 2 ^ ((n + reflFix i) / 2) := by
  classical
  have e : ↥(fixedBy (Coloring n) (DihedralGroup.sr i))
      ≃ {c : Coloring n // ∀ p, c (refl i p) = c p} :=
    Equiv.subtypeEquivRight (fun c => by rw [mem_fixedBy]; exact fixed_iff_symm i c)
  rw [Fintype.card_congr e, card_invariant_colorings_involutive (refl i) (refl_involutive i),
    ZMod.card]
  rfl

/-! ### Odd `n`: every reflection fixes `2^{(n+1)/2}` colourings -/

/-- For odd `n`, the involution `refl i` has a **unique** fixed point (`2` is a unit in `ZMod n`),
so `reflFix i = 1`. -/
theorem reflFix_odd [NeZero n] (hn : Odd n) (i : ZMod n) : reflFix i = 1 := by
  -- `2` is a unit in `ZMod n` for odd `n`
  have h2unit : IsUnit (2 : ZMod n) := by
    have h2 : (2 : ZMod n) = ((2 : ℕ) : ZMod n) := by norm_cast
    rw [h2, ZMod.isUnit_iff_coprime]
    exact Nat.coprime_two_left.mpr hn
  obtain ⟨u, hu⟩ := h2unit
  -- multiplication by the unit `2` is a bijection, so `2p = -i` has a unique solution
  have hbij : Function.Bijective (fun p : ZMod n => (2 : ZMod n) * p) := by
    have hb := Units.mulLeft_bijective u
    rwa [hu] at hb
  obtain ⟨p₀, hp₀, huniq⟩ := hbij.existsUnique (-i)
  -- `refl i p = p` is exactly `2p = -i`
  have hcond : ∀ p : ZMod n, refl i p = p ↔ (2 : ZMod n) * p = -i := by
    intro p
    simp only [refl]
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  rw [reflFix, Finset.card_eq_one]
  refine ⟨p₀, ?_⟩
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_singleton, hcond]
  constructor
  · intro h; exact huniq p h
  · intro h; subst h; exact hp₀

/-- **The reflection half for odd `n`.**

      ∑_{i ∈ ZMod n} |Fix(sr i)|  =  n · 2^{(n+1)/2}. -/
theorem reflection_sum_odd [NeZero n] (hn : Odd n) :
    ∑ i : ZMod n, Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i))
      = n * 2 ^ ((n + 1) / 2) := by
  have h1 : ∀ i : ZMod n,
      Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i)) = 2 ^ ((n + 1) / 2) := by
    intro i
    rw [card_fixedBy_reflection, reflFix_odd hn i]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul]

/-! ### Even `n`: reflections split by parity

For even `n = 2m` (`m := n/2`), doubling `p ↦ 2p` on `ZMod n` has the two-element kernel
`{0, m}`, so `2p = -i` has either `0` or exactly `2` solutions: `reflFix i ∈ {0, 2}`.  The
*total* `∑_i reflFix i = n` (each position `p` is the unique fixed point of exactly one axis
`i = -2p`), which forces exactly `n/2` of the reflections to be the "even" ones with
`reflFix = 2`.  Hence

      ∑_{i} |Fix(sr i)|  =  (n/2)·2^{n/2+1} + (n/2)·2^{n/2}  =  3·(n/2)·2^{n/2}.
-/

/-- For even `n = 2m`, doubling on `ZMod n` has kernel exactly `{0, (m : ZMod n)}`. -/
theorem two_mul_eq_zero_iff [NeZero n] (hn : Even n) (p : ZMod n) :
    (2 : ZMod n) * p = 0 ↔ p = 0 ∨ p = ((n / 2 : ℕ) : ZMod n) := by
  obtain ⟨m, hm⟩ := hn                       -- n = m + m
  have hn2 : n = 2 * m := by omega
  have hmpos : 0 < m := by
    have := NeZero.pos n; omega
  have hhalf : n / 2 = m := by omega
  constructor
  · intro h
    -- 2 * p = 0  ⇒  n ∣ 2 * p.val  ⇒  m ∣ p.val  ⇒  p.val ∈ {0, m}
    have hp : ((2 * p.val : ℕ) : ZMod n) = 0 := by
      push_cast
      rw [ZMod.natCast_rightInverse p]; exact h
    rw [ZMod.natCast_eq_zero_iff] at hp
    have hdvd : m ∣ p.val := by
      -- `n = 2m` and `n ∣ 2·p.val` give `2·p.val = 2·(m·c)`, so `p.val = m·c`.
      obtain ⟨c, hc⟩ := hp
      refine ⟨c, ?_⟩
      have h2 : 2 * p.val = 2 * (m * c) := by rw [hc, hn2]; ring
      omega
    have hlt : p.val < n := ZMod.val_lt p
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : k < 2 := by
      rw [hk, hn2] at hlt
      by_contra hcon
      push_neg at hcon
      have : 2 * m ≤ m * k := by nlinarith
      omega
    have hinv := ZMod.natCast_rightInverse (n := n) p   -- ↑(p.val) = p
    interval_cases k
    · left
      have h0 : p.val = 0 := by omega
      rw [← hinv, h0, Nat.cast_zero]
    · right
      have h1 : p.val = m := by omega
      rw [← hinv, h1, hhalf]
  · rintro (h | h)
    · rw [h, mul_zero]
    · rw [h, hhalf]
      have : (2 : ZMod n) * (m : ZMod n) = ((2 * m : ℕ) : ZMod n) := by push_cast; ring
      rw [this, ← hn2, ZMod.natCast_self]

/-- For even `n`, the involution `refl i` has either `0` or exactly `2` fixed points: the
solution set of `2p = -i` is empty or a coset of the kernel `{0, n/2}`. -/
theorem reflFix_even [NeZero n] (hn : Even n) (i : ZMod n) :
    reflFix i = 0 ∨ reflFix i = 2 := by
  classical
  rw [reflFix]
  by_cases hne : (univ.filter (fun p : ZMod n => refl i p = p)).Nonempty
  · right
    obtain ⟨p₀, hp₀⟩ := hne
    rw [mem_filter] at hp₀
    have hp₀eq : (2 : ZMod n) * p₀ = -i := by
      have h := hp₀.2; simp only [refl] at h; linear_combination -h
    have hmne : ((n / 2 : ℕ) : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have hpos := NeZero.pos n
      obtain ⟨k, hk⟩ := hn
      have h1 : 0 < n / 2 := by omega
      have h2 : n / 2 < n := by omega
      exact absurd (Nat.le_of_dvd h1 hdvd) (by omega)
    have hm2 : (2 : ZMod n) * ((n / 2 : ℕ) : ZMod n) = 0 :=
      (two_mul_eq_zero_iff hn _).2 (Or.inr rfl)
    have hset : (univ.filter (fun p : ZMod n => refl i p = p))
        = {p₀, p₀ + ((n / 2 : ℕ) : ZMod n)} := by
      ext p
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, refl]
      constructor
      · intro hp
        have h2p : (2 : ZMod n) * (p - p₀) = 0 := by linear_combination -hp - hp₀eq
        rcases (two_mul_eq_zero_iff hn _).1 h2p with h | h
        · left; linear_combination h
        · right; linear_combination h
      · rintro (h | h)
        · subst h; linear_combination -hp₀eq
        · subst h; linear_combination -hp₀eq - hm2
    rw [hset, Finset.card_insert_of_notMem (by
          simp only [mem_singleton]
          intro hc
          exact hmne (by linear_combination -hc)), Finset.card_singleton]
  · left
    rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty]

/-- The total of all fixed-point counts is `n`: each position `p` is the unique fixed point of
the single reflection axis `i = -2p`.  (Holds for every `n`; we use it for even `n`.) -/
theorem reflFix_sum [NeZero n] : ∑ i : ZMod n, reflFix i = n := by
  classical
  have hcard : ∑ i : ZMod n, reflFix i
      = ∑ i : ZMod n, ∑ p : ZMod n, (if refl i p = p then (1 : ℕ) else 0) := by
    simp only [reflFix, Finset.card_filter]
  rw [hcard, Finset.sum_comm]
  have hp : ∀ p : ZMod n, ∑ i : ZMod n, (if refl i p = p then (1 : ℕ) else 0) = 1 := by
    intro p
    have hset : (univ.filter (fun i : ZMod n => refl i p = p)) = {-(2 * p)} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_singleton, refl]
      constructor
      · intro h; linear_combination -h
      · intro h; rw [h]; ring
    rw [← Finset.card_filter, hset, Finset.card_singleton]
  rw [Finset.sum_congr rfl (fun p _ => hp p), Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul, mul_one]

/-- For even `n`, exactly `n/2` of the reflections have a (doubled) fixed pair, because
`∑_i reflFix i = n` and every `reflFix i ∈ {0, 2}`. -/
theorem card_even_reflections [NeZero n] (hn : Even n) :
    (univ.filter (fun i : ZMod n => reflFix i = 2)).card = n / 2 := by
  classical
  have heq : ∑ i : ZMod n, reflFix i
      = ∑ i : ZMod n, (if reflFix i = 2 then (2 : ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    rcases reflFix_even hn i with h | h <;> simp [h]
  have h2 : ∑ i : ZMod n, (if reflFix i = 2 then (2 : ℕ) else 0)
      = 2 * (univ.filter (fun i : ZMod n => reflFix i = 2)).card := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  have hkey : 2 * (univ.filter (fun i : ZMod n => reflFix i = 2)).card = n := by
    rw [← h2, ← heq, reflFix_sum]
  omega

/-- **The reflection half for even `n`.**

      ∑_{i ∈ ZMod n} |Fix(sr i)|  =  3 · (n/2) · 2^{n/2}. -/
theorem reflection_sum_even [NeZero n] (hn : Even n) :
    ∑ i : ZMod n, Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i))
      = 3 * (n / 2) * 2 ^ (n / 2) := by
  classical
  -- Write each term additively so only the *positive* filter `{i : reflFix i = 2}` appears.
  have hterm : ∀ i : ZMod n, Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i))
      = 2 ^ (n / 2) + (if reflFix i = 2 then 2 ^ (n / 2) else 0) := by
    intro i
    rw [card_fixedBy_reflection]
    rcases reflFix_even hn i with h | h
    · rw [h, if_neg (by norm_num)]
      simp                                             -- 2^((n+0)/2) = 2^(n/2) + 0
    · rw [h, if_pos rfl, show (n + 2) / 2 = n / 2 + 1 by omega, pow_succ]
      ring                                             -- 2^(n/2)*2 = 2^(n/2) + 2^(n/2)
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_const,
    ← Finset.sum_filter, Finset.sum_const, Finset.card_univ, ZMod.card,
    card_even_reflections hn, smul_eq_mul, smul_eq_mul]
  -- goal: n * 2^(n/2) + (n/2) * 2^(n/2) = 3 * (n/2) * 2^(n/2)
  obtain ⟨k, hk⟩ := hn
  have hsum : n + n / 2 = 3 * (n / 2) := by omega
  calc n * 2 ^ (n / 2) + n / 2 * 2 ^ (n / 2)
      = (n + n / 2) * 2 ^ (n / 2) := by ring
    _ = 3 * (n / 2) * 2 ^ (n / 2) := by rw [hsum]

end BurnsideCountingOQ04OQ02OQ02

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms BurnsideCountingOQ04OQ02OQ02.card_invariant_colorings_involutive
#print axioms BurnsideCountingOQ04OQ02OQ02.card_fixedBy_reflection
#print axioms BurnsideCountingOQ04OQ02OQ02.reflection_sum_odd
#print axioms BurnsideCountingOQ04OQ02OQ02.reflection_sum_even
