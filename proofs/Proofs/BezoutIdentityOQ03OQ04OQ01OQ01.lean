import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-
# Bézout Identity OQ03-OQ04-OQ01-OQ01:
# Iterated CRT for Multiple Coprime Moduli over Commutative Rings

## Open Question (bezout-identity-oq-03-oq-04-oq-01-oq-01)

Parent open question #1 of `bezout-identity-oq-03-oq-04-oq-01`
("CRT for Commutative Rings via Bézout Coefficients"):

"Can the folding approach for multiple coprime moduli (iterated CRT) be
generalized to commutative rings? The key lemma needed: if IsCoprime m₁ m₂
and IsCoprime (m₁*m₂) m₃, then IsCoprime m₁ (m₂*m₃) — available in Mathlib
as IsCoprime.mul_right."

## Answer

YES. Given a list of (residue, modulus) pairs whose moduli are *pairwise*
coprime in an arbitrary `CommRing R`, the CRT system always has a solution,
and any two solutions agree modulo the product of the moduli.

The construction folds the two-modulus CRT (from the parent file) over the
list. The crux is that a single modulus that is coprime to each modulus in a
list is coprime to their product — proved here by induction from
`IsCoprime.mul_right` (exactly the lemma flagged in the open question).

## Builds On
- BezoutIdentityOQ03OQ04OQ01.lean: the two-modulus `crtRing` over a CommRing.
  The two-modulus construction is reproduced inline so this file is
  self-contained (Mathlib-only imports).
-/

namespace BezoutIdentityOQ03OQ04OQ01OQ01

/-! ## Part 1: Two-modulus CRT (reproduced from the parent, self-contained) -/

/-- The direct Bézout CRT formula over any commutative ring. -/
def crtRing {R : Type*} [CommRing R] (a b s t m n : R) : R :=
  b * s * m + a * t * n

theorem crtRing_mod_m {R : Type*} [CommRing R] (a b s t m n : R)
    (hbez : s * m + t * n = 1) :
    m ∣ (crtRing a b s t m n - a) :=
  ⟨b * s - a * s, by unfold crtRing; linear_combination a * hbez⟩

theorem crtRing_mod_n {R : Type*} [CommRing R] (a b s t m n : R)
    (hbez : s * m + t * n = 1) :
    n ∣ (crtRing a b s t m n - b) :=
  ⟨a * t - b * t, by unfold crtRing; linear_combination b * hbez⟩

/-- Two-modulus existence: coprime `m, n` ⟹ the system `(a,m), (b,n)` is solvable. -/
theorem crtRing_exists {R : Type*} [CommRing R] (a b m n : R)
    (hcop : IsCoprime m n) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) := by
  obtain ⟨s, t, hst⟩ := hcop
  exact ⟨crtRing a b s t m n,
         crtRing_mod_m a b s t m n hst,
         crtRing_mod_n a b s t m n hst⟩

/-! ## Part 2: Coprimality to a product

The lemma named in the open question: an element coprime to every factor is
coprime to the product. Folded from `IsCoprime.mul_right`
(`IsCoprime a b → IsCoprime a c → IsCoprime a (b*c)`) and
`isCoprime_one_right` (`IsCoprime a 1`). -/

/-- If `a` is coprime to every element of a list `l`, then `a` is coprime to
    `l.prod`. This is the iterated form of `IsCoprime.mul_right`. -/
theorem isCoprime_list_prod {R : Type*} [CommRing R] (a : R) :
    ∀ l : List R, (∀ b ∈ l, IsCoprime a b) → IsCoprime a l.prod
  | [], _ => by simp only [List.prod_nil]; exact isCoprime_one_right
  | b :: t, h => by
      rw [List.prod_cons]
      exact (h b (List.mem_cons_self)).mul_right
        (isCoprime_list_prod a t (fun c hc => h c (List.mem_cons_of_mem _ hc)))

/-! ## Part 3: Iterated CRT existence (the folding approach)

We work over a list of `(residue, modulus)` pairs whose moduli are pairwise
coprime, encoded by `List.Pairwise (fun p q => IsCoprime p.2 q.2)`.

The fold: given a solution `x` for the tail with modulus product `M`, the head
modulus `p.2` is coprime to `M` (Part 2), so the two-modulus CRT produces a
`y` congruent to the head residue mod `p.2` and to `x` mod `M`. Since every
tail modulus divides `M`, `y` inherits every tail congruence. -/

/-- **Iterated CRT existence over an arbitrary commutative ring.**
    For pairwise-coprime moduli, the simultaneous congruence system is solvable. -/
theorem crtRing_list_exists {R : Type*} [CommRing R] :
    ∀ l : List (R × R),
      l.Pairwise (fun p q => IsCoprime p.2 q.2) →
      ∃ x : R, ∀ p ∈ l, p.2 ∣ (x - p.1)
  | [], _ => ⟨0, by simp⟩
  | p :: t, hpw => by
      obtain ⟨htp, htail⟩ := List.pairwise_cons.mp hpw
      obtain ⟨x, hx⟩ := crtRing_list_exists t htail
      -- M = product of the tail moduli
      set M := (t.map Prod.snd).prod with hM
      have hcopM : IsCoprime p.2 M := by
        apply isCoprime_list_prod
        intro b hb
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
        exact htp q hq
      obtain ⟨y, hy1, hy2⟩ := crtRing_exists p.1 x p.2 M hcopM
      refine ⟨y, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hqt
      · exact hy1
      · -- q.2 ∣ M ∣ (y - x), and q.2 ∣ (x - q.1), so q.2 ∣ (y - q.1)
        have hdvdM : q.2 ∣ M := by
          rw [hM]; exact List.dvd_prod (List.mem_map.mpr ⟨q, hqt, rfl⟩)
        have h1 : q.2 ∣ (y - x) := hdvdM.trans hy2
        have h2 : q.2 ∣ (x - q.1) := hx q hqt
        have h3 : q.2 ∣ ((y - x) + (x - q.1)) := dvd_add h1 h2
        simpa using h3

/-! ## Part 4: Iterated CRT uniqueness

Any two solutions of the system agree modulo the product of all moduli. The
crux is the dual of Part 2: pairwise-coprime elements each dividing `d` have
their product dividing `d`, folded from `IsCoprime.mul_dvd`. -/

/-- If a list of pairwise-coprime elements each divide `d`, so does their product. -/
theorem prod_dvd_of_pairwise_coprime {R : Type*} [CommRing R] (d : R) :
    ∀ l : List R, l.Pairwise IsCoprime → (∀ b ∈ l, b ∣ d) → l.prod ∣ d
  | [], _, _ => by simpa using one_dvd d
  | b :: t, hpw, hd => by
      obtain ⟨hbt, htail⟩ := List.pairwise_cons.mp hpw
      have hcop : IsCoprime b t.prod :=
        isCoprime_list_prod b t (fun c hc => hbt c hc)
      have ht : t.prod ∣ d :=
        prod_dvd_of_pairwise_coprime d t htail
          (fun c hc => hd c (List.mem_cons_of_mem _ hc))
      have hb : b ∣ d := hd b (List.mem_cons_self)
      rw [List.prod_cons]
      exact hcop.mul_dvd hb ht

/-- **Iterated CRT uniqueness over an arbitrary commutative ring.**
    Two solutions `x, y` of the same pairwise-coprime system agree modulo the
    product of all moduli. -/
theorem crtRing_list_unique {R : Type*} [CommRing R] (l : List (R × R)) (x y : R)
    (hpw : l.Pairwise (fun p q => IsCoprime p.2 q.2))
    (hxy : ∀ p ∈ l, p.2 ∣ (x - y)) :
    (l.map Prod.snd).prod ∣ (x - y) := by
  apply prod_dvd_of_pairwise_coprime
  · exact List.pairwise_map.mpr hpw
  · intro b hb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact hxy q hq

/-! ## Part 5: Worked instance — three pairwise-coprime moduli -/

/-- The iterated theorem specializes to any fixed number of moduli. Here three
    pairwise-coprime moduli in an arbitrary `CommRing`. -/
theorem crtRing_three {R : Type*} [CommRing R]
    (a₁ a₂ a₃ m₁ m₂ m₃ : R)
    (h₁₂ : IsCoprime m₁ m₂) (h₁₃ : IsCoprime m₁ m₃) (h₂₃ : IsCoprime m₂ m₃) :
    ∃ x : R, m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃) := by
  have hpw : [(a₁, m₁), (a₂, m₂), (a₃, m₃)].Pairwise (fun p q => IsCoprime p.2 q.2) := by
    refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
    · intro q hq; fin_cases hq
      · exact h₁₂
      · exact h₁₃
    · intro q hq; fin_cases hq
      · exact h₂₃
    · intro q hq; fin_cases hq
  obtain ⟨x, hx⟩ := crtRing_list_exists _ hpw
  exact ⟨x, hx (a₁, m₁) (by simp), hx (a₂, m₂) (by simp), hx (a₃, m₃) (by simp)⟩

/-! ## Summary -/

/-
## The Answer to OQ-03-OQ-04-OQ-01-OQ-01

**YES**, the folding approach for iterated CRT generalizes to any commutative ring.

Key facts:
1. `isCoprime_list_prod` — an element coprime to each factor is coprime to the
   product. This is the iterated `IsCoprime.mul_right` flagged in the question.
2. `crtRing_list_exists` — pairwise-coprime moduli give a solvable system. The
   proof folds the two-modulus `crtRing`, using that every tail modulus divides
   the tail product (`List.dvd_prod`) to inherit congruences.
3. `prod_dvd_of_pairwise_coprime` / `crtRing_list_unique` — solutions are unique
   modulo the product of all moduli, folding `IsCoprime.mul_dvd`.
4. Everything is stated over an arbitrary `CommRing R`: ℤ, k[X], ℤ[i], any PID.
-/

#check @crtRing_list_exists
#check @crtRing_list_unique
#check @isCoprime_list_prod
#check @crtRing_three

end BezoutIdentityOQ03OQ04OQ01OQ01
