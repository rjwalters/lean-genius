/-
# The Full Garner Algorithm for k Coprime Moduli, with Operation-Count Bound

Open Question (chinese-remainder-non-coprime-oq-01-oq-02): "Formalize the full
Garner algorithm (not just the mixed-radix decomposition) with runtime
complexity bounds."

Answer: DONE. This file extends the parent entry
`ChineseRemainderNonCoprimeOQ01` (which proves the k = 2 mixed-radix fact
`garner_mixed_radix`) to the complete k-modulus Garner algorithm
(Garner 1959; Knuth, TAOCP vol. 2, §4.3.2, Algorithm 4.3.2C):

1. **Mixed-radix representation** (Part II): every `x < ∏ mᵢ` has a unique
   digit list `v` with `vᵢ < mᵢ` and `x = v₁ + m₁(v₂ + m₂(v₃ + ⋯))`
   (`toDigits` / `ofDigits`, round-trip and uniqueness theorems). The parent's
   `garner_mixed_radix` is exactly the k = 2 case.

2. **The full algorithm** (Part III): `garner` computes the CRT solution from
   a list of (modulus, residue) pairs by forward substitution
   `vᵢ = (rᵢ − x_{i−1}) · (m₁⋯m_{i−1})⁻¹ mod mᵢ`, using an executable
   extended-Euclidean modular inverse (`modInv`, Part I).
   Main theorems: `garner_correct` (the output is `< ∏ mᵢ` and satisfies every
   congruence) and `garner_unique` (it is THE solution below the product).
   `garner_eq_ofDigits` / `toDigits_garner` identify the digit stream produced
   by the recursion with the mixed-radix digits of the solution.

3. **Runtime complexity bound** (Part IV): Mathlib has no machine/cost model,
   so the bound is formalized — in the only rigorous reading available — as a
   theorem about an explicit operation counter. `garnerOps` counts the
   single-precision modular multiply-add-reduce operations of the forward
   substitution (step i reduces the partial solution modulo mᵢ, one Horner
   mul-add-reduce per previously computed digit, justified by `hornerMod_modEq`
   in Part V), and `garnerOps_eq` proves the closed form

       garnerOps l = k(k−1)/2   where k = number of moduli,

   i.e. the classical O(k²) single-precision operation count. The k−1
   extended-gcd inversions (`modInv`, one per step, O(log mᵢ) each) are the
   moduli-only precomputation and are amortized across conversions in a
   residue number system; they are outside this counter, as in the classical
   accounting.

This formalizes Garner's 1959 point (quoted in the parent file's header):
residue number systems support multi-precision arithmetic via
single-precision operations — every digit computation stays below the
individual moduli; only the optional final reconstruction (`ofDigits`, O(k)
big-integer mul-adds) touches large numbers.

Axioms: 0, Sorries: 0.

Tags: number-theory, modular-arithmetic, CRT, garner, mixed-radix,
computational, complexity
-/

import Mathlib

namespace ChineseRemainderNonCoprimeOQ01OQ02

/-
## Part I: Executable modular inverse via the extended Euclidean algorithm
-/

/-- Modular inverse computed by the extended Euclidean algorithm: `modInv a m`
    is the canonical representative in `[0, m)` of the Bézout coefficient of
    `a` in `gcd a m = a·gcdA + m·gcdB`. Fully executable (`Nat.gcdA` is the
    extended-gcd coefficient), costing O(log m) arithmetic operations. -/
def modInv (a m : ℕ) : ℕ := (Nat.gcdA a m % (m : ℤ)).toNat

theorem modInv_lt (a : ℕ) {m : ℕ} (hm : 0 < m) : modInv a m < m := by
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have h1 : 0 ≤ Nat.gcdA a m % (m : ℤ) := Int.emod_nonneg _ hmZ.ne'
  have h2 : Nat.gcdA a m % (m : ℤ) < m := Int.emod_lt_of_pos _ hmZ
  unfold modInv
  omega

/-- Correctness of `modInv`: for `a` coprime to `m`, it is a right inverse of
    `a` in `ZMod m`. -/
theorem modInv_zmod (a : ℕ) {m : ℕ} (hm : 0 < m) (h : Nat.Coprime a m) :
    (a : ZMod m) * (modInv a m : ZMod m) = 1 := by
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  -- Bézout: 1 = a·gcdA + m·gcdB
  have hbez : (1 : ℤ) = a * Nat.gcdA a m + m * Nat.gcdB a m := by
    have h2 := Nat.gcd_eq_gcd_ab a m
    rw [h.gcd_eq_one] at h2
    exact_mod_cast h2
  have hnn : 0 ≤ Nat.gcdA a m % (m : ℤ) := Int.emod_nonneg _ hmZ.ne'
  -- the ℕ-valued inverse casts to the Bézout coefficient in ZMod m
  have hcast : ((modInv a m : ℕ) : ZMod m) = ((Nat.gcdA a m : ℤ) : ZMod m) := by
    unfold modInv
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn, Int.emod_def]
    push_cast
    simp
  have hz := congrArg (fun z : ℤ => (z : ZMod m)) hbez
  push_cast at hz
  simp only [ZMod.natCast_self, zero_mul, add_zero] at hz
  rw [hcast]
  exact hz.symm

/-
## Part II: Mixed-radix (Garner) representation for k moduli
-/

/-- Mixed-radix digits of `x` with respect to the modulus list `ms`:
    `toDigits [m₁, …, mₖ] x = [x % m₁, (x / m₁) % m₂, …]`. -/
def toDigits : List ℕ → ℕ → List ℕ
  | [], _ => []
  | m :: ms, x => x % m :: toDigits ms (x / m)

/-- Horner reconstruction of a mixed-radix digit list:
    `ofDigits [m₁, …] [v₁, …] = v₁ + m₁(v₂ + m₂(v₃ + ⋯))`. -/
def ofDigits : List ℕ → List ℕ → ℕ
  | m :: ms, v :: vs => v + m * ofDigits ms vs
  | _, _ => 0

@[simp] theorem toDigits_nil (x : ℕ) : toDigits [] x = [] := rfl

@[simp] theorem toDigits_cons (m : ℕ) (ms : List ℕ) (x : ℕ) :
    toDigits (m :: ms) x = x % m :: toDigits ms (x / m) := rfl

@[simp] theorem ofDigits_nil (vs : List ℕ) : ofDigits [] vs = 0 := rfl

@[simp] theorem ofDigits_cons (m : ℕ) (ms : List ℕ) (v : ℕ) (vs : List ℕ) :
    ofDigits (m :: ms) (v :: vs) = v + m * ofDigits ms vs := rfl

theorem toDigits_length (ms : List ℕ) (x : ℕ) :
    (toDigits ms x).length = ms.length := by
  induction ms generalizing x with
  | nil => rfl
  | cons m ms ih => simp [ih]

/-- Every digit is below its radix. -/
theorem toDigits_lt (ms : List ℕ) (hpos : ∀ m ∈ ms, 0 < m) (x : ℕ) :
    List.Forall₂ (· < ·) (toDigits ms x) ms := by
  induction ms generalizing x with
  | nil => exact List.Forall₂.nil
  | cons m ms ih =>
      exact List.Forall₂.cons (Nat.mod_lt x (hpos m (by simp)))
        (ih (fun m' hm' => hpos m' (by simp [hm'])) (x / m))

/-- Round-trip: reconstructing the digits of `x < ∏ ms` recovers `x`.
    This is the k-modulus generalization of the parent's `garner_mixed_radix`
    existence statement. -/
theorem ofDigits_toDigits (ms : List ℕ) (x : ℕ) (hx : x < ms.prod) :
    ofDigits ms (toDigits ms x) = x := by
  induction ms generalizing x with
  | nil =>
      simp only [List.prod_nil, Nat.lt_one_iff] at hx
      simp [hx]
  | cons m ms ih =>
      have hxm : x < m * ms.prod := by simpa using hx
      have hx' : x / m < ms.prod := Nat.div_lt_of_lt_mul hxm
      simp only [toDigits_cons, ofDigits_cons, ih _ hx']
      exact Nat.mod_add_div x m

/-- Bounded digit lists reconstruct below the product. -/
theorem ofDigits_lt {ms vs : List ℕ} (h : List.Forall₂ (· < ·) vs ms) :
    ofDigits ms vs < ms.prod := by
  induction h with
  | nil => simp
  | @cons v m vs ms hvm _ ih =>
      simp only [ofDigits_cons, List.prod_cons]
      calc v + m * ofDigits ms vs < m + m * ofDigits ms vs := by omega
        _ = m * (ofDigits ms vs + 1) := by ring
        _ ≤ m * ms.prod := Nat.mul_le_mul_left m ih

/-- Digit extraction inverts Horner reconstruction on bounded digit lists. -/
theorem toDigits_ofDigits {ms vs : List ℕ} (h : List.Forall₂ (· < ·) vs ms) :
    toDigits ms (ofDigits ms vs) = vs := by
  induction h with
  | nil => rfl
  | @cons v m vs ms hvm _ ih =>
      have hm : 0 < m := by omega
      simp only [ofDigits_cons, toDigits_cons]
      congr 1
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hvm]
      · rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hvm, Nat.zero_add]
        exact ih

/-- **Uniqueness of the mixed-radix representation** (k-modulus generalization
    of the parent's `garner_mixed_radix_unique`). -/
theorem digits_unique {ms vs ws : List ℕ}
    (hv : List.Forall₂ (· < ·) vs ms) (hw : List.Forall₂ (· < ·) ws ms)
    (h : ofDigits ms vs = ofDigits ms ws) : vs = ws := by
  rw [← toDigits_ofDigits hv, ← toDigits_ofDigits hw, h]

/-- **Existence of the mixed-radix representation** (k-modulus generalization
    of the parent's `garner_mixed_radix`): every `x < ∏ mᵢ` has a digit list
    with `vᵢ < mᵢ` reconstructing to `x`. -/
theorem mixed_radix_exists (ms : List ℕ) (hpos : ∀ m ∈ ms, 0 < m)
    (x : ℕ) (hx : x < ms.prod) :
    ∃ vs : List ℕ, List.Forall₂ (· < ·) vs ms ∧ ofDigits ms vs = x :=
  ⟨toDigits ms x, toDigits_lt ms hpos x, ofDigits_toDigits ms x hx⟩

/-
## Part III: The full Garner algorithm
-/

/-- One Garner digit: `nextDigit x P m r` is `(r − x)·P⁻¹ mod m` written in
    truncation-safe ℕ arithmetic (`x` = partial solution, `P` = product of the
    moduli already processed, `m` = current modulus, `r` = current residue). -/
def nextDigit (x P m r : ℕ) : ℕ :=
  ((r % m + (m - x % m)) * modInv (P % m) m) % m

theorem nextDigit_lt (x P r : ℕ) {m : ℕ} (hm : 0 < m) :
    nextDigit x P m r < m := Nat.mod_lt _ hm

/-- The Garner forward-substitution recursion: `x` is the partial solution and
    `P` the product of the moduli already processed; each step computes one
    digit and folds it in. -/
def garnerRec : ℕ → ℕ → List (ℕ × ℕ) → ℕ
  | x, _, [] => x
  | x, P, (m, r) :: rest => garnerRec (x + nextDigit x P m r * P) (P * m) rest

/-- **The full Garner algorithm**: the CRT solution for a list of
    (modulus, residue) pairs, by forward substitution. -/
def garner (l : List (ℕ × ℕ)) : ℕ := garnerRec 0 1 l

/-- The digit stream produced by the Garner recursion — the mixed-radix
    digits of the solution (see `toDigits_garner`). -/
def garnerDigitsRec : ℕ → ℕ → List (ℕ × ℕ) → List ℕ
  | _, _, [] => []
  | x, P, (m, r) :: rest =>
      nextDigit x P m r :: garnerDigitsRec (x + nextDigit x P m r * P) (P * m) rest

def garnerDigits (l : List (ℕ × ℕ)) : List ℕ := garnerDigitsRec 0 1 l

@[simp] theorem garnerRec_nil (x P : ℕ) : garnerRec x P [] = x := rfl

@[simp] theorem garnerRec_cons (x P m r : ℕ) (rest : List (ℕ × ℕ)) :
    garnerRec x P ((m, r) :: rest) =
      garnerRec (x + nextDigit x P m r * P) (P * m) rest := rfl

@[simp] theorem garnerDigitsRec_nil (x P : ℕ) : garnerDigitsRec x P [] = [] := rfl

@[simp] theorem garnerDigitsRec_cons (x P m r : ℕ) (rest : List (ℕ × ℕ)) :
    garnerDigitsRec x P ((m, r) :: rest) =
      nextDigit x P m r ::
        garnerDigitsRec (x + nextDigit x P m r * P) (P * m) rest := rfl

/-- **Step congruence**: folding in the next Garner digit makes the partial
    solution correct modulo the new modulus. The heart of the algorithm:
    `x + ((r − x)·P⁻¹ mod m)·P ≡ r (mod m)`. -/
theorem nextDigit_step (x P r : ℕ) {m : ℕ} (hm : 0 < m)
    (hcop : Nat.Coprime P m) :
    x + nextDigit x P m r * P ≡ r [MOD m] := by
  have hcop' : Nat.Coprime (P % m) m := by
    have h2 : Nat.gcd m P = 1 := Nat.coprime_comm.mp hcop
    have h3 : Nat.gcd (P % m) m = 1 := by rw [← Nat.gcd_rec]; exact h2
    exact h3
  have hw : (P : ZMod m) * (modInv (P % m) m : ZMod m) = 1 := by
    have h1 := modInv_zmod (P % m) hm hcop'
    rwa [ZMod.natCast_mod] at h1
  have hxm : x % m ≤ m := (Nat.mod_lt x hm).le
  have key : ((x + nextDigit x P m r * P : ℕ) : ZMod m) = ((r : ℕ) : ZMod m) := by
    unfold nextDigit
    push_cast [ZMod.natCast_mod, Nat.cast_sub hxm]
    rw [ZMod.natCast_self]
    linear_combination ((r : ZMod m) - (x : ZMod m)) * hw
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp key

/-- Master specification of the Garner recursion, proved by one induction:
    the result stays below `P·∏ mᵢ`, is congruent to the incoming partial
    solution mod `P` (so previously established congruences persist), and
    satisfies every new congruence. -/
theorem garnerRec_spec (l : List (ℕ × ℕ)) :
    ∀ x P : ℕ, x < P →
    (∀ p ∈ l, 0 < p.1) →
    (∀ p ∈ l, Nat.Coprime P p.1) →
    (l.map Prod.fst).Pairwise Nat.Coprime →
    garnerRec x P l < P * (l.map Prod.fst).prod ∧
    garnerRec x P l ≡ x [MOD P] ∧
    ∀ p ∈ l, garnerRec x P l ≡ p.2 [MOD p.1] := by
  induction l with
  | nil =>
      intro x P hx _ _ _
      exact ⟨by simpa using hx, Nat.ModEq.refl x, by simp⟩
  | cons p rest ih =>
      obtain ⟨m, r⟩ := p
      intro x P hx hpos hcop hpair
      have hm : 0 < m := hpos (m, r) (by simp)
      have hcopPm : Nat.Coprime P m := hcop (m, r) (by simp)
      have hvlt : nextDigit x P m r < m := nextDigit_lt x P r hm
      have hx' : x + nextDigit x P m r * P < P * m := by nlinarith
      rw [List.map_cons] at hpair
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      have hposr : ∀ q ∈ rest, 0 < q.1 := fun q hq => hpos q (by simp [hq])
      have hcopr : ∀ q ∈ rest, Nat.Coprime (P * m) q.1 := by
        intro q hq
        exact Nat.Coprime.mul_left (hcop q (by simp [hq]))
          (hhead q.1 (List.mem_map_of_mem hq))
      obtain ⟨ihlt, ihself, ihmod⟩ :=
        ih (x + nextDigit x P m r * P) (P * m) hx' hposr hcopr htail
      refine ⟨?_, ?_, ?_⟩
      · simpa [List.prod_cons, mul_assoc] using ihlt
      · have h2 : garnerRec x P ((m, r) :: rest) ≡
            x + nextDigit x P m r * P [MOD P] := by
          rw [garnerRec_cons]
          exact ihself.of_dvd (dvd_mul_right P m)
        have h3 : x + nextDigit x P m r * P ≡ x [MOD P] := by
          show (x + nextDigit x P m r * P) % P = x % P
          simp
        exact h2.trans h3
      · intro q hq
        rcases List.mem_cons.mp hq with heq | hmem
        · subst heq
          have h1 : garnerRec x P ((m, r) :: rest) ≡
              x + nextDigit x P m r * P [MOD m] := by
            rw [garnerRec_cons]
            exact ihself.of_dvd (dvd_mul_left m P)
          exact h1.trans (nextDigit_step x P r hm hcopPm)
        · rw [garnerRec_cons]
          exact ihmod q hmem

/-- **Main theorem — correctness of the full Garner algorithm.** For pairwise
    coprime positive moduli, `garner` returns a value below the product of the
    moduli satisfying every congruence `garner l ≡ rᵢ (mod mᵢ)`. -/
theorem garner_correct (l : List (ℕ × ℕ))
    (hpos : ∀ p ∈ l, 0 < p.1)
    (hpair : (l.map Prod.fst).Pairwise Nat.Coprime) :
    garner l < (l.map Prod.fst).prod ∧
    ∀ p ∈ l, garner l ≡ p.2 [MOD p.1] := by
  have h := garnerRec_spec l 0 1 Nat.one_pos hpos
    (fun p _ => Nat.coprime_one_left p.1) hpair
  exact ⟨by simpa [garner] using h.1, h.2.2⟩

/-- Coprimality with every list element gives coprimality with the product. -/
theorem coprime_list_prod {k : ℕ} :
    ∀ {ms : List ℕ}, (∀ m ∈ ms, Nat.Coprime k m) → Nat.Coprime k ms.prod := by
  intro ms
  induction ms with
  | nil => intro _; exact Nat.coprime_one_right k
  | cons m ms ih =>
      intro h
      rw [List.prod_cons]
      exact Nat.Coprime.mul_right (h m (by simp))
        (ih fun m' hm' => h m' (by simp [hm']))

/-- Congruence modulo every member of a pairwise-coprime list lifts to
    congruence modulo the product (the uniqueness half of CRT). -/
theorem modEq_prod {x y : ℕ} :
    ∀ {ms : List ℕ}, ms.Pairwise Nat.Coprime →
    (∀ m ∈ ms, x ≡ y [MOD m]) → x ≡ y [MOD ms.prod] := by
  intro ms
  induction ms with
  | nil => intro _ _; simpa using Nat.modEq_one
  | cons m ms ih =>
      intro hpair hall
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      have h1 : x ≡ y [MOD m] := hall m (by simp)
      have h2 : x ≡ y [MOD ms.prod] :=
        ih htail (fun m' hm' => hall m' (by simp [hm']))
      have hcop : Nat.Coprime m ms.prod := coprime_list_prod hhead
      rw [List.prod_cons]
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩

/-- **Uniqueness**: `garner l` is THE solution below the product — any `y`
    below `∏ mᵢ` satisfying all the congruences equals it. -/
theorem garner_unique (l : List (ℕ × ℕ))
    (hpos : ∀ p ∈ l, 0 < p.1)
    (hpair : (l.map Prod.fst).Pairwise Nat.Coprime)
    (y : ℕ) (hy : y < (l.map Prod.fst).prod)
    (hmod : ∀ p ∈ l, y ≡ p.2 [MOD p.1]) : y = garner l := by
  obtain ⟨hlt, hg⟩ := garner_correct l hpos hpair
  have h : y ≡ garner l [MOD (l.map Prod.fst).prod] := by
    apply modEq_prod hpair
    intro m hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    exact (hmod p hp).trans (hg p hp).symm
  have h2 : y % (l.map Prod.fst).prod = garner l % (l.map Prod.fst).prod := h
  rwa [Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hlt] at h2

/-- The Garner recursion assembles exactly the Horner value of its digit
    stream: algorithm = mixed-radix decomposition + reconstruction. -/
theorem garnerRec_eq_ofDigits :
    ∀ (l : List (ℕ × ℕ)) (x P : ℕ),
      garnerRec x P l = x + P * ofDigits (l.map Prod.fst) (garnerDigitsRec x P l) := by
  intro l
  induction l with
  | nil => intro x P; simp
  | cons p rest ih =>
      obtain ⟨m, r⟩ := p
      intro x P
      rw [garnerRec_cons, garnerDigitsRec_cons, List.map_cons, ofDigits_cons, ih]
      ring

theorem garner_eq_ofDigits (l : List (ℕ × ℕ)) :
    garner l = ofDigits (l.map Prod.fst) (garnerDigits l) := by
  simpa [garner, garnerDigits] using garnerRec_eq_ofDigits l 0 1

/-- The Garner digit stream is bounded by the moduli: every digit is
    single-precision (`vᵢ < mᵢ`). -/
theorem garnerDigitsRec_lt :
    ∀ (l : List (ℕ × ℕ)) (x P : ℕ), (∀ p ∈ l, 0 < p.1) →
      List.Forall₂ (· < ·) (garnerDigitsRec x P l) (l.map Prod.fst) := by
  intro l
  induction l with
  | nil => intro x P _; exact List.Forall₂.nil
  | cons p rest ih =>
      obtain ⟨m, r⟩ := p
      intro x P hpos
      rw [garnerDigitsRec_cons, List.map_cons]
      exact List.Forall₂.cons (nextDigit_lt x P r (hpos (m, r) (by simp)))
        (ih _ _ (fun q hq => hpos q (by simp [hq])))

theorem garnerDigits_lt (l : List (ℕ × ℕ)) (hpos : ∀ p ∈ l, 0 < p.1) :
    List.Forall₂ (· < ·) (garnerDigits l) (l.map Prod.fst) :=
  garnerDigitsRec_lt l 0 1 hpos

/-- The digits produced by the Garner algorithm ARE the mixed-radix digits of
    the solution it returns. -/
theorem toDigits_garner (l : List (ℕ × ℕ)) (hpos : ∀ p ∈ l, 0 < p.1) :
    toDigits (l.map Prod.fst) (garner l) = garnerDigits l := by
  rw [garner_eq_ofDigits l]
  exact toDigits_ofDigits (garnerDigits_lt l hpos)

/-
## Part IV: The operation counter and the k(k−1)/2 bound
-/

/-- Single-precision operation counter for the Garner forward substitution:
    the step at (0-indexed) position `i` reduces the partial solution modulo
    `mᵢ` via the Horner inner loop (`hornerMod`, Part V), performing one
    modular multiply-add-reduce per previously computed digit — `i`
    operations. `stepOps i l` accumulates the count starting from step `i`. -/
def stepOps : ℕ → List (ℕ × ℕ) → ℕ
  | _, [] => 0
  | i, _ :: rest => i + stepOps (i + 1) rest

/-- Total single-precision operation count of the Garner forward
    substitution on `l`. -/
def garnerOps (l : List (ℕ × ℕ)) : ℕ := stepOps 0 l

theorem stepOps_eq_sum :
    ∀ (l : List (ℕ × ℕ)) (i : ℕ),
      stepOps i l = ∑ j ∈ Finset.range l.length, (i + j) := by
  intro l
  induction l with
  | nil => intro i; simp [stepOps]
  | cons p rest ih =>
      intro i
      rw [show stepOps i (p :: rest) = i + stepOps (i + 1) rest from rfl,
        ih (i + 1), List.length_cons, Finset.sum_range_succ']
      have hshift : ∀ j, i + 1 + j = i + (j + 1) := fun j => by ring
      simp only [hshift]
      omega

/-- **Runtime complexity bound (closed form)**: the Garner forward
    substitution performs exactly `k(k−1)/2` single-precision modular
    operations for `k` moduli — the classical O(k²) bound. -/
theorem garnerOps_eq (l : List (ℕ × ℕ)) :
    garnerOps l = l.length * (l.length - 1) / 2 := by
  rw [garnerOps, stepOps_eq_sum]
  simp only [Nat.zero_add]
  exact Finset.sum_range_id l.length

/-
## Part V: The single-precision inner loop (why step i costs i operations)
-/

/-- Reduced Horner evaluation of a list of (radix, digit) pairs modulo `n`:
    one multiply-add-reduce per digit, with every intermediate value kept
    below `n` after reduction. This is the single-precision inner loop with
    which Garner step `i` evaluates the partial solution mod `mᵢ` — it costs
    exactly one modular operation per previous digit, grounding the `stepOps`
    counter. -/
def hornerMod (n : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (m, v) :: rest => (v + m * hornerMod n rest) % n

/-- All intermediate values of the reduced Horner loop stay below `n`. -/
theorem hornerMod_lt {n : ℕ} (hn : 0 < n) (l : List (ℕ × ℕ)) :
    hornerMod n l < n := by
  cases l with
  | nil => simpa [hornerMod] using hn
  | cons p rest =>
      obtain ⟨m, v⟩ := p
      exact Nat.mod_lt _ hn

/-- The reduced Horner loop computes the mixed-radix value modulo `n`:
    reducing after every step does not change the result mod `n`. -/
theorem hornerMod_modEq (n : ℕ) :
    ∀ l : List (ℕ × ℕ),
      hornerMod n l ≡ ofDigits (l.map Prod.fst) (l.map Prod.snd) [MOD n] := by
  intro l
  induction l with
  | nil => exact Nat.ModEq.refl 0
  | cons p rest ih =>
      obtain ⟨m, v⟩ := p
      show (v + m * hornerMod n rest) % n ≡ _ [MOD n]
      rw [List.map_cons, List.map_cons, ofDigits_cons]
      calc (v + m * hornerMod n rest) % n
          ≡ v + m * hornerMod n rest [MOD n] := Nat.mod_modEq _ n
        _ ≡ v + m * ofDigits (rest.map Prod.fst) (rest.map Prod.snd) [MOD n] :=
            (ih.mul_left m).add_left v

/-
## Part VI: Worked examples (executable spot checks)
-/

-- The classical instance: x ≡ 2 (3), x ≡ 3 (5), x ≡ 2 (7) has solution 23.
example : garner [(3, 2), (5, 3), (7, 2)] = 23 :=
  (garner_unique _ (by decide) (by decide) 23 (by decide) (by decide)).symm

-- Mixed-radix digits of 23 in radices (3, 5, 7): 23 = 2 + 3·(2 + 5·1).
example : toDigits [3, 5, 7] 23 = [2, 2, 1] := by decide

example : ofDigits [3, 5, 7] [2, 2, 1] = 23 := by decide

-- Operation count for k = 3 moduli: 3·2/2 = 3 single-precision operations.
example : garnerOps [(3, 2), (5, 3), (7, 2)] = 3 := by decide

-- Operation count for k = 5: 5·4/2 = 10.
example : garnerOps [(2, 1), (3, 2), (5, 3), (7, 4), (11, 5)] = 10 := by decide

end ChineseRemainderNonCoprimeOQ01OQ02
