import Mathlib

/-
# Garner's Algorithm: Mixed-Radix CRT Reconstruction (bezout-identity-oq-03-oq-05)

## Open Question

Extending the two-modulus Chinese Remainder solver `crtInt`
(`Proofs/BezoutIdentityOQ03.lean`) to `k` pairwise-coprime moduli, formalize
**Garner's algorithm** — the classical mixed-radix reconstruction — and prove
it returns the canonical CRT solution.

## The algorithm

Given pairwise-coprime moduli `m₁, …, m_k > 0` and residues `r₁, …, r_k`, Garner
builds the unique `x ∈ [0, ∏ mᵢ)` in **mixed-radix** form

    x = v₁ + v₂·m₁ + v₃·m₁m₂ + ⋯ + v_k·m₁⋯m_{k-1}

by a single left-to-right sweep that carries only the running value `x` and the
running partial product `P = m₁⋯m_{j-1}`.  At step `j` the digit is

    vⱼ = (rⱼ − x) · (P⁻¹ mod mⱼ)   reduced into `[0, mⱼ)`,     x ← x + vⱼ·P,   P ← P·mⱼ.

The modular inverse `P⁻¹ mod mⱼ` exists because `mⱼ` is coprime to every earlier
modulus, hence to their product `P`.  We realize it **without** any `ZMod.inv`
plumbing: the Bézout cofactor `Int.gcdA P mⱼ` already satisfies
`P · Int.gcdA P mⱼ ≡ 1 [ZMOD mⱼ]` — the very identity behind `crtInt`.  (Indeed the
un-reduced increment `x + (r−x)·(Int.gcdA P m)·P` equals `crtInt P m x r` exactly,
since `1 − P·gcdA = m·gcdB`; the `% m` reduction is what keeps the digits — and the
running value — bounded, the defining feature of *Garner's* form.)

## Results

* `garner_modEq`   — for every congruence `(mᵢ, rᵢ)`, `garner pairs ≡ rᵢ [ZMOD mᵢ]`.
* `garner_range`   — `0 ≤ garner pairs < ∏ mᵢ` (genuine mixed-radix bound).
* `garner_unique`  — any `y ∈ [0, ∏ mᵢ)` satisfying all the congruences equals
                     `garner pairs`; i.e. Garner returns *the* CRT solution.

All proofs are `sorry`-free and axiom-free (only Lean's foundational axioms).
The arithmetic core is a single Bézout step, reused from the gallery's `crtInt`.

## Status
- [x] Complete proof (0 sorries, 0 `axiom`)
-/

namespace BezoutIdentityOQ03OQ05

/-- Garner digit: `(r − x)·(P⁻¹ mod m)` reduced into `[0, m)`, using the Bézout
    cofactor `Int.gcdA P m` as the modular inverse of `P` modulo `m`. -/
def digit (x P m r : ℤ) : ℤ := ((r - x) * Int.gcdA P m) % m

/-- Garner sweep accumulator: carry the running value `x` and partial product `P`
    left-to-right across the list of `(modulus, residue)` pairs. -/
def garnerAux : ℤ → ℤ → List (ℤ × ℤ) → ℤ × ℤ
  | x, P, [] => (x, P)
  | x, P, (m, r) :: rest => garnerAux (x + digit x P m r * P) (P * m) rest

/-- Garner's reconstruction: the mixed-radix CRT value for the system `pairs`. -/
def garner (pairs : List (ℤ × ℤ)) : ℤ := (garnerAux 0 1 pairs).1

/-! ### Digit facts. -/

theorem digit_nonneg (x P m r : ℤ) (hm : 0 < m) : 0 ≤ digit x P m r := by
  unfold digit; exact Int.emod_nonneg _ (ne_of_gt hm)

theorem digit_lt (x P m r : ℤ) (hm : 0 < m) : digit x P m r < m := by
  unfold digit; exact Int.emod_lt_of_pos _ hm

theorem digit_modEq (x P m r : ℤ) : digit x P m r ≡ (r - x) * Int.gcdA P m [ZMOD m] := by
  unfold digit; exact Int.mod_modEq _ _

/-! ### Bookkeeping: the running product is the product of the moduli. -/

theorem garnerAux_snd (pairs : List (ℤ × ℤ)) (x P : ℤ) :
    (garnerAux x P pairs).2 = P * (pairs.map Prod.fst).prod := by
  induction pairs generalizing x P with
  | nil => simp [garnerAux]
  | cons hd tl ih =>
    obtain ⟨m, r⟩ := hd
    simp only [garnerAux, List.map_cons, List.prod_cons, ih]
    ring

/-! ### Modular inverse from Bézout (the single arithmetic fact we need). -/

/-- The Bézout cofactor inverts `P` modulo any `m` coprime to `P`. -/
theorem gcdA_mul_modEq_one {P m : ℤ} (h : IsCoprime P m) :
    P * Int.gcdA P m ≡ 1 [ZMOD m] := by
  have hg : Int.gcd P m = 1 := Int.isCoprime_iff_gcd_eq_one.mp h
  have hbez : (1 : ℤ) = P * Int.gcdA P m + m * Int.gcdB P m := by
    have := Int.gcd_eq_gcd_ab P m
    rw [hg] at this; push_cast at this; linarith
  rw [Int.modEq_iff_dvd]
  exact ⟨Int.gcdB P m, by linarith⟩

/-- `IsCoprime` distributes over a `List.prod` on the right. -/
theorem isCoprime_list_prod_right {a : ℤ} :
    ∀ (l : List ℤ), (∀ b ∈ l, IsCoprime a b) → IsCoprime a l.prod
  | [], _ => by simpa using isCoprime_one_right
  | b :: t, h => by
      simp only [List.prod_cons]
      exact (h b List.mem_cons_self).mul_right
        (isCoprime_list_prod_right t (fun q hq => h q (List.mem_cons_of_mem _ hq)))

/-! ### Preservation: the sweep never disturbs the residue already accumulated. -/

/-- After processing `pairs` from `(x, P)`, the result is still `≡ x [ZMOD P]`.
    This is what protects the residues of *earlier* moduli (`m ∣ P`). -/
theorem garnerAux_modEq_self (pairs : List (ℤ × ℤ)) :
    ∀ (x P : ℤ), (∀ p ∈ pairs, IsCoprime P p.1) →
      pairs.Pairwise (fun a b => IsCoprime a.1 b.1) →
      (garnerAux x P pairs).1 ≡ x [ZMOD P] := by
  induction pairs with
  | nil => intro x P _ _; simp [garnerAux]
  | cons hd tl ih =>
    obtain ⟨m, r⟩ := hd
    intro x P hcop hpair
    simp only [garnerAux]
    -- Step value `x₁ = x + digit·P ≡ x [ZMOD P]` since `P ∣ digit·P`.
    have hstep : x + digit x P m r * P ≡ x [ZMOD P] := by
      rw [Int.modEq_iff_dvd]; exact ⟨-(digit x P m r), by ring⟩
    have hmtl : ∀ q ∈ tl, IsCoprime m q.1 := (List.pairwise_cons.mp hpair).1
    have hcop' : ∀ q ∈ tl, IsCoprime (P * m) q.1 := by
      intro q hq
      exact (hcop q (List.mem_cons_of_mem _ hq)).mul_left (hmtl q hq)
    have hpair' : tl.Pairwise (fun a b => IsCoprime a.1 b.1) :=
      (List.pairwise_cons.mp hpair).2
    have hrec := ih (x + digit x P m r * P) (P * m) hcop' hpair'
    have hrec' : (garnerAux (x + digit x P m r * P) (P * m) tl).1
        ≡ x + digit x P m r * P [ZMOD P] :=
      hrec.of_dvd (dvd_mul_right P m)
    exact hrec'.trans hstep

/-! ### Correctness: every congruence is satisfied. -/

theorem garnerAux_modEq (pairs : List (ℤ × ℤ)) :
    ∀ (x P : ℤ), (∀ p ∈ pairs, IsCoprime P p.1) →
      pairs.Pairwise (fun a b => IsCoprime a.1 b.1) →
      ∀ p ∈ pairs, (garnerAux x P pairs).1 ≡ p.2 [ZMOD p.1] := by
  induction pairs with
  | nil => intro x P _ _ p hp; simp at hp
  | cons hd tl ih =>
    obtain ⟨m, r⟩ := hd
    intro x P hcop hpair p hp
    simp only [garnerAux]
    have hcopP : IsCoprime P m := hcop (m, r) List.mem_cons_self
    have hmtl : ∀ q ∈ tl, IsCoprime m q.1 := (List.pairwise_cons.mp hpair).1
    have hcop' : ∀ q ∈ tl, IsCoprime (P * m) q.1 := by
      intro q hq
      exact (hcop q (List.mem_cons_of_mem _ hq)).mul_left (hmtl q hq)
    have hpair' : tl.Pairwise (fun a b => IsCoprime a.1 b.1) :=
      (List.pairwise_cons.mp hpair).2
    rcases List.mem_cons.mp hp with hp | hp
    · -- Head congruence: `x + digit·P ≡ r [ZMOD m]`.
      subst hp
      have h1 : digit x P m r * P ≡ (r - x) * Int.gcdA P m * P [ZMOD m] :=
        (digit_modEq x P m r).mul_right P
      have h2 : (r - x) * Int.gcdA P m * P ≡ (r - x) [ZMOD m] := by
        have he : (r - x) * Int.gcdA P m * P = (r - x) * (P * Int.gcdA P m) := by ring
        rw [he]
        calc (r - x) * (P * Int.gcdA P m)
            ≡ (r - x) * 1 [ZMOD m] := (gcdA_mul_modEq_one hcopP).mul_left _
          _ = (r - x) := by ring
      have hdigP : digit x P m r * P ≡ (r - x) [ZMOD m] := h1.trans h2
      have hx1 : x + digit x P m r * P ≡ r [ZMOD m] := by
        calc x + digit x P m r * P
            ≡ x + (r - x) [ZMOD m] := hdigP.add_left x
          _ = r := by ring
      have hpres := garnerAux_modEq_self tl (x + digit x P m r * P) (P * m) hcop' hpair'
      have hpres' : (garnerAux (x + digit x P m r * P) (P * m) tl).1
          ≡ x + digit x P m r * P [ZMOD m] :=
        hpres.of_dvd (dvd_mul_left m P)
      exact hpres'.trans hx1
    · -- Tail congruences: directly by induction.
      exact ih (x + digit x P m r * P) (P * m) hcop' hpair' p hp

/-! ### Range: the mixed-radix bound `0 ≤ x < ∏ mᵢ`. -/

theorem garnerAux_range (pairs : List (ℤ × ℤ)) :
    ∀ (x P : ℤ), 0 < P → 0 ≤ x → x < P → (∀ p ∈ pairs, 0 < p.1) →
      0 ≤ (garnerAux x P pairs).1 ∧ (garnerAux x P pairs).1 < (garnerAux x P pairs).2 := by
  induction pairs with
  | nil => intro x P _ hx0 hxP _; simpa [garnerAux] using ⟨hx0, hxP⟩
  | cons hd tl ih =>
    obtain ⟨m, r⟩ := hd
    intro x P hP hx0 hxP hpos
    simp only [garnerAux]
    have hm : 0 < m := hpos (m, r) List.mem_cons_self
    have hpos' : ∀ q ∈ tl, 0 < q.1 := fun q hq => hpos q (List.mem_cons_of_mem _ hq)
    have hvlo : 0 ≤ digit x P m r := digit_nonneg x P m r hm
    have hvhi : digit x P m r < m := digit_lt x P m r hm
    have hx1lo : 0 ≤ x + digit x P m r * P :=
      add_nonneg hx0 (mul_nonneg hvlo (le_of_lt hP))
    have hx1hi : x + digit x P m r * P < P * m := by
      have hd1 : digit x P m r ≤ m - 1 := by omega
      have hstep : digit x P m r * P ≤ (m - 1) * P :=
        mul_le_mul_of_nonneg_right hd1 (le_of_lt hP)
      have hring : P + (m - 1) * P = P * m := by ring
      linarith [hstep, hxP, hring]
    have hPm : 0 < P * m := mul_pos hP hm
    exact ih (x + digit x P m r * P) (P * m) hPm hx1lo hx1hi hpos'

/-! ### Public interface (sweeping from `(0, 1)`). -/

/-- **Garner correctness.** For pairwise-coprime positive moduli, `garner` solves
    every congruence of the system. -/
theorem garner_modEq (pairs : List (ℤ × ℤ))
    (hpair : pairs.Pairwise (fun a b => IsCoprime a.1 b.1))
    {p : ℤ × ℤ} (hp : p ∈ pairs) :
    garner pairs ≡ p.2 [ZMOD p.1] :=
  garnerAux_modEq pairs 0 1 (fun _ _ => isCoprime_one_left) hpair p hp

/-- **Garner range.** The reconstruction is the canonical representative in
    `[0, ∏ mᵢ)`. -/
theorem garner_range (pairs : List (ℤ × ℤ)) (hpos : ∀ p ∈ pairs, 0 < p.1) :
    0 ≤ garner pairs ∧ garner pairs < (pairs.map Prod.fst).prod := by
  have h := garnerAux_range pairs 0 1 one_pos le_rfl one_pos hpos
  rw [garnerAux_snd pairs 0 1, one_mul] at h
  exact h

/-- **Garner uniqueness.** Any `y ∈ [0, ∏ mᵢ)` satisfying all the congruences is
    exactly `garner pairs`: Garner returns *the* CRT solution. -/
theorem garner_unique (pairs : List (ℤ × ℤ))
    (hpair : pairs.Pairwise (fun a b => IsCoprime a.1 b.1))
    (hpos : ∀ p ∈ pairs, 0 < p.1)
    (y : ℤ) (hy0 : 0 ≤ y) (hyP : y < (pairs.map Prod.fst).prod)
    (hcong : ∀ p ∈ pairs, y ≡ p.2 [ZMOD p.1]) :
    y = garner pairs := by
  -- Each modulus divides `garner pairs - y`; pairwise coprimality lifts this to
  -- their product.
  have key : ∀ (l : List (ℤ × ℤ)), l.Pairwise (fun a b => IsCoprime a.1 b.1) →
      (∀ p ∈ l, (p.1 : ℤ) ∣ (garner pairs - y)) →
      (l.map Prod.fst).prod ∣ (garner pairs - y) := by
    intro l
    induction l with
    | nil => intro _ _; simp
    | cons hd tl ih =>
      intro hpr hdvd
      simp only [List.map_cons, List.prod_cons]
      have hhd : (hd.1 : ℤ) ∣ (garner pairs - y) := hdvd hd List.mem_cons_self
      have htl : (tl.map Prod.fst).prod ∣ (garner pairs - y) :=
        ih (List.pairwise_cons.mp hpr).2 (fun p hp => hdvd p (List.mem_cons_of_mem _ hp))
      have hcoptl : IsCoprime hd.1 ((tl.map Prod.fst).prod) := by
        apply isCoprime_list_prod_right
        intro q hq
        obtain ⟨pq, hpq, rfl⟩ := List.mem_map.mp hq
        exact (List.pairwise_cons.mp hpr).1 pq hpq
      exact hcoptl.mul_dvd hhd htl
  have hdvd : ∀ p ∈ pairs, (p.1 : ℤ) ∣ (garner pairs - y) := by
    intro p hp
    rw [← Int.modEq_iff_dvd]
    exact (hcong p hp).trans (garner_modEq pairs hpair hp).symm
  have hdvdP : (pairs.map Prod.fst).prod ∣ (garner pairs - y) := key pairs hpair hdvd
  -- Two representatives in `[0, ∏)` differing by a multiple of `∏` coincide.
  have hg := garner_range pairs hpos
  obtain ⟨glo, ghi⟩ := hg
  obtain ⟨c, hc⟩ := hdvdP
  have hP : (0 : ℤ) < (pairs.map Prod.fst).prod := lt_of_le_of_lt glo ghi
  have hc1 : c < 1 := by
    have hlt : (pairs.map Prod.fst).prod * c < (pairs.map Prod.fst).prod * 1 := by
      rw [mul_one, ← hc]; omega
    exact lt_of_mul_lt_mul_left hlt (le_of_lt hP)
  have hc2 : -1 < c := by
    have hlt : (pairs.map Prod.fst).prod * (-1) < (pairs.map Prod.fst).prod * c := by
      rw [mul_neg, mul_one, ← hc]; omega
    exact lt_of_mul_lt_mul_left hlt (le_of_lt hP)
  have hc0 : c = 0 := by omega
  rw [hc0, mul_zero] at hc
  omega

end BezoutIdentityOQ03OQ05
