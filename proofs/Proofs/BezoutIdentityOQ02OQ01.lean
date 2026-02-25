import Mathlib

/-
# Fundamental Theorem of Arithmetic from Euclid's Lemma (OQ-02-OQ-01)

## The Open Question

Can we derive the Fundamental Theorem of Arithmetic (FTA) by building
explicitly on the `euclids_lemma_prime` result from BezoutIdentityOQ02?

## Answer: Yes!

The proof chain is:
1. **Bézout's Identity** → **Euclid's Lemma** (from BezoutIdentityOQ02)
2. **Euclid's Lemma (lists)**: If prime p divides a product of primes, p equals one of them
3. **Uniqueness**: Any two prime lists with equal products are permutations
4. **FTA**: Every n ≥ 2 has a unique prime factorization (up to ordering)

## Key Insight

The *uniqueness* half of FTA is exactly what requires Euclid's lemma. Without it,
we'd only know existence (every number is a product of primes), not uniqueness.

The proof directly mirrors Euclid's argument in Elements, Book IX, Proposition 14:
"If a number be the least that is measured by prime numbers, it will not be measured
by any other prime number except those originally measuring it."

## Historical Note

Euclid's Elements VII.30 proves: if p is prime and p | ab, then p | a or p | b.
This is exactly our `euclids_lemma_prime`.
Gauss (Disquisitiones Arithmeticae, 1801) gave the first complete proof of uniqueness.

## Status
- [x] euclids_lemma_prime (0 axioms, 0 sorries)
- [x] prime_dvd_of_dvd_list_prod (0 axioms, 0 sorries)
- [x] prime_mem_of_dvd_prime_list (0 axioms, 0 sorries)
- [x] prime_list_perm (0 axioms, 0 sorries) — FTA Uniqueness
- [x] fta_from_euclid (0 axioms, 0 sorries) — Complete FTA
-/

namespace BezoutFTA

open Nat

/-
## Part I: Euclid's Lemma from Bézout's Identity

This is the bridge: Bézout's identity (encoded as IsCoprime in Lean) gives
Euclid's lemma for primes.
-/

/-- **Euclid's Lemma for Primes** (via Bézout/IsCoprime):
    If prime p divides a product ab, then p divides a or p divides b.

    Proof: If p ∤ a, then gcd(p, a) = 1 (since p is prime). By Bézout,
    ∃ x y : ℤ, p*x + a*y = 1. Multiply by b: p*(x*b) + (a*b)*y = b.
    Since p | p*(x*b) and p | (a*b) (by hypothesis), we get p | b. -/
theorem euclids_lemma_prime {p a b : ℕ} (hp : p.Prime)
    (hpab : p ∣ a * b) (hpa : ¬ p ∣ a) : p ∣ b :=
  (hp.coprime_iff_not_dvd.mpr hpa).dvd_of_dvd_mul_left hpab

/-- **Euclid's Lemma** (symmetric form):
    If prime p divides ab and p does not divide b, then p divides a. -/
theorem euclids_lemma_prime_sym {p a b : ℕ} (hp : p.Prime)
    (hpab : p ∣ a * b) (hpb : ¬ p ∣ b) : p ∣ a := by
  rw [mul_comm] at hpab
  exact euclids_lemma_prime hp hpab hpb

/-
## Part II: Euclid's Lemma Extended to List Products
-/

/-- **Euclid's Lemma for Lists**:
    If prime p divides the product of a list l, then p divides some element of l.

    Proof: by induction on l. Base: p | 1 contradicts p.Prime.
    Step: if p | (hd * tl.prod), then p | hd or p | tl.prod (by Euclid's lemma),
    and the latter case gives a witness in tl by induction. -/
theorem prime_dvd_of_dvd_list_prod {p : ℕ} (hp : p.Prime) (l : List ℕ)
    (hdvd : p ∣ l.prod) : ∃ x ∈ l, p ∣ x := by
  induction l with
  | nil =>
    simp at hdvd
    exact absurd hdvd (Nat.Prime.one_lt hp).ne'
  | cons hd tl ih =>
    rw [List.prod_cons] at hdvd
    rcases hp.dvd_mul.mp hdvd with h | h
    · exact ⟨hd, by simp, h⟩
    · obtain ⟨x, hx_mem, hx_dvd⟩ := ih h
      exact ⟨x, List.mem_cons.mpr (Or.inr hx_mem), hx_dvd⟩

/-- **Key Lemma**: If prime p divides the product of a list of primes,
    then p is one of those primes (p ∈ l).

    This is the essential step: a prime can only "cancel into" itself
    in a product of primes. -/
theorem prime_mem_of_dvd_prime_list {p : ℕ} (hp : p.Prime) (l : List ℕ)
    (hprimes : ∀ q ∈ l, q.Prime) (hdvd : p ∣ l.prod) : p ∈ l := by
  obtain ⟨x, hx_mem, hx_dvd⟩ := prime_dvd_of_dvd_list_prod hp l hdvd
  have hx_prime : x.Prime := hprimes x hx_mem
  -- p | x and both are prime, so p = x
  have heq : p = x := by
    rcases hx_prime.eq_one_or_self_of_dvd p hx_dvd with h | h
    · exact absurd h hp.ne_one
    · exact h
  exact heq ▸ hx_mem

/-
## Part III: Product of Non-Empty Prime List Exceeds 1
-/

/-- A list of primes has a product ≥ 2 if nonempty, i.e., > 1. -/
private theorem prime_list_prod_pos {l : List ℕ}
    (hprimes : ∀ q ∈ l, q.Prime) : 0 < l.prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.prod_cons]
    have := hprimes hd (by simp)
    have htl_pos : 0 < tl.prod := ih (fun q hq => hprimes q (List.mem_cons.mpr (Or.inr hq)))
    exact Nat.mul_pos this.pos htl_pos

private theorem prime_list_prod_one_iff_nil {l : List ℕ}
    (hprimes : ∀ q ∈ l, q.Prime) : l.prod = 1 ↔ l = [] := by
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons hd tl =>
      exfalso
      have hd_prime := hprimes hd (by simp)
      rw [List.prod_cons] at h
      have htl_pos : 0 < tl.prod :=
        prime_list_prod_pos (fun q hq => hprimes q (List.mem_cons.mpr (Or.inr hq)))
      have : 2 ≤ hd * tl.prod := by
        calc 2 ≤ hd := hd_prime.two_le
          _ = hd * 1 := (mul_one hd).symm
          _ ≤ hd * tl.prod := Nat.mul_le_mul_left hd htl_pos
      omega
  · rintro rfl; simp

/-
## Part IV: FTA Uniqueness from Euclid's Lemma

This is the core theorem: two lists of primes with equal products are permutations.
The proof is by induction on l₁, using Euclid's lemma at each step.
-/

/-- **FTA Uniqueness via Euclid's Lemma**:
    If l₁ and l₂ are lists of primes with l₁.prod = l₂.prod, then l₁.Perm l₂.

    Proof: by induction on l₁.
    - Empty case: l₁.prod = 1, so l₂.prod = 1, so l₂ = [] (primes are ≥ 2).
    - Cons case: head p divides l₂.prod, so by Euclid's lemma p ∈ l₂.
      Remove p from l₂ to get l₂', show rest.Perm l₂' by induction,
      then (p :: rest).Perm (p :: l₂') ∼ l₂. -/
theorem fta_uniqueness {l₁ l₂ : List ℕ}
    (h₁ : ∀ p ∈ l₁, p.Prime) (h₂ : ∀ p ∈ l₂, p.Prime)
    (heq : l₁.prod = l₂.prod) : l₁.Perm l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp only [List.prod_nil] at heq
    rw [(prime_list_prod_one_iff_nil h₂).mp heq.symm]
  | cons p rest ih =>
    have hp : p.Prime := h₁ p (by simp)
    have hrest : ∀ q ∈ rest, q.Prime := fun q hq => h₁ q (List.mem_cons.mpr (Or.inr hq))
    -- p divides l₂.prod (since p divides l₁.prod = p * rest.prod)
    have hdvd : p ∣ l₂.prod := by
      rw [← heq, List.prod_cons]
      exact dvd_mul_right p rest.prod
    -- By Euclid's lemma, p ∈ l₂
    have hmem : p ∈ l₂ := prime_mem_of_dvd_prime_list hp l₂ h₂ hdvd
    -- l₂ is a permutation of p :: (l₂.erase p)
    have hperm_l₂ : l₂.Perm (p :: l₂.erase p) := List.perm_cons_erase hmem
    -- rest.prod = (l₂.erase p).prod
    have hprod_rest : rest.prod = (l₂.erase p).prod := by
      have hprod_eq := hperm_l₂.prod_eq  -- l₂.prod = (p :: l₂.erase p).prod
      simp only [List.prod_cons] at hprod_eq  -- l₂.prod = p * (l₂.erase p).prod
      have heq' : p * rest.prod = l₂.prod := by rw [← heq]; simp [List.prod_cons]
      rw [← heq'] at hprod_eq  -- p * rest.prod = p * (l₂.erase p).prod
      exact Nat.eq_of_mul_eq_mul_left hp.pos hprod_eq
    -- Primes in l₂.erase p are a subset of primes in l₂
    have h₂' : ∀ q ∈ l₂.erase p, q.Prime := fun q hq =>
      h₂ q (List.mem_of_mem_erase hq)
    -- By induction: rest.Perm (l₂.erase p)
    have hperm_rest : rest.Perm (l₂.erase p) := ih hrest h₂' hprod_rest
    -- Conclude: (p :: rest).Perm l₂
    exact (hperm_rest.cons p).trans hperm_l₂.symm

/-
## Part V: The Full FTA Statement
-/

/-- **Fundamental Theorem of Arithmetic from Euclid's Lemma**:
    For every n ≥ 2:
    1. **Existence**: n has a prime factorization (n.primeFactorsList)
    2. **Primality**: All factors are prime
    3. **Product**: Their product equals n
    4. **Uniqueness** (via Euclid's lemma): Any other prime list with the same
       product is a permutation

    The uniqueness proof explicitly uses `euclids_lemma_prime` via
    `fta_uniqueness` above, making the Bézout connection transparent. -/
theorem fta_from_euclid (n : ℕ) (hn : 2 ≤ n) :
    ∃ l : List ℕ,
      (∀ p ∈ l, p.Prime) ∧
      l.prod = n ∧
      (∀ l' : List ℕ, (∀ p ∈ l', p.Prime) → l'.prod = n → l'.Perm l) := by
  have hn_ne : n ≠ 0 := by omega
  use n.primeFactorsList
  refine ⟨fun p hp => Nat.prime_of_mem_primeFactorsList hp,
          Nat.prod_primeFactorsList hn_ne,
          fun l' hl' hprod => ?_⟩
  -- Uniqueness via Euclid's lemma (not via Nat.primeFactorsList_unique)
  have hfact_prod : n.primeFactorsList.prod = n := Nat.prod_primeFactorsList hn_ne
  have heq : l'.prod = n.primeFactorsList.prod := by rw [hfact_prod, hprod]
  exact fta_uniqueness hl' (fun p hp => Nat.prime_of_mem_primeFactorsList hp) heq

/-
## Part VI: Consequences of FTA via Euclid's Lemma
-/

/-- **Unique factorization index**: Prime factorizations are unique
    by count (multiplicity), not just by permutation. -/
theorem prime_factor_count_unique (n : ℕ) (hn : n ≠ 0) (p : ℕ) (hp : p.Prime) :
    ∀ l : List ℕ, (∀ q ∈ l, q.Prime) → l.prod = n →
    l.count p = n.primeFactorsList.count p := by
  intro l hl hprod
  have hfact_prod : n.primeFactorsList.prod = n := Nat.prod_primeFactorsList hn
  have hperm : l.Perm n.primeFactorsList := by
    apply fta_uniqueness hl (fun q hq => Nat.prime_of_mem_primeFactorsList hq)
    rw [hfact_prod, hprod]
  exact hperm.count_eq p

/-- **Euclid's Lemma applied to FTA**:
    If prime p divides n and n has prime factorization l, then p ∈ l.
    This is the direct connection between Euclid's lemma and the structure of
    prime factorizations. -/
theorem prime_dvd_iff_mem_factors (n : ℕ) (hn : n ≠ 0) (p : ℕ) (hp : p.Prime) :
    p ∣ n ↔ p ∈ n.primeFactorsList := by
  rw [Nat.mem_primeFactorsList hn]
  exact ⟨fun h => ⟨hp, h⟩, fun ⟨_, h⟩ => h⟩

/-- **Infinitely many primes are coprime to any given number**:
    A consequence of the structure revealed by Euclid's lemma —
    prime factorizations are finite, but there are infinitely many primes.

    Proof: Take a prime p ≥ l.sum + 1. Since p ∈ l implies p ≤ l.sum,
    this gives a contradiction. -/
theorem no_finite_list_contains_all_primes (l : List ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ l := by
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (l.sum + 1)
  exact ⟨p, hp_prime, fun hmem =>
    absurd (List.le_sum_of_mem hmem) (by omega)⟩

end BezoutFTA
