import Mathlib

/-!
# A Uniform Power-of-Two Obstruction for Constructibility (OQ-02)

## Open Question

The parent entry *"Wantzel-Galois Constructibility from Mathlib Galois Theory"*
(`AngleTrisectionOQ02OQ01OQ02`) proves the three classical impossibility
results — angle trisection (`cos 20°`), doubling the cube (`∛2`), and the
regular 7-gon (`cos 2π/7`) — but each is dispatched by its **own** ad-hoc
`interval_cases k <;> simp_all` argument that `3 ≠ 2 ^ k`.  This raises the
question:

> Is there a single, reusable arithmetic criterion that subsumes all of the
> classical degree obstructions at once, and that applies identically to the
> *degree* side (Wantzel necessity) and the *Galois-group-order* side
> (sufficiency, the `wantzel_galois_iff` direction left open in the parent)?

## Answer

Yes.  The whole content of "degree `d` is not a power of two" is the single
fact **`d` has an odd prime factor**.  We isolate this as
`not_isPowTwo_of_odd_prime_dvd` and derive everything from it:

* the full characterization `IsPowTwo d ↔ (every prime factor of d is 2)`;
* the corollary that an odd `d > 1` is never a power of two;
* the **degree obstruction** `not_degreePowerOfTwo_of_odd_prime_dvd`, which
  uniformly recovers the three classical degree-3 impossibilities (and extends
  for free to degree 5, e.g. the regular 11-gon, and any odd-prime degree);
* the **Galois-side mirror** `not_isTwoGroup_of_odd_prime_dvd`: the very same
  lemma shows a group whose order is divisible by an odd prime is not a
  2-group, which is the obstruction the *sufficiency* half of the
  Wantzel–Galois criterion turns on.

Both the Wantzel degree predicate `DegreePowerOfTwo` and the Galois 2-group
predicate `IsTwoGroup` are *definitionally* `IsPowTwo` applied to a natural
number (`p.natDegree` resp. `Fintype.card G`), so a single arithmetic lemma
serves both, making the parent's three separate proofs instances of one fact.

0 axioms, 0 sorries.

## References
- Wantzel (1837): *Recherches sur les moyens de reconnaître si un problème
  de géométrie peut se résoudre avec la règle et le compas.*
- Mathlib: `Nat.eq_prime_pow_of_unique_prime_dvd`, `Nat.prime_dvd_prime_iff_eq`,
  `Nat.Prime.dvd_of_dvd_pow`.
-/

set_option linter.unusedVariables false

namespace AngleTrisectionOQ02OQ01OQ02OQ02

open Polynomial

-- ============================================================
-- PART 1: The power-of-two predicate and its core obstruction
-- ============================================================

/-- A natural number is a **power of two** if `d = 2 ^ k` for some `k`. -/
def IsPowTwo (d : ℕ) : Prop := ∃ k : ℕ, d = 2 ^ k

theorem isPowTwo_one : IsPowTwo 1 := ⟨0, rfl⟩

theorem isPowTwo_two : IsPowTwo 2 := ⟨1, rfl⟩

theorem isPowTwo_pow (k : ℕ) : IsPowTwo (2 ^ k) := ⟨k, rfl⟩

/-- **Core obstruction.**  If an odd prime `q` divides `d`, then `d` is not a
    power of two.  This single fact is the arithmetic heart of every classical
    compass-and-straightedge impossibility proof. -/
theorem not_isPowTwo_of_odd_prime_dvd {d q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ d) : ¬ IsPowTwo d := by
  rintro ⟨k, rfl⟩
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd))

/-- **Characterization.**  A positive natural number is a power of two iff its
    only prime factor is `2`. -/
theorem isPowTwo_iff_unique_prime_two {d : ℕ} (hd : d ≠ 0) :
    IsPowTwo d ↔ ∀ q, q.Prime → q ∣ d → q = 2 := by
  constructor
  · rintro ⟨k, rfl⟩ q hq hdvd
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hdvd)
  · intro h
    exact ⟨d.primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd hd (fun {q} hq hqd => h q hq hqd)⟩

/-- An odd number greater than one is never a power of two. -/
theorem not_isPowTwo_of_odd_gt_one {d : ℕ} (hodd : Odd d) (hgt : 1 < d) :
    ¬ IsPowTwo d := by
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨m, hm⟩ := hodd        -- d = 2 * m + 1
    obtain ⟨c, hc⟩ := hqd         -- d = 2 * c
    omega
  exact not_isPowTwo_of_odd_prime_dvd hq hq2 hqd

-- Concrete instances reused by the applications below.

theorem not_isPowTwo_three : ¬ IsPowTwo 3 :=
  not_isPowTwo_of_odd_prime_dvd (by norm_num) (by norm_num) (dvd_refl 3)

theorem not_isPowTwo_five : ¬ IsPowTwo 5 :=
  not_isPowTwo_of_odd_prime_dvd (by norm_num) (by norm_num) (dvd_refl 5)

theorem not_isPowTwo_six : ¬ IsPowTwo 6 :=
  not_isPowTwo_of_odd_prime_dvd (by norm_num) (by norm_num) (show (3 : ℕ) ∣ 6 by norm_num)

-- ============================================================
-- PART 2: Wantzel degree side
-- ============================================================

/-- A polynomial's degree is a power of two — the Wantzel necessary condition
    for a root to be constructible. -/
def DegreePowerOfTwo (p : ℚ[X]) : Prop := IsPowTwo p.natDegree

/-- **Uniform degree obstruction.**  If the degree of `p` has an odd prime
    factor, then `p` fails the Wantzel power-of-two test.  By Wantzel's
    criterion any root of such an irreducible `p` is non-constructible. -/
theorem not_degreePowerOfTwo_of_odd_prime_dvd {p : ℚ[X]} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ p.natDegree) :
    ¬ DegreePowerOfTwo p :=
  not_isPowTwo_of_odd_prime_dvd hq hq2 hdvd

/-- Odd-degree (> 1) polynomials never satisfy the Wantzel condition. -/
theorem not_degreePowerOfTwo_of_odd_degree {p : ℚ[X]}
    (hodd : Odd p.natDegree) (hgt : 1 < p.natDegree) : ¬ DegreePowerOfTwo p :=
  not_isPowTwo_of_odd_gt_one hodd hgt

/-- **Degree-3 obstruction** — the uniform replacement for the parent's three
    separate proofs.  Covers angle trisection (`cos 20°`), doubling the cube
    (`∛2`), and the regular 7-gon (`cos 2π/7`), each of whose minimal
    polynomials has degree `3`. -/
theorem not_degreePowerOfTwo_of_natDegree_three {p : ℚ[X]}
    (h : p.natDegree = 3) : ¬ DegreePowerOfTwo p := by
  rw [DegreePowerOfTwo, h]; exact not_isPowTwo_three

/-- **Degree-5 obstruction** — a *new* case the parent does not cover, e.g. the
    regular 11-gon, whose `cos(2π/11)` has a degree-5 minimal polynomial. -/
theorem not_degreePowerOfTwo_of_natDegree_five {p : ℚ[X]}
    (h : p.natDegree = 5) : ¬ DegreePowerOfTwo p := by
  rw [DegreePowerOfTwo, h]; exact not_isPowTwo_five

-- ============================================================
-- PART 3: Galois-group side (the sufficiency mirror)
-- ============================================================

/-- A finite group is a **2-group** if its order is a power of two — the
    Galois-theoretic condition appearing in the Wantzel–Galois criterion. -/
def IsTwoGroup (G : Type*) [Group G] [Fintype G] : Prop :=
  IsPowTwo (Fintype.card G)

/-- **Galois-side mirror of the obstruction.**  A finite group whose order is
    divisible by an odd prime is not a 2-group — the *same* arithmetic lemma
    that drives the degree obstruction, now driving the group obstruction that
    the sufficiency half of `wantzel_galois_iff` rests on. -/
theorem not_isTwoGroup_of_odd_prime_dvd {G : Type*} [Group G] [Fintype G]
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ Fintype.card G) :
    ¬ IsTwoGroup G :=
  not_isPowTwo_of_odd_prime_dvd hq hq2 hdvd

/-- `IsTwoGroup` is exactly `IsPowTwo` of the order, by definition; recorded
    here to make the link between the two predicates explicit. -/
theorem isTwoGroup_iff_isPowTwo_card {G : Type*} [Group G] [Fintype G] :
    IsTwoGroup G ↔ IsPowTwo (Fintype.card G) := Iff.rfl

/-- By Cauchy's theorem, the obstruction is witnessed concretely: whenever a
    prime `q` divides `|G|`, the group contains an element of order `q`.  Applied
    to an odd prime divisor of `|G|`, this exhibits a concrete element whose
    existence is incompatible with `G` being a 2-group. -/
theorem exists_orderOf_eq_of_prime_dvd_card {G : Type*} [Group G] [Fintype G]
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Fintype.card G) :
    ∃ g : G, orderOf g = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact exists_prime_orderOf_dvd_card q hdvd

-- ============================================================
-- PART 4: Summary
-- ============================================================

/-
## Summary of Results (0 axioms, 0 sorries)

### Arithmetic core
1. `not_isPowTwo_of_odd_prime_dvd` — the single obstruction lemma.
2. `isPowTwo_iff_unique_prime_two` — full characterization of powers of two.
3. `not_isPowTwo_of_odd_gt_one` — odd `d > 1` is never a power of two.

### Wantzel degree side
4. `not_degreePowerOfTwo_of_odd_prime_dvd` / `_of_odd_degree` — uniform criterion.
5. `not_degreePowerOfTwo_of_natDegree_three` — one proof covering trisection,
   cube doubling, and the regular 7-gon (all degree 3).
6. `not_degreePowerOfTwo_of_natDegree_five` — new degree-5 case (regular 11-gon).

### Galois group side
7. `not_isTwoGroup_of_odd_prime_dvd` — same lemma, group-order version.
8. `isTwoGroup_iff_isPowTwo_card` — the two predicates share one arithmetic core.
9. `exists_orderOf_eq_of_prime_dvd_card` — Cauchy witness for the obstruction.

### Contribution
Refactors the parent's three independent degree arguments into instances of a
single reusable obstruction lemma, extends it to new degrees, and exhibits the
identical lemma governing the Galois-group-order side of the Wantzel–Galois
criterion — clarifying *why* "power of two" is the shared invariant on both
sides of the constructibility characterization.
-/

#check @not_isPowTwo_of_odd_prime_dvd
#check @not_degreePowerOfTwo_of_natDegree_three
#check @not_isTwoGroup_of_odd_prime_dvd

end AngleTrisectionOQ02OQ01OQ02OQ02
