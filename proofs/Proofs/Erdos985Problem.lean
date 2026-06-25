/-
Erdős Problem #985: Prime Primitive Roots

Is it true that, for every prime p, there is a prime q < p which is a
primitive root modulo p?

**Status**: OPEN - This conjecture remains unresolved.

**Background**:
- A primitive root modulo p is an integer g such that ord_p(g) = p - 1
- This means g generates the multiplicative group (ℤ/pℤ)×
- Artin conjectured that any non-square integer is a primitive root for
  infinitely many primes (still unproven unconditionally)
- Hooley (1967) proved Artin's conjecture assuming GRH
- Heath-Brown (1986) proved unconditionally that at least one of 2, 3, or 5
  is a primitive root for infinitely many primes

Reference: https://erdosproblems.com/985
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/- ## Primitive Roots -/

/-- A primitive root modulo p is an element whose multiplicative order is p - 1.
    This means it generates the entire multiplicative group (ℤ/pℤ)×. -/
def isPrimitiveRoot (g : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ orderOf (g : ZMod p) = p - 1

/-- A prime q is a prime primitive root modulo p if q < p and q is a primitive root. -/
def isPrimePrimitiveRoot (q : ℕ) (p : ℕ) : Prop :=
  q.Prime ∧ q < p ∧ isPrimitiveRoot q p

/-- The set of primes that have a prime primitive root less than themselves. -/
def primesWithPrimePrimitiveRoot : Set ℕ :=
  {p : ℕ | p.Prime ∧ p ≠ 2 ∧ ∃ q, isPrimePrimitiveRoot q p}

/- ## Basic Properties of Primitive Roots -/

/-- The multiplicative group `(ℤ/pℤ)ˣ` of a finite prime field is cyclic.
    Proved via Mathlib's instance for finite fields. -/
theorem zmod_units_cyclic (p : ℕ) (hp : p.Prime) :
    IsCyclic (ZMod p)ˣ := by
  haveI : Fact p.Prime := ⟨hp⟩
  infer_instance

/-- **Every prime `p` has a primitive root in the range `0 < g < p`.**

    This is the *unconditional* counterpart of Erdős 985: the existence of a
    primitive root below `p` is automatic, because `(ℤ/pℤ)ˣ` is cyclic of order
    `p - 1`, so a generator exists and its canonical representative lies in
    `{1, …, p-1}`. The entire difficulty of Erdős 985 is therefore concentrated
    in the single extra requirement that the witness `g` be **prime** — this
    theorem strips that requirement away and shows the rest is free.

    Proof: take a generator `u` of `(ℤ/pℤ)ˣ` (cyclicity), so `orderOf u = p - 1`
    by `orderOf_eq_card_of_forall_mem_zpowers` together with `ZMod.card_units`.
    Its underlying value `g := (u : ZMod p).val` satisfies `0 < g < p` (it is a
    unit, hence nonzero, and `val < p`), and
    `orderOf (g : ZMod p) = orderOf u = p - 1` via `orderOf_units`. -/
theorem exists_primitiveRoot_lt (p : ℕ) (hp : p.Prime) :
    ∃ g : ℕ, 0 < g ∧ g < p ∧ orderOf (g : ZMod p) = p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf u = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card,
      ZMod.card_units p]
  set g : ℕ := (u : ZMod p).val with hg
  have hcast : (g : ZMod p) = (u : ZMod p) := by rw [hg, ZMod.natCast_zmod_val]
  refine ⟨g, ?_, ZMod.val_lt _, ?_⟩
  · have hne : (g : ZMod p) ≠ 0 := by rw [hcast]; exact u.ne_zero
    refine Nat.pos_of_ne_zero (fun h0 => hne ?_)
    rw [h0, Nat.cast_zero]
  · rw [hcast, orderOf_units, hord]

/- ## Small Prime Examples

   The multiplicative order of a concrete element is *not* evaluable by
   `decide`/`native_decide` (Mathlib's `orderOf` carries no executable code).
   Instead we rewrite with `orderOf_eq_iff`, which reduces `orderOf x = n` to
   the *bounded*, decidable claim `x ^ n = 1 ∧ ∀ m < n, 0 < m → x ^ m ≠ 1`;
   powers in `ZMod p` are computable, so `decide` closes each goal. -/

/-- Example: 2 is a primitive root modulo 3.  ord_3(2) = 2 = 3 - 1. -/
theorem primitiveRoot_2_mod_3 : orderOf (2 : ZMod 3) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- Example: 2 is a primitive root modulo 5.  ord_5(2) = 4 = 5 - 1. -/
theorem primitiveRoot_2_mod_5 : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- Example: 3 is a primitive root modulo 7.  ord_7(3) = 6 = 7 - 1. -/
theorem primitiveRoot_3_mod_7 : orderOf (3 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- Example: 2 is NOT a primitive root modulo 7.  ord_7(2) = 3 ≠ 6. -/
theorem not_primitiveRoot_2_mod_7 : orderOf (2 : ZMod 7) ≠ 6 := by
  have h : orderOf (2 : ZMod 7) = 3 := by rw [orderOf_eq_iff (by norm_num)]; decide
  omega

/-- Example: 3 is **not** a primitive root modulo 11: ord_11(3) = 5 ≠ 10,
    since 3^5 = 1 (mod 11). This illustrates exactly the subtlety of Erdős 985 —
    not every prime `q < p` is a primitive root, so finding a *prime* witness
    is a genuine constraint. (Here 2 works instead; see the next lemma.) -/
theorem orderOf_3_mod_11 : orderOf (3 : ZMod 11) = 5 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- Example: 2 is a primitive root modulo 11.  ord_11(2) = 10 = 11 - 1. -/
theorem primitiveRoot_2_mod_11 : orderOf (2 : ZMod 11) = 10 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- Example: 2 is a primitive root modulo 13.  ord_13(2) = 12 = 13 - 1. -/
theorem primitiveRoot_2_mod_13 : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- Example: 5 is a primitive root modulo 23.  ord_23(5) = 22 = 23 - 1. -/
theorem primitiveRoot_5_mod_23 : orderOf (5 : ZMod 23) = 22 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/- ## Verification of Erdős Conjecture for Small Primes -/

/-- For p = 3: q = 2 is a prime primitive root (ord_3(2) = 2). -/
theorem erdos985_for_3 : ∃ q : ℕ, q.Prime ∧ q < 3 ∧ orderOf (q : ZMod 3) = 2 :=
  ⟨2, Nat.prime_two, by norm_num, by rw [orderOf_eq_iff (by norm_num)]; decide⟩

/-- For p = 5: q = 2 is a prime primitive root (ord_5(2) = 4). -/
theorem erdos985_for_5 : ∃ q : ℕ, q.Prime ∧ q < 5 ∧ orderOf (q : ZMod 5) = 4 :=
  ⟨2, Nat.prime_two, by norm_num, by rw [orderOf_eq_iff (by norm_num)]; decide⟩

/-- For p = 7: q = 3 is a prime primitive root (ord_7(3) = 6). -/
theorem erdos985_for_7 : ∃ q : ℕ, q.Prime ∧ q < 7 ∧ orderOf (q : ZMod 7) = 6 :=
  ⟨3, Nat.prime_three, by norm_num, by rw [orderOf_eq_iff (by norm_num)]; decide⟩

/-- For p = 11: q = 2 is a prime primitive root (ord_11(2) = 10). -/
theorem erdos985_for_11 : ∃ q : ℕ, q.Prime ∧ q < 11 ∧ orderOf (q : ZMod 11) = 10 :=
  ⟨2, Nat.prime_two, by norm_num, by rw [orderOf_eq_iff (by norm_num)]; decide⟩

/-- For p = 13: q = 2 is a prime primitive root (ord_13(2) = 12). -/
theorem erdos985_for_13 : ∃ q : ℕ, q.Prime ∧ q < 13 ∧ orderOf (q : ZMod 13) = 12 :=
  ⟨2, Nat.prime_two, by norm_num, by rw [orderOf_eq_iff (by norm_num)]; decide⟩

/-- For p = 23: q = 5 is a prime primitive root (ord_23(5) = 22). -/
theorem erdos985_for_23 : ∃ q : ℕ, q.Prime ∧ q < 23 ∧ orderOf (q : ZMod 23) = 22 :=
  ⟨5, by decide, by norm_num, by rw [orderOf_eq_iff (by norm_num)]; decide⟩

/- ## Artin's Conjecture and Related Results -/

/- Artin's Conjecture (1927): For any integer a ≠ -1, 0, 1 that is not a
   perfect square, there are infinitely many primes p for which a is a
   primitive root modulo p.  This is still open unconditionally, but Hooley
   proved it assuming GRH. -/

/-- Heath-Brown's Theorem (1986): At least one of 2, 3, or 5 is a primitive
    root for infinitely many primes. This is an unconditional result. -/
axiom heath_brown_theorem :
    Set.Infinite {p : ℕ | p.Prime ∧
      (orderOf (2 : ZMod p) = p - 1 ∨
       orderOf (3 : ZMod p) = p - 1 ∨
       orderOf (5 : ZMod p) = p - 1)}

/- ## Main Conjecture -/

/-- Erdős Problem #985 Conjecture: For every prime p > 2, there exists a
    prime q < p which is a primitive root modulo p.

    Status: OPEN

    This is a stronger statement than asking whether there exists ANY
    primitive root less than p (which is always true, see
    `exists_primitiveRoot_lt`). Erdős asks specifically for a PRIME primitive
    root.

    The conjecture has been verified computationally for small primes,
    but a proof or counterexample remains elusive. -/
axiom erdos_985_conjecture :
    ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1

/-- Alternative formulation: the set of "good" primes (those with a prime
    primitive root) equals all odd primes. -/
theorem erdos_985_iff_all_odd_primes :
    (∀ (p : ℕ), p.Prime → p ≠ 2 → ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1) ↔
    primesWithPrimePrimitiveRoot = {p : ℕ | p.Prime ∧ p ≠ 2} := by
  constructor
  · intro h
    ext p
    simp only [primesWithPrimePrimitiveRoot, isPrimePrimitiveRoot, isPrimitiveRoot,
               Set.mem_setOf_eq]
    constructor
    · intro ⟨hp, hp2, _⟩
      exact ⟨hp, hp2⟩
    · intro ⟨hp, hp2⟩
      refine ⟨hp, hp2, ?_⟩
      obtain ⟨q, hq_prime, hq_lt, hq_ord⟩ := h p hp hp2
      exact ⟨q, hq_prime, hq_lt, hp, hp2, hq_ord⟩
  · intro h p hp hp2
    have : p ∈ primesWithPrimePrimitiveRoot := by
      rw [h]
      exact ⟨hp, hp2⟩
    simp only [primesWithPrimePrimitiveRoot, isPrimePrimitiveRoot, isPrimitiveRoot,
               Set.mem_setOf_eq] at this
    obtain ⟨_, _, q, hq_prime, hq_lt, _, _, hq_ord⟩ := this
    exact ⟨q, hq_prime, hq_lt, hq_ord⟩

/- ## Density Considerations -/

/- Among the primitive roots modulo p, the proportion that are prime is roughly
   1/log(p) by the prime number theorem. Since there are φ(p-1) primitive roots
   among 1,...,p-1, we expect roughly φ(p-1)/log(p) prime primitive roots. For p
   large enough, this is > 0, suggesting the conjecture should hold. -/

/- ## Connection to Other Problems -/

/- **Caveat on Artin's conjecture.** It is tempting to claim that the
   *qualitative* Artin conjecture — "each prime `q` is a primitive root for
   infinitely many primes `p`" — implies Erdős 985. It does **not**: knowing
   that each fixed `q` is a primitive root for infinitely many `p` says nothing
   about whether *some* prime `q < p` is a primitive root for a *given* `p`.
   Bridging that gap requires an *effective* (Linnik-type) version of Artin
   bounding the least such `p` in terms of `q`, which is not available
   unconditionally. We therefore do **not** state a spurious
   `artin_implies_erdos_985`; instead we extract the genuine unconditional
   consequence of Heath-Brown's theorem below. -/

/-- A prime `q ∈ {2, 3, 5}` that is a primitive root modulo `p` (with `p > 5`,
    so that `q < p`) witnesses Erdős 985 at `p`. This is the elementary engine
    that turns Heath-Brown's `{2, 3, 5}` covering into actual cases of Erdős
    985. -/
theorem erdos985_of_heathBrown_witness (p : ℕ) (_hp : p.Prime) (hp5 : 5 < p)
    (h : orderOf (2 : ZMod p) = p - 1 ∨ orderOf (3 : ZMod p) = p - 1 ∨
         orderOf (5 : ZMod p) = p - 1) :
    ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  rcases h with h2 | h3 | h5
  · exact ⟨2, Nat.prime_two, by omega, h2⟩
  · exact ⟨3, Nat.prime_three, by omega, h3⟩
  · exact ⟨5, by decide, by omega, h5⟩

/-- **Heath-Brown's theorem yields infinitely many primes satisfying Erdős 985.**

    For every prime `p > 5` in the Heath-Brown set, one of `2, 3, 5` is a prime
    primitive root below `p`, so Erdős 985 holds at `p`. Since the Heath-Brown
    set is infinite and we discard only the finitely many primes `≤ 5`, the set
    of primes confirmed to satisfy Erdős 985 is itself infinite.

    This is the honest unconditional progress available toward Erdős 985: not a
    proof of the full conjecture (which remains the axiom `erdos_985_conjecture`),
    but a verified derivation of infinitely many of its instances from the
    Heath-Brown axiom alone. -/
theorem infinitely_many_erdos985_primes :
    Set.Infinite {p : ℕ | p.Prime ∧
      ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1} := by
  have hHB := heath_brown_theorem
  have hsub :
      ({p : ℕ | p.Prime ∧
          (orderOf (2 : ZMod p) = p - 1 ∨ orderOf (3 : ZMod p) = p - 1 ∨
           orderOf (5 : ZMod p) = p - 1)} \ {p : ℕ | p ≤ 5})
        ⊆ {p : ℕ | p.Prime ∧
            ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1} := by
    rintro p ⟨⟨hp, hcov⟩, hle⟩
    simp only [Set.mem_setOf_eq, not_le] at hle ⊢
    exact ⟨hp, erdos985_of_heathBrown_witness p hp hle hcov⟩
  exact Set.Infinite.mono hsub (hHB.diff (Set.finite_le_nat 5))

/- ## Summary -/

/-- Summary of Erdős Problem #985:

    **Question**: For every prime p > 2, does there exist a prime q < p
    that is a primitive root modulo p?

    **Status**: OPEN

    **Verified for**: p = 3, 5, 7, 11, 13, 23, and many more computationally

    **Related Results**:
    - Artin's Conjecture (conditional on GRH via Hooley)
    - Heath-Brown's unconditional result for {2, 3, 5}, from which we derive
      infinitely many confirmed instances (`infinitely_many_erdos985_primes`)

    **Heuristic**: Should be true based on prime number theorem estimates -/
theorem erdos_985_summary :
    -- Verified for several small primes
    (∃ q : ℕ, q.Prime ∧ q < 3 ∧ orderOf (q : ZMod 3) = 2) ∧
    (∃ q : ℕ, q.Prime ∧ q < 5 ∧ orderOf (q : ZMod 5) = 4) ∧
    (∃ q : ℕ, q.Prime ∧ q < 7 ∧ orderOf (q : ZMod 7) = 6) ∧
    (∃ q : ℕ, q.Prime ∧ q < 11 ∧ orderOf (q : ZMod 11) = 10) ∧
    (∃ q : ℕ, q.Prime ∧ q < 13 ∧ orderOf (q : ZMod 13) = 12) ∧
    -- Heath-Brown's result holds
    Set.Infinite {p : ℕ | p.Prime ∧
      (orderOf (2 : ZMod p) = p - 1 ∨
       orderOf (3 : ZMod p) = p - 1 ∨
       orderOf (5 : ZMod p) = p - 1)} :=
  ⟨erdos985_for_3, erdos985_for_5, erdos985_for_7, erdos985_for_11,
   erdos985_for_13, heath_brown_theorem⟩
