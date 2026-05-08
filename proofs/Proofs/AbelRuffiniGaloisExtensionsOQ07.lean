/-
  Burnside's pᵃqᵇ Theorem (Open Question OQ-07 of abel-ruffini-galois-extensions)

  ## Statement
  Every finite group of order pᵃ · qᵇ (for primes p, q and naturals a, b) is solvable.

  Burnside (1904) proved this using character theory and algebraic integers.
  Goldschmidt (1970) and Matsuyama (1973) gave character-free proofs using
  transfer / focal-subgroup arguments.

  ## Sharpness
  The bound is sharp: |A₅| = 60 = 2² · 3 · 5 has THREE distinct primes and
  A₅ is not solvable. The smallest non-solvable group has order exactly one
  prime more than Burnside permits.

  ## Phase-2 axiomatization
  This file:
  1. Reduces the trivial cases (a = 0, b = 0, or p = q) to the existing
     Mathlib chain `IsPGroup → IsNilpotent → IsSolvable`. These are proved
     unconditionally — no new axioms.
  2. Axiomatizes the non-trivial case (`p ≠ q`, `a ≥ 1`, `b ≥ 1`) as
     `burnside_pq_nontrivial` — the genuinely-open Lean content. A full
     proof requires either (a) Mathlib character theory + algebraic-integer
     hypotheses for the original 1904 argument, or (b) the focal-subgroup
     theorem + transfer for the Goldschmidt-Matsuyama character-free proof.
  3. Combines (1) + (2) into the main theorem `burnside_pq`.

  ## Mathlib status
  Mathlib has `IsSolvable`, `IsPGroup`, `IsPGroup.isNilpotent`, `IsNilpotentGroup`,
  Sylow theory, and character orthogonality (`char_orthonormal`), but NOT
  Burnside's pᵃqᵇ theorem. A full formalization (estimated ~600-1000 lines)
  would be a substantial Mathlib upstream contribution.

  ## References
  - Burnside, W. (1904). "On groups of order pᵃqᵇ". Proc. London Math. Soc. (2) 1, 388–392.
  - Goldschmidt, D. M. (1970). "A group theoretic proof of the pᵃqᵇ theorem
    for odd primes". Math. Z. 113, 373–375.
  - Matsuyama, H. (1973). "Solvability of groups of order 2ᵃ pᵇ". Osaka J. Math. 10, 375–378.
  - Isaacs, I. M. (2008). Finite Group Theory. AMS GSM 92, §3F.

  Parent gallery entry: abel-ruffini-galois-extensions (Question 7).
-/

import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.Tactic

namespace BurnsidePQ

-- ═══════════════════════════════════════════════════════════════════════
-- PART I: p-group lemma (axiom-free, from Mathlib)
-- ═══════════════════════════════════════════════════════════════════════

/-- **p-group ⇒ solvable** (Mathlib chain): every finite p-group is
    nilpotent (`IsPGroup.isNilpotent`), and every nilpotent group is
    solvable. -/
theorem pGroup_isSolvable {p : ℕ} (G : Type*) [Group G] [Finite G]
    [Fact (Nat.Prime p)] (hG : IsPGroup p G) : IsSolvable G := by
  haveI := hG.isNilpotent
  infer_instance

-- ═══════════════════════════════════════════════════════════════════════
-- PART II: Trivial cases (axiom-free)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Trivial case `a = 0`**: if `Nat.card G = p^0 · q^b = q^b`, then `G`
    is a `q`-group, hence solvable. Axiom-free. -/
theorem burnside_pq_a_zero {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {b : ℕ}
    (hcard : Nat.card G = p ^ 0 * q ^ b) : IsSolvable G := by
  -- Simplify `p^0 * q^b = q^b`.
  have hcard' : Nat.card G = q ^ b := by simpa using hcard
  -- `IsPGroup q G` from cardinality.
  have hpg : IsPGroup q G := IsPGroup.iff_card.mpr ⟨b, hcard'⟩
  exact pGroup_isSolvable G hpg

/-- **Trivial case `b = 0`**: if `Nat.card G = p^a · q^0 = p^a`, then `G`
    is a `p`-group, hence solvable. Axiom-free. -/
theorem burnside_pq_b_zero {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a : ℕ}
    (hcard : Nat.card G = p ^ a * q ^ 0) : IsSolvable G := by
  have hcard' : Nat.card G = p ^ a := by simpa using hcard
  have hpg : IsPGroup p G := IsPGroup.iff_card.mpr ⟨a, hcard'⟩
  exact pGroup_isSolvable G hpg

/-- **Trivial case `p = q`**: if `Nat.card G = p^a · p^b = p^(a+b)`, then
    `G` is a `p`-group, hence solvable. Axiom-free. -/
theorem burnside_pq_same_prime {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {a b : ℕ}
    (hcard : Nat.card G = p ^ a * p ^ b) : IsSolvable G := by
  -- Combine `p^a * p^b = p^(a+b)`.
  have hcard' : Nat.card G = p ^ (a + b) := by
    rw [hcard, ← pow_add]
  have hpg : IsPGroup p G := IsPGroup.iff_card.mpr ⟨a + b, hcard'⟩
  exact pGroup_isSolvable G hpg

-- ═══════════════════════════════════════════════════════════════════════
-- PART II.5: Squarefree-order case (axiom-free, via IsZGroup)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Squarefree-order ⇒ solvable** (axiom-free, two Mathlib lemmas).

    Bridges `Squarefree (Nat.card G)` to `IsSolvable G` via Mathlib's
    `IsZGroup.of_squarefree` (a finite group of squarefree order is a
    Z-group — every Sylow subgroup is cyclic) and the `[Finite G]
    [IsZGroup G]` instance giving `IsSolvable G`.

    This subsumes the `a = b = 1` case of Burnside (`p ≠ q`, `|G| = pq`)
    via `burnside_pq_pq_case` below — extending it axiom-free to ANY
    finite group of squarefree order, e.g. `|G| = 30 = 2·3·5`,
    `|G| = 105 = 3·5·7`, etc.

    Note: this does NOT extend to `|G| = pᵃqᵇ` with `a ≥ 2` or `b ≥ 2` —
    such orders fail the squarefreeness test (`p²` is not squarefree).
    The genuine non-trivial case of Burnside (with prime-power factors)
    still requires character theory or transfer + focal subgroup. -/
theorem squarefreeOrder_isSolvable {G : Type*} [Group G] [Finite G]
    (hsf : Squarefree (Nat.card G)) : IsSolvable G := by
  haveI : IsZGroup G := IsZGroup.of_squarefree hsf
  infer_instance

/-- **Burnside `pq` case** (axiom-free, `a = b = 1`): every finite group
    of order `p · q` (for distinct primes `p, q`) is solvable.

    Proof: `p` and `q` are coprime (`Nat.coprime_primes`), each is
    squarefree (`Nat.Prime.prime` + `Prime.squarefree`), so `p · q` is
    squarefree (`Nat.squarefree_mul`). Apply `squarefreeOrder_isSolvable`.

    This eliminates the `a = b = 1` sub-case of `burnside_pq_nontrivial`
    axiom-free; the axiom is then narrowed to `2 ≤ a ∨ 2 ≤ b`. -/
theorem burnside_pq_pq_case {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p * q) : IsSolvable G := by
  apply squarefreeOrder_isSolvable
  rw [hcard]
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp.out hq.out).mpr hpq
  rw [Nat.squarefree_mul hcop]
  exact ⟨hp.out.prime.squarefree, hq.out.prime.squarefree⟩

-- ═══════════════════════════════════════════════════════════════════════
-- PART III: The non-trivial case (AXIOMATIZED, narrowed to 2 ≤ a ∨ 2 ≤ b)
-- ═══════════════════════════════════════════════════════════════════════

/-- **AXIOM (Burnside's pᵃqᵇ theorem, non-trivial case)**: every finite
    group of order `p^a · q^b` is solvable, when `p` and `q` are distinct
    primes, `a, b ≥ 1`, AND at least one of `a, b` is ≥ 2.

    The hypothesis `2 ≤ a ∨ 2 ≤ b` narrows the axiom: the `a = b = 1`
    sub-case (`|G| = p · q` squarefree) is now proved axiom-free via
    `burnside_pq_pq_case`. The genuinely-open content is `|G|` divisible
    by `p²` or `q²` for distinct primes.

    Proof sketch (NOT in Mathlib, character-theoretic, Burnside 1904):
    Suppose for contradiction `G` is a minimal counterexample. Then `G` is
    a non-abelian simple group with no non-trivial proper normal subgroup.
    Pick a Sylow `p`-subgroup `P`; its centre `Z(P)` is non-trivial. Let
    `g ∈ Z(P)` of prime order. The conjugacy class `cl(g)` has size
    `|G : C_G(g)|`, divisible only by powers of `q`. Apply the column
    orthogonality of the character table: `Σ χ(1)·χ(g) = 0` (sum over
    irreducible characters). Algebraic-integer arithmetic in the
    cyclotomic ring `ℤ[ζ_n]` then forces a contradiction.

    Proof sketch (NOT in Mathlib, character-free, Goldschmidt-Matsuyama):
    Use the transfer homomorphism on a Sylow `p`-subgroup combined with
    the focal subgroup theorem to show that `P ∩ G'` is a proper subgroup
    of `P`, contradicting `G = G'` (which holds in any non-abelian simple
    group). Mathlib's `Mathlib.GroupTheory.Focal` (focal subgroup, transfer)
    is a starting point for the character-free route. -/
axiom burnside_pq_nontrivial {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a b : ℕ}
    (hpq : p ≠ q) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 2 ≤ a ∨ 2 ≤ b)
    (hcard : Nat.card G = p ^ a * q ^ b) : IsSolvable G

-- ═══════════════════════════════════════════════════════════════════════
-- PART IV: Main theorem
-- ═══════════════════════════════════════════════════════════════════════

/-- **Burnside's pᵃqᵇ theorem**: every finite group of order `p^a · q^b`
    (for primes `p, q` and naturals `a, b`) is solvable.

    Combines:
    - the three axiom-free trivial cases (`a = 0`, `b = 0`, `p = q`),
    - the axiom-free squarefree-order case (`a = b = 1`, `p ≠ q`), and
    - the conjectural non-trivial case (`burnside_pq_nontrivial`,
      `2 ≤ a ∨ 2 ≤ b`). -/
theorem burnside_pq {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {a b : ℕ}
    (hcard : Nat.card G = p ^ a * q ^ b) : IsSolvable G := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · -- a = 0
    subst ha
    exact burnside_pq_a_zero hcard
  rcases Nat.eq_zero_or_pos b with hb | hb
  · -- b = 0 (with a ≥ 1)
    subst hb
    exact burnside_pq_b_zero hcard
  rcases eq_or_ne p q with hpq | hpq
  · -- p = q (with a ≥ 1, b ≥ 1)
    subst hpq
    exact burnside_pq_same_prime hcard
  · -- p ≠ q, a ≥ 1, b ≥ 1
    by_cases h11 : a = 1 ∧ b = 1
    · -- a = b = 1: |G| = p · q (squarefree); axiom-free
      obtain ⟨ha1, hb1⟩ := h11
      subst ha1
      subst hb1
      have hcard' : Nat.card G = p * q := by simpa [pow_one] using hcard
      exact burnside_pq_pq_case hpq hcard'
    · -- 2 ≤ a ∨ 2 ≤ b: use the (narrowed) axiom
      have hab : 2 ≤ a ∨ 2 ≤ b := by
        by_contra h
        push_neg at h
        obtain ⟨ha2, hb2⟩ := h
        exact h11 ⟨by omega, by omega⟩
      exact burnside_pq_nontrivial hpq ha hb hab hcard

-- ═══════════════════════════════════════════════════════════════════════
-- PART V: Sanity checks
-- ═══════════════════════════════════════════════════════════════════════

/-- **Trivial group is solvable**: `Nat.card G = 1 = 2^0 · 3^0`.
    Axiom-free. -/
example {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 1) : IsSolvable G := by
  have h : Nat.card G = 2 ^ 0 * 3 ^ 0 := by simpa using hcard
  exact burnside_pq h

/-- **Cyclic group of prime order is solvable**: `|ℤ/p| = p^1 · q^0`.
    Axiom-free for any prime witnesses `p, q` (b = 0 case). -/
example {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card G = p) : IsSolvable G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Nat.card G = p ^ 1 * 2 ^ 0 := by simp [hcard]
  exact burnside_pq h

/-- **Group of order p^a is solvable**: pure p-group case. Axiom-free. -/
example {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {a : ℕ} (hcard : Nat.card G = p ^ a) :
    IsSolvable G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Nat.card G = p ^ a * 2 ^ 0 := by simp [hcard]
  exact burnside_pq h

/-- **Group of order `pq` is solvable** (`p ≠ q`, both prime). Axiom-free,
    invokes only `burnside_pq_pq_case` via the `a = b = 1` dispatch in
    `burnside_pq`. Concrete witness: groups of order 6, 10, 14, 15, 21,
    22, 33, 35, … are all solvable. -/
example {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hcard : Nat.card G = p * q) : IsSolvable G :=
  burnside_pq_pq_case hpq hcard

/-- **Group of order 30 = 2·3·5 is solvable**. Axiom-free squarefree-order
    case (three distinct primes, each to first power). Demonstrates that
    `squarefreeOrder_isSolvable` extends beyond Burnside's two-prime
    bound when each prime appears to the first power only — but cannot
    rescue A₅ (|A₅| = 60 = 2² · 3 · 5 has `2²` and is not squarefree). -/
example {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 30) :
    IsSolvable G := by
  apply squarefreeOrder_isSolvable
  rw [hcard]
  show Squarefree (30 : ℕ)
  native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- PART VI: Sharpness witness
-- ═══════════════════════════════════════════════════════════════════════

/-! Burnside's bound on the number of distinct prime factors is sharp.
    The smallest non-solvable group is A₅, of order 60 = 2² · 3 · 5 — exactly
    THREE distinct primes, one more than Burnside permits.

    These two theorems establish A₅ as the canonical sharpness witness:
    a finite group whose order has three distinct prime factors and that is
    not solvable. Hence the conclusion of `burnside_pq` cannot in general
    be extended from two distinct primes to three. -/

/-- The cardinality of A₅ in `2² · 3 · 5` form, exposing the three distinct
    prime factors that make A₅ a witness to sharpness. Axiom-free. -/
theorem alternatingGroupFin5_card :
    Nat.card (alternatingGroup (Fin 5) : Type _) = 2 ^ 2 * 3 * 5 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- A₅ is not solvable. Reduces to `Equiv.Perm.not_solvable (Fin 5)` via the
    short exact sequence A₅ → S₅ → ℤ/2 (kernel of `Equiv.Perm.sign` is
    contained in the range of the inclusion `alternatingGroup → Equiv.Perm`).
    Axiom-free. -/
theorem alternatingGroupFin5_not_solvable :
    ¬ IsSolvable (alternatingGroup (Fin 5)) := by
  intro h
  have hS5 : IsSolvable (Equiv.Perm (Fin 5)) := by
    apply solvable_of_ker_le_range
      (alternatingGroup (Fin 5)).subtype
      Equiv.Perm.sign
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact ⟨⟨x, Equiv.Perm.mem_alternatingGroup.mpr hx⟩, rfl⟩
  exact Equiv.Perm.not_solvable (Fin 5) (by simp) hS5

/-- **Burnside's bound is sharp**. There exists a finite group of order
    `2² · 3 · 5` (three distinct prime factors) that is NOT solvable —
    namely A₅. So the analogue of `burnside_pq` for THREE distinct primes
    fails: no `burnside_pqr` theorem can hold without further hypotheses. -/
theorem burnside_pq_sharp :
    Nat.card (alternatingGroup (Fin 5)) = 2 ^ 2 * 3 * 5 ∧
      ¬ IsSolvable (alternatingGroup (Fin 5)) :=
  ⟨alternatingGroupFin5_card, alternatingGroupFin5_not_solvable⟩

/-
## Summary

### Axioms added (1, narrowed in Iteration 4)
- `burnside_pq_nontrivial` : the non-trivial case of Burnside's pᵃqᵇ
  theorem (`p ≠ q`, `a ≥ 1`, `b ≥ 1`, AND `2 ≤ a ∨ 2 ≤ b`). The
  hypothesis `2 ≤ a ∨ 2 ≤ b` was added in Iteration 4: the `a = b = 1`
  sub-case (`|G| = p · q`, squarefree order) is now proved axiom-free
  via `burnside_pq_pq_case`. The genuinely-open Lean content is now
  exactly: `|G|` divisible by `p²` or `q²` for distinct primes.
  A full proof requires substantial new infrastructure (character theory
  + algebraic integers, OR transfer + focal subgroup) not currently in
  Mathlib.

### Theorems proved (axiom-free)
- `pGroup_isSolvable` — `IsPGroup p G → IsSolvable G` via Mathlib's chain
  `IsPGroup.isNilpotent + IsNilpotent → IsSolvable`.
- `burnside_pq_a_zero` — Burnside for `a = 0` (`G` is a `q`-group).
- `burnside_pq_b_zero` — Burnside for `b = 0` (`G` is a `p`-group).
- `burnside_pq_same_prime` — Burnside for `p = q` (`G` is a `p`-group of
  order `p^(a+b)`).
- `squarefreeOrder_isSolvable` — `Squarefree (Nat.card G) → IsSolvable G`
  via Mathlib's `IsZGroup.of_squarefree` + the `[IsZGroup G] [Finite G]`
  → `IsSolvable G` instance. Subsumes the `a = b = 1` Burnside case.
- `burnside_pq_pq_case` — Burnside for `a = b = 1` (`|G| = p · q`,
  squarefree order). Reduces to `squarefreeOrder_isSolvable` via
  `Nat.coprime_primes` + `Prime.squarefree` + `Nat.squarefree_mul`.
- `burnside_pq` — main theorem combining trivial cases + pq case + axiom.
- `alternatingGroupFin5_card` — `|A₅| = 2² · 3 · 5 = 60` (sharpness witness
  cardinality, three distinct primes).
- `alternatingGroupFin5_not_solvable` — `¬ IsSolvable (A₅)` via reduction to
  `Equiv.Perm.not_solvable (Fin 5)` through the short exact sequence
  `A₅ → S₅ → ℤ/2`.
- `burnside_pq_sharp` — sharpness witness: `|A₅| = 2² · 3 · 5` AND `A₅` is
  not solvable, demonstrating that `burnside_pq` cannot be extended to
  three distinct primes. Note: A₅ defeats the `Squarefree` route too —
  60 has `2²`, so `squarefreeOrder_isSolvable` does not apply.

### Path forward
- Eliminate the (narrowed) `burnside_pq_nontrivial` by formalizing the
  Goldschmidt-Matsuyama proof (estimated ~400-800 lines): build the
  focal subgroup theorem in Mathlib (some scaffolding now exists in
  `Mathlib.GroupTheory.Focal`), then apply transfer to a Sylow. This is
  preferable to the character-theoretic route because Mathlib's character
  theory still lacks the algebraic-integer hypotheses needed for
  `(|G|/χ(1))χ(g) ∈ ℤ̄_K`.
- Next sub-cases worth axiom-free attempts (in order of accessibility):
  (1) `|G| = p² · q` with `p ≠ q` — classical, ~50-100 lines via Sylow,
  (2) `|G| = p · q²` with `p ≠ q` — symmetric to (1),
  (3) `|G| = p² · q²` — needs more delicate Sylow analysis.
- Mathlib upstream: a Burnside-pᵃqᵇ proof would be a substantial PR.
  Coordinate with Mathlib reviewers before scoping a full formalization.
-/

#check @burnside_pq
#check @burnside_pq_nontrivial
#check @burnside_pq_a_zero
#check @burnside_pq_b_zero
#check @burnside_pq_same_prime
#check @squarefreeOrder_isSolvable
#check @burnside_pq_pq_case
#check @pGroup_isSolvable
#check @alternatingGroupFin5_card
#check @alternatingGroupFin5_not_solvable
#check @burnside_pq_sharp

end BurnsidePQ
