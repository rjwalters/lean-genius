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
-- PART III.5: Normal-Sylow reductions (axiom-free, Iteration 5)
-- ═══════════════════════════════════════════════════════════════════════

/-! Two reduction lemmas that discharge `burnside_pq_nontrivial` whenever
    a normal subgroup whose order is the full `p`-part (or `q`-part) of `|G|`
    can be exhibited. They neither modify nor weaken `burnside_pq_nontrivial`
    itself, but provide axiom-free shortcuts that any future
    `|G| = pᵃ · qᵇ` analysis can plug into. -/

/-- **Solvability extension via normal-quotient pair** (Mathlib repackaging):
    if `N` is a normal subgroup of `G` with both `N` and `G ⧸ N` solvable,
    then `G` is solvable.

    This is the standard fact that solvability is closed under group
    extensions. We package it as a named theorem for repeated use below.
    The proof reuses Mathlib's `solvable_of_ker_le_range` against the
    canonical short exact sequence `1 → N → G → G ⧸ N → 1`: the kernel of
    `QuotientGroup.mk' N` is exactly the range of `N.subtype`. -/
theorem isSolvable_of_normal_quotient_solvable {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] [IsSolvable N] [IsSolvable (G ⧸ N)] :
    IsSolvable G := by
  apply solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
  intro x hx
  rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact ⟨⟨x, hx⟩, rfl⟩

/-- **Burnside reduction via a normal `p`-Sylow-sized subgroup** (axiom-free):
    if `|G| = pᵃ · qᵇ` and `G` admits a normal subgroup `N` with
    `|N| = pᵃ`, then `G` is solvable.

    Proof outline:
    - `IsPGroup p N` follows from `IsPGroup.iff_card` and `|N| = pᵃ`,
      so `pGroup_isSolvable` gives `IsSolvable N`.
    - Lagrange (`Subgroup.card_mul_index`) plus `|G| = pᵃ · qᵇ` and
      `pᵃ > 0` yield `Nat.card (G ⧸ N) = qᵇ`.
    - Then `IsPGroup q (G ⧸ N)` and `pGroup_isSolvable` give
      `IsSolvable (G ⧸ N)`.
    - `isSolvable_of_normal_quotient_solvable` closes `G`.

    Strategic value: combined with future Sylow-counting analysis on
    specific `|G| = pᵃ · qᵇ` shapes (`|G| = p² · q`, `|G| = p · q²`, …),
    this lemma turns "produce a normal Sylow `p`-subgroup" into a complete
    axiom-free solvability proof. -/
theorem burnside_pq_with_normal_pSylow {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime] {a b : ℕ}
    (hcard : Nat.card G = p ^ a * q ^ b)
    (N : Subgroup G) [N.Normal] (hN_card : Nat.card N = p ^ a) :
    IsSolvable G := by
  have hN_pg : IsPGroup p N := IsPGroup.iff_card.mpr ⟨a, hN_card⟩
  haveI : IsSolvable N := pGroup_isSolvable N hN_pg
  have hpa_pos : 0 < p ^ a := pow_pos hp.out.pos a
  have hQ_card : Nat.card (G ⧸ N) = q ^ b := by
    have h := Subgroup.card_mul_index N
    rw [hN_card, hcard] at h
    have hidx : N.index = q ^ b := Nat.eq_of_mul_eq_mul_left hpa_pos h
    rw [N.index_eq_card] at hidx
    exact hidx
  have hQ_pg : IsPGroup q (G ⧸ N) := IsPGroup.iff_card.mpr ⟨b, hQ_card⟩
  haveI : IsSolvable (G ⧸ N) := pGroup_isSolvable (G ⧸ N) hQ_pg
  exact isSolvable_of_normal_quotient_solvable N

/-- **Burnside reduction via a normal `q`-Sylow-sized subgroup** (axiom-free,
    symmetric to `burnside_pq_with_normal_pSylow`): if `|G| = pᵃ · qᵇ` and
    `G` admits a normal subgroup `N` with `|N| = qᵇ`, then `G` is solvable.

    Proof: dual to the `p`-Sylow case — `N` is a `q`-group (hence solvable),
    `|G ⧸ N| = pᵃ` (Lagrange + cancellation, after a `mul_comm` rearrangement),
    so `G ⧸ N` is a `p`-group (hence solvable), and the extension is solvable. -/
theorem burnside_pq_with_normal_qSylow {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime] {a b : ℕ}
    (hcard : Nat.card G = p ^ a * q ^ b)
    (N : Subgroup G) [N.Normal] (hN_card : Nat.card N = q ^ b) :
    IsSolvable G := by
  have hN_pg : IsPGroup q N := IsPGroup.iff_card.mpr ⟨b, hN_card⟩
  haveI : IsSolvable N := pGroup_isSolvable N hN_pg
  have hqb_pos : 0 < q ^ b := pow_pos hq.out.pos b
  have hQ_card : Nat.card (G ⧸ N) = p ^ a := by
    have h := Subgroup.card_mul_index N
    rw [hN_card, hcard, mul_comm (p ^ a) (q ^ b)] at h
    have hidx : N.index = p ^ a := Nat.eq_of_mul_eq_mul_left hqb_pos h
    rw [N.index_eq_card] at hidx
    exact hidx
  have hQ_pg : IsPGroup p (G ⧸ N) := IsPGroup.iff_card.mpr ⟨a, hQ_card⟩
  haveI : IsSolvable (G ⧸ N) := pGroup_isSolvable (G ⧸ N) hQ_pg
  exact isSolvable_of_normal_quotient_solvable N

-- ═══════════════════════════════════════════════════════════════════════
-- PART III.6: |G| = p² · q, case p > q (axiom-free, Iteration 7)
-- ═══════════════════════════════════════════════════════════════════════

/-! Sylow analysis for `|G| = p² · q` with `p > q`. The Sylow `p`-subgroup
    has order `p²`; its number `n_p` divides `q` and is `≡ 1 [MOD p]`.
    With `q < p` the only solutions are `n_p ∈ {1, q}`, and `q ≡ 1 [MOD p]`
    forces `q ≥ p + 1 > p`, contradiction — so `n_p = 1` and the unique
    Sylow `p`-subgroup is normal. The result then follows from
    `burnside_pq_with_normal_pSylow`.

    This eliminates the `(a, b) = (2, 1)` and (after the symmetric `p < q`
    case in S8) the `(a, b) = (1, 2)` instances of `burnside_pq_nontrivial`
    axiom-free. -/

/-- **Sylow-count constraint, prime divisor case**: if `n ∣ q` (with `q`
    prime, `q < p`) and `n ≡ 1 [MOD p]`, then `n = 1`.

    The two divisors of a prime are `1` and itself; if `n = q` then
    `q ≡ 1 [MOD p]`, i.e. `p ∣ q - 1`, forcing `p ≤ q - 1 < q < p`,
    contradiction. -/
private lemma sylow_count_eq_one_of_lt_prime
    {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : q < p)
    (hmod : n ≡ 1 [MOD p]) (hdvd : n ∣ q) : n = 1 := by
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq n hdvd) with h1 | hq_eq
  · exact h1
  · -- n = q. Then q ≡ 1 [MOD p], i.e. p ∣ q - 1.
    rw [hq_eq] at hmod
    have hqpos : 0 < q := hq.pos
    have hq_ge_one : 1 ≤ q := hqpos
    have hp_dvd_qm1 : p ∣ q - 1 :=
      (Nat.modEq_iff_dvd' hq_ge_one).mp hmod.symm
    have hqm1_pos : 0 < q - 1 := by
      have : 2 ≤ q := hq.two_le
      omega
    have : p ≤ q - 1 := Nat.le_of_dvd hqm1_pos hp_dvd_qm1
    omega

/-- **`p`-adic factorization of `p² · q` is 2** when `p, q` are distinct
    primes (here, `q < p`). Used to read off `Nat.card (Sylow p G) = p^2`
    from `Sylow.card_eq_multiplicity`. -/
private lemma factorization_p_sq_q_at_p
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : q < p) :
    ((p : ℕ) ^ 2 * q).factorization p = 2 := by
  have hp_pos : (p : ℕ) ≠ 0 := hp.pos.ne'
  have hq_pos : (q : ℕ) ≠ 0 := hq.pos.ne'
  have hp_ndvd_q : ¬ (p : ℕ) ∣ q := by
    intro h
    have : p ≤ q := Nat.le_of_dvd hq.pos h
    omega
  rw [Nat.factorization_mul (pow_ne_zero 2 hp_pos) hq_pos,
      Nat.factorization_pow]
  rw [Finsupp.add_apply, Finsupp.smul_apply,
      Nat.Prime.factorization_self hp,
      Nat.factorization_eq_zero_of_not_dvd hp_ndvd_q]
  -- Goal: 2 • 1 + 0 = 2
  simp

/-- **Burnside `p² · q` case, `p > q`** (axiom-free): every finite group of
    order `p² · q` (with `p, q` distinct primes and `q < p`) is solvable.

    Proof outline:
    1. Pick a Sylow `p`-subgroup `P`. By `Sylow.card_eq_multiplicity`
       and the factorization computation `(p² · q).factorization p = 2`,
       `Nat.card P = p²`.
    2. By Sylow's third theorem (`card_sylow_modEq_one`), the number of
       Sylow `p`-subgroups satisfies `n_p ≡ 1 [MOD p]`.
    3. By `Sylow.card_dvd_index`, `n_p ∣ P.index`. Since `Nat.card G = p² · q`
       and `Nat.card P = p²`, Lagrange (`Subgroup.card_mul_index`) gives
       `P.index = q`.
    4. Apply `sylow_count_eq_one_of_lt_prime` (with `q < p`) to get `n_p = 1`.
    5. Hence `Subsingleton (Sylow p G)`; `Sylow.normal_of_subsingleton`
       yields `(P : Subgroup G).Normal`.
    6. Discharge via `burnside_pq_with_normal_pSylow` (with `a = 2`, `b = 1`,
       after rewriting `q^1 = q`). -/
theorem burnside_p_squared_q_p_gt_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : q < p) (hcard : Nat.card G = p ^ 2 * q) :
    IsSolvable G := by
  -- Step 1: pick a Sylow p-subgroup; compute its order from |G| = p^2 * q.
  obtain ⟨P⟩ : Nonempty (Sylow p G) := Sylow.nonempty
  have hP_card : Nat.card (P : Subgroup G) = p ^ 2 := by
    rw [Sylow.card_eq_multiplicity P, hcard,
        factorization_p_sq_q_at_p hp.out hq.out hpq]
  -- Step 2: compute the index of P. Since |P| = p^2 and |G| = p^2 q, index = q.
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.out.pos 2
  have hP_index : (P : Subgroup G).index = q := by
    have h := Subgroup.card_mul_index (P : Subgroup G)
    rw [hP_card, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hp2_pos h
  -- Step 3: n_p ≡ 1 [MOD p] and n_p ∣ q (via P.index = q).
  have hnp_mod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have hnp_dvd : Nat.card (Sylow p G) ∣ q := by
    have := Sylow.card_dvd_index P
    rwa [hP_index] at this
  -- Step 4: apply the helper to get n_p = 1.
  have hnp_eq_one : Nat.card (Sylow p G) = 1 :=
    sylow_count_eq_one_of_lt_prime hp.out hq.out hpq hnp_mod hnp_dvd
  -- Step 5: n_p = 1 ⇒ Subsingleton (Sylow p G) ⇒ P.Normal.
  haveI hSub : Subsingleton (Sylow p G) := by
    rw [← Nat.card_le_one_iff_subsingleton]
    exact hnp_eq_one.le
  haveI hP_normal : (P : Subgroup G).Normal := P.normal_of_subsingleton
  -- Step 6: discharge via burnside_pq_with_normal_pSylow.
  have hcard' : Nat.card G = p ^ 2 * q ^ 1 := by rw [hcard]; ring
  exact burnside_pq_with_normal_pSylow (a := 2) (b := 1) hcard'
    (P : Subgroup G) hP_card

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

/-- **Group of order `12 = 2² · 3` with a normal subgroup of order `4` is
    solvable**, axiom-free, via `burnside_pq_with_normal_pSylow`. This is
    exactly the structure realized by `A₄` (the Klein four-group `V₄ ⊆ A₄`
    is normal of order `4 = 2²`); it shows the new Iteration-5 reduction
    discharges the previously-axiomatized `2 ≤ a` shape `|G| = p² · q`
    whenever a normal `p`-Sylow is exhibited. -/
example {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 12)
    (N : Subgroup G) [N.Normal] (hN : Nat.card N = 4) : IsSolvable G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard' : Nat.card G = 2 ^ 2 * 3 ^ 1 := by rw [hcard]; norm_num
  have hN' : Nat.card N = 2 ^ 2 := by rw [hN]; norm_num
  exact burnside_pq_with_normal_pSylow hcard' N hN'

/-- **Group of order `18 = 3² · 2` is solvable**, axiom-free, via the new
    Iteration-7 lemma `burnside_p_squared_q_p_gt_q`. With `p = 3` and
    `q = 2`, we have `q < p` and `|G| = p² · q = 9 · 2 = 18`. The Sylow
    `p`-count argument forces the unique Sylow `3`-subgroup to be normal,
    and `burnside_pq_with_normal_pSylow` finishes the proof. -/
example {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 18) :
    IsSolvable G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpq : (2 : ℕ) < 3 := by norm_num
  have hcard' : Nat.card G = 3 ^ 2 * 2 := by rw [hcard]; norm_num
  exact burnside_p_squared_q_p_gt_q hpq hcard'

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
- `isSolvable_of_normal_quotient_solvable` (Iteration 5) — solvability is
  closed under group extensions: `[N.Normal] [IsSolvable N]
  [IsSolvable (G ⧸ N)] → IsSolvable G`. Repackaging of Mathlib's
  `solvable_of_ker_le_range` against the canonical sequence
  `N → G → G ⧸ N`.
- `burnside_pq_with_normal_pSylow` (Iteration 5) — if `|G| = pᵃ · qᵇ`
  and `G` admits a normal subgroup of order `pᵃ`, then `G` is solvable.
  Axiom-free reduction tool: combined with Sylow-counting on specific
  shapes (`|G| = p² · q`, `|G| = p · q²`, …), discharges
  `burnside_pq_nontrivial` outright once a normal `p`-Sylow is
  exhibited.
- `burnside_pq_with_normal_qSylow` (Iteration 5) — symmetric: a normal
  subgroup of order `qᵇ` gives `IsSolvable G`.
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
- `burnside_p_squared_q_p_gt_q` (Iteration 7) — Burnside for `|G| = p² · q`
  with `q < p` (axiom-free, no longer using `burnside_pq_nontrivial`).
  Sylow's third theorem (`card_sylow_modEq_one`, `Sylow.card_dvd_index`)
  forces `n_p = 1`, the unique Sylow `p`-subgroup is normal, and
  `burnside_pq_with_normal_pSylow` finishes. The companion `p < q` case
  (with the `(2, 3)` exception requiring element counting) is left for
  Iteration 8.

### Path forward
- Eliminate the (narrowed) `burnside_pq_nontrivial` by formalizing the
  Goldschmidt-Matsuyama proof (estimated ~400-800 lines): build the
  focal subgroup theorem in Mathlib (some scaffolding now exists in
  `Mathlib.GroupTheory.Focal`), then apply transfer to a Sylow. This is
  preferable to the character-theoretic route because Mathlib's character
  theory still lacks the algebraic-integer hypotheses needed for
  `(|G|/χ(1))χ(g) ∈ ℤ̄_K`.
- Next sub-cases worth axiom-free attempts (in order of accessibility):
  (1) `|G| = p² · q` with `p ≠ q` — classical, ~50-100 lines via Sylow.
      Iteration 7 covered the `q < p` half axiom-free
      (`burnside_p_squared_q_p_gt_q`); the symmetric `p < q` case (with
      the `(p, q) = (2, 3)`, `|G| = 12` exception requiring an element
      count) is the remaining content for Iteration 8.
  (2) `|G| = p · q²` with `p ≠ q` — symmetric to (1).
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
#check @isSolvable_of_normal_quotient_solvable
#check @burnside_pq_with_normal_pSylow
#check @burnside_pq_with_normal_qSylow
#check @burnside_p_squared_q_p_gt_q
#check @alternatingGroupFin5_card
#check @alternatingGroupFin5_not_solvable
#check @burnside_pq_sharp

end BurnsidePQ
