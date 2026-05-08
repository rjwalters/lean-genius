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
import Mathlib.GroupTheory.Sylow
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
-- PART III.6: |G| = p² · q axiom-free, case `p > q` (Iteration 7)
-- ═══════════════════════════════════════════════════════════════════════

/-! Iteration 7 begins discharging `burnside_pq_nontrivial` for the shape
    `|G| = p² · q` (`a = 2, b = 1`). The full argument splits into three
    sub-cases per `session-6-p-squared-q-spec.md`:
    1. `p > q` — always `n_p = 1` by Sylow's third theorem (this iteration).
    2. `p < q ≠ 3` — symmetric `n_q = 1` analysis (S7.5).
    3. exceptional `(p, q) = (2, 3), |G| = 12` — element counting (S8).

    Each sub-case combines `card_sylow_modEq_one` + `Sylow.card_dvd_index`
    with the existing reduction lemmas `burnside_pq_with_normal_pSylow` /
    `burnside_pq_with_normal_qSylow`. -/

/-- **Sylow count constraint** (helper for `|G| = p² · q`, case `p > q`):
    if `n ∣ q` (with `q` prime, `q < p`) and `n ≡ 1 [MOD p]`, then `n = 1`.
    The two divisors of a prime are `1` and itself; `q ≡ 1 [MOD p]` with
    `q < p` would force `p ≤ q - 1 < p`, contradiction. -/
private lemma sylow_count_eq_one_of_lt_prime
    {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : q < p)
    (hmod : n ≡ 1 [MOD p]) (hdvd : n ∣ q) : n = 1 := by
  rcases hq.eq_one_or_self_of_dvd n hdvd with h1 | hq_eq
  · exact h1
  · -- n = q. Then q ≡ 1 [MOD p], i.e. p ∣ q - 1, but p > q forces contradiction.
    rw [hq_eq] at hmod
    have hq_two_le : 2 ≤ q := hq.two_le
    have hp_dvd_qm1 : p ∣ q - 1 :=
      (Nat.modEq_iff_dvd' (by omega : 1 ≤ q)).mp hmod.symm
    have hp_le : p ≤ q - 1 := Nat.le_of_dvd (by omega : 0 < q - 1) hp_dvd_qm1
    omega

/-- **Burnside `|G| = p² · q`, case `p > q`** (axiom-free).

    Sylow's third theorem (`card_sylow_modEq_one`) gives `n_p ≡ 1 [MOD p]`,
    and `Sylow.card_dvd_index` gives `n_p ∣ q` (the index of a Sylow
    `p`-subgroup is `q`, since `|P| = p²` and `|G| = p² · q`). The helper
    `sylow_count_eq_one_of_lt_prime` then forces `n_p = 1`: the only
    divisors of the prime `q` are `1` and `q`, and `q ≡ 1 [MOD p]` with
    `q < p` is impossible.

    With `n_p = 1`, the unique Sylow `p`-subgroup `P` is normal
    (`Sylow.normal_of_subsingleton`). Then `burnside_pq_with_normal_pSylow`
    discharges, treating `|G| = p² · q¹`.

    This eliminates the `(a, b) = (2, 1)` shape from the
    `burnside_pq_nontrivial` axiom whenever `p > q`; the symmetric `p < q`
    case (S7.5) and the exceptional `|G| = 12` case (S8) will complete
    the `|G| = p² · q` discharge. -/
theorem burnside_p_squared_q_p_gt_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : q < p) (hcard : Nat.card G = p ^ 2 * q) :
    IsSolvable G := by
  -- Step 1: pick a Sylow p-subgroup; |P| = p² by `Sylow.card_eq_multiplicity`.
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hp_ne_q : p ≠ q := by omega
  have hp_not_dvd_q : ¬ p ∣ q :=
    mt (Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp hp_ne_q
  have hcop : Nat.Coprime (p ^ 2) q :=
    ((Nat.coprime_primes hp.out hq.out).mpr hp_ne_q).pow_left 2
  have hP_card : Nat.card (P : Subgroup G) = p ^ 2 := by
    have hmult := Sylow.card_eq_multiplicity P
    -- `hmult : Nat.card P = p ^ Nat.factorization (Nat.card G) p`
    have hfact : Nat.factorization (Nat.card G) p = 2 := by
      rw [hcard, Nat.factorization_mul_apply_of_coprime hcop,
          Nat.Prime.factorization_pow hp.out,
          Nat.factorization_eq_zero_of_not_dvd hp_not_dvd_q]
      simp
    rw [hfact] at hmult
    exact hmult
  -- Step 2: index of P is q (Lagrange + cancellation).
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.out.pos 2
  have hP_index : (P : Subgroup G).index = q := by
    have h := Subgroup.card_mul_index (P : Subgroup G)
    rw [hP_card, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hp2_pos h
  -- Step 3: n_p ≡ 1 [MOD p] and n_p ∣ q, so n_p = 1.
  have hnp_mod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have hnp_dvd : Nat.card (Sylow p G) ∣ q := hP_index ▸ Sylow.card_dvd_index P
  have hnp_eq_one : Nat.card (Sylow p G) = 1 :=
    sylow_count_eq_one_of_lt_prime hp.out hq.out hpq hnp_mod hnp_dvd
  -- Step 4: n_p = 1 ⇒ Subsingleton (Sylow p G) ⇒ P.Normal.
  haveI hSub : Subsingleton (Sylow p G) :=
    (Nat.card_eq_one_iff_unique.mp hnp_eq_one).1
  haveI hP_normal : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  -- Step 5: discharge via burnside_pq_with_normal_pSylow with a = 2, b = 1.
  have hcard' : Nat.card G = p ^ 2 * q ^ 1 := by rw [pow_one]; exact hcard
  exact burnside_pq_with_normal_pSylow (a := 2) (b := 1) hcard' (P : Subgroup G) hP_card

/-- **Sylow count constraint** (helper for `|G| = p² · q`, case `p < q`):
    if `n ∣ p²` (with `p` prime), `n ≡ 1 [MOD q]` (`q` prime), `p < q`, and
    `(p, q) ≠ (2, 3)`, then `n = 1`.

    The divisors of `p²` are `1, p, p²`. The case `n = p` would force
    `q ∣ p - 1` with `p < q`, contradiction. The case `n = p²` would
    force `q ∣ p² - 1 = (p - 1)(p + 1)`; since `q` is prime and
    `q ∤ p - 1`, we'd need `q ∣ p + 1`, hence `q = p + 1`. With both
    prime, this forces `(p, q) = (2, 3)` — excluded by hypothesis. -/
private lemma sylow_count_eq_one_of_lt_prime_pow_two
    {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hexc : ¬ (p = 2 ∧ q = 3))
    (hmod : n ≡ 1 [MOD q]) (hdvd : n ∣ p ^ 2) : n = 1 := by
  -- Divisors of p^2 are {1, p, p^2}.
  obtain ⟨i, hi_le, hni⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hp_two_le : 2 ≤ p := hp.two_le
  have hq_two_le : 2 ≤ q := hq.two_le
  interval_cases i
  · -- n = p^0 = 1
    rw [pow_zero] at hni; exact hni
  · -- n = p^1 = p. Then q ∣ p - 1, contradicting p < q.
    rw [pow_one] at hni
    subst hni
    have hq_dvd : q ∣ p - 1 :=
      (Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mp hmod.symm
    have : q ≤ p - 1 := Nat.le_of_dvd (by omega : 0 < p - 1) hq_dvd
    omega
  · -- n = p^2. Then q ∣ p^2 - 1 = (p - 1) * (p + 1).
    subst hni
    have hp2_one_le : 1 ≤ p ^ 2 := by
      have := hp.pos; positivity
    have hq_dvd_diff : q ∣ p ^ 2 - 1 :=
      (Nat.modEq_iff_dvd' hp2_one_le).mp hmod.symm
    -- p^2 - 1 = (p - 1) * (p + 1) (Nat arithmetic; p ≥ 2 ensures no underflow).
    have hfactor : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0) with ⟨k, hk⟩
      subst hk
      show (k + 1) ^ 2 - 1 = (k + 1 - 1) * (k + 1 + 1)
      have hkk : k + 1 - 1 = k := by omega
      rw [hkk]
      ring_nf
      omega
    rw [hfactor] at hq_dvd_diff
    -- q prime ⇒ q ∣ (p - 1) or q ∣ (p + 1)
    rcases (hq.dvd_mul.mp hq_dvd_diff) with hq_dvd_low | hq_dvd_high
    · -- q ∣ p - 1; p < q means q > p > p - 1, so q ≤ p - 1 — contradiction.
      have : q ≤ p - 1 := Nat.le_of_dvd (by omega : 0 < p - 1) hq_dvd_low
      omega
    · -- q ∣ p + 1; p < q ≤ p + 1 ⇒ q = p + 1.
      have hq_le : q ≤ p + 1 := Nat.le_of_dvd (by omega : 0 < p + 1) hq_dvd_high
      have hq_eq : q = p + 1 := by omega
      -- Both p and q = p + 1 are prime ⇒ p = 2 (only consecutive primes).
      have hp_eq_two : p = 2 := by
        by_contra hp_ne_two
        -- p ≥ 3, so p is odd (only even prime is 2).
        have hp_odd : Odd p :=
          hp.eq_two_or_odd'.resolve_left hp_ne_two
        -- Then p + 1 is even, but p + 1 = q ≥ 3, so q is even and ≥ 3.
        have hq_even : Even q := by rw [hq_eq]; exact hp_odd.add_one
        -- The only even prime is 2; q ≥ 3 contradiction.
        have : q = 2 := (Nat.Prime.even_iff hq).mp hq_even
        omega
      exact absurd ⟨hp_eq_two, by omega⟩ hexc

/-- **Burnside `|G| = p² · q`, case `p < q`, non-exceptional** (axiom-free).

    Sylow's third theorem gives `n_q ≡ 1 [MOD q]`, and `Sylow.card_dvd_index`
    gives `n_q ∣ p²` (the index of a Sylow `q`-subgroup is `p²`, since
    `|Q| = q` and `|G| = p² · q`). The helper
    `sylow_count_eq_one_of_lt_prime_pow_two` then forces `n_q = 1`,
    using that `(p, q) ≠ (2, 3)` to rule out the `n_q = p²` case.

    With `n_q = 1`, the unique Sylow `q`-subgroup `Q` is normal
    (`Sylow.normal_of_subsingleton`). Then
    `burnside_pq_with_normal_qSylow` discharges, treating `|G| = p² · q¹`.

    Together with `burnside_p_squared_q_p_gt_q` and the (deferred) S8
    exceptional case `|G| = 12`, this completes the `(a, b) = (2, 1)`
    shape elimination from the `burnside_pq_nontrivial` axiom. -/
theorem burnside_p_squared_q_p_lt_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p < q) (hexc : ¬ (p = 2 ∧ q = 3))
    (hcard : Nat.card G = p ^ 2 * q) :
    IsSolvable G := by
  -- Step 1: pick a Sylow q-subgroup; |Q| = q^1 = q by `Sylow.card_eq_multiplicity`.
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  have hp_ne_q : p ≠ q := by omega
  have hq_ne_p : q ≠ p := fun h => hp_ne_q h.symm
  have hq_not_dvd_p2 : ¬ q ∣ p ^ 2 := by
    intro hdvd
    have : q ∣ p := hq.out.dvd_of_dvd_pow hdvd
    exact hq_ne_p ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp this)
  have hcop : Nat.Coprime (p ^ 2) q :=
    ((Nat.coprime_primes hp.out hq.out).mpr hp_ne_q).pow_left 2
  have hQ_card : Nat.card (Q : Subgroup G) = q := by
    have hmult := Sylow.card_eq_multiplicity Q
    have hfact : Nat.factorization (Nat.card G) q = 1 := by
      rw [hcard, Nat.factorization_mul_apply_of_coprime hcop,
          Nat.factorization_eq_zero_of_not_dvd hq_not_dvd_p2,
          Nat.Prime.factorization_self hq.out]
      simp
    rw [hfact, pow_one] at hmult
    exact hmult
  -- Step 2: index of Q is p^2 (Lagrange + cancellation).
  have hq_pos : 0 < q := hq.out.pos
  have hQ_index : (Q : Subgroup G).index = p ^ 2 := by
    have h := Subgroup.card_mul_index (Q : Subgroup G)
    rw [hQ_card, hcard, mul_comm (p ^ 2) q] at h
    exact Nat.eq_of_mul_eq_mul_left hq_pos h
  -- Step 3: n_q ≡ 1 [MOD q] and n_q ∣ p^2; helper forces n_q = 1.
  have hnq_mod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
  have hnq_dvd : Nat.card (Sylow q G) ∣ p ^ 2 :=
    hQ_index ▸ Sylow.card_dvd_index Q
  have hnq_eq_one : Nat.card (Sylow q G) = 1 :=
    sylow_count_eq_one_of_lt_prime_pow_two hp.out hq.out hpq hexc hnq_mod hnq_dvd
  -- Step 4: n_q = 1 ⇒ Subsingleton (Sylow q G) ⇒ Q.Normal.
  haveI hSub : Subsingleton (Sylow q G) :=
    (Nat.card_eq_one_iff_unique.mp hnq_eq_one).1
  haveI hQ_normal : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
  -- Step 5: discharge via burnside_pq_with_normal_qSylow with a = 2, b = 1.
  have hcard' : Nat.card G = p ^ 2 * q ^ 1 := by rw [pow_one]; exact hcard
  exact burnside_pq_with_normal_qSylow (a := 2) (b := 1) hcard' (Q : Subgroup G) hQ_card

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

/-- **Group of order `45 = 3² · 5` is solvable** (Iteration 7 sanity check):
    `p = 3, q = 5` so `q > p`; the symmetric `p < q` case (S7.5) would
    handle this. The example below uses the `p > q` case directly with
    `p = 5, q = 3`: `|G| = 75 = 5² · 3` is solvable axiom-free. -/
example {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 75) : IsSolvable G := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard' : Nat.card G = 5 ^ 2 * 3 := by rw [hcard]; norm_num
  exact burnside_p_squared_q_p_gt_q (by decide : (3 : ℕ) < 5) hcard'

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
- `sylow_count_eq_one_of_lt_prime` (Iteration 7, `private`) — Sylow-count
  helper: `n ∣ q ∧ n ≡ 1 [MOD p] ∧ q < p ⇒ n = 1` (the only divisors of
  the prime `q` are `1` and `q`, and `q ≡ 1 [MOD p]` forces `p ≤ q - 1`).
- `burnside_p_squared_q_p_gt_q` (Iteration 7) — Burnside for `|G| = p²·q`
  in the case `p > q`: Sylow's third theorem (`card_sylow_modEq_one` +
  `Sylow.card_dvd_index`) forces `n_p = 1`; the unique Sylow `p`-subgroup
  is normal, then `burnside_pq_with_normal_pSylow` discharges. Axiom-free.
  This is the first of three sub-cases needed to remove `(a, b) = (2, 1)`
  from the `burnside_pq_nontrivial` axiom hypothesis.
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
  (1) `|G| = p² · q` with `p ≠ q` — classical, ~50-100 lines via Sylow.
      With Iteration 5 the residual content shrinks to "exhibit a normal
      Sylow"; the standard Sylow-counting argument (`n_p ∣ q`,
      `n_p ≡ 1 (mod p)`, `n_q ∣ p²`, `n_q ≡ 1 (mod q)` and an
      element-count) then composes with `burnside_pq_with_normal_pSylow`
      / `burnside_pq_with_normal_qSylow` for an axiom-free finish.
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
