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
import Mathlib.Data.Set.Card.Arithmetic
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
    primes, `a, b ≥ 1`, AND `a + b ≥ 4` (i.e., not one of the three
    axiom-free shapes `(a, b) ∈ {(1, 1), (2, 1), (1, 2)}`).

    Iteration history of the hypothesis: original was `2 ≤ a ∨ 2 ≤ b`
    after S4's `burnside_pq_pq_case` peeled off `(1, 1)`. S25 (this
    iteration) further narrows to `4 ≤ a + b` after S7+S7.5+S9+S24
    peeled off the `(2, 1)` shape (via `burnside_p_squared_q`) and
    S11.1+S11.2+S11.3+S24 peeled off the `(1, 2)` shape (via
    `burnside_p_q_squared`). The S25-narrowed axiom covers exactly
    the residue `(a, b)` with `a + b ≥ 4`, i.e., `(2, 2)`, `(3, 1)`,
    `(1, 3)`, `(2, 3)`, `(3, 2)`, `(3, 3)`, …, `(4, 1)`, `(1, 4)`, …
    The genuinely-open content is `|G|` with at least one prime
    appearing to the second power AND the total exponent at least 4.

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
    (hpq : p ≠ q) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 ≤ a + b)
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

/-- **Burnside `|G| = p^a · q`, case `q < p`** (axiom-free, S31 peel-off
    per S26 §3.2): Sylow's third theorem gives `n_p ≡ 1 [MOD p]` and
    `Sylow.card_dvd_index` gives `n_p ∣ q`; the helper
    `sylow_count_eq_one_of_lt_prime` forces `n_p = 1`. The unique Sylow
    `p`-subgroup is normal and discharges via
    `burnside_pq_with_normal_pSylow` with exponents `(a, 1)`.

    For `a = 1` this would reduce to the squarefree case (already covered
    axiom-free by `burnside_pq_pq_case` via `IsZGroup.of_squarefree`).
    For `a = 2` this is `burnside_p_squared_q_p_gt_q` (which this theorem
    subsumes for `q < p`).  For `a ≥ 3` this is new content peeling
    `(a, 1)` shapes off `burnside_pq_nontrivial` whenever `q < p`. -/
theorem burnside_p_pow_a_q_q_lt_p
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] {a : ℕ}
    (ha : 1 ≤ a) (hpq : q < p)
    (hcard : Nat.card G = p ^ a * q) :
    IsSolvable G := by
  -- Step 1: pick a Sylow p-subgroup; |P| = p^a by `Sylow.card_eq_multiplicity`.
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hp_ne_q : p ≠ q := by omega
  have hp_not_dvd_q : ¬ p ∣ q :=
    mt (Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp hp_ne_q
  have hcop : Nat.Coprime (p ^ a) q :=
    ((Nat.coprime_primes hp.out hq.out).mpr hp_ne_q).pow_left a
  have hP_card : Nat.card (P : Subgroup G) = p ^ a := by
    have hmult := Sylow.card_eq_multiplicity P
    have hfact : Nat.factorization (Nat.card G) p = a := by
      rw [hcard, Nat.factorization_mul_apply_of_coprime hcop,
          Nat.Prime.factorization_pow hp.out,
          Nat.factorization_eq_zero_of_not_dvd hp_not_dvd_q]
      simp
    rw [hfact] at hmult
    exact hmult
  -- Step 2: index of P is q (Lagrange + cancellation).
  have hpa_pos : 0 < p ^ a := pow_pos hp.out.pos a
  have hP_index : (P : Subgroup G).index = q := by
    have h := Subgroup.card_mul_index (P : Subgroup G)
    rw [hP_card, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hpa_pos h
  -- Step 3: n_p ≡ 1 [MOD p] and n_p ∣ q, so n_p = 1.
  have hnp_mod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have hnp_dvd : Nat.card (Sylow p G) ∣ q := hP_index ▸ Sylow.card_dvd_index P
  have hnp_eq_one : Nat.card (Sylow p G) = 1 :=
    sylow_count_eq_one_of_lt_prime hp.out hq.out hpq hnp_mod hnp_dvd
  -- Step 4: n_p = 1 ⇒ Subsingleton (Sylow p G) ⇒ P.Normal.
  haveI hSub : Subsingleton (Sylow p G) :=
    (Nat.card_eq_one_iff_unique.mp hnp_eq_one).1
  haveI hP_normal : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  -- Step 5: discharge via burnside_pq_with_normal_pSylow with (a, b) = (a, 1).
  have hcard' : Nat.card G = p ^ a * q ^ 1 := by rw [pow_one]; exact hcard
  exact burnside_pq_with_normal_pSylow (a := a) (b := 1) hcard' (P : Subgroup G) hP_card

/-- **Burnside `|G| = p · q^b`, case `p < q`** (axiom-free, S31 peel-off
    per S26 §3.3): mirror of `burnside_p_pow_a_q_q_lt_p` with primes
    swapped. Reduces to the previous theorem with `(p, q) ↦ (q, p)` and
    `a ↦ b`. -/
theorem burnside_p_q_pow_b_p_lt_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] {b : ℕ}
    (hb : 1 ≤ b) (hpq : p < q)
    (hcard : Nat.card G = p * q ^ b) :
    IsSolvable G := by
  -- Apply burnside_p_pow_a_q_q_lt_p with (p, q) ↦ (q, p) and a ↦ b.
  have hcard' : Nat.card G = q ^ b * p := by rw [hcard]; ring
  exact burnside_p_pow_a_q_q_lt_p (p := q) (q := p) (a := b) hb hpq hcard'

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
    subst n
    have hq_dvd : q ∣ p - 1 :=
      (Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mp hmod.symm
    have : q ≤ p - 1 := Nat.le_of_dvd (by omega : 0 < p - 1) hq_dvd
    omega
  · -- n = p^2. Then q ∣ p^2 - 1 = (p - 1) * (p + 1).
    subst hni
    have hp2_one_le : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp.pos
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
  have hQ_card' : Nat.card (Q : Subgroup G) = q ^ 1 := by rw [pow_one]; exact hQ_card
  exact burnside_pq_with_normal_qSylow (a := 2) (b := 1) hcard' (Q : Subgroup G) hQ_card'

/-! Iteration 9 (S9) — exceptional `(p, q) = (2, 3), |G| = 12` case.

    The S7.5 theorem `burnside_p_squared_q_p_lt_q` explicitly excludes
    `(p, q) = (2, 3)` via the `hexc : ¬ (p = 2 ∧ q = 3)` hypothesis,
    because the divisor analysis fails: when `p = 2, q = 3`, we have
    `q = p + 1`, so `q ∣ p² - 1 = (p - 1)(p + 1)` is consistent with
    `n_q = p² = 4`. Hence Sylow's third theorem alone does NOT force a
    normal Sylow 3-subgroup when `|G| = 12`.

    The classical fix is element-counting on Sylow 3-subgroups: when
    `n_3 = 4`, the four Sylow 3-subgroups each have order `3` and pairwise
    intersect trivially. The set `{g : G | g^3 = 1}` is the disjoint
    union `{e} ⊔ ⋃ᵢ (Q_i \ {e})`, of cardinality `1 + 4·2 = 9`. Then
    `G \ {g | g^3 = 1}` has exactly `12 - 9 = 3` elements. Any Sylow
    2-subgroup `P` has `P \ {e}` of cardinality `3` consisting of
    elements of order in `{2, 4}` (none with `g^3 = 1`), so
    `P \ {e} ⊆ G \ {g | g^3 = 1}`. Cardinalities force equality, fixing
    `P` as a set independent of choice — so `Subsingleton (Sylow 2 G)`,
    `P` is normal, and the discharge proceeds via
    `burnside_pq_with_normal_pSylow`.

    This iteration:
    - **Adds** `sylow_count_dvd_four_modEq_one_three` (axiom-free helper).
    - **Adds** `burnside_p_squared_q_twelve` (axiom-free main, modulo
      `sylow_two_unique_when_n3_four` whose element-counting proof is
      isolated as a single `sorry` for S10).
    - **Does NOT** modify `burnside_pq` dispatch — that update waits
      until S10 closes the sorry, completing the `(a, b) = (2, 1)`
      shape discharge.

    Together with S7 (`p > q`) and S7.5 (`p < q ≠ p + 1`), this is the
    final sub-case of the `(a, b) = (2, 1)` shape. After S10 closes the
    sorry, `burnside_pq` can peel off `(2, 1)` axiom-free; with the
    symmetric `(1, 2)` shape (S11), `burnside_pq_nontrivial` narrows to
    require `2 ≤ a ∧ 2 ≤ b` (genuinely both ≥ 2). -/

/-- **Sylow count constraint** (helper for `|G| = 12 = 2² · 3`):
    if `n ∣ 4` and `n ≡ 1 [MOD 3]` and `n ≥ 1`, then `n = 1 ∨ n = 4`.
    The four divisors of `4` are `{1, 2, 4}`; only `1` and `4` satisfy
    `≡ 1 [MOD 3]` (`2 ≡ 2` and `3 ∤ 4`). Decidable on `Nat`. -/
private lemma sylow_count_dvd_four_modEq_one_three
    {n : ℕ} (hpos : 0 < n) (hdvd : n ∣ 4) (hmod : n ≡ 1 [MOD 3]) :
    n = 1 ∨ n = 4 := by
  have hn_le : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n
  · left; rfl
  · -- n = 2: 2 ≢ 1 [MOD 3]
    exact absurd hmod (by decide)
  · -- n = 3: 3 ∤ 4
    exact absurd hdvd (by decide)
  · right; rfl

/-- **S10 helper (S11.5, this session)**: distinct Sylow `p`-subgroups
    of prime order intersect trivially.

    For Sylow `p`-subgroups `Q ≠ Q'` with `|Q| = |Q'| = p` (which holds
    when `|G| = p · m` with `gcd(p, m) = 1`, e.g. `|G| = 12 = 2² · 3`
    and `p = 3`), the intersection `Q ⊓ Q'` is a subgroup of `Q` whose
    cardinality divides `|Q| = p` (prime), so it's either `1` or `p`.

    The case `card = p` would force `Q ⊓ Q' = Q` (both are subgroups
    of `Q` with the same cardinality), hence `Q ≤ Q'` (via the `inf_le_right`
    side); and then `Q = Q'` as subgroups (both order `p`), which lifts
    to `Q = Q'` as `Sylow` via `Sylow.ext` — contradicting `hne`. So
    `card = 1`, equivalently `Q ⊓ Q' = ⊥`.

    **First ingredient** of S10's element-counting closure: the set
    `{g : G | g^3 = 1}` decomposes as the disjoint union `{e} ⊔ ⊔ᵢ (Qᵢ \ {e})`,
    requiring this disjointness fact for the `n_3 = 4` Sylow 3-subgroups
    of `|G| = 12`. -/
private lemma sylow_prime_order_disjoint_of_ne
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)]
    (Q Q' : Sylow p G)
    (hQ_card : Nat.card (Q : Subgroup G) = p)
    (hQ'_card : Nat.card (Q' : Subgroup G) = p)
    (hne : Q ≠ Q') :
    (Q : Subgroup G) ⊓ (Q' : Subgroup G) = ⊥ := by
  -- Strategy: |Q ⊓ Q'| ∣ |Q| = p (prime), so it's 1 or p; rule out p.
  -- (S12 build-fix: replaces non-existent Mathlib API references in the
  -- original S11.5 commit. `Subgroup.card_dvd_card_of_le`,
  -- `Subgroup.card_eq_one_iff_eq_bot`, and `Subgroup.eq_of_le_of_card_le`
  -- are NOT in current Mathlib. The corrected proof uses
  -- `Subgroup.card_dvd_of_le`, `Subgroup.eq_bot_of_card_le`, and the
  -- `subgroupOf` relativization via `Subgroup.subgroupOfEquivOfLe` +
  -- `Subgroup.eq_top_of_card_eq` + `Subgroup.subgroupOf_eq_top`.)
  have hint_le_Q : (Q : Subgroup G) ⊓ (Q' : Subgroup G) ≤ (Q : Subgroup G) := inf_le_left
  have hint_le_Q' : (Q : Subgroup G) ⊓ (Q' : Subgroup G) ≤ (Q' : Subgroup G) := inf_le_right
  have hp_prime : Nat.Prime p := Fact.out
  have hdvd : Nat.card ((Q : Subgroup G) ⊓ (Q' : Subgroup G) : Subgroup G) ∣ p := by
    have h := Subgroup.card_dvd_of_le hint_le_Q
    rwa [hQ_card] at h
  rcases hp_prime.eq_one_or_self_of_dvd _ hdvd with h1 | hp_eq
  · -- |inter| = 1 ⇒ inter = ⊥ via `Subgroup.eq_bot_of_card_eq`
    -- (`H` is an explicit argument in current Mathlib).
    exact Subgroup.eq_bot_of_card_eq _ h1
  · -- |inter| = p = |Q| = |Q'|: forces Q = Q' as Sylow, contradicting hne.
    -- Use `subgroupOf` relativization to derive Q ≤ Q' and Q' ≤ Q.
    exfalso
    apply hne
    apply Sylow.ext
    -- Sub-step 1: derive Q ≤ Q'.
    -- `(Q ⊓ Q').subgroupOf Q ≃* Q ⊓ Q'` has card |Q ⊓ Q'| = p = |Q|;
    -- hence it's `⊤` in the lattice of subgroups of Q, giving Q ≤ Q ⊓ Q' ≤ Q'.
    have hequiv1 :
        (((Q : Subgroup G) ⊓ (Q' : Subgroup G)).subgroupOf (Q : Subgroup G)) ≃*
        ((Q : Subgroup G) ⊓ (Q' : Subgroup G) : Subgroup G) :=
      Subgroup.subgroupOfEquivOfLe hint_le_Q
    have hcard1 :
        Nat.card ((((Q : Subgroup G) ⊓ (Q' : Subgroup G)).subgroupOf (Q : Subgroup G))) =
        Nat.card (Q : Subgroup G) := by
      rw [Nat.card_congr hequiv1.toEquiv]
      exact hp_eq.trans hQ_card.symm
    have htop1 :
        ((Q : Subgroup G) ⊓ (Q' : Subgroup G)).subgroupOf (Q : Subgroup G) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ hcard1
    have h_Q_le_inter : (Q : Subgroup G) ≤ (Q : Subgroup G) ⊓ (Q' : Subgroup G) :=
      Subgroup.subgroupOf_eq_top.mp htop1
    have h_Q_le_Q' : (Q : Subgroup G) ≤ (Q' : Subgroup G) := h_Q_le_inter.trans hint_le_Q'
    -- Sub-step 2: derive Q' ≤ Q symmetrically.
    -- `Q.subgroupOf Q' ≃* Q` has card |Q| = |Q'|; hence ⊤ in subgroups of Q',
    -- giving Q' ≤ Q.
    have hequiv2 : ((Q : Subgroup G).subgroupOf (Q' : Subgroup G)) ≃* (Q : Subgroup G) :=
      Subgroup.subgroupOfEquivOfLe h_Q_le_Q'
    have hcard2 :
        Nat.card ((Q : Subgroup G).subgroupOf (Q' : Subgroup G)) = Nat.card (Q' : Subgroup G) := by
      rw [Nat.card_congr hequiv2.toEquiv]
      exact hQ_card.trans hQ'_card.symm
    have htop2 : (Q : Subgroup G).subgroupOf (Q' : Subgroup G) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ hcard2
    have h_Q'_le_Q : (Q' : Subgroup G) ≤ (Q : Subgroup G) :=
      Subgroup.subgroupOf_eq_top.mp htop2
    -- Conclusion: Q = Q' as subgroups; Sylow.ext lifts to Sylow p G.
    exact le_antisymm h_Q_le_Q' h_Q'_le_Q

/-- **S13 ingredient (cardinality)**: every Sylow 3-subgroup of a finite
    group of order 12 has exactly 3 elements.

    Direct application of `Sylow.card_eq_multiplicity` together with the
    explicit factorization `12 = 2² · 3¹`. Identical proof skeleton to
    the inline computation at line ~660 of this file inside
    `burnside_p_squared_q_twelve`, factored out so that the S10
    element-counting closure of `sylow_two_unique_when_n3_four` and any
    follow-up `|G| = 12` analyses can refer to it as a single named
    lemma rather than re-deriving it inline.

    **Second ingredient** for S10's element-counting proof of
    `sylow_two_unique_when_n3_four`. The first ingredient is
    `sylow_prime_order_disjoint_of_ne` (S11.5) above, which in this
    setting reduces to the Sylow 3 case because each Sylow 3-subgroup
    has prime order 3 by this lemma. With both ingredients at hand the
    disjoint-union decomposition

        {g : G | g^3 = 1} = {e} ⊔ ⊔_{Q : Sylow 3 G} ((Q : Set G) \ {1})

    has cardinality `1 + 4·(3 - 1) = 9`. The remaining S10 work is the
    set-theoretic packaging of that count
    (`Set.ncard_biUnion_disjoint` etc.) plus the symmetric Sylow-2
    argument, deferred to the next iteration. -/
private lemma sylow_three_card_eq_three_of_card_twelve
    {G : Type*} [Group G] [Finite G] [Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12) (Q : Sylow 3 G) :
    Nat.card (Q : Subgroup G) = 3 := by
  -- |G| = 12 = 2² · 3¹
  have hcard' : Nat.card G = 2 ^ 2 * 3 ^ 1 := by rw [hcard]; norm_num
  have hcop : Nat.Coprime (2 ^ 2) (3 ^ 1) := by decide
  have h3_not_dvd_4 : ¬ (3 : ℕ) ∣ 2 ^ 2 := by decide
  have hp3 : Nat.Prime 3 := Fact.out
  have hmult := Sylow.card_eq_multiplicity Q
  have hfact : Nat.factorization (Nat.card G) 3 = 1 := by
    rw [hcard',
        Nat.factorization_mul_apply_of_coprime hcop,
        Nat.factorization_eq_zero_of_not_dvd h3_not_dvd_4,
        Nat.Prime.factorization_pow hp3]
    simp
  rw [hfact, pow_one] at hmult
  exact hmult

/-- **S13 ingredient (cardinality, mirror)**: every Sylow 2-subgroup of
    a finite group of order 12 has exactly 4 elements.

    Companion to `sylow_three_card_eq_three_of_card_twelve`, packaged
    for the S10 closure's `P \ {1} ⊆ G \ {g | g^3 = 1}` step where the
    cardinality `|P| = 4` (hence `|P \ {1}| = 3 = 12 - 9`) is the
    quantitative driver pinning down `P` independently of choice. Mirror
    of the inline computation at line ~688 of this file inside
    `burnside_p_squared_q_twelve`. -/
private lemma sylow_two_card_eq_four_of_card_twelve
    {G : Type*} [Group G] [Finite G] [Fact (Nat.Prime 2)]
    (hcard : Nat.card G = 12) (P : Sylow 2 G) :
    Nat.card (P : Subgroup G) = 4 := by
  have hcard' : Nat.card G = 2 ^ 2 * 3 ^ 1 := by rw [hcard]; norm_num
  have hcop : Nat.Coprime (2 ^ 2) (3 ^ 1) := by decide
  have h2_not_dvd_3 : ¬ (2 : ℕ) ∣ 3 ^ 1 := by decide
  have hp2 : Nat.Prime 2 := Fact.out
  have hmult := Sylow.card_eq_multiplicity P
  have hfact : Nat.factorization (Nat.card G) 2 = 2 := by
    rw [hcard',
        Nat.factorization_mul_apply_of_coprime hcop,
        Nat.Prime.factorization_pow hp2,
        Nat.factorization_eq_zero_of_not_dvd h2_not_dvd_3]
    simp
  rw [hfact] at hmult
  -- hmult : Nat.card (P : Subgroup G) = 2 ^ 2; reduce 2^2 = 4
  have h_pow_two : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [h_pow_two] at hmult
  exact hmult

/-- **S14 ingredient (first of five)**: in a finite group of order 12, an
    element satisfies `g ^ 3 = 1` iff it lies in some Sylow 3-subgroup.

    *Forward*: `g ^ 3 = 1` gives `orderOf g ∣ 3`, so `orderOf g ∈ {1, 3}`.
    The cyclic subgroup `Subgroup.zpowers g` has cardinality
    `Nat.card (Subgroup.zpowers g) = orderOf g ∈ {3⁰, 3¹}` (`Nat.card_zpowers`),
    hence is a 3-subgroup via `IsPGroup.of_card`. By
    `IsPGroup.exists_le_sylow` it embeds in some Sylow 3-subgroup `Q`, and
    `g ∈ Subgroup.zpowers g ≤ Q`.

    *Backward*: if `g ∈ (Q : Subgroup G)` for some `Q : Sylow 3 G`, then by
    `sylow_three_card_eq_three_of_card_twelve` the subgroup `Q` has
    cardinality 3, so `pow_card_eq_one'` applied inside `(Q : Subgroup G)`
    forces `(⟨g, hg⟩ : (Q : Subgroup G)) ^ 3 = 1`. Pushing through the
    inclusion via `Subgroup.coe_pow` / `Subgroup.coe_one` gives `g ^ 3 = 1`.

    **First ingredient** of S10's element-counting closure of
    `sylow_two_unique_when_n3_four` (per
    `research/problems/abel-ruffini-galois-extensions-oq-07/session-13-s10-element-count-spec.md`
    §1). The four-Sylow-3 hypothesis is not used here; this is a
    pointwise membership characterization that holds for any `|G| = 12`
    regardless of `n_3`. The exact-four count enters S14 ingredient 3
    (cardinality of the disjoint union). -/
private lemma g_pow_three_iff_mem_some_sylow_three
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12) (g : G) :
    g ^ 3 = 1 ↔ ∃ Q : Sylow 3 G, g ∈ (Q : Subgroup G) := by
  refine ⟨fun h => ?_, ?_⟩
  · -- Forward: zpowers g is a 3-subgroup, hence contained in some Sylow 3.
    have hp3 : Nat.Prime 3 := Fact.out
    have horder_dvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h
    -- orderOf g ∈ {1, 3} = {3^0, 3^1}; package as ∃ n, orderOf g = 3^n.
    have hord_pow : ∃ n : ℕ, orderOf g = 3 ^ n := by
      rcases hp3.eq_one_or_self_of_dvd _ horder_dvd with h_one | h_three
      · exact ⟨0, by rw [h_one, pow_zero]⟩
      · exact ⟨1, by rw [h_three, pow_one]⟩
    obtain ⟨n, hn⟩ := hord_pow
    have hpg : IsPGroup 3 ((Subgroup.zpowers g) : Subgroup G) :=
      IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
    obtain ⟨Q, hQle⟩ := hpg.exists_le_sylow
    exact ⟨Q, hQle (Subgroup.mem_zpowers g)⟩
  · -- Backward: |Q| = 3 ⇒ g^Nat.card Q = 1 ⇒ g^3 = 1 after pushing through ↑.
    rintro ⟨Q, hg⟩
    have hQ_card : Nat.card ((Q : Subgroup G)) = 3 :=
      sylow_three_card_eq_three_of_card_twelve hcard Q
    have h_pow_in_Q :
        (⟨g, hg⟩ : (Q : Subgroup G)) ^ Nat.card ((Q : Subgroup G)) = 1 :=
      pow_card_eq_one'
    rw [hQ_card] at h_pow_in_Q
    -- h_pow_in_Q : (⟨g, hg⟩ : (Q : Subgroup G)) ^ 3 = 1.
    -- Push to G via Subgroup.coe_pow + Subgroup.coe_one (both rfl on coerce).
    calc g ^ 3
        = (((⟨g, hg⟩ : (Q : Subgroup G)) ^ 3 : (Q : Subgroup G)) : G) := rfl
      _ = ((1 : (Q : Subgroup G)) : G) := by rw [h_pow_in_Q]
      _ = 1 := rfl

/-- **S15 ingredient 2**: set-equality decomposition of the cube-identity
    set `{g : G | g^3 = 1}` as the union of the singleton `{1}` and the
    non-identity portions of all Sylow 3-subgroups.

    Combined with `sylow_prime_order_disjoint_of_ne` (S11.5), this becomes
    a *disjoint* union once `|Q| = 3` is plugged in via S13's
    `sylow_three_card_eq_three_of_card_twelve`; the cardinality count
    `|{g | g^3 = 1}| = 1 + n_3 · (3 - 1)` is the third ingredient
    of the S10 closure.

    **Proof**: pointwise via `g_pow_three_iff_mem_some_sylow_three`
    (S14 ingredient 1):
    - **(⊆)**: `g^3 = 1 → ∃ Q, g ∈ Q`. Case `g = 1`: contributes to `{1}`.
      Case `g ≠ 1`: contributes to `(Q : Set G) \ {1}`.
    - **(⊇)**: `g = 1` gives `1^3 = 1`. `g ∈ Q` (with `|Q| = 3`)
      gives `g^3 = 1` via the backward direction of S14. -/
private lemma cube_id_set_eq_disjoint_union
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12) :
    {g : G | g ^ 3 = 1} =
      {1} ∪ ⋃ (Q : Sylow 3 G), ((Q : Set G) \ {1}) := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff,
             Set.mem_iUnion, Set.mem_diff]
  constructor
  · -- Forward: g^3 = 1 → g = 1 ∨ ∃ Q, g ∈ Q ∧ g ≠ 1.
    intro hg3
    by_cases hg : g = 1
    · exact Or.inl hg
    · obtain ⟨Q, hgQ⟩ :=
        (g_pow_three_iff_mem_some_sylow_three hcard g).mp hg3
      exact Or.inr ⟨Q, hgQ, hg⟩
  · -- Backward: g = 1 ∨ (∃ Q, g ∈ Q ∧ g ≠ 1) → g^3 = 1.
    rintro (hg1 | ⟨Q, hgQ, _⟩)
    · subst hg1; exact one_pow 3
    · exact (g_pow_three_iff_mem_some_sylow_three hcard g).mpr ⟨Q, hgQ⟩

/-- **S17 ingredient (4 forward fragment)**: in a finite group of order 12,
    the intersection of any Sylow 2-subgroup `P` with the cube-identity set
    `{g | g^3 = 1}` is exactly the singleton `{1}`.

    Equivalently: every non-identity element of a Sylow 2-subgroup fails
    `g^3 = 1`.

    **Proof**: every `g ∈ P` satisfies `g ^ Nat.card P = 1` (i.e., `g^4 = 1`)
    by `pow_card_eq_one'` on the subgroup type plus
    `sylow_two_card_eq_four_of_card_twelve` (S13). Combined with the
    hypothesis `g^3 = 1`: `g = 1 · g = g^3 · g = g^(3+1) = g^4 = 1`, so
    `g = 1`. The reverse inclusion `{1} ⊆ (P : Set G) ∩ {g | g^3 = 1}` is
    trivial: `1 ∈ P` (subgroup) and `1^3 = 1` (`one_pow`).

    **Significance**: this is the *cardinality-free containment* fragment
    of ingredient 4 of the S10 element-counting closure (per
    `session-13-s10-element-count-spec.md` §4). The full ingredient-4
    statement
    `(P : Set G) = {1} ∪ ((Set.univ : Set G) \ {g | g^3 = 1})`
    requires a cardinality count via ingredient 3 (`cube_id_card_eq_nine`)
    plus the four-Sylow-3 hypothesis `n_3 = 4`; this sub-lemma is
    independent of those — it holds for *any* `|G| = 12` regardless of
    `n_3`, exposing the underlying coprimality
    `gcd(|P|, 3) = gcd(4, 3) = 1` between the Sylow-2 order and the
    cube exponent.

    **Complementary, non-overlapping with PRs #17586 / #17587** (S16
    parallel fragments of ingredient 3): #17586 supplies Set-level
    pairwise disjointness of `(Q : Set G) \ {1}` for distinct
    Sylow 3-subgroups; #17587 supplies the per-fiber count
    `Set.ncard ((Q : Set G) \ {1}) = 2`. Both target the cardinality of
    the Sylow-3 disjoint union (ingredient 3); this lemma targets the
    Sylow-2 / cube-id intersection (ingredient 4 forward), which uses
    `|P| = 4` rather than `|Q| = 3` and so does not interact with
    either of those PRs' Sylow-3 lemmas. -/
private theorem sylow_two_inter_cube_id_eq_singleton_one
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 2)]
    (hcard : Nat.card G = 12) (P : Sylow 2 G) :
    (P : Set G) ∩ {g : G | g ^ 3 = 1} = ({1} : Set G) := by
  ext g
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_setOf_eq,
             Set.mem_singleton_iff]
  refine ⟨fun ⟨hgP, hg3⟩ => ?_, ?_⟩
  · -- Forward: g ∈ P, g^3 = 1 → g = 1.
    have hP_card : Nat.card ((P : Subgroup G)) = 4 :=
      sylow_two_card_eq_four_of_card_twelve hcard P
    have h_pow_in_P :
        (⟨g, hgP⟩ : (P : Subgroup G)) ^ Nat.card ((P : Subgroup G)) = 1 :=
      pow_card_eq_one'
    rw [hP_card] at h_pow_in_P
    -- h_pow_in_P : (⟨g, hgP⟩ : (P : Subgroup G)) ^ 4 = 1.
    -- Push down to G via Subgroup.coe_pow + Subgroup.coe_one (both rfl on coerce).
    have h_g4 : g ^ 4 = 1 := by
      calc g ^ 4
          = (((⟨g, hgP⟩ : (P : Subgroup G)) ^ 4 : (P : Subgroup G)) : G) := rfl
        _ = ((1 : (P : Subgroup G)) : G) := by rw [h_pow_in_P]
        _ = 1 := rfl
    -- Combine with g^3 = 1: g = 1 · g = g^3 · g = g^(3+1) = g^4 = 1.
    calc g = 1 * g := (one_mul g).symm
      _ = g^3 * g := by rw [hg3]
      _ = g^(3+1) := by rw [← pow_succ]
      _ = g^4 := rfl
      _ = 1 := h_g4
  · -- Backward: g = 1 → g ∈ P ∧ g^3 = 1.
    rintro rfl
    exact ⟨(P : Subgroup G).one_mem, one_pow 3⟩

/-- **S18 ingredient 4 cardinality (per session-13 spec §4)**: in a finite
    group of order 12, each Sylow 2-subgroup `P` has exactly 3 non-identity
    elements when viewed as a set: `Set.ncard ((P : Set G) \ {1}) = 3`.

    Direct combination of `sylow_two_card_eq_four_of_card_twelve`
    (S13: `|P| = 4`) with `Set.ncard_diff_singleton_of_mem` and
    `Nat.card_coe_set_eq` (which bridges `Nat.card (P : Subgroup G)` to
    `Set.ncard (P : Set G)` via the `SetLike (Sylow 2 G) G` coercion).

    Sylow-2 mirror of `sylow_three_set_diff_one_ncard_eq_two`
    (PR #17587, S16 ingredient 3a): same proof template with `(2, 4, 3)`
    substituted for `(3, 3, 2)`. Together with the `Set`-level
    forward containment supplied by `sylow_two_inter_cube_id_eq_singleton_one`
    (S17, immediately above) and the cardinality coincidence
    `|G| − 9 = 3` (which awaits S16's `cube_id_card_eq_nine`, in flight
    via PRs #17586 / #17587), this lemma closes the cardinality side
    of ingredient 4 of the S10 element-counting closure: any Sylow
    2-subgroup `P` satisfies `(P : Set G) \ {1} = G \ {g | g^3 = 1}`
    once the cube-identity set has size 9, since the forward containment
    already lives at the set level (S17) and both sides have `ncard = 3`.
    The set-equality is independent of the choice of `P`, hence
    `Subsingleton (Sylow 2 G)` (ingredient 5).

    **Complementary, non-overlapping with PRs #17586 / #17587** (Sylow-3
    side of ingredient 3) and merged PR #17630 (S17, Sylow-2 / cube-id
    set-level intersection). This lemma carries no hypothesis on
    `n_3 = 4` — it holds for any Sylow 2-subgroup of any |G| = 12. -/
private lemma sylow_two_set_diff_one_ncard_eq_three
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 2)]
    (hcard : Nat.card G = 12) (P : Sylow 2 G) :
    Set.ncard ((P : Set G) \ ({1} : Set G)) = 3 := by
  -- Step 1: |P| = 4 from S13.
  have h4 : Nat.card (P : Subgroup G) = 4 :=
    sylow_two_card_eq_four_of_card_twelve hcard P
  -- Step 2: 1 ∈ (P : Set G) (the subgroup contains the identity).
  have h1mem : (1 : G) ∈ (P : Set G) := (P : Subgroup G).one_mem
  -- Step 3: Set.ncard (P : Set G) = 4 via Nat.card_coe_set_eq + S13.
  -- The subtypes ↥((P : Sylow 2 G) : Set G) and ↥(P : Subgroup G)
  -- are defeq via the SetLike coercion chain Sylow → Subgroup → Set
  -- (same elaboration path as S16 ingredient 3a, PR #17587).
  have hncard : Set.ncard ((P : Set G) : Set G) = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact h4
  rw [Set.ncard_diff_singleton_of_mem h1mem, hncard]

/-- **S20 ingredient 4 reverse containment via cardinality** (per
    `session-13-s10-element-count-spec.md` §4): closes the set equality

        (P : Set G) \ {1} = (Set.univ : Set G) \ {g : G | g ^ 3 = 1}

    for any Sylow 2-subgroup `P` of `|G| = 12`, *conditional on* the
    cardinality of the cube-identity complement
    `Set.ncard ((Set.univ : Set G) \ {g | g^3 = 1}) = 3`.

    **Three composing ingredients**:
    * S17 `sylow_two_inter_cube_id_eq_singleton_one` (merged PR #17630):
      forward set-level containment
      `(P : Set G) ∩ {g | g^3 = 1} = {1}`, equivalently
      `(P : Set G) \ {1} ⊆ (Set.univ : Set G) \ {g | g^3 = 1}` (after
      Boolean rearrangement, performed inline in the proof below).
    * S18 `sylow_two_set_diff_one_ncard_eq_three` (merged PR #17648):
      LHS cardinality `Set.ncard ((P : Set G) \ {1}) = 3`.
    * Hypothesis `hncard_compl`: RHS cardinality
      `Set.ncard ((Set.univ : Set G) \ {g | g^3 = 1}) = 3`.

    The three give set equality via `Set.eq_of_subset_of_ncard_le`
    (finite-set version of subset + ncard match → equality).

    **Conditional on `hncard_compl`**: this hypothesis is the cardinality
    corollary of S16's `cube_id_card_eq_nine` (in flight via PRs #17586 +
    #17587 supplying the Sylow-3 disjoint-union ingredients), since for
    `|G| = 12` and `n_3 = 4`:
    `Set.ncard ((Set.univ : Set G) \ {g | g^3 = 1}) = 12 - 9 = 3`.
    Once S16 lands, the hypothesis is dischargeable by elementary
    `Set.ncard_diff` / `Set.ncard_univ` arithmetic, and S20 inlines
    immediately into the closure of `sylow_two_unique_when_n3_four`
    (the S10 placeholder).

    **Carries no hypothesis on `n_3 = 4`**: the `n_3 = 4` dependency of
    the closure is fully encapsulated in `hncard_compl`. S20 itself is a
    pure "subset + cardinality match → equality" argument, no Sylow
    count involved.

    **Strategic complementarity** with the in-flight S16 PRs (#17586,
    #17587) and merged S17 (#17630) and S18 (#17648): the three landed
    pieces supply (a) the forward set-level containment and (b) the LHS
    cardinality; this S20 piece supplies the cardinality-driven reverse
    containment that combines them with the S16 corollary into a full
    set equality. No overlap with the Sylow-3 cube-id cardinality work
    of S15 / S16. -/
private lemma sylow_two_set_diff_one_eq_compl_cube_id
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 2)]
    (hcard : Nat.card G = 12)
    (hncard_compl :
      Set.ncard ((Set.univ : Set G) \ {g : G | g ^ 3 = 1}) = 3)
    (P : Sylow 2 G) :
    (P : Set G) \ ({1} : Set G) =
      (Set.univ : Set G) \ {g : G | g ^ 3 = 1} := by
  -- Step 1: forward set-level containment from S17.
  -- Boolean rearrangement: (P ∩ cube_id = {1}) ⟹ (P \ {1} ⊆ univ \ cube_id).
  have h_subset :
      (P : Set G) \ ({1} : Set G) ⊆
        (Set.univ : Set G) \ {g : G | g ^ 3 = 1} := by
    intro g hg
    rw [Set.mem_diff, Set.mem_singleton_iff] at hg
    obtain ⟨hgP, hg_ne⟩ := hg
    refine ⟨Set.mem_univ g, ?_⟩
    intro hg3
    -- g ∈ P ∩ {g | g^3 = 1} = {1} (S17) ⟹ g = 1, contradicting hg_ne.
    have h17 :
        (P : Set G) ∩ {g : G | g ^ 3 = 1} = ({1} : Set G) :=
      sylow_two_inter_cube_id_eq_singleton_one hcard P
    have h_inter :
        g ∈ (P : Set G) ∩ {g : G | g ^ 3 = 1} :=
      Set.mem_inter hgP hg3
    rw [h17, Set.mem_singleton_iff] at h_inter
    exact hg_ne h_inter
  -- Step 2: LHS cardinality from S18.
  have hncard_lhs :
      Set.ncard ((P : Set G) \ ({1} : Set G)) = 3 :=
    sylow_two_set_diff_one_ncard_eq_three hcard P
  -- Step 3: subset + ncard match → equality.
  -- RHS finiteness explicitly via Set.toFinite (G has [Finite G]).
  have hle :
      Set.ncard ((Set.univ : Set G) \ {g : G | g ^ 3 = 1}) ≤
        Set.ncard ((P : Set G) \ ({1} : Set G)) := by
    omega
  exact Set.eq_of_subset_of_ncard_le h_subset hle (Set.toFinite _)

/-- **S20 corollary** — full set-equality form. Under the same
    conditional hypothesis on cube-identity complement cardinality,
    every Sylow 2-subgroup `P` satisfies

        (P : Set G) = ({1} : Set G) ∪ ((Set.univ : Set G) \ {g | g^3 = 1}).

    The RHS is *independent of `P`*: it depends only on `G`, not on the
    choice of Sylow 2-subgroup. This P-independence is the final
    ingredient needed to derive `Subsingleton (Sylow 2 G)` — ingredient
    5 of the S10 closure of `sylow_two_unique_when_n3_four`. The
    `Subsingleton` step itself (composing this with `Sylow.ext` +
    `SetLike.coe_injective`) is deferred to the next iteration, alongside
    discharge of `hncard_compl` from the upcoming S16 cardinality lemma.

    **Proof skeleton**: combine
    * `(P : Set G) = {1} ∪ ((P : Set G) \ {1})` (since `1 ∈ P`, via
      `Set.union_diff_cancel` on the singleton subset),
    * S20's `(P : Set G) \ {1} = (Set.univ : Set G) \ {g | g^3 = 1}`. -/
private lemma sylow_two_set_eq_one_union_compl_cube_id
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 2)]
    (hcard : Nat.card G = 12)
    (hncard_compl :
      Set.ncard ((Set.univ : Set G) \ {g : G | g ^ 3 = 1}) = 3)
    (P : Sylow 2 G) :
    (P : Set G) =
      ({1} : Set G) ∪ ((Set.univ : Set G) \ {g : G | g ^ 3 = 1}) := by
  -- Step 1: 1 ∈ (P : Set G); hence {1} ⊆ (P : Set G).
  have h1mem : (1 : G) ∈ (P : Set G) := (P : Subgroup G).one_mem
  have h_singleton_subset : ({1} : Set G) ⊆ (P : Set G) :=
    Set.singleton_subset_iff.mpr h1mem
  -- Step 2: P = {1} ∪ (P \ {1}) via Set.union_diff_cancel.
  have h_split :
      ({1} : Set G) ∪ ((P : Set G) \ ({1} : Set G)) = (P : Set G) :=
    Set.union_diff_cancel h_singleton_subset
  -- Step 3: rewrite (P \ {1}) using S20.
  have h_diff_eq :
      (P : Set G) \ ({1} : Set G) =
        (Set.univ : Set G) \ {g : G | g ^ 3 = 1} :=
    sylow_two_set_diff_one_eq_compl_cube_id hcard hncard_compl P
  rw [← h_split, h_diff_eq]

/-- **S21 ingredient 5 — Subsingleton step under conditional
    cardinality hypothesis** (private, axiom-free, conditional).

    Composes S20's `sylow_two_set_eq_one_union_compl_cube_id`
    P-independent set-equality with `Sylow.ext + SetLike.coe_injective`
    to derive `Subsingleton (Sylow 2 G)`:

        Subsingleton (Sylow 2 G)

    under the same conditional hypothesis
    `Set.ncard ((Set.univ : Set G) \ {g | g^3 = 1}) = 3` that S20
    requires. The hypothesis is the cardinality corollary of the S16
    target `cube_id_card_eq_nine` (in flight via PRs #17586 + #17587),
    since for `|G| = 12`: `Set.ncard univ = 12` and
    `Set.ncard {g | g^3 = 1} = 9` give `Set.ncard (univ \ ...) = 3`
    by `Set.ncard_diff` + `Set.ncard_univ`.

    This lemma is ingredient 5 of the S10 element-counting closure
    of `sylow_two_unique_when_n3_four`. With S21 in hand, the only
    remaining work to close S10 is to discharge `hncard_compl` from
    `hn3 : Nat.card (Sylow 3 G) = 4` via the (still in-flight) S16
    cardinality lemma plus the elementary
    `Set.ncard_diff` / `Set.ncard_univ` bridge.

    **Proof skeleton**: take two Sylow 2-subgroups `P` and `P'`; apply
    S20 to each to get
    `(P : Set G) = ({1} : Set G) ∪ ((univ : Set G) \ {g | g^3 = 1})`
    and the same for `P'`. The RHS is `P`-independent, so transitivity
    gives `(P : Set G) = (P' : Set G)`. Then `SetLike.coe_injective`
    lifts to `(P : Subgroup G) = (P' : Subgroup G)`, and `Sylow.ext`
    lifts further to `P = P'`. -/
private lemma sylow_two_subsingleton_of_compl_ncard
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 2)]
    (hcard : Nat.card G = 12)
    (hncard_compl :
      Set.ncard ((Set.univ : Set G) \ {g : G | g ^ 3 = 1}) = 3) :
    Subsingleton (Sylow 2 G) := by
  refine ⟨fun P P' => ?_⟩
  -- Both (P : Set G) and (P' : Set G) equal the same P-independent RHS.
  have hP :
      (P : Set G) =
        ({1} : Set G) ∪ ((Set.univ : Set G) \ {g : G | g ^ 3 = 1}) :=
    sylow_two_set_eq_one_union_compl_cube_id hcard hncard_compl P
  have hP' :
      (P' : Set G) =
        ({1} : Set G) ∪ ((Set.univ : Set G) \ {g : G | g ^ 3 = 1}) :=
    sylow_two_set_eq_one_union_compl_cube_id hcard hncard_compl P'
  -- Transitivity at the Set level.
  have hset : (P : Set G) = (P' : Set G) := hP.trans hP'.symm
  -- Lift Set-equality to Subgroup-equality, then to Sylow-equality.
  exact Sylow.ext (SetLike.coe_injective hset)

/-- **S22 cardinality bridge** (private, axiom-free).

    From the cube-identity element count
    `Set.ncard {g : G | g^3 = 1} = 9` (the S16 target, in flight via
    PRs #17586 + #17587) together with `Nat.card G = 12`, derives the
    complement-side cardinality
    `Set.ncard ((Set.univ : Set G) \ {g | g^3 = 1}) = 3`
    via elementary `Set.ncard_diff` + `Set.ncard_univ` arithmetic
    (`12 − 9 = 3`).

    This is exactly the `hncard_compl` hypothesis taken by S20's
    `sylow_two_set_diff_one_eq_compl_cube_id` /
    `sylow_two_set_eq_one_union_compl_cube_id` and S21's
    `sylow_two_subsingleton_of_compl_ncard`, expressed in terms of
    the S16 target. With this bridge in hand, the S10 closure of
    `sylow_two_unique_when_n3_four` reduces to deriving the cube-id
    count `= 9` from `Nat.card (Sylow 3 G) = 4` (the in-flight S16
    composition target `cube_id_card_eq_nine`).

    **Non-overlap with in-flight PRs**:
    * #17586 / #17587 target the *cube-id count* (S16 ingredient 3);
      this lemma takes that count as a hypothesis and bridges to the
      complement form. No content overlap.
    * #17685 (S19) and the merged S17/S18/S20/S21 lemmas all operate
      on the Sylow-2 side under the *already-derived* `hncard_compl`
      hypothesis; this lemma supplies the derivation, not a refactor
      of consumers.

    **Proof skeleton**: `{g | g^3 = 1} ⊆ Set.univ` is `Set.subset_univ`,
    `Set.ncard (Set.univ : Set G) = Nat.card G = 12` via `Set.ncard_univ`
    + `hcard`, then `Set.ncard_diff` gives
    `Set.ncard (univ \ S) = Set.ncard univ − Set.ncard S`. Closing
    `12 − 9 = 3` is `rfl` for closed `Nat` literals. -/
private lemma cube_id_complement_ncard_eq_three_of_card_nine
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 12)
    (hcube_card : Set.ncard {g : G | g ^ 3 = 1} = 9) :
    Set.ncard ((Set.univ : Set G) \ {g : G | g ^ 3 = 1}) = 3 := by
  have hsubset : {g : G | g ^ 3 = 1} ⊆ (Set.univ : Set G) := Set.subset_univ _
  have hncard_univ : Set.ncard (Set.univ : Set G) = 12 := by
    rw [Set.ncard_univ]; exact hcard
  rw [Set.ncard_diff hsubset, hncard_univ, hcube_card]

/-- **S22 Subsingleton composition** (private, axiom-free): composes
    the cardinality bridge `cube_id_complement_ncard_eq_three_of_card_nine`
    with S21's `sylow_two_subsingleton_of_compl_ncard` to derive
    `Subsingleton (Sylow 2 G)` directly from the S16 target form
    (`Set.ncard {g | g^3 = 1} = 9`) without the user needing to thread
    the complement-cardinality hypothesis manually.

    With this corollary in hand, closing the S10 sorry in
    `sylow_two_unique_when_n3_four` reduces to a *single* discharge —
    deriving `Set.ncard {g : G | g^3 = 1} = 9` from
    `Nat.card (Sylow 3 G) = 4`, which is the composition of the
    in-flight S16 PRs #17586 + #17587 plus the `1 + 4·2 = 9`
    disjoint-union arithmetic (S15 supplies the set decomposition). -/
private lemma sylow_two_subsingleton_of_cube_id_card_nine
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 2)]
    (hcard : Nat.card G = 12)
    (hcube_card : Set.ncard {g : G | g ^ 3 = 1} = 9) :
    Subsingleton (Sylow 2 G) :=
  sylow_two_subsingleton_of_compl_ncard hcard
    (cube_id_complement_ncard_eq_three_of_card_nine hcard hcube_card)

/-- **S23 cube-id count from partition ingredients** (private, axiom-free,
    conditional).

    Composes S15's set decomposition `cube_id_set_eq_disjoint_union` with
    the two atomic partition ingredients in flight on PRs #17586 + #17587
    (taken here as hypotheses) plus the Sylow-3 count `n_3 = 4`, to derive
    the cube-identity element count

        Set.ncard {g : G | g ^ 3 = 1} = 9.

    With this lemma in hand, closing the S10 placeholder
    `sylow_two_unique_when_n3_four` becomes a one-line composition with
    `sylow_two_subsingleton_of_cube_id_card_nine` (S22 above):

        intro hcard hn3
        haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
        let hdisj := fun Q Q' hne =>
          sylow_three_diff_singleton_disjoint hcard hne     -- in flight #17586
        let hfiber := sylow_three_set_diff_one_ncard_eq_two hcard  -- in flight #17587
        have h9 := cube_id_card_eq_nine_of_partition_ingredients
                      hcard hdisj hfiber hn3
        exact sylow_two_subsingleton_of_cube_id_card_nine hcard h9

    **Proof skeleton**: rewrites `{g | g ^ 3 = 1}` via S15 to the
    disjoint-union form `{1} ∪ ⋃ Q : Sylow 3 G, ((Q : Set G) \ {1})`,
    then splits the cardinality across the three pieces:
    * Disjointness of `{1}` from each `Q \ {1}` (trivial: `1 ∉ Q \ {1}`)
      plus `Set.disjoint_iUnion_right` gives `{1}` disjoint from the union.
    * `Set.ncard_union_eq` peels off `{1}` (ncard 1).
    * `Set.ncard_iUnion_of_finite` (from `Mathlib.Data.Set.Card.Arithmetic`)
      converts the iUnion ncard to `∑ᶠ Q, Set.ncard ((Q : Set G) \ {1})`
      using `hdisj` (the in-flight S16 PR #17586 target).
    * `hfiber` (the in-flight S16 PR #17587 target) makes each summand
      `2`, giving `∑ᶠ Q, 2`.
    * `finsum_eq_sum_of_fintype` + `Finset.sum_const` + `Finset.card_univ`
      + `Nat.card_eq_fintype_card` + `hn3` yields `Nat.card (Sylow 3 G) • 2
      = 4 • 2 = 8`.
    * Final: `1 + 8 = 9` by `decide`.

    **Non-overlap with in-flight PRs**:
    * #17586 / #17587 target the *atomic ingredients* of the partition
      (Set-level pairwise disjointness and per-fiber cardinality);
      S23 *composes* them with S15 and the Mathlib `Set.ncard_iUnion`
      arithmetic to produce the cube-id count. Strictly downstream — no
      content overlap.
    * #17685 (S19, forward subset for ingredient 4) targets the Sylow-2
      side; independent of the Sylow-3-side partition arithmetic here.

    **Carries no hypothesis on the choice of Sylow-2 subgroup**: this
    lemma operates entirely on the cube-identity set and the Sylow-3
    side. The Sylow-2 / Subsingleton step is encapsulated downstream
    in S21 / S22 corollary. -/
private lemma cube_id_card_eq_nine_of_partition_ingredients
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12)
    (hdisj : ∀ Q Q' : Sylow 3 G, Q ≠ Q' →
             Disjoint ((Q : Set G) \ ({1} : Set G))
                      ((Q' : Set G) \ ({1} : Set G)))
    (hfiber : ∀ Q : Sylow 3 G,
              Set.ncard ((Q : Set G) \ ({1} : Set G)) = 2)
    (hn3 : Nat.card (Sylow 3 G) = 4) :
    Set.ncard {g : G | g ^ 3 = 1} = 9 := by
  -- Step 1: S15 decomposition rewrites the cube-identity set as a
  -- singleton ∪ iUnion of punctured Sylow-3 subgroups.
  rw [cube_id_set_eq_disjoint_union hcard]
  -- Step 2: Disjointness of {1} from the iUnion. Pointwise: `1 ∉ Q \ {1}`
  -- for every Sylow 3 subgroup `Q`, hence `Set.disjoint_iUnion_right`
  -- discharges disjointness against the indexed family.
  have h_disj_singleton_iUnion :
      Disjoint ({1} : Set G)
               (⋃ Q : Sylow 3 G, ((Q : Set G) \ ({1} : Set G))) := by
    rw [Set.disjoint_iUnion_right]
    intro Q
    refine Set.disjoint_left.mpr ?_
    intro g hg hg'
    rw [Set.mem_singleton_iff] at hg
    exact hg'.2 hg
  -- Step 3: ncard of the singleton-iUnion union via `Set.ncard_union_eq`,
  -- yielding `1 + Set.ncard (⋃ Q, Q \ {1})`.
  rw [Set.ncard_union_eq h_disj_singleton_iUnion (Set.finite_singleton _)
        (Set.toFinite _),
      Set.ncard_singleton]
  -- Step 4: ncard of the disjoint iUnion via `Set.ncard_iUnion_of_finite`.
  -- Converts `hdisj` to the `Pairwise (Disjoint on _)` form expected by
  -- the Mathlib API.
  have hfin :
      ∀ Q : Sylow 3 G, ((Q : Set G) \ ({1} : Set G)).Finite :=
    fun _ => Set.toFinite _
  have hdisj_pairwise :
      Pairwise (Function.onFun Disjoint
                fun Q : Sylow 3 G => (Q : Set G) \ ({1} : Set G)) := by
    intro Q Q' hne
    exact hdisj Q Q' hne
  rw [Set.ncard_iUnion_of_finite hfin hdisj_pairwise]
  -- Step 5: substitute the per-fiber cardinality `hfiber` via
  -- `finsum_congr` to convert each `Set.ncard (Q \ {1})` to `2`.
  have hsum_eq :
      (∑ᶠ Q : Sylow 3 G, Set.ncard ((Q : Set G) \ ({1} : Set G)))
        = ∑ᶠ _Q : Sylow 3 G, (2 : ℕ) :=
    finsum_congr (fun Q => hfiber Q)
  rw [hsum_eq]
  -- Step 6: collapse `∑ᶠ Q, 2` to `Nat.card (Sylow 3 G) • 2 = 4 • 2 = 8`
  -- via the `Fintype`/`Finset` bridge, using `Fintype.ofFinite` to obtain
  -- a `Fintype` instance from the ambient `Finite (Sylow 3 G)` synthesis.
  haveI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hn3]
  -- Final arithmetic: 1 + 4 • 2 = 9.
  decide

/-- **S10 closure** (S24 inline): when `|G| = 12` has 4 Sylow 3-subgroups,
    the Sylow 2-subgroup is unique. Proof via element counting:
    `|{g : G | g^3 = 1}| = 1 + 4 · 2 = 9` (using pairwise trivial
    intersection of distinct prime-order Sylow 3-subgroups, now provided
    by `sylow_prime_order_disjoint_of_ne` above), so
    `|G \ {g | g^3 = 1}| = 3 = |P| - 1` for any Sylow 2-subgroup `P`,
    pinning down `P` as `{e} ∪ (G \ {g | g^3 = 1})` independent of choice.
    The pointwise membership characterization `g^3 = 1 ↔ ∃ Q, g ∈ Q` is
    provided by `g_pow_three_iff_mem_some_sylow_three` (S14 ingredient 1,
    above); the set-decomposition `{g | g^3 = 1} = {1} ∪ ⋃ Q, (Q \ {1})`
    is provided by `cube_id_set_eq_disjoint_union` (S15 ingredient 2,
    above). The S24 inline closure composes those with the S22 corollary
    `sylow_two_subsingleton_of_cube_id_card_nine` and S23
    `cube_id_card_eq_nine_of_partition_ingredients` after discharging
    the two atomic partition ingredients (`hdisj`, `hfiber`) in-place.
    See
    `research/problems/abel-ruffini-galois-extensions-oq-07/session-24-s10-inline-closure-prep.md` §2
    for the detailed line-by-line plan and Mathlib API audit. -/
private lemma sylow_two_unique_when_n3_four
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 2)] [Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12)
    (hn3 : Nat.card (Sylow 3 G) = 4) :
    Subsingleton (Sylow 2 G) := by
  -- (a) hdisj: punctured Sylow-3 subgroups are pairwise Set-disjoint.
  have hdisj : ∀ Q Q' : Sylow 3 G, Q ≠ Q' →
      Disjoint ((Q : Set G) \ ({1} : Set G))
               ((Q' : Set G) \ ({1} : Set G)) := by
    intro Q Q' hne
    have hQ_card : Nat.card (Q : Subgroup G) = 3 :=
      sylow_three_card_eq_three_of_card_twelve hcard Q
    have hQ'_card : Nat.card (Q' : Subgroup G) = 3 :=
      sylow_three_card_eq_three_of_card_twelve hcard Q'
    have h_inter_bot : (Q : Subgroup G) ⊓ (Q' : Subgroup G) = ⊥ :=
      sylow_prime_order_disjoint_of_ne Q Q' hQ_card hQ'_card hne
    refine Set.disjoint_left.mpr ?_
    rintro g ⟨hgQ, hg_ne_one⟩ ⟨hgQ', _⟩
    have hg_mem : g ∈ (Q : Subgroup G) ⊓ (Q' : Subgroup G) := ⟨hgQ, hgQ'⟩
    rw [h_inter_bot, Subgroup.mem_bot] at hg_mem
    exact hg_ne_one (by rw [Set.mem_singleton_iff]; exact hg_mem)
  -- (b) hfiber: each punctured Sylow-3 subgroup has Set.ncard 2.
  have hfiber : ∀ Q : Sylow 3 G,
      Set.ncard ((Q : Set G) \ ({1} : Set G)) = 2 := by
    intro Q
    have h3 : Nat.card (Q : Subgroup G) = 3 :=
      sylow_three_card_eq_three_of_card_twelve hcard Q
    have h1mem : (1 : G) ∈ (Q : Set G) := (Q : Subgroup G).one_mem
    have hncard : Set.ncard ((Q : Set G) : Set G) = 3 := by
      rw [← Nat.card_coe_set_eq]
      exact h3
    rw [Set.ncard_diff_singleton_of_mem h1mem, hncard]
  -- (c) Composition: S23 partition-ingredients composition + S22 corollary.
  have h9 := cube_id_card_eq_nine_of_partition_ingredients hcard hdisj hfiber hn3
  exact sylow_two_subsingleton_of_cube_id_card_nine hcard h9

/-- **Burnside `|G| = 12 = 2² · 3`** (axiom-free post-S24; the S10 closure
    in `sylow_two_unique_when_n3_four` above is now sorry-free).

    Sylow's third theorem (`card_sylow_modEq_one`) and `Sylow.card_dvd_index`
    give `n_3 ≡ 1 [MOD 3]` and `n_3 ∣ 4`, hence `n_3 ∈ {1, 4}` via
    `sylow_count_dvd_four_modEq_one_three`.

    - **`n_3 = 1`**: the unique Sylow 3-subgroup `Q` is normal
      (`Sylow.normal_of_subsingleton`); discharge via
      `burnside_pq_with_normal_qSylow` with `(a, b) = (2, 1)`.
    - **`n_3 = 4`**: `sylow_two_unique_when_n3_four` (S10) gives
      `Subsingleton (Sylow 2 G)`; the unique Sylow 2-subgroup `P` is
      normal with `|P| = 4 = 2²`; discharge via
      `burnside_pq_with_normal_pSylow` with `(a, b) = (2, 1)`. -/
theorem burnside_p_squared_q_twelve
    {G : Type*} [Group G] [Finite G]
    [hp : Fact (Nat.Prime 2)] [hq : Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12) :
    IsSolvable G := by
  -- |G| = 12 = 2² · 3¹
  have hcard' : Nat.card G = 2 ^ 2 * 3 ^ 1 := by rw [hcard]; norm_num
  -- Coprimality witness
  have hcop : Nat.Coprime (2 ^ 2) (3 ^ 1) := by decide
  -- Step 1: Sylow 3-subgroup Q has |Q| = 3
  obtain ⟨Q⟩ : Nonempty (Sylow 3 G) := inferInstance
  have h3_not_dvd_4 : ¬ (3 : ℕ) ∣ 2 ^ 2 := by decide
  have hQ_card : Nat.card (Q : Subgroup G) = 3 := by
    have hmult := Sylow.card_eq_multiplicity Q
    have hfact : Nat.factorization (Nat.card G) 3 = 1 := by
      rw [hcard']
      rw [Nat.factorization_mul_apply_of_coprime hcop,
          Nat.factorization_eq_zero_of_not_dvd h3_not_dvd_4,
          Nat.Prime.factorization_pow hq.out]
      simp
    rw [hfact, pow_one] at hmult
    exact hmult
  -- Step 2: Q.index = 4 (Lagrange + cancellation)
  have hQ_index : (Q : Subgroup G).index = 4 := by
    have h := Subgroup.card_mul_index (Q : Subgroup G)
    rw [hQ_card, hcard] at h
    omega
  -- Step 3: n_3 ≡ 1 [MOD 3] and n_3 ∣ 4; helper forces n_3 ∈ {1, 4}.
  have hn3_mod : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hn3_dvd : Nat.card (Sylow 3 G) ∣ 4 := hQ_index ▸ Sylow.card_dvd_index Q
  have hn3_pos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  rcases sylow_count_dvd_four_modEq_one_three hn3_pos hn3_dvd hn3_mod with hn3 | hn3
  · -- Case n_3 = 1: Q is normal; discharge.
    haveI hSub : Subsingleton (Sylow 3 G) :=
      (Nat.card_eq_one_iff_unique.mp hn3).1
    haveI hQ_normal : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
    exact burnside_pq_with_normal_qSylow (a := 2) (b := 1) hcard' (Q : Subgroup G) hQ_card
  · -- Case n_3 = 4: derive Subsingleton (Sylow 2 G) via S10 lemma; discharge.
    haveI hSub2 : Subsingleton (Sylow 2 G) := sylow_two_unique_when_n3_four hcard hn3
    obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
    have h2_not_dvd_3 : ¬ (2 : ℕ) ∣ 3 ^ 1 := by decide
    have hP_card : Nat.card (P : Subgroup G) = 2 ^ 2 := by
      have hmult := Sylow.card_eq_multiplicity P
      have hfact : Nat.factorization (Nat.card G) 2 = 2 := by
        rw [hcard']
        rw [Nat.factorization_mul_apply_of_coprime hcop,
            Nat.Prime.factorization_pow hp.out,
            Nat.factorization_eq_zero_of_not_dvd h2_not_dvd_3]
        simp
      rw [hfact] at hmult
      exact hmult
    haveI hP_normal : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
    exact burnside_pq_with_normal_pSylow (a := 2) (b := 1) hcard' (P : Subgroup G) hP_card

/-! Iteration 11 (S11) — symmetric `(a, b) = (1, 2)` shape, axiom-free.

    The S7/S7.5/S9 trio fully discharges `(a, b) = (2, 1)` (with the S10
    sorry). This iteration mirrors it for `(a, b) = (1, 2)`: `|G| = p · q²`.

    The two non-exceptional cases follow by direct mirroring:
      * **`p < q` (mirror of S7)**: `n_q ∣ p` and `n_q ≡ 1 [MOD q]` with
        `p < q` forces `n_q = 1` (helper `sylow_count_eq_one_of_lt_prime`,
        applied with `(p, q)` swapped).
      * **`q < p`, `(p, q) ≠ (3, 2)` (mirror of S7.5)**: `n_p ∣ q²` and
        `n_p ≡ 1 [MOD p]` with `q < p` and `(q, p) ≠ (2, 3)` forces
        `n_p = 1` (helper `sylow_count_eq_one_of_lt_prime_pow_two`,
        applied with `(p, q)` swapped).

    The exceptional case `(p, q) = (3, 2)` gives `|G| = 3 · 4 = 12`, which
    coincides with the `|G| = 12 = 2² · 3` group order from S9. Reuses
    `burnside_p_squared_q_twelve` directly via a thin wrapper.

    After S11, `burnside_pq_nontrivial` will be axiom-only for shapes with
    `2 ≤ a ∧ 2 ≤ b` (modulo the S10 sorry); S12 updates the dispatch. -/

/-- **Burnside `|G| = p · q²`, case `p < q`** (axiom-free).

    Mirror of `burnside_p_squared_q_p_gt_q`. Sylow's third theorem
    (`card_sylow_modEq_one`) gives `n_q ≡ 1 [MOD q]`, and
    `Sylow.card_dvd_index` gives `n_q ∣ p` (the index of a Sylow
    `q`-subgroup is `p`, since `|Q| = q²` and `|G| = p · q²`). The helper
    `sylow_count_eq_one_of_lt_prime`, with primes swapped to `(q, p)`,
    forces `n_q = 1`: `p ≡ 1 [MOD q]` with `p < q` is impossible.

    With `n_q = 1`, the unique Sylow `q`-subgroup `Q` is normal
    (`Sylow.normal_of_subsingleton`). Then `burnside_pq_with_normal_qSylow`
    discharges, treating `|G| = p¹ · q²`.

    This eliminates the `(a, b) = (1, 2)` shape from the
    `burnside_pq_nontrivial` axiom whenever `p < q`. -/
theorem burnside_p_q_squared_p_lt_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p < q) (hcard : Nat.card G = p * q ^ 2) :
    IsSolvable G := by
  -- Step 1: pick a Sylow q-subgroup; |Q| = q² by `Sylow.card_eq_multiplicity`.
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  have hp_ne_q : p ≠ q := by omega
  have hq_ne_p : q ≠ p := fun h => hp_ne_q h.symm
  have hq_not_dvd_p : ¬ q ∣ p :=
    mt (Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp hq_ne_p
  have hcop : Nat.Coprime p (q ^ 2) :=
    (((Nat.coprime_primes hp.out hq.out).mpr hp_ne_q)).pow_right 2
  have hQ_card : Nat.card (Q : Subgroup G) = q ^ 2 := by
    have hmult := Sylow.card_eq_multiplicity Q
    have hfact : Nat.factorization (Nat.card G) q = 2 := by
      rw [hcard, Nat.factorization_mul_apply_of_coprime hcop,
          Nat.factorization_eq_zero_of_not_dvd hq_not_dvd_p,
          Nat.Prime.factorization_pow hq.out]
      simp
    rw [hfact] at hmult
    exact hmult
  -- Step 2: index of Q is p (Lagrange + cancellation).
  have hq2_pos : 0 < q ^ 2 := pow_pos hq.out.pos 2
  have hQ_index : (Q : Subgroup G).index = p := by
    have h := Subgroup.card_mul_index (Q : Subgroup G)
    rw [hQ_card, hcard, mul_comm p (q ^ 2)] at h
    exact Nat.eq_of_mul_eq_mul_left hq2_pos h
  -- Step 3: n_q ≡ 1 [MOD q] and n_q ∣ p; helper (with primes swapped) forces n_q = 1.
  have hnq_mod : Nat.card (Sylow q G) ≡ 1 [MOD q] := card_sylow_modEq_one q G
  have hnq_dvd : Nat.card (Sylow q G) ∣ p := hQ_index ▸ Sylow.card_dvd_index Q
  have hnq_eq_one : Nat.card (Sylow q G) = 1 :=
    sylow_count_eq_one_of_lt_prime hq.out hp.out hpq hnq_mod hnq_dvd
  -- Step 4: n_q = 1 ⇒ Subsingleton (Sylow q G) ⇒ Q.Normal.
  haveI hSub : Subsingleton (Sylow q G) :=
    (Nat.card_eq_one_iff_unique.mp hnq_eq_one).1
  haveI hQ_normal : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
  -- Step 5: discharge via burnside_pq_with_normal_qSylow with a = 1, b = 2.
  have hcard' : Nat.card G = p ^ 1 * q ^ 2 := by rw [pow_one]; exact hcard
  exact burnside_pq_with_normal_qSylow (a := 1) (b := 2) hcard' (Q : Subgroup G) hQ_card

/-- **Burnside `|G| = p · q²`, case `q < p`, non-exceptional** (axiom-free).

    Mirror of `burnside_p_squared_q_p_lt_q`. Sylow's third theorem
    gives `n_p ≡ 1 [MOD p]`, and `Sylow.card_dvd_index` gives
    `n_p ∣ q²` (the index of a Sylow `p`-subgroup is `q²`, since
    `|P| = p` and `|G| = p · q²`). The helper
    `sylow_count_eq_one_of_lt_prime_pow_two`, with primes swapped to
    `(q, p)`, then forces `n_p = 1`, using `(q, p) ≠ (2, 3)` (i.e.,
    `(p, q) ≠ (3, 2)`) to rule out the `n_p = q²` case.

    With `n_p = 1`, the unique Sylow `p`-subgroup `P` is normal
    (`Sylow.normal_of_subsingleton`). Then `burnside_pq_with_normal_pSylow`
    discharges, treating `|G| = p¹ · q²`.

    Together with `burnside_p_q_squared_p_lt_q` and the exceptional case
    `(p, q) = (3, 2)` handled via `burnside_p_q_squared_twelve_mirror`,
    this completes the `(a, b) = (1, 2)` shape elimination. -/
theorem burnside_p_q_squared_q_lt_p
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : q < p) (hexc : ¬ (p = 3 ∧ q = 2))
    (hcard : Nat.card G = p * q ^ 2) :
    IsSolvable G := by
  -- Step 1: pick a Sylow p-subgroup; |P| = p^1 = p by `Sylow.card_eq_multiplicity`.
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hp_ne_q : p ≠ q := by omega
  have hp_not_dvd_q2 : ¬ p ∣ q ^ 2 := by
    intro hdvd
    have : p ∣ q := hp.out.dvd_of_dvd_pow hdvd
    exact hp_ne_q ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp this)
  have hcop : Nat.Coprime p (q ^ 2) :=
    (((Nat.coprime_primes hp.out hq.out).mpr hp_ne_q)).pow_right 2
  have hP_card : Nat.card (P : Subgroup G) = p := by
    have hmult := Sylow.card_eq_multiplicity P
    have hfact : Nat.factorization (Nat.card G) p = 1 := by
      rw [hcard, Nat.factorization_mul_apply_of_coprime hcop,
          Nat.Prime.factorization_self hp.out,
          Nat.factorization_eq_zero_of_not_dvd hp_not_dvd_q2]
    rw [hfact, pow_one] at hmult
    exact hmult
  -- Step 2: index of P is q² (Lagrange + cancellation).
  have hp_pos : 0 < p := hp.out.pos
  have hP_index : (P : Subgroup G).index = q ^ 2 := by
    have h := Subgroup.card_mul_index (P : Subgroup G)
    rw [hP_card, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hp_pos h
  -- Step 3: n_p ≡ 1 [MOD p] and n_p ∣ q²; helper (primes swapped) forces n_p = 1.
  have hnp_mod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have hnp_dvd : Nat.card (Sylow p G) ∣ q ^ 2 := hP_index ▸ Sylow.card_dvd_index P
  -- Translate `hexc : ¬ (p = 3 ∧ q = 2)` to the helper's swapped frame.
  have hexc' : ¬ (q = 2 ∧ p = 3) := fun ⟨hq2, hp3⟩ => hexc ⟨hp3, hq2⟩
  have hnp_eq_one : Nat.card (Sylow p G) = 1 :=
    sylow_count_eq_one_of_lt_prime_pow_two hq.out hp.out hpq hexc' hnp_mod hnp_dvd
  -- Step 4: n_p = 1 ⇒ Subsingleton (Sylow p G) ⇒ P.Normal.
  haveI hSub : Subsingleton (Sylow p G) :=
    (Nat.card_eq_one_iff_unique.mp hnp_eq_one).1
  haveI hP_normal : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  -- Step 5: discharge via burnside_pq_with_normal_pSylow with a = 1, b = 2.
  have hcard' : Nat.card G = p ^ 1 * q ^ 2 := by rw [pow_one]; exact hcard
  have hP_card' : Nat.card (P : Subgroup G) = p ^ 1 := by rw [pow_one]; exact hP_card
  exact burnside_pq_with_normal_pSylow (a := 1) (b := 2) hcard' (P : Subgroup G) hP_card'

/-- **Burnside `|G| = 12 = 3 · 2²`, mirror of S9** (axiom-free post-S24;
    inherits `burnside_p_squared_q_twelve`'s now-closed S10 status).

    The exceptional case `(p, q) = (3, 2)` of the `(a, b) = (1, 2)`
    shape: `|G| = p · q² = 3 · 4 = 12`. This is the same group order as
    the S9 case `|G| = 12 = 2² · 3`, just viewed under the mirror
    factorisation. The proof is a thin wrapper around
    `burnside_p_squared_q_twelve`. -/
theorem burnside_p_q_squared_twelve_mirror
    {G : Type*} [Group G] [Finite G]
    [Fact (Nat.Prime 2)] [Fact (Nat.Prime 3)]
    (hcard : Nat.card G = 12) :
    IsSolvable G :=
  burnside_p_squared_q_twelve hcard

-- ═══════════════════════════════════════════════════════════════════════
-- PART III.7: Consolidated `(a, b) ∈ {(2, 1), (1, 2)}` theorems
--             (S25 — uniform dispatch interface)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Burnside `|G| = p² · q`** (consolidated, axiom-free).

    Combines `burnside_p_squared_q_p_gt_q` (S7),
    `burnside_p_squared_q_p_lt_q` (S7.5), and
    `burnside_p_squared_q_twelve` (S9 + S24 inline closure) into a
    single interface keyed only on `p ≠ q` and `Nat.card G = p² · q`.
    The internal case-split on the `(p, q)` relation:
    * `q < p`           → S7  (axiom-free)
    * `p < q ∧ ¬ (p = 2 ∧ q = 3)` → S7.5 (axiom-free)
    * `p = 2 ∧ q = 3`   → S9 wrapper (`|G| = 12`); axiom-free post-S24.

    The S25 `burnside_pq` dispatch uses this consolidated form to peel
    off the `(a, b) = (2, 1)` shape without enumerating the `(p, q)`
    cases at the top level. -/
theorem burnside_p_squared_q
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p ^ 2 * q) :
    IsSolvable G := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · -- p < q
    by_cases hexc : p = 2 ∧ q = 3
    · -- |G| = 2² · 3 = 12
      obtain ⟨hp2, hq3⟩ := hexc
      subst hp2
      subst hq3
      have h12 : Nat.card G = 12 := by rw [hcard]; norm_num
      exact burnside_p_squared_q_twelve h12
    · exact burnside_p_squared_q_p_lt_q hlt hexc hcard
  · exact absurd heq hpq
  · -- q < p
    exact burnside_p_squared_q_p_gt_q hgt hcard

/-- **Burnside `|G| = p · q²`** (consolidated, axiom-free).

    Mirror of `burnside_p_squared_q`. Combines
    `burnside_p_q_squared_p_lt_q` (S11.1), `burnside_p_q_squared_q_lt_p`
    (S11.2), and `burnside_p_q_squared_twelve_mirror` (S11.3 +
    S24 inline closure) into a single interface. The case-split:
    * `p < q`           → S11.1 (axiom-free)
    * `q < p ∧ ¬ (p = 3 ∧ q = 2)` → S11.2 (axiom-free)
    * `p = 3 ∧ q = 2`   → S11.3 wrapper (`|G| = 12`); axiom-free post-S24.

    The exceptional case `(p, q) = (3, 2)` lives inside `q < p` (since
    `q = 2 < 3 = p`), in contrast to `burnside_p_squared_q`'s `(2, 3)`
    case which lives inside `p < q`.

    The S25 `burnside_pq` dispatch uses this consolidated form to peel
    off the `(a, b) = (1, 2)` shape. -/
theorem burnside_p_q_squared
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hcard : Nat.card G = p * q ^ 2) :
    IsSolvable G := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · -- p < q
    exact burnside_p_q_squared_p_lt_q hlt hcard
  · exact absurd heq hpq
  · -- q < p
    by_cases hexc : p = 3 ∧ q = 2
    · -- |G| = 3 · 4 = 12 (mirror)
      obtain ⟨hp3, hq2⟩ := hexc
      subst hp3
      subst hq2
      have h12 : Nat.card G = 12 := by rw [hcard]; norm_num
      exact burnside_p_q_squared_twelve_mirror h12
    · exact burnside_p_q_squared_q_lt_p hgt hexc hcard

-- ═══════════════════════════════════════════════════════════════════════
-- PART IV: Main theorem
-- ═══════════════════════════════════════════════════════════════════════

/-- **Burnside's pᵃqᵇ theorem**: every finite group of order `p^a · q^b`
    (for primes `p, q` and naturals `a, b`) is solvable.

    Combines:
    - the three axiom-free trivial cases (`a = 0`, `b = 0`, `p = q`),
    - the axiom-free squarefree-order case (`a = b = 1`, `p ≠ q`),
    - the axiom-free `(a, b) = (2, 1)` case via `burnside_p_squared_q`
      (S25 consolidation of S7+S7.5+S9+S24),
    - the axiom-free `(a, b) = (1, 2)` case via `burnside_p_q_squared`
      (S25 consolidation of S11.1+S11.2+S11.3+S24),
    - the conjectural non-trivial case (`burnside_pq_nontrivial`,
      narrowed in S25 to `4 ≤ a + b`). -/
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
    · -- S25: peel off (a, b) = (2, 1) via burnside_p_squared_q
      by_cases h21 : a = 2 ∧ b = 1
      · obtain ⟨ha2, hb1⟩ := h21
        subst ha2
        subst hb1
        have hcard' : Nat.card G = p ^ 2 * q := by simpa [pow_one] using hcard
        exact burnside_p_squared_q hpq hcard'
      · -- S25: peel off (a, b) = (1, 2) via burnside_p_q_squared
        by_cases h12 : a = 1 ∧ b = 2
        · obtain ⟨ha1, hb2⟩ := h12
          subst ha1
          subst hb2
          have hcard' : Nat.card G = p * q ^ 2 := by simpa [pow_one] using hcard
          exact burnside_p_q_squared hpq hcard'
        · -- Residue: a + b ≥ 4. Apply narrowed axiom.
          have hab : 4 ≤ a + b := by
            by_contra hcontra
            push_neg at hcontra
            -- a ≥ 1, b ≥ 1, a + b < 4 ⇒ (a, b) ∈ {(1,1), (2,1), (1,2)}
            have ha_le : a ≤ 2 := by omega
            have hb_le : b ≤ 2 := by omega
            interval_cases a <;> interval_cases b <;>
              first
                | exact h11 ⟨rfl, rfl⟩
                | exact h12 ⟨rfl, rfl⟩
                | exact h21 ⟨rfl, rfl⟩
                | omega
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
#check @burnside_p_squared_q
#check @burnside_p_q_squared
#check @alternatingGroupFin5_card
#check @alternatingGroupFin5_not_solvable
#check @burnside_pq_sharp

end BurnsidePQ
