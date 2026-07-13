/-
# L1: Index-2 subgroup chain for a finite 2-group  (SCRATCH DRAFT — UNVERIFIED)

Problem: angle-trisection-oq-02-oq-01-oq-02-oq-03
  "Full Wantzel-Galois constructibility theorem via Mathlib Galois
   correspondence and 2-group structure"

## What this file delivers

The pure group-theory core ("2-group structure") of the still-open sorry
`AngleTrisectionOQ02OQ04OQ01.galois_two_group_implies_tower` (line 240).

`galois_two_group_implies_tower` decomposes as:
  L1 (this file): a finite 2-group G has a descending chain of subgroups
       ⊤ = H₀ ⊋ H₁ ⊋ … ⊋ Hₙ = ⊥  with [Hᵢ : Hᵢ₊₁] = 2 for every i.
  L2: transport the chain through the Galois correspondence
       (`IsGalois.intermediateFieldEquivSubgroup`) to a quadratic field tower
       ℚ = E^H₀ ⊊ … ⊊ E^Hₙ = E, using `finrank_fixedField_eq_card`.
  L3: membership α ∈ E and real-descent (E is a non-real subfield of ℂ).

L1 is self-contained group theory; it is the concrete increment named by the
problem title ("2-group structure"). It extends the ALREADY-PROVED single step
`AngleTrisectionOQ02OQ04OQ01.exists_index_two_subgroup` into a full chain by
strong induction on the exponent of |G| = 2ᵏ.

## VERIFICATION STATUS

**UNVERIFIED.** Written during a Docker-build + Aristotle blackout (both tools
down, 2026-07-04). It has NOT been compiled. It lives in the problem `lean/`
scratch dir, which is *not* globbed by `proofs/lakefile.toml`, so it cannot
break the gallery build. On tool recovery: copy the two theorems into
`proofs/Proofs/AngleTrisectionOQ02OQ04OQ01.lean` (Part 3, after
`exists_index_two_subgroup`), run `docker-build.sh`, fix the name risks listed
at the bottom, THEN ship the gallery entry.

The mathematical argument is fully traced; residual risk is Lean *elaboration*
(exact lemma names for `Fin`/`Subgroup.map`), not mathematics.
-/

import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace AngleTrisectionOQ02OQ01OQ02OQ03

open scoped Classical

-- ============================================================
-- Copy of the already-proved single step (context; the real file has this).
-- ============================================================

/-- Every non-trivial finite 2-group has a subgroup of index 2.
    (Proved in `AngleTrisectionOQ02OQ04OQ01`; restated here so this scratch
    file is self-contained.) -/
theorem exists_index_two_subgroup {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (hnt : 1 < Nat.card G) :
    ∃ H : Subgroup G, H.index = 2 := by
  haveI : Fact (Nat.Prime 2) := Fact.mk (by norm_num)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [pow_zero] at hn; omega
    · exact h
  have hdvd : 2 ^ (n - 1) ∣ Nat.card G := by
    rw [hn]; exact Nat.pow_dvd_pow 2 (Nat.sub_le n 1)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨H, ?_⟩
  have hmi := H.card_mul_index
  have h2n : (2 : ℕ) ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]; rw [pow_succ]
  rw [hH, hn, h2n] at hmi
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmi

-- ============================================================
-- L1 building blocks (high-confidence; corpus-verified idioms)
-- ============================================================

/-- If `H` has index 2 in a group of order `2^(k+1)`, then `|H| = 2^k`. -/
theorem card_of_index_two {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    {k : ℕ} (hidx : H.index = 2) (hcard : Nat.card G = 2 ^ (k + 1)) :
    Nat.card H = 2 ^ k := by
  have hmi := H.card_mul_index          -- Nat.card H * H.index = Nat.card G
  rw [hidx, hcard, pow_succ] at hmi     -- Nat.card H * 2 = 2^k * 2
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) hmi

/-- Mapping a subgroup of `H` into `G` along `H.subtype` preserves cardinality.
    Idiom lifted verbatim from `LagrangeTheoremOQ03OQ02.lean:115`. -/
theorem card_map_subtype {G : Type*} [Group G] (H : Subgroup G)
    (K : Subgroup H) : Nat.card (K.map H.subtype) = Nat.card K :=
  (Nat.card_congr (Subgroup.equivMapOfInjective K H.subtype
    (Subgroup.subtype_injective H)).toEquiv).symm

/-- `⊤ ⊆ H` maps onto `H`. -/
theorem map_subtype_top {G : Type*} [Group G] (H : Subgroup G) :
    (⊤ : Subgroup H).map H.subtype = H := by
  rw [Subgroup.map_top]           -- RISK: name; goal becomes H.subtype.range = H
  exact H.range_subtype

/-- `⊥ ⊆ H` maps to `⊥`. -/
theorem map_subtype_bot {G : Type*} [Group G] (H : Subgroup G) :
    (⊥ : Subgroup H).map H.subtype = ⊥ := Subgroup.map_bot _

-- ============================================================
-- L1 main theorem
-- ============================================================

/-- **Index-2 chain (exponent-indexed auxiliary).**
    A finite 2-group of order `2^k` has a descending chain
    `⊤ = c₀ ⊋ c₁ ⊋ … ⊋ cₖ = ⊥` of subgroups with each consecutive index 2,
    encoded as `|cᵢ| = 2·|cᵢ₊₁|`. Proof by induction on `k`, generalizing `G`. -/
theorem exists_index_two_chain_aux (k : ℕ) :
    ∀ (G : Type*) [Group G] [Finite G],
      IsPGroup 2 G → Nat.card G = 2 ^ k →
      ∃ c : Fin (k + 1) → Subgroup G,
        c 0 = ⊤ ∧ c (Fin.last k) = ⊥ ∧
        ∀ i : Fin k, c i.succ ≤ c i.castSucc ∧
          Nat.card (c i.castSucc) = 2 * Nat.card (c i.succ) := by
  induction k with
  | zero =>
    intro G _ _ _ hcard
    -- |G| = 1 ⇒ G subsingleton ⇒ ⊤ = ⊥.  Chain is the single point ⊤ = ⊥.
    have hsub : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hcard).1
    have htb : (⊤ : Subgroup G) = ⊥ := by
      haveI := hsub
      exact Subsingleton.elim _ _   -- RISK: needs `Subsingleton (Subgroup G)` from `Subsingleton G`
    refine ⟨fun _ => ⊤, rfl, ?_, ?_⟩
    · simpa using htb                -- c (Fin.last 0) = ⊤ = ⊥
    · exact fun i => i.elim0         -- Fin 0 is empty
  | succ k ih =>
    intro G _ _ hG hcard
    -- G nontrivial: 1 < 2^(k+1) = |G|.
    have hnt : 1 < Nat.card G := by rw [hcard]; exact Nat.one_lt_two_pow (by omega)
    obtain ⟨H, hHidx⟩ := exists_index_two_subgroup hG hnt
    have hcardH : Nat.card H = 2 ^ k := card_of_index_two hHidx hcard
    haveI : Finite H := Subtype.finite
    have hHp : IsPGroup 2 H := hG.to_subgroup H
    obtain ⟨d, hd0, hdlast, hdstep⟩ := ih H hHp hcardH
    -- New chain: prepend ⊤, then the mapped-in chain of H.
    refine ⟨Fin.cons ⊤ (fun i => (d i).map H.subtype), Fin.cons_zero _ _, ?_, ?_⟩
    · -- last: Fin.last (k+1) = (Fin.last k).succ, cons_succ, d last = ⊥, map_bot
      rw [show (Fin.last (k + 1)) = (Fin.last k).succ from (Fin.succ_last k).symm,
          Fin.cons_succ, hdlast, map_subtype_bot]
    · -- steps: case i = 0  vs  i = j.succ
      refine Fin.cases ?_ ?_
      · -- i = 0:  ⊤  ⊋  H
        refine ⟨?_, ?_⟩
        · -- (cons ⊤ e) (0.succ) ≤ (cons ⊤ e) (0.castSucc)
          rw [Fin.castSucc_zero, Fin.cons_zero]
          -- (0 : Fin (k+1)).succ = (1 : Fin (k+2)); cons_succ gives e 0 = (d 0).map _
          rw [show ((0 : Fin (k + 1)).succ) = ((0 : Fin (k + 1)).succ) from rfl,
              Fin.cons_succ, hd0, map_subtype_top]
          exact le_top
        · -- cards: |⊤| = |G| = 2^(k+1) = 2 · 2^k = 2 · |H|
          rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hd0, map_subtype_top]
          rw [show (⊤ : Subgroup G) = ⊤ from rfl]
          have : Nat.card (⊤ : Subgroup G) = Nat.card G := Nat.card_congr Subgroup.topEquiv.toEquiv
          rw [this, hcard, hcardH, pow_succ]; ring
      · -- i = j.succ:  cᵢ = (d jₛ).map,  cᵢ₊₁ handled by cons_succ after succ_castSucc
        intro j
        have hstep := hdstep j
        refine ⟨?_, ?_⟩
        · rw [show ((j.succ).castSucc) = (j.castSucc).succ from (Fin.succ_castSucc j).symm,
              Fin.cons_succ, Fin.cons_succ]
          exact Subgroup.map_mono hstep.1
        · rw [show ((j.succ).castSucc) = (j.castSucc).succ from (Fin.succ_castSucc j).symm,
              Fin.cons_succ, Fin.cons_succ, card_map_subtype, card_map_subtype]
          exact hstep.2

/-- **Index-2 chain (public form).**
    Every finite 2-group `G` admits `n` and a descending chain
    `⊤ = c₀ ⊋ … ⊋ cₙ = ⊥` with each consecutive index 2 (`|cᵢ| = 2·|cᵢ₊₁|`).
    Here `n` is the 2-adic valuation of `|G|`. -/
theorem exists_index_two_chain {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) :
    ∃ (n : ℕ) (c : Fin (n + 1) → Subgroup G),
      c 0 = ⊤ ∧ c (Fin.last n) = ⊥ ∧
      ∀ i : Fin n, c i.succ ≤ c i.castSucc ∧
        Nat.card (c i.castSucc) = 2 * Nat.card (c i.succ) := by
  obtain ⟨n, hn⟩ := (by
    haveI : Fact (Nat.Prime 2) := Fact.mk (by norm_num)
    exact IsPGroup.iff_card.mp hG : ∃ n, Nat.card G = 2 ^ n)
  exact ⟨n, exists_index_two_chain_aux n G hG hn⟩

end AngleTrisectionOQ02OQ01OQ02OQ03

/-
## RESIDUAL ELABORATION RISKS (fix on build recovery — none are mathematical)

R1. `Subgroup.map_top` : `Subgroup.map f ⊤ = f.range`.
      If misnamed, fallbacks: `Subgroup.map_top_eq_range`, or prove
      `map_subtype_top` directly by `ext x; simp [Subgroup.mem_map, H.range_subtype]`.
R2. `Subsingleton.elim (⊤ : Subgroup G) ⊥` in the base case relies on
      `Subsingleton (Subgroup G)` being derivable from `Subsingleton G`.
      Fallback: `Subgroup.ext fun x => by simp [Subsingleton.elim x 1]` or
      `(Subgroup.eq_bot_iff_card ... )`.  (Base case k=0 is a degenerate leaf;
      worst case, state the public theorem for `1 < Nat.card G` and treat the
      trivial group separately — the tower application never needs the leaf.)
R3. `Fin.succ_last k : (Fin.last k).succ = Fin.last (k+1)` — verify direction;
      may be `Fin.succ_last` or need `Fin.last_succ`.
R4. `Fin.succ_castSucc j : (j.castSucc).succ = (j.succ).castSucc` — verify the
      orientation; Mathlib has `Fin.succ_castSucc` and/or `Fin.castSucc_succ`.
R5. `Fin.castSucc_zero : (0 : Fin (n+1)).castSucc = 0` — verify name.
R6. `Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G` — used for `|⊤| = |G|`; verify.
R7. `Subgroup.map_mono : H ≤ K → H.map f ≤ K.map f` — verify name (may be
      `Subgroup.map_mono` / `Subgroup.map_le_map`).
R8. `Subgroup.map_bot : (⊥).map f = ⊥` — standard, verify name.

CONFIRMED PRESENT in the compiling proofs/Proofs corpus (grep):
  `Subgroup.equivMapOfInjective`, `Subgroup.subtype_injective`,
  `Subgroup.card_map_of_injective`, `Nat.card_congr`, `range_subtype`,
  `card_mul_index`, `Fin.cons_zero`, `Fin.cons_succ`, `Fin.last`,
  `IsPGroup.to_subgroup`, `IsPGroup.iff_card`, `Sylow.exists_subgroup_card_pow_prime`.

## HANDOFF FOR L2 (the real remaining bottleneck)
After L1 lands, `galois_two_group_implies_tower` still needs:
  - `IsGalois ℚ E` for E = (minpoly ℚ α).SplittingField, then transport L1's
    subgroup chain to a field tower via `IsGalois.intermediateFieldEquivSubgroup`
    and `IntermediateField.finrank_fixedField_eq_card`
    (index-2 subgroup ↦ degree-2 field step).
  - The bridge `Polynomial.Gal p ≃ Gal(E/ℚ)` as `fixingSubgroup`/`fixedField`
    target (~100 lines API glue) — recorded as the main blocker in knowledge.md.
  - Real-descent: E is generally a NON-real subfield of ℂ; the file's
    `ConstructibleViaTower` is ℝ-phrased. Recommend proving a ℂ-valued
    `galois_two_group_implies_tower_C` first, then descend.
-/
