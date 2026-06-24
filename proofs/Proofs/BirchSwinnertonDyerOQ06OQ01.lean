import Mathlib

/-
# Cremona Classification: 389a1 is the Smallest-Conductor Rank-2 Elliptic Curve

## Open Question: birch-swinnerton-dyer-oq-06-oq-01

The parent entry (OQ-06) records, as a docstring remark, that the curve
**389a1: y² + y = x³ + x² - 2x** (conductor N = 389) is "the smallest-conductor
rank-2 elliptic curve over ℚ", but only proves the trivial arithmetic facts
`389 = 389` and `Nat.Prime 389`. This entry formalizes the *content* of that
minimality claim.

## What is and is not provable here

The genuine mathematical statement — *no* elliptic curve over ℚ of rank 2 has
conductor below 389 — is **Cremona's exhaustive computation**: every isogeny
class of conductor < 389 was enumerated and its Mordell–Weil rank determined by
descent, and none reaches rank 2. This is a finite but enormous verification
(thousands of curves, each needing a rigorous rank computation) that lies far
outside what can be reproduced inside Lean today.

We therefore formalize the **logical structure** of the result:

  * an abstract minimal-conductor predicate `IsMinConductorForRank`,
  * the derivation that the classification lower bound implies minimality,
  * uniqueness of the minimal conductor value and its contrapositive form,
  * the verified arithmetic of the Cremona *rank records* (smallest conductor
    realised at each rank): 11 (rank 0), 37 (rank 1), 389 (rank 2), 5077 (rank 3),
    including their strict monotonicity in the rank.

The deep computational input enters as an **explicit hypothesis**
`hcremona : ∀ E', rk E' = 2 → 389 ≤ cond E'`, *not* as an axiom. Consequently
every declaration below is a fully machine-checked theorem with **no axioms and
no `sorry`**; the headline result is the implication
"Cremona's classification ⟹ 389a1 is minimal", which is the honest maximal
content available for this problem.

## References
  * J.E. Cremona, *Algorithms for Modular Elliptic Curves* (Cambridge, 1992);
    online Elliptic Curve Database.
  * J.P. Buhler, B.H. Gross, D.B. Zagier, "On the conjecture of Birch and
    Swinnerton-Dyer for an elliptic curve of rank 3" (Math. Comp. 44, 1985).
  * LMFDB curves 11.a, 37.a, 389.a, 5077.a.

**Axiom count**: 0   **Sorry count**: 0
-/

namespace BirchSwinnertonDyerOQ06OQ01

/-! ## Part I: Abstract minimal-conductor framework

We work over an abstract carrier `E` of elliptic curves over ℚ, equipped with a
conductor function `cond : E → ℕ` and an (algebraic / Mordell–Weil) rank
function `rk : E → ℕ`. Nothing here depends on the analytic theory; the
statements are purely about the order structure of conductors at a fixed rank. -/

section Abstract

variable {E : Type*}

/-- `IsMinConductorForRank cond rk E₀ r` asserts that `E₀` has rank `r` and that
no curve of rank `r` has strictly smaller conductor — i.e. `E₀` realises the
smallest conductor among all rank-`r` curves. -/
def IsMinConductorForRank (cond rk : E → ℕ) (E₀ : E) (r : ℕ) : Prop :=
  rk E₀ = r ∧ ∀ E', rk E' = r → cond E₀ ≤ cond E'

/-- **Master derivation.** If `E₀` has rank `r`, conductor `N`, and *every*
rank-`r` curve has conductor `≥ N` (the classification lower bound), then `E₀`
is a minimal-conductor curve for rank `r`. -/
theorem isMinConductorForRank_of_lb
    {cond rk : E → ℕ} {E₀ : E} {r N : ℕ}
    (hrank : rk E₀ = r) (hcond : cond E₀ = N)
    (hlb : ∀ E', rk E' = r → N ≤ cond E') :
    IsMinConductorForRank cond rk E₀ r := by
  refine ⟨hrank, ?_⟩
  intro E' hE'
  rw [hcond]
  exact hlb E' hE'

/-- A minimal-conductor curve dominates every rank-`r` curve. -/
theorem le_conductor_of_minConductor
    {cond rk : E → ℕ} {E₀ E' : E} {r : ℕ}
    (h : IsMinConductorForRank cond rk E₀ r) (hE' : rk E' = r) :
    cond E₀ ≤ cond E' := h.2 E' hE'

/-- **Uniqueness of the minimal conductor value.** Any two minimal-conductor
curves for the same rank have equal conductor (the minimum is well defined even
though the minimising curve need not be unique up to isomorphism). -/
theorem minConductor_unique
    {cond rk : E → ℕ} {E₁ E₂ : E} {r : ℕ}
    (h₁ : IsMinConductorForRank cond rk E₁ r)
    (h₂ : IsMinConductorForRank cond rk E₂ r) :
    cond E₁ = cond E₂ :=
  le_antisymm (h₁.2 E₂ h₂.1) (h₂.2 E₁ h₁.1)

/-- **Contrapositive form.** A curve whose conductor is below the minimum for
rank `r` cannot itself have rank `r`. -/
theorem rank_ne_of_conductor_lt
    {cond rk : E → ℕ} {E₀ E' : E} {r : ℕ}
    (h : IsMinConductorForRank cond rk E₀ r) (hlt : cond E' < cond E₀) :
    rk E' ≠ r := by
  intro hE'
  exact absurd (h.2 E' hE') (not_le.mpr hlt)

end Abstract

/-! ## Part II: The Cremona rank-record registry (verified arithmetic)

The Cremona database singles out, for each small rank, the curve of smallest
conductor achieving that rank. These four "records" are the backbone of the
classification; their conductors are strictly increasing in the rank. -/

/-- The smallest-conductor curve realising a given rank, as a data record. -/
structure RankRecord where
  /-- Mordell–Weil rank realised. -/
  rank : ℕ
  /-- Conductor of the record curve. -/
  conductor : ℕ
  /-- Cremona label. -/
  label : String

/-- Rank 0 record: 11a1, conductor 11 (smallest conductor of any elliptic curve /ℚ). -/
def record0 : RankRecord := ⟨0, 11, "11a1"⟩
/-- Rank 1 record: 37a1, conductor 37. -/
def record1 : RankRecord := ⟨1, 37, "37a1"⟩
/-- Rank 2 record: 389a1, conductor 389 — the curve of this entry. -/
def record2 : RankRecord := ⟨2, 389, "389a1"⟩
/-- Rank 3 record: 5077a1, conductor 5077. -/
def record3 : RankRecord := ⟨3, 5077, "5077a1"⟩

/-- The ordered list of Cremona rank records for ranks 0–3. -/
def cremonaRecords : List RankRecord := [record0, record1, record2, record3]

/-- Curve 389a1 carries conductor 389 and rank 2. -/
theorem record2_data : record2.conductor = 389 ∧ record2.rank = 2 := ⟨rfl, rfl⟩

/-- The conductor 389 of the rank-2 record is prime. -/
theorem record2_conductor_prime : Nat.Prime 389 := by norm_num

/-- **Minimal conductors strictly increase with rank.**
`11 < 37 < 389 < 5077`. -/
theorem records_conductor_strictMono :
    record0.conductor < record1.conductor ∧
    record1.conductor < record2.conductor ∧
    record2.conductor < record3.conductor := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Among the rank records, 389 is the smallest conductor attaining rank `≥ 2`. -/
theorem records_min_conductor_rank_ge_two :
    ∀ r ∈ cremonaRecords, 2 ≤ r.rank → 389 ≤ r.conductor := by decide

/-- The rank-2 record is the *unique* record of rank exactly 2 in the registry. -/
theorem records_rank_two_unique :
    ∀ r ∈ cremonaRecords, r.rank = 2 → r.conductor = 389 := by decide

/-! ## Part III: The classification theorem for 389a1

We now state the headline result over an abstract curve space. The two
curve-specific facts (`rk c389 = 2`, `cond c389 = 389`) and Cremona's
classification lower bound are supplied as hypotheses; the conclusion is genuine
minimality, obtained from the Part I machinery. -/

section Classification

variable {E : Type*} (cond rk : E → ℕ) (c389 : E)

/-- **Main theorem (conditional on Cremona's classification).**
Let `cond, rk` assign conductor and rank to elliptic curves over ℚ and let
`c389` denote 389a1, with `rk c389 = 2` and `cond c389 = 389`. If Cremona's
exhaustive computation holds — *no rank-2 curve has conductor below 389* — then
389a1 has the smallest conductor among all rank-2 elliptic curves over ℚ. -/
theorem curve389a_isMinConductorForRank2
    (hrank : rk c389 = 2) (hcond : cond c389 = 389)
    (hcremona : ∀ E', rk E' = 2 → 389 ≤ cond E') :
    IsMinConductorForRank cond rk c389 2 :=
  isMinConductorForRank_of_lb hrank hcond hcremona

/-- Consequence: under the classification, every rank-2 curve has conductor
`≥ 389` (with 389a1 attaining the bound). -/
theorem rank2_conductor_ge_389
    (hrank : rk c389 = 2) (hcond : cond c389 = 389)
    (hcremona : ∀ E', rk E' = 2 → 389 ≤ cond E')
    (E' : E) (hE' : rk E' = 2) :
    389 ≤ cond E' := by
  have h := curve389a_isMinConductorForRank2 cond rk c389 hrank hcond hcremona
  have := le_conductor_of_minConductor h hE'
  rwa [hcond] at this

/-- Contrapositive consequence: any curve of conductor below 389 has rank `≠ 2`.
This is the precise sense in which 389 is the *threshold* conductor for rank 2. -/
theorem conductor_lt_389_rank_ne_two
    (hrank : rk c389 = 2) (hcond : cond c389 = 389)
    (hcremona : ∀ E', rk E' = 2 → 389 ≤ cond E')
    (E' : E) (hlt : cond E' < 389) :
    rk E' ≠ 2 := by
  have h := curve389a_isMinConductorForRank2 cond rk c389 hrank hcond hcremona
  refine rank_ne_of_conductor_lt h ?_
  rwa [hcond]

end Classification

/-- **Summary of the verified (unconditional) content of this entry.**
389 is prime, the rank-record conductors are strictly increasing, and 389a1 is
the rank-2 record. The minimality statement itself is the conditional theorem
`curve389a_isMinConductorForRank2`. -/
theorem cremona_389a_summary :
    Nat.Prime 389 ∧
    record0.conductor < record1.conductor ∧
    record1.conductor < record2.conductor ∧
    record2.conductor < record3.conductor ∧
    record2.rank = 2 ∧ record2.conductor = 389 := by
  refine ⟨by norm_num, ?_, ?_, ?_, rfl, rfl⟩ <;> decide

end BirchSwinnertonDyerOQ06OQ01
