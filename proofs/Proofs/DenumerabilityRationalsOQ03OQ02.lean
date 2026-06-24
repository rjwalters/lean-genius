import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Proofs.DenumerabilityRationalsOQ03

/-
# Surjectivity of the Stern-Brocot Encoding (OQ-03-OQ-02)

## What This Proves

The parent file `DenumerabilityRationalsOQ03.lean` builds the Stern-Brocot tree
as a state machine on left/right paths and proves that the path-evaluation map
is **injective** (`eval_injective`): different left/right paths reach different
nodes.

This file proves the complementary half — **surjectivity** — and assembles the
two into the full **Stern-Brocot bijection** between binary paths and the
positive rationals:

1. `reach_aux`     — the key reachability lemma: from any det=1 state, every
                     pair of positive "ancestor coordinates" `(a, b)` is reached
                     by some path. The proof is the subtractive Euclidean
                     algorithm, with `a + b` as the strictly decreasing measure.
2. `reach_root`    — every coprime pair `(p, q)` with `p, q ≥ 1` occurs as the
                     `(numerator, denominator)` of some Stern-Brocot node.
3. `toRat_surjective` — every positive rational is `toRat t` for some path `t`.
4. `mediant_inj` / `toRat_injective` — the value map (numerator/denominator, and
                     hence `toRat`) is injective: distinct paths give distinct
                     rationals. This sharpens the parent's *state* injectivity to
                     injectivity of the *rational value*.
5. `sternBrocot_bijection` — `toRat` is injective and its range is exactly the
                     positive rationals. This is a constructive, duplicate-free
                     enumeration of `ℚ⁺` with no use of Cantor pairing or choice.

## Why This Matters

The parent left "surjectivity onto every positive rational" as the explicit open
follow-up. Mathlib has no Stern-Brocot / Calkin-Wilf tree, so this is an original
formalization. Together with the parent's injectivity it gives the headline
denumerability fact in its sharpest constructive form: a bijection
`paths ≃ ℚ⁺` whose nodes are automatically in lowest terms.

## The Coordinate Trick

A reachable state `s = ⟨la, lb, ra, rb⟩` with `det = ra·lb − la·rb = 1` has left
ancestor `la/lb`, right ancestor `ra/rb`, and current node (mediant)
`(la+ra)/(lb+rb)`. Any target node in this subtree can be written uniquely as

    (num, den) = a·(la, lb) + b·(ra, rb),   a, b ≥ 1,

with the node itself being the case `a = b = 1`. Stepping **left** sends
`(a, b) ↦ (a − b, b)` and stepping **right** sends `(a, b) ↦ (a, b − a)`: exactly
subtractive Euclid on `(a, b)`, which preserves `gcd(a, b)` and strictly
decreases `a + b`. From the root `init = ⟨0,1,1,0⟩` the target `p/q` has
coordinates `(a, b) = (q, p)`, so `a + b = p + q` is the familiar Euclidean
measure.

## Extends
- DenumerabilityRationalsOQ03.lean (OQ-03): Stern-Brocot state machine + injectivity
-/

namespace SternBrocot

-- ========================================================================
-- Part I: The Reachability Lemma (Surjectivity Engine)
-- ========================================================================

/-- **Key reachability lemma.**  From any state `s` (no determinant hypothesis
needed), and any positive coprime coordinates `(a, b)`, there is a path `t` whose
node has numerator `a·s.la + b·s.ra` and denominator `a·s.lb + b·s.rb` — i.e. the
target `a·(la,lb) + b·(ra,rb)` is reached.

The proof is strong induction on `a + b` (subtractive Euclid):
- `a = b`: coprimality forces `a = b = 1`; the node *is* `s`'s mediant (empty path).
- `a > b`: step left, recurse on `(a − b, b)`.
- `a < b`: step right, recurse on `(a, b − a)`. -/
theorem reach_aux :
    ∀ (n a b : ℕ) (s : State), a + b = n → 1 ≤ a → 1 ≤ b → Nat.Coprime a b →
      ∃ t : Path,
        (eval s t).la + (eval s t).ra = a * s.la + b * s.ra ∧
        (eval s t).lb + (eval s t).rb = a * s.lb + b * s.rb := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b s hn ha hb hcop
    rcases lt_trichotomy a b with hlt | heq | hgt
    · -- a < b : step right, target coords become (a, b - a)
      obtain ⟨c, rfl⟩ : ∃ c, b = c + a := ⟨b - a, by omega⟩
      have hc : 1 ≤ c := by omega
      have hcop' : Nat.Coprime a c := (Nat.coprime_add_self_right).mp hcop
      obtain ⟨t', ht1, ht2⟩ :=
        ih (a + c) (by omega) a c s.right (by omega) ha hc hcop'
      refine ⟨Dir.R :: t', ?_, ?_⟩
      · simp only [eval]; rw [ht1]; simp only [State.right]; ring
      · simp only [eval]; rw [ht2]; simp only [State.right]; ring
    · -- a = b : coprimality forces a = b = 1
      have hg : Nat.gcd a b = 1 := hcop
      have ha1 : a = 1 := by rw [← heq, Nat.gcd_self] at hg; exact hg
      have hb1 : b = 1 := by omega
      refine ⟨[], ?_, ?_⟩
      · simp only [eval]; rw [ha1, hb1]; ring
      · simp only [eval]; rw [ha1, hb1]; ring
    · -- a > b : step left, target coords become (a - b, b)
      obtain ⟨c, rfl⟩ : ∃ c, a = c + b := ⟨a - b, by omega⟩
      have hc : 1 ≤ c := by omega
      have hcop' : Nat.Coprime c b := (Nat.coprime_add_self_left).mp hcop
      obtain ⟨t', ht1, ht2⟩ :=
        ih (c + b) (by omega) c b s.left (by omega) hc hb hcop'
      refine ⟨Dir.L :: t', ?_, ?_⟩
      · simp only [eval]; rw [ht1]; simp only [State.left]; ring
      · simp only [eval]; rw [ht2]; simp only [State.left]; ring

/-- **Surjectivity onto coprime pairs.** Every coprime `(p, q)` with `p, q ≥ 1`
is the `(numerator, denominator)` of some Stern-Brocot node. -/
theorem reach_root (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∃ t : Path, pathNum t = p ∧ pathDen t = q := by
  obtain ⟨t, h1, h2⟩ := reach_aux (q + p) q p State.init rfl hq hp hcop.symm
  refine ⟨t, ?_, ?_⟩
  · simpa [pathNum, evalPath, State.init] using h1
  · simpa [pathDen, evalPath, State.init] using h2

-- ========================================================================
-- Part II: Surjectivity onto the Positive Rationals
-- ========================================================================

/-- **Surjectivity.** Every positive rational equals `toRat t` for some path. -/
theorem toRat_surjective (x : ℚ) (hx : 0 < x) : ∃ t : Path, toRat t = x := by
  have hnpos : 0 < x.num := Rat.num_pos.mpr hx
  obtain ⟨t, hnum, hden⟩ :=
    reach_root x.num.natAbs x.den
      (Int.natAbs_pos.mpr (ne_of_gt hnpos))
      x.pos
      x.reduced
  refine ⟨t, ?_⟩
  rw [toRat, hnum, hden]
  have h1 : (x.num.natAbs : ℤ) = x.num := by
    rw [Int.natCast_natAbs, abs_of_nonneg hnpos.le]
  have hcast : (x.num.natAbs : ℚ) = (x.num : ℚ) := by
    have h2 : ((x.num.natAbs : ℤ) : ℚ) = ((x.num : ℤ) : ℚ) := by rw [h1]
    rwa [Int.cast_natCast] at h2
  rw [hcast]
  exact Rat.num_div_den x

-- ========================================================================
-- Part III: Injectivity of the Rational Value (Mediant Injectivity)
-- ========================================================================

/-- A node in the **left** subtree of `s` has value strictly below `s`'s mediant
(cross-multiplied, over `ℕ`): `num · (lb+rb) < (la+ra) · den`. -/
theorem left_lt_mediant (s : State) (p : Path) (hdet : s.det = 1) :
    ((eval s.left p).la + (eval s.left p).ra) * (s.lb + s.rb)
      < (s.la + s.ra) * ((eval s.left p).lb + (eval s.left p).rb) := by
  have h := (value_between_ancestors s.left p (det_left s hdet)).2
  simp only [State.left] at h
  exact_mod_cast h

/-- A node in the **right** subtree of `s` has value strictly above `s`'s mediant
(cross-multiplied, over `ℕ`): `(la+ra) · den < num · (lb+rb)`. -/
theorem mediant_lt_right (s : State) (p : Path) (hdet : s.det = 1) :
    (s.la + s.ra) * ((eval s.right p).lb + (eval s.right p).rb)
      < ((eval s.right p).la + (eval s.right p).ra) * (s.lb + s.rb) := by
  have h := (value_between_ancestors s.right p (det_right s hdet)).1
  simp only [State.right] at h
  exact_mod_cast h

/-- **Mediant injectivity, generalized.** From any state `s` with `det = 1`, if
two paths reach nodes with equal numerator *and* equal denominator, the paths are
equal. (The parent's `eval_injective_gen` proves the stronger hypothesis that the
full 4-tuple states agree; here only the mediant value is assumed equal, which is
what injectivity of `toRat` actually needs.)

The contradictions all come from the BST ordering above: a left-subtree node sits
strictly *below* the parent mediant and a right-subtree node strictly *above* it,
so equal values cannot straddle the mediant. Substitutions are done over `ℕ` with
`omega`, avoiding any cast bookkeeping. -/
theorem mediant_inj_gen (s : State) (p1 p2 : Path) (hdet : s.det = 1)
    (hn : (eval s p1).la + (eval s p1).ra = (eval s p2).la + (eval s p2).ra)
    (hd : (eval s p1).lb + (eval s p1).rb = (eval s p2).lb + (eval s p2).rb) :
    p1 = p2 := by
  induction p1 generalizing s p2 with
  | nil =>
    cases p2 with
    | nil => rfl
    | cons d rest =>
      exfalso
      cases d with
      | L =>
        simp only [eval] at hn hd
        have key := left_lt_mediant s rest hdet
        have e1 : (eval s.left rest).la + (eval s.left rest).ra = s.la + s.ra := by omega
        have e2 : (eval s.left rest).lb + (eval s.left rest).rb = s.lb + s.rb := by omega
        rw [e1, e2] at key
        exact absurd key (lt_irrefl _)
      | R =>
        simp only [eval] at hn hd
        have key := mediant_lt_right s rest hdet
        have e1 : (eval s.right rest).la + (eval s.right rest).ra = s.la + s.ra := by omega
        have e2 : (eval s.right rest).lb + (eval s.right rest).rb = s.lb + s.rb := by omega
        rw [e1, e2] at key
        exact absurd key (lt_irrefl _)
  | cons d1 rest1 ih =>
    cases p2 with
    | nil =>
      exfalso
      cases d1 with
      | L =>
        simp only [eval] at hn hd
        have key := left_lt_mediant s rest1 hdet
        have e1 : (eval s.left rest1).la + (eval s.left rest1).ra = s.la + s.ra := by omega
        have e2 : (eval s.left rest1).lb + (eval s.left rest1).rb = s.lb + s.rb := by omega
        rw [e1, e2] at key
        exact absurd key (lt_irrefl _)
      | R =>
        simp only [eval] at hn hd
        have key := mediant_lt_right s rest1 hdet
        have e1 : (eval s.right rest1).la + (eval s.right rest1).ra = s.la + s.ra := by omega
        have e2 : (eval s.right rest1).lb + (eval s.right rest1).rb = s.lb + s.rb := by omega
        rw [e1, e2] at key
        exact absurd key (lt_irrefl _)
    | cons d2 rest2 =>
      cases d1 with
      | L =>
        cases d2 with
        | L =>
          simp only [eval] at hn hd ⊢
          exact congrArg (List.cons Dir.L) (ih s.left rest2 (det_left s hdet) hn hd)
        | R =>
          exfalso
          simp only [eval] at hn hd
          -- left-subtree node (rest1) below mediant, right-subtree node (rest2)
          -- above it; hn/hd force the two values equal — contradiction.
          have keyL := left_lt_mediant s rest1 hdet
          have keyR := mediant_lt_right s rest2 hdet
          have e1 : (eval s.left rest1).la + (eval s.left rest1).ra
              = (eval s.right rest2).la + (eval s.right rest2).ra := by omega
          have e2 : (eval s.left rest1).lb + (eval s.left rest1).rb
              = (eval s.right rest2).lb + (eval s.right rest2).rb := by omega
          rw [e1, e2] at keyL
          linarith
      | R =>
        cases d2 with
        | L =>
          exfalso
          simp only [eval] at hn hd
          have keyR := mediant_lt_right s rest1 hdet
          have keyL := left_lt_mediant s rest2 hdet
          have e1 : (eval s.right rest1).la + (eval s.right rest1).ra
              = (eval s.left rest2).la + (eval s.left rest2).ra := by omega
          have e2 : (eval s.right rest1).lb + (eval s.right rest1).rb
              = (eval s.left rest2).lb + (eval s.left rest2).rb := by omega
          rw [e1, e2] at keyR
          linarith
        | R =>
          simp only [eval] at hn hd ⊢
          exact congrArg (List.cons Dir.R) (ih s.right rest2 (det_right s hdet) hn hd)

/-- **Mediant injectivity.** Distinct paths give distinct `(numerator, denominator)`
pairs: the Stern-Brocot value map is injective. -/
theorem mediant_inj (p1 p2 : Path)
    (hn : pathNum p1 = pathNum p2) (hd : pathDen p1 = pathDen p2) : p1 = p2 :=
  mediant_inj_gen State.init p1 p2 det_init hn hd

/-- **`toRat` is injective.** Equal Stern-Brocot rationals come from equal paths.
Sharper than the parent's state injectivity: here only the rational *value* is
compared, using coprimality of every node to recover the `(num, den)` pair. -/
theorem toRat_injective : Function.Injective toRat := by
  intro p1 p2 h
  apply mediant_inj
  all_goals
    have hd1 : (0 : ℚ) < (pathDen p1 : ℚ) := by exact_mod_cast den_pos_path p1
    have hd2 : (0 : ℚ) < (pathDen p2 : ℚ) := by exact_mod_cast den_pos_path p2
    have hcross : pathNum p1 * pathDen p2 = pathNum p2 * pathDen p1 := by
      have hh := h
      rw [toRat, toRat, div_eq_div_iff hd1.ne' hd2.ne'] at hh
      exact_mod_cast hh
    have hN12 : pathNum p1 ∣ pathNum p2 :=
      (coprime_path p1).dvd_of_dvd_mul_right ⟨pathDen p2, hcross.symm⟩
    have hN21 : pathNum p2 ∣ pathNum p1 :=
      (coprime_path p2).dvd_of_dvd_mul_right ⟨pathDen p1, hcross⟩
    have hNum : pathNum p1 = pathNum p2 := Nat.dvd_antisymm hN12 hN21
  · exact hNum
  · have hpos : 0 < pathNum p1 := num_pos_path p1
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc pathNum p1 * pathDen p1
        = pathNum p2 * pathDen p1 := by rw [hNum]
      _ = pathNum p1 * pathDen p2 := hcross.symm

-- ========================================================================
-- Part IV: The Stern-Brocot Bijection
-- ========================================================================

/-- **The Stern-Brocot bijection.** `toRat` is injective and its range is exactly
the positive rationals. Hence binary left/right paths enumerate `ℚ⁺` bijectively,
with every node automatically in lowest terms — a constructive denumerability of
`ℚ⁺` with no Cantor pairing and no use of choice. -/
theorem sternBrocot_bijection :
    Function.Injective toRat ∧ Set.range toRat = {x : ℚ | 0 < x} := by
  refine ⟨toRat_injective, ?_⟩
  ext x
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, rfl⟩; exact toRat_pos t
  · intro hx; exact toRat_surjective x hx

-- ========================================================================
-- Part V: Concrete Witnesses
-- ========================================================================

/-- The path encoding `2/3` exists (and `[Dir.L, Dir.R]` is one such path). -/
example : ∃ t : Path, pathNum t = 2 ∧ pathDen t = 3 :=
  reach_root 2 3 (by norm_num) (by norm_num) (by decide)

/-- The path encoding `3/2` exists. -/
example : ∃ t : Path, pathNum t = 3 ∧ pathDen t = 2 :=
  reach_root 3 2 (by norm_num) (by norm_num) (by decide)

/-- A larger coprime pair `22/7` is reached too. -/
example : ∃ t : Path, pathNum t = 22 ∧ pathDen t = 7 :=
  reach_root 22 7 (by norm_num) (by norm_num) (by decide)

-- ========================================================================
-- Verification
-- ========================================================================

#check @reach_aux
#check @reach_root
#check @toRat_surjective
#check @mediant_inj
#check @toRat_injective
#check @sternBrocot_bijection

end SternBrocot
