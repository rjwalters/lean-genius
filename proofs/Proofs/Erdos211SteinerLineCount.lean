/-
  Erdős Problem #211 (Lines determined by points in the plane): the extremal
  `1/6` constant, via an axiom-free double count.

  Source problem: https://erdosproblems.com/211
  Parent gallery entry: `erdos-211` (`Erdos211Problem.lean`).

  Background.  Given `n` points in the plane with at most `n - k` on any line,
  Beck (1983) and Szemerédi–Trotter (1983) proved there are `≫ k·n` lines
  containing at least two of the points.  Erdős speculated the sharp constant is
  `1/6`: in the extremal configurations *every* line through the points contains
  exactly three of them, so the number of lines is
  `(n choose 2) / (3 choose 2) = (n choose 2)/3 ≈ n²/6`.

  The parent file `Erdos211Problem.lean` records this `1/6` phenomenon only as an
  unproved hypothesis (`constant_one_sixth_optimal`, `furedi_palasti_optimal`).
  This file isolates and *proves* its combinatorial core, with no axioms and no
  geometry: it is a pure double-counting fact about a Steiner triple system
  `S(2, 3, n)` — a family of 3-element "lines" on an `n`-point set in which every
  pair of points lies on exactly one line.  Counting incidences `(pair, line)`
  with `pair ⊆ line` two ways gives

      3 · (number of lines) = (n choose 2),

  i.e. the number of lines is exactly `(n choose 2)/3 = n(n-1)/6`.  This is the
  honest source of Erdős's `1/6`: such configurations are precisely the ones in
  which the `≈ n²/6` lines are forced, and they exist exactly when `n ≡ 1, 3`
  (mod 6) (the Kirkman/Steiner existence condition — not needed here, but the
  divisibility `3 ∣ (n choose 2)` it requires is an immediate consequence of the
  count below).

  Verified, 0 axioms, original.
-/

import Mathlib

open Finset

namespace Erdos211Steiner

variable {α : Type*} [DecidableEq α]

/-- `IsLineCover V L` says that `L` is a family of "lines" on the point set `V`
that realises the extremal `1/6` configuration of Erdős #211:

* every line is a 3-element subset of `V` (`hcard`, `hsub`);
* every pair of points of `V` lies on exactly one line (`hcover`).

This is exactly a *Steiner triple system* `S(2, 3, n)` on the points `V`. -/
def IsLineCover (V : Finset α) (L : Finset (Finset α)) : Prop :=
  (∀ l ∈ L, l.card = 3) ∧
  (∀ l ∈ L, l ⊆ V) ∧
  (∀ p ∈ V.powersetCard 2, ∃! l, l ∈ L ∧ p ⊆ l)

omit [DecidableEq α] in
/-- Each line, being a 3-element set, contains exactly `3 choose 2 = 3` pairs. -/
theorem card_pairs_of_line (L : Finset (Finset α))
    (hcard : ∀ l ∈ L, l.card = 3) :
    ∀ l ∈ L, (l.powersetCard 2).card = 3 := by
  intro l hl
  rw [Finset.card_powersetCard, hcard l hl]
  decide

/-- A line `l ⊆ V` selects exactly the pairs of `V` that it contains:
`l.powersetCard 2 = (V.powersetCard 2).filter (· ⊆ l)`. -/
theorem powersetCard_two_eq_filter (V l : Finset α) (hl : l ⊆ V) :
    l.powersetCard 2 = (V.powersetCard 2).filter (fun p => p ⊆ l) := by
  ext p
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hpl, hp2⟩
    exact ⟨⟨hpl.trans hl, hp2⟩, hpl⟩
  · rintro ⟨⟨_, hp2⟩, hpl⟩
    exact ⟨hpl, hp2⟩

/-- Each pair of points lies on exactly one line, so the lines through a fixed
pair number exactly one. -/
theorem card_lines_through_pair (V : Finset α) (L : Finset (Finset α))
    (hcover : ∀ p ∈ V.powersetCard 2, ∃! l, l ∈ L ∧ p ⊆ l)
    {p : Finset α} (hp : p ∈ V.powersetCard 2) :
    (L.filter (fun l => p ⊆ l)).card = 1 := by
  obtain ⟨l₀, ⟨hl₀L, hl₀p⟩, huniq⟩ := hcover p hp
  rw [Finset.card_eq_one]
  refine ⟨l₀, ?_⟩
  ext l
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hlL, hlp⟩
    exact huniq l ⟨hlL, hlp⟩
  · rintro rfl
    exact ⟨hl₀L, hl₀p⟩

/-- **The incidence double count.**  Counting pairs `(line, pair)` with
`pair ⊆ line`: grouped by line each contributes `3`, grouped by pair each
contributes `1`. -/
theorem incidence_double_count (V : Finset α) (L : Finset (Finset α))
    (hcover : IsLineCover V L) :
    ∑ l ∈ L, (l.powersetCard 2).card
      = ∑ p ∈ V.powersetCard 2, (L.filter (fun l => p ⊆ l)).card := by
  obtain ⟨_, hsub, _⟩ := hcover
  calc
    ∑ l ∈ L, (l.powersetCard 2).card
        = ∑ l ∈ L, ∑ p ∈ V.powersetCard 2, (if p ⊆ l then 1 else 0) := by
          refine Finset.sum_congr rfl (fun l hl => ?_)
          rw [powersetCard_two_eq_filter V l (hsub l hl), Finset.card_filter]
    _ = ∑ p ∈ V.powersetCard 2, ∑ l ∈ L, (if p ⊆ l then 1 else 0) :=
          Finset.sum_comm
    _ = ∑ p ∈ V.powersetCard 2, (L.filter (fun l => p ⊆ l)).card := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [Finset.card_filter]

/-- **Main theorem (Erdős #211 extremal count).**  If the pairs of an `n`-point
set are covered by 3-point lines, each pair exactly once (a Steiner triple
system `S(2,3,n)`), then the number of lines is exactly `(n choose 2)/3`:

    `3 · L.card = V.card.choose 2`.

This is the precise combinatorial reason for Erdős's conjectured constant `1/6`:
every line uses three points, so it consumes three of the `(n choose 2)` pairs. -/
theorem three_mul_card_lines (V : Finset α) (L : Finset (Finset α))
    (hcover : IsLineCover V L) :
    3 * L.card = V.card.choose 2 := by
  obtain ⟨hcard, hsub, hcov⟩ := hcover
  have hleft : ∑ l ∈ L, (l.powersetCard 2).card = 3 * L.card := by
    rw [Finset.sum_congr rfl (card_pairs_of_line L hcard)]
    rw [Finset.sum_const, smul_eq_mul]
    ring
  have hright : ∑ p ∈ V.powersetCard 2, (L.filter (fun l => p ⊆ l)).card
      = V.card.choose 2 := by
    rw [Finset.sum_congr rfl
      (fun p hp => card_lines_through_pair V L hcov hp)]
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_powersetCard]
  rw [← hleft, incidence_double_count V L ⟨hcard, hsub, hcov⟩, hright]

/-- **Divisibility corollary.**  A Steiner triple system on `n` points can only
exist when `3 ∣ (n choose 2)`.  (Combined with the parity condition this gives
the classical `n ≡ 1, 3 (mod 6)` requirement.) -/
theorem three_dvd_choose_two (V : Finset α) (L : Finset (Finset α))
    (hcover : IsLineCover V L) :
    3 ∣ V.card.choose 2 :=
  ⟨L.card, (three_mul_card_lines V L hcover).symm⟩

/-- **Real-valued form: the `n(n-1)/6` count.**  In `ℝ`, the number of lines is
`n(n-1)/6`, exhibiting the `1/6` constant explicitly. -/
theorem card_lines_real (V : Finset α) (L : Finset (Finset α))
    (hcover : IsLineCover V L) :
    (L.card : ℝ) = (V.card : ℝ) * ((V.card : ℝ) - 1) / 6 := by
  have h : (3 : ℝ) * (L.card : ℝ) = (V.card.choose 2 : ℝ) := by
    have := three_mul_card_lines V L hcover
    exact_mod_cast this
  have hc : (V.card.choose 2 : ℝ) = (V.card : ℝ) * ((V.card : ℝ) - 1) / 2 := by
    rcases Nat.eq_zero_or_pos V.card with h0 | hpos
    · simp [h0]
    · have : V.card.choose 2 = V.card * (V.card - 1) / 2 := Nat.choose_two_right _
      have heven : 2 ∣ V.card * (V.card - 1) := by
        have := Nat.even_mul_pred_self V.card
        exact this.two_dvd
      rw [this]
      rw [Nat.cast_div heven (by norm_num)]
      push_cast [Nat.cast_sub hpos]
      ring
  rw [hc] at h
  linarith

/-! ### Numerical sanity checks (existence of the configurations is classical) -/

/-- Fano plane `S(2,3,7)`: 7 points, 7 lines, `3·7 = 21 = (7 choose 2)`. -/
example : 3 * 7 = Nat.choose 7 2 := by decide

/-- Affine plane `AG(2,3) = S(2,3,9)`: 9 points, 12 lines, `3·12 = 36 = (9 choose 2)`. -/
example : 3 * 12 = Nat.choose 9 2 := by decide

/-- `13`-point system `S(2,3,13)`: 26 lines, `3·26 = 78 = (13 choose 2)`. -/
example : 3 * 26 = Nat.choose 13 2 := by decide

end Erdos211Steiner
