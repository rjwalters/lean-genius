import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# K-law classification for the size-two eigenline grid (connected shape)

Node: `SIZE-TWO-EIGENLINE(q)` (outline v2.2, child of GAP A-REG-NONBIP).

For the normalized connected internal shape — `H` the circulant with shifts
`{0, -1}` on `ZMod q` (the single cycle `C_{2q}` in grid coordinates) — we
classify the hole 2-factors `K` compatible with the two K-laws
(`|K(a) ∩ H(b)| = |K(b) ∩ H(a)|` for rows, and the column dual):
they are exactly the reflection circulants `K(x) = {x + s, x - 1 - s}`.

The laws are stated abstractly (integer-valued counting equalities); the
graph-side derivation lives in `Erdos85MuThreeMixedGridKSymmetry` and its
q-generic analogues.  Verified computationally at `q = 8` (3 solutions),
`q = 12` (5), and for the circulant subfamily at `q = 16` (7).

Proof: pass to shift coordinates `r x e = k x (x + e)`.  Subtracting the two
laws yields `ψ e a = ψ (-e-3) (a+e+1)` for `ψ e a = r a e - r (a+1) e`;
applying this involution twice gives `ψ e a = ψ e (a-1)`, so `ψ e` is
constant, and its telescoping sum over the cycle vanishes, forcing `ψ ≡ 0`:
all rows carry the same shift set.  The row law then says the smeared support
`{s, s+1, t, t+1}` is negation-closed; since `2·s = -1` has no solution for
even `q`, negation must exchange the two intervals, i.e. `t = -1 - s`.
-/

open Finset

namespace Erdos85

variable {q : ℕ}

/-- Row-shift indicator: `kShift k x e` iff `k x (x + e)`. -/
def kShift (k : ZMod q → ZMod q → Bool) (x e : ZMod q) : Bool :=
  k x (x + e)

section Laws

variable (k : ZMod q → ZMod q → Bool)

/-- The row K-law: `|K(a) ∩ {b, b-1}| = |K(b) ∩ {a, a-1}|`. -/
def RowLaw : Prop :=
  ∀ a b : ZMod q,
    ((if k a b then 1 else 0) + (if k a (b - 1) then 1 else 0) : ℤ) =
      (if k b a then 1 else 0) + (if k b (a - 1) then 1 else 0)

/-- The column K-law: `|K^T(b) ∩ {a, a+1}| = |K^T(a) ∩ {b, b+1}|` (rows
H-adjacent to a column `y` are `{y, y+1}`). -/
def ColLaw : Prop :=
  ∀ a b : ZMod q,
    ((if k a b then 1 else 0) + (if k (a + 1) b then 1 else 0) : ℤ) =
      (if k b a then 1 else 0) + (if k (b + 1) a then 1 else 0)

end Laws


section ShiftLaws

variable (k : ZMod q → ZMod q → Bool)

/-- Row law in shift form: `r_a(d) + r_a(d-1) = r_{a+d}(-d) + r_{a+d}(-d-1)`. -/
theorem rowLaw_shift (hR : RowLaw k) (a d : ZMod q) :
    ((if kShift k a d then 1 else 0) + (if kShift k a (d - 1) then 1 else 0) : ℤ) =
      (if kShift k (a + d) (-d) then 1 else 0) +
        (if kShift k (a + d) (-d - 1) then 1 else 0) := by
  have h := hR a (a + d)
  simp only [kShift]
  simp only [show a + (d - 1) = a + d - 1 from by ring,
    show a + d + -d = a from by ring, show a + d + (-d - 1) = a - 1 from by ring]
  exact h

/-- Column law in shift form:
`r_a(d) + r_{a+1}(d-1) = r_{a+d}(-d) + r_{a+d+1}(-d-1)`. -/
theorem colLaw_shift (hC : ColLaw k) (a d : ZMod q) :
    ((if kShift k a d then 1 else 0) + (if kShift k (a + 1) (d - 1) then 1 else 0) : ℤ) =
      (if kShift k (a + d) (-d) then 1 else 0) +
        (if kShift k (a + d + 1) (-d - 1) then 1 else 0) := by
  have h := hC a (a + d)
  simp only [kShift]
  simp only [show a + 1 + (d - 1) = a + d from by ring,
    show a + d + -d = a from by ring, show a + d + 1 + (-d - 1) = a from by ring]
  exact h

end ShiftLaws

section Constancy

variable (k : ZMod q → ZMod q → Bool)

/-- Boolean extraction from an integer indicator equality. -/
theorem bool_eq_of_ite_eq {a c : Bool}
    (h : (if a then (1 : ℤ) else 0) = if c then 1 else 0) : a = c := by
  cases a <;> cases c <;> simp_all

/-- A function on `ZMod q` equal at successors is constant. -/
theorem const_of_succ [NeZero q] {α : Type*} {f : ZMod q → α}
    (h : ∀ b, f b = f (b + 1)) (b b' : ZMod q) : f b = f b' := by
  have key : ∀ (n : ℕ) (c : ZMod q), f c = f (c + (n : ZMod q)) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ m ih =>
        intro c
        have h1 : f c = f (c + (m : ZMod q)) := ih c
        have h2 : f (c + (m : ZMod q)) = f (c + (m : ZMod q) + 1) := h _
        rw [h1, h2]
        congr 1
        push_cast
        ring
  have hb : b' = b + (((b' - b).val : ℕ) : ZMod q) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
    ring
  rw [hb]
  exact key _ b

/-- **Constancy and reflection.**  With the two K-laws and the H-avoidance
zeros, every shift level `j` is constant across rows and equals the reflected
level `-1-j`. -/
theorem shift_const_reflect [NeZero q] (hR : RowLaw k) (hC : ColLaw k)
    (h0 : ∀ x, kShift k x 0 = false) (hm1 : ∀ x, kShift k x (-1) = false) :
    ∀ j : ℕ, (∀ x x' : ZMod q, kShift k x (j : ZMod q) = kShift k x' (j : ZMod q)) ∧
      (∀ x x' : ZMod q, kShift k x (-1 - (j : ZMod q)) = kShift k x' (j : ZMod q)) := by
  intro j
  induction j with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro x x'; simp only [Nat.cast_zero]; rw [h0 x, h0 x']
      · intro x x'
        simp only [Nat.cast_zero, sub_zero]
        rw [hm1 x, h0 x']
  | succ m ih =>
      obtain ⟨ihc, ihr⟩ := ih
      set J : ZMod q := (m : ZMod q) with hJ
      have hcast : ((m + 1 : ℕ) : ZMod q) = J + 1 := by push_cast; ring
      have step1 : ∀ a : ZMod q,
          kShift k a (J + 1) = kShift k (a + J + 1) (-J - 2) := by
        intro a
        have h := rowLaw_shift k hR a (J + 1)
        simp only [show (J + 1 - 1 : ZMod q) = J from by ring,
          show (-(J + 1) : ZMod q) = -1 - J from by ring,
          show (-1 - J - 1 : ZMod q) = -J - 2 from by ring,
          show (a + (J + 1) : ZMod q) = a + J + 1 from by ring] at h
        have hc : kShift k (a + J + 1) (-1 - J) = kShift k a J := ihr _ _
        rw [hc] at h
        exact bool_eq_of_ite_eq (by linarith)
      have step2 : ∀ a : ZMod q,
          kShift k a (J + 1) = kShift k (a + J + 2) (-J - 2) := by
        intro a
        have h := colLaw_shift k hC a (J + 1)
        simp only [show (J + 1 - 1 : ZMod q) = J from by ring,
          show (-(J + 1) : ZMod q) = -1 - J from by ring,
          show (-1 - J - 1 : ZMod q) = -J - 2 from by ring,
          show (a + (J + 1) : ZMod q) = a + J + 1 from by ring,
          show (a + J + 1 + 1 : ZMod q) = a + J + 2 from by ring] at h
        have hc : kShift k (a + J + 1) (-1 - J) = kShift k (a + 1) J :=
          ihr (a + J + 1) (a + 1)
        rw [hc] at h
        exact bool_eq_of_ite_eq (by linarith)
      have hsucc : ∀ b : ZMod q,
          kShift k b (-J - 2) = kShift k (b + 1) (-J - 2) := by
        intro b
        have h1 := step1 (b - J - 1)
        have h2 := step2 (b - J - 1)
        simp only [show (b - J - 1 + J + 1 : ZMod q) = b from by ring,
          show (b - J - 1 + J + 2 : ZMod q) = b + 1 from by ring] at h1 h2
        rw [← h1, ← h2]
      have hconst : ∀ b b' : ZMod q,
          kShift k b (-J - 2) = kShift k b' (-J - 2) :=
        fun b b' => const_of_succ (f := fun b => kShift k b (-J - 2)) hsucc b b'
      refine ⟨?_, ?_⟩
      · intro x x'
        rw [hcast, step1 x, step1 x']
        exact hconst _ _
      · intro x x'
        rw [hcast, show (-1 - (J + 1) : ZMod q) = -J - 2 from by ring, step1 x']
        exact hconst _ _

end Constancy

section Endgame

/-- For even `q` the reflection `e ↦ -1-e` has no fixed point: `2e = -1` is
impossible (map through `ZMod 2`). -/
theorem ne_neg_one_sub_self [NeZero q] (hq : 2 ∣ q) (e : ZMod q) :
    e ≠ -1 - e := by
  intro h
  have h2 : (2 : ZMod q) * e = -1 := by
    rw [two_mul]
    nth_rewrite 1 [h]
    ring
  have hphi := congrArg (ZMod.castHom hq (ZMod 2)) h2
  simp only [map_mul, map_neg, map_one, map_ofNat] at hphi
  rw [show (2 : ZMod 2) = 0 from by decide, zero_mul] at hphi
  exact absurd hphi (by decide)

/-- Support extraction: a reflection-symmetric two-element support avoiding
`{0, -1}` is a reflection pair `{s, -1-s}`. -/
theorem support_reflection_pair [NeZero q] (hq : 2 ∣ q) (r : ZMod q → Bool)
    (hcard : (Finset.univ.filter fun e => r e).card = 2)
    (h0 : r 0 = false) (hm1 : r (-1) = false)
    (hrefl : ∀ e, r (-1 - e) = r e) :
    ∃ s : ZMod q, s ≠ 0 ∧ s ≠ -1 ∧ ∀ e, r e = true ↔ e = s ∨ e = -1 - s := by
  classical
  have hne : (Finset.univ.filter fun e => r e).Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  obtain ⟨s, hs⟩ := hne
  have hrs : r s = true := (Finset.mem_filter.mp hs).2
  have hrs' : r (-1 - s) = true := (hrefl s).trans hrs
  have hne' : s ≠ -1 - s := ne_neg_one_sub_self hq s
  have hsub : ({s, -1 - s} : Finset (ZMod q)) ⊆
      Finset.univ.filter fun e => r e := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he'
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs⟩
    · rcases Finset.mem_singleton.mp he' with rfl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs'⟩
  have hcard' : ({s, -1 - s} : Finset (ZMod q)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne'), Finset.card_singleton]
  have heq : (Finset.univ.filter fun e => r e) = {s, -1 - s} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard'])).symm
  refine ⟨s, ?_, ?_, ?_⟩
  · rintro rfl; rw [h0] at hrs; exact absurd hrs (by simp)
  · rintro rfl; rw [hm1] at hrs; exact absurd hrs (by simp)
  · intro e
    constructor
    · intro hre
      have : e ∈ Finset.univ.filter fun e => r e :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hre⟩
      rw [heq] at this
      simpa using this
    · rintro (rfl | rfl)
      · exact hrs
      · exact hrs'

end Endgame

/-- **K-law classification (connected shape).**  On `ZMod q` with `q` even,
a 2-regular-by-rows hole relation avoiding the internal shifts `{0, -1}` and
satisfying the two K-laws is a reflection circulant: `k x y ↔ y - x ∈
{s, -1-s}` for some `s ∉ {0, -1}`.  This is the classification half of the
`SIZE-TWO-EIGENLINE(q)` node: it reduces the eigenline block's hole freedom
to `(q-2)/2` explicit circulants, uniformly in `q`. -/
theorem klaw_classification [NeZero q] (hq : 2 ∣ q)
    (k : ZMod q → ZMod q → Bool)
    (row2 : (Finset.univ.filter fun y => k 0 y).card = 2)
    (h0 : ∀ x, k x x = false) (hm1 : ∀ x, k x (x - 1) = false)
    (hR : RowLaw k) (hC : ColLaw k) :
    ∃ s : ZMod q, s ≠ 0 ∧ s ≠ -1 ∧
      ∀ x y, k x y = true ↔ y - x = s ∨ y - x = -1 - s := by
  classical
  have hs0 : ∀ x, kShift k x 0 = false := by
    intro x; simpa [kShift] using h0 x
  have hsm1 : ∀ x, kShift k x (-1) = false := by
    intro x
    simp only [kShift, show (x + (-1) : ZMod q) = x - 1 from by ring]
    exact hm1 x
  have SCR := shift_const_reflect k hR hC hs0 hsm1
  have hcaste : ∀ e : ZMod q, ((e.val : ℕ) : ZMod q) = e := by
    intro e; rw [ZMod.natCast_val, ZMod.cast_id]
  have hconst : ∀ x e, kShift k x e = kShift k 0 e := by
    intro x e
    have h := (SCR e.val).1 x 0
    rwa [hcaste e] at h
  have hrefl : ∀ e, kShift k 0 (-1 - e) = kShift k 0 e := by
    intro e
    have h := (SCR e.val).2 0 0
    rwa [hcaste e] at h
  have hcard : (Finset.univ.filter fun e => kShift k 0 e).card = 2 := by
    have hset : (Finset.univ.filter fun e => kShift k 0 e) =
        (Finset.univ.filter fun y => k 0 y) := by
      apply Finset.filter_congr
      intro e _
      simp [kShift]
    rw [hset]
    exact row2
  obtain ⟨s, hsne0, hsnem1, hiff⟩ :=
    support_reflection_pair hq (kShift k 0) hcard (hs0 0) (hsm1 0) hrefl
  refine ⟨s, hsne0, hsnem1, ?_⟩
  intro x y
  have hxy : k x y = kShift k x (y - x) := by
    simp only [kShift, show (x + (y - x) : ZMod q) = y from by ring]
  rw [hxy, hconst x (y - x)]
  exact hiff (y - x)

end Erdos85
