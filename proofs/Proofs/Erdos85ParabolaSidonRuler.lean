import Proofs.Erdos85SidonNoWrap
import Mathlib.NumberTheory.Bertrand

/-!
# A quadratic-length Sidon ruler from a finite-field parabola

The points `(t,t²)` form a difference-Sidon set in a field of odd
characteristic.  Encoding the two coordinates in base `2q` gives the integer
marks

`t + 2q (t² mod q)`,  `0 ≤ t < q`,

all lying below `2q²`.  Equality of two integer differences first recovers
the first-coordinate difference (there is no carry across a base-`2q`
digit), then the second-coordinate difference, and hence the original
ordered pair by the parabola identity.
-/

namespace Erdos85

/-- Difference and square-difference determine a nontrivial ordered pair on
an odd-characteristic parabola. -/
theorem parabola_ordered_difference_unique
    {K : Type*} [Field K] {a b c d : K}
    (htwo : (2 : K) ≠ 0)
    (hdiff : a - b = c - d)
    (hsq : a ^ 2 - b ^ 2 = c ^ 2 - d ^ 2) :
    a = b ∨ (a = c ∧ b = d) := by
  by_cases hab : a = b
  · exact Or.inl hab
  right
  have hδ : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hfactorLeft : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  have hfactorRight : c ^ 2 - d ^ 2 = (c - d) * (c + d) := by ring
  have hsum : a + b = c + d := by
    apply mul_left_cancel₀ hδ
    rw [← hfactorLeft, hsq, hfactorRight, hdiff]
  have hac2 : (2 : K) * a = 2 * c := by
    linear_combination hdiff + hsum
  have hac : a = c := by
    exact mul_left_cancel₀ htwo hac2
  refine ⟨hac, ?_⟩
  rw [hac] at hdiff
  exact sub_right_injective hdiff

/-- The integer mark encoding the point `(i,i²)` over `ZMod q`. -/
def parabolaRulerMark (q : ℕ) (i : Fin q) : ℤ :=
  ((i.1 + 2 * q * (i.1 ^ 2 % q) : ℕ) : ℤ)

@[simp] theorem parabolaRulerMark_eq (q : ℕ) (i : Fin q) :
    parabolaRulerMark q i =
      (i.1 : ℤ) + 2 * (q : ℤ) * ((i.1 ^ 2 % q : ℕ) : ℤ) := by
  simp [parabolaRulerMark]

/-- Distinct parabola parameters give distinct integer marks. -/
theorem parabolaRulerMark_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (parabolaRulerMark q) := by
  intro i j hij
  have hdvd : (q : ℤ) ∣ (j.1 : ℤ) - i.1 := by
    rw [parabolaRulerMark_eq, parabolaRulerMark_eq] at hij
    have heq : (j.1 : ℤ) - i.1 =
        (q : ℤ) * (2 * ((i.1 ^ 2 % q : ℕ) : ℤ) -
          2 * ((j.1 ^ 2 % q : ℕ) : ℤ)) := by
      linear_combination -hij
    rw [heq]
    exact dvd_mul_right _ _
  have habs : |(j.1 : ℤ) - i.1| < (q : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hz := Int.eq_zero_of_abs_lt_dvd hdvd habs
  apply Fin.ext
  omega

/-- The full `q`-mark parabola ruler. -/
def parabolaSidonRuler (q : ℕ) : Finset ℤ :=
  Finset.univ.image (parabolaRulerMark q)

theorem card_parabolaSidonRuler {q : ℕ} (hq : 0 < q) :
    (parabolaSidonRuler q).card = q := by
  rw [parabolaSidonRuler, Finset.card_image_of_injective _
    (parabolaRulerMark_injective hq), Finset.card_univ, Fintype.card_fin]

/-- Every parabola mark lies in `[0,2q²)`. -/
theorem parabolaRulerMark_bound {q : ℕ} (hq : 0 < q) (i : Fin q) :
    0 ≤ parabolaRulerMark q i ∧ parabolaRulerMark q i < 2 * q * q := by
  have hi : i.1 < q := i.2
  have hs : i.1 ^ 2 % q < q := Nat.mod_lt _ hq
  dsimp [parabolaRulerMark]
  constructor
  · exact Int.natCast_nonneg _
  · push_cast
    nlinarith

theorem parabolaSidonRuler_bound {q : ℕ} (hq : 0 < q)
    {a : ℤ} (ha : a ∈ parabolaSidonRuler q) :
    0 ≤ a ∧ a < 2 * q * q := by
  rw [parabolaSidonRuler, Finset.mem_image] at ha
  obtain ⟨i, _, rfl⟩ := ha
  exact parabolaRulerMark_bound hq i

/-- Equality of encoded differences recovers the first-coordinate integer
difference. -/
theorem parabolaRulerMark_difference_parameter
    {q : ℕ} (hq : 0 < q) {a b c d : Fin q}
    (hmark : parabolaRulerMark q a - parabolaRulerMark q b =
      parabolaRulerMark q c - parabolaRulerMark q d) :
    (a.1 : ℤ) - b.1 = c.1 - d.1 := by
  let sa : ℤ := a.1 ^ 2 % q
  let sb : ℤ := b.1 ^ 2 % q
  let sc : ℤ := c.1 ^ 2 % q
  let sd : ℤ := d.1 ^ 2 % q
  have hdvd : (2 * q : ℤ) ∣
      ((c.1 : ℤ) - d.1) - ((a.1 : ℤ) - b.1) := by
    use (sa - sb) - (sc - sd)
    dsimp [parabolaRulerMark, sa, sb, sc, sd] at hmark ⊢
    push_cast at hmark ⊢
    nlinarith
  have habs :
      |((c.1 : ℤ) - d.1) - ((a.1 : ℤ) - b.1)| < (2 * q : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hz := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

/-- Once the parameter differences agree, equality of encoded differences
also recovers the square-residue differences. -/
theorem parabolaRulerMark_difference_squareResidue
    {q : ℕ} (hq : 0 < q) {a b c d : Fin q}
    (hmark : parabolaRulerMark q a - parabolaRulerMark q b =
      parabolaRulerMark q c - parabolaRulerMark q d) :
    ((a.1 ^ 2 % q : ℕ) : ℤ) - (b.1 ^ 2 % q : ℕ) =
      (c.1 ^ 2 % q : ℕ) - (d.1 ^ 2 % q : ℕ) := by
  have hparam := parabolaRulerMark_difference_parameter hq hmark
  rw [parabolaRulerMark_eq, parabolaRulerMark_eq,
    parabolaRulerMark_eq, parabolaRulerMark_eq] at hmark
  have hcoef : (2 * q : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hcoef
  linear_combination hmark - hparam

/-- The encoded parabola marks have unique nonzero ordered differences when
`q` is odd. -/
theorem isDifferenceSidon_parabolaSidonRuler
    {q : ℕ} (hqPrime : q.Prime) (hqOdd : Odd q) :
    IsDifferenceSidon (parabolaSidonRuler q) := by
  have hq : 0 < q := hqPrime.pos
  letI : Fact q.Prime := ⟨hqPrime⟩
  intro α hα β hβ γ hγ δ hδ heq
  rw [parabolaSidonRuler, Finset.mem_image] at hα hβ hγ hδ
  obtain ⟨a, _, rfl⟩ := hα
  obtain ⟨b, _, rfl⟩ := hβ
  obtain ⟨c, _, rfl⟩ := hγ
  obtain ⟨d, _, rfl⟩ := hδ
  have hparam := parabolaRulerMark_difference_parameter hq heq
  have hsquare := parabolaRulerMark_difference_squareResidue hq heq
  have hparamZ : (a.1 : ZMod q) - b.1 = (c.1 : ZMod q) - d.1 := by
    have := congrArg (fun z : ℤ => (z : ZMod q)) hparam
    simpa only [Int.cast_sub, Int.cast_natCast] using this
  have hsquareZ : (a.1 : ZMod q) ^ 2 - (b.1 : ZMod q) ^ 2 =
      (c.1 : ZMod q) ^ 2 - (d.1 : ZMod q) ^ 2 := by
    have hcast :
        ((((a.1 ^ 2 % q : ℕ) : ℤ) : ZMod q) -
          (((b.1 ^ 2 % q : ℕ) : ℤ) : ZMod q)) =
        ((((c.1 ^ 2 % q : ℕ) : ℤ) : ZMod q) -
          (((d.1 ^ 2 % q : ℕ) : ℤ) : ZMod q)) := by
      simpa only [Int.cast_sub, Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ZMod q)) hsquare
    simpa using hcast
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro hzero
    have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hzero
    have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hqge : 2 ≤ q := hqPrime.two_le
    have hq2 : q = 2 := by omega
    subst q
    norm_num at hqOdd
  rcases parabola_ordered_difference_unique htwo hparamZ hsquareZ with
      hab | hpair
  · left
    have habVal := congrArg (fun z : ZMod q => z.val) hab
    have habFin : a = b := by
      apply Fin.ext
      simpa [ZMod.val_natCast_of_lt a.2,
        ZMod.val_natCast_of_lt b.2] using habVal
    rw [habFin]
  · right
    have hacVal := congrArg (fun z : ZMod q => z.val) hpair.1
    have hbdVal := congrArg (fun z : ZMod q => z.val) hpair.2
    have hacFin : a = c := by
      apply Fin.ext
      simpa [ZMod.val_natCast_of_lt a.2,
        ZMod.val_natCast_of_lt c.2] using hacVal
    have hbdFin : b = d := by
      apply Fin.ext
      simpa [ZMod.val_natCast_of_lt b.2,
        ZMod.val_natCast_of_lt d.2] using hbdVal
    exact ⟨by rw [hacFin], by rw [hbdFin]⟩

/-- **Quadratic even-order conductor.**  Every even order `2M` with
`M ≥ 16d²` carries a `C₄`-free graph of minimum degree at least `d`.

Choose a prime `q ∈ (d,2d]` by Bertrand.  Its parabola ruler has `q ≥ d`
marks below `2q²`; the hypothesis gives `4q² ≤ M`, so reduction modulo `M`
has no wrap and the difference-Sidon Cayley construction applies. -/
theorem c4FreeMinDegreeWitness_even_quadratic
    {d M : ℕ} [NeZero M] (hd : 2 ≤ d) (hM : 16 * d * d ≤ M) :
    C4FreeMinDegreeWitness (2 * M) d := by
  obtain ⟨q, hqPrime, hdq, hqd⟩ :=
    Nat.exists_prime_lt_and_le_two_mul d (by omega)
  have hqOdd : Odd q := hqPrime.odd_of_ne_two (by omega)
  let L := 2 * q * q
  apply c4FreeMinDegreeWitness_two_mul_of_sidonRuler
    (A := parabolaSidonRuler q) (L := L)
  · dsimp [L]
    nlinarith
  · intro a ha
    exact parabolaSidonRuler_bound hqPrime.pos ha
  · exact isDifferenceSidon_parabolaSidonRuler hqPrime hqOdd
  · rw [card_parabolaSidonRuler hqPrime.pos]
    omega

end Erdos85
