import Proofs.Erdos85ParabolaSidonRuler
import Proofs.Erdos85CofinalLowerBound
import Proofs.Erdos85RamseyPlateau

/-!
# A quadratic conductor for C₄-free minimum-degree witnesses

The parabola Sidon construction supplies every sufficiently large even order.
For odd orders, split off one odd-order polarity graph and apply the even
construction to the remainder.  Consequently a minimal plateau core has
quadratic, rather than cubic, order.
-/

open SimpleGraph

namespace Erdos85

/-- **Quadratic all-order conductor.** Every order at least `40d²` supports a
`C₄`-free graph of minimum degree at least `d`.

Even orders use the parabola Sidon Cayley graph directly.  For an odd order,
Bertrand supplies an odd prime `q ∈ (d,2d]`; split off the polarity graph of
order `q²+q+1`, leaving a sufficiently large even remainder. -/
theorem c4FreeMinDegreeWitness_quadratic
    {n d : ℕ} (hd : 2 ≤ d) (hn : 40 * d * d ≤ n) :
    C4FreeMinDegreeWitness n d := by
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · obtain ⟨M, rfl⟩ := hnEven
    letI : NeZero M := ⟨by nlinarith⟩
    simpa [two_mul] using
      c4FreeMinDegreeWitness_even_quadratic (M := M) hd (by nlinarith)
  · obtain ⟨q, hqPrime, hdq, hqd⟩ :=
      Nat.exists_prime_lt_and_le_two_mul d (by omega)
    have hqOdd : Odd q := hqPrime.odd_of_ne_two (by omega)
    let b := (q + 1) * q + 1
    have hbOdd : Odd b := by
      dsimp [b]
      have heven : Even ((q + 1) * q) := by
        simpa [mul_comm] using Even.mul_left (Odd.add_one hqOdd) q
      exact heven.add_one
    obtain ⟨N, hN⟩ : ∃ N, n - b = 2 * N := by
      rcases hnOdd with ⟨a, ha⟩
      rcases hbOdd with ⟨c, hc⟩
      have hb : b ≤ n := by
        dsimp [b]
        nlinarith
      refine ⟨a - c, ?_⟩
      omega
    have hNlarge : 16 * d * d ≤ N := by
      have hb : b ≤ 8 * d * d := by
        have hmul : (q + 1) * q ≤ (2 * d + 1) * (2 * d) :=
          Nat.mul_le_mul (Nat.add_le_add_right hqd 1) hqd
        dsimp [b]
        nlinarith
      have hbn : b ≤ n := by
        calc
          b ≤ 8 * d * d := hb
          _ ≤ 40 * d * d := by nlinarith
          _ ≤ n := hn
      have hnDecomp : n = b + 2 * N := by omega
      simp only [Nat.mul_assoc] at hn hb ⊢
      omega
    have hNpos : 0 < N :=
      lt_of_lt_of_le (by positivity : 0 < 16 * d * d) hNlarge
    letI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
    have heven : C4FreeMinDegreeWitness (2 * N) d :=
      c4FreeMinDegreeWitness_even_quadratic hd hNlarge
    letI : Fact q.Prime := ⟨hqPrime⟩
    let K := ZMod q
    letI : DecidableEq K := Classical.decEq K
    have hpolarityQ : C4FreeMinDegreeWitness ((q + 1) * q + 1) q := by
      simpa [TightC4Witness, K] using Polarity.tightC4Witness K
    have hpolarity : C4FreeMinDegreeWitness b d := by
      dsimp [b]
      exact hpolarityQ.mono_degree hdq.le
    have hsum := C4FreeMinDegreeWitness.add (a := b) (b := 2 * N)
      (by dsimp [b]; positivity) (by positivity) hpolarity heven
    convert hsum using 1
    omega

/-- A minimal plateau core occurs strictly before the quadratic conductor. -/
theorem C4PlateauCore.order_succ_lt_quadratic
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) :
    m + 1 < 40 * d * d := by
  have hd : 2 ≤ d := hcore.two_le_degree hm
  by_contra hnot
  have hw : C4FreeMinDegreeWitness (m + 1) d :=
    c4FreeMinDegreeWitness_quadratic hd (by omega)
  rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  rcases hw with ⟨H, hHdec, hHmin, hHfree⟩
  exact hHfree (hnext H hHdec hHmin)

end Erdos85
