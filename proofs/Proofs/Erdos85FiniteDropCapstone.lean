import Proofs.Erdos85RamseyPlateau

/-!
# A conditional finite drop for the Erdős 85 threshold

This file isolates the final, purely order-theoretic step of the order-49
classification program.  It deliberately does **not** claim to settle Erdős
85: one finite downward jump disproves global monotonicity, but says nothing by
itself about eventual monotonicity.

The substantive inputs are kept in their native graph-theoretic form:

* a `C₄`-free graph on 48 vertices of minimum degree at least 7; and
* nonexistence of such a graph on 49 vertices.

Once those inputs have been certified, threshold/witness duality gives the
drop `minDegreeForC4 49 < minDegreeForC4 48` immediately.  The same result is
also exposed as the corresponding consecutive `C₄`-versus-star Ramsey
plateau.
-/

namespace Erdos85

/-- Nonexistence of a degree-`d` witness is exactly the assertion that `d`
already forces a `C₄`. -/
theorem not_c4FreeMinDegreeWitness_iff_minDegreeForC4_le
    {n d : ℕ} (hn : 4 ≤ n) :
    ¬ C4FreeMinDegreeWitness n d ↔ minDegreeForC4 n ≤ d := by
  rw [c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn]
  omega

/-- A witness at order `n` and its nonexistence at order `n+1`, at the same
minimum degree, force a strict downward jump of the threshold. -/
theorem minDegreeForC4_drop_of_witness_of_no_succ_witness
    {n d : ℕ} (hn : 4 ≤ n)
    (hw : C4FreeMinDegreeWitness n d)
    (hnext : ¬ C4FreeMinDegreeWitness (n + 1) d) :
    minDegreeForC4 (n + 1) < minDegreeForC4 n := by
  have hold : d < minDegreeForC4 n :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn).1 hw
  have hnew : minDegreeForC4 (n + 1) ≤ d :=
    (not_c4FreeMinDegreeWitness_iff_minDegreeForC4_le (by omega)).1 hnext
  omega

/-- The exact capstone required by the current order-49 program. -/
theorem minDegreeForC4_fortyNine_lt_fortyEight
    (hw48 : C4FreeMinDegreeWitness 48 7)
    (hno49 : ¬ C4FreeMinDegreeWitness 49 7) :
    minDegreeForC4 49 < minDegreeForC4 48 := by
  simpa using minDegreeForC4_drop_of_witness_of_no_succ_witness
    (n := 48) (d := 7) (by norm_num) hw48 hno49

/-- The same conditional finite result in the convention-free Ramsey language:
star sizes 41 and 42 first become forced at order 49. -/
theorem consecutiveC4StarPlateauAt_fortyEight
    (hw48 : C4FreeMinDegreeWitness 48 7)
    (hno49 : ¬ C4FreeMinDegreeWitness 49 7) :
    ConsecutiveC4StarPlateauAt 48 41 := by
  -- The two witness bounds pin the capacity jump across 48/49 around degree 7;
  -- unfold the plateau directly to identify the star parameter as 41.
  have hold : 7 < minDegreeForC4 48 :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by norm_num)).1 hw48
  have hnew : minDegreeForC4 49 ≤ 7 :=
    (not_c4FreeMinDegreeWitness_iff_minDegreeForC4_le (by norm_num)).1 hno49
  constructor
  · intro h
    have hle := (c4StarRamseyAt_iff_threshold (m := 48) (s := 41)
      (by norm_num) (by norm_num)).1 h
    omega
  constructor
  · intro h
    have hle := (c4StarRamseyAt_iff_threshold (m := 48) (s := 42)
      (by norm_num) (by norm_num)).1 h
    omega
  constructor
  · exact (c4StarRamseyAt_iff_threshold (m := 49) (s := 41)
      (by norm_num) (by norm_num)).2 (by omega)
  · exact (c4StarRamseyAt_iff_threshold (m := 49) (s := 42)
      (by norm_num) (by norm_num)).2 (by omega)

end Erdos85
