/-
# Cantor Diagonalization OQ-06-OQ-01: the explicit diagonal real

## Open Question
The parent entry `CantorDiagonalizationOQ06` proves `¬ Countable ℝ` abstractly, through
the cardinal inequality `ℵ₀ < #ℝ` (Mathlib's `Cardinal.not_countable_real`). This entry
supplies Cantor's *constructive* 1891 diagonal argument at the level of decimal digits:
given any enumeration `f : ℕ → ℝ` it builds an **explicit, definable** real
`diagonalReal f` and proves directly, digit by digit, that `diagonalReal f ≠ f n` for
every `n` — with no appeal to `Cardinal.not_countable_real` or `#ℝ = 𝔠`.

## Construction
* `digit r n := ⌊r * 10^(n+1)⌋ % 10` is the `n`-th decimal digit of `r` (an integer in
  `[0,10)`).
* `db f n := if digit (f n) n = 1 then 2 else 1` is a digit in `{1,2}` that *disagrees*
  with the `n`-th digit of `f n`.  Restricting the produced digits to `{1,2}` sidesteps
  the `0.999… = 1.000…` non-uniqueness that would make a naive digit argument false.
* `diagonalReal f := ∑' n, (db f n : ℝ) / 10^(n+1)` assembles the disagreeing digits into
  a real in `[0,1]`.

The crux lemma `digit_diagonalReal : digit (diagonalReal f) n = db f n` is proved by a
head/tail split of `diagonalReal f * 10^(n+1) = A + T`, where `A : ℤ` is the integer head
and `0 ≤ T ≤ 2/9 < 1` is a geometric tail, so `⌊diagonalReal f * 10^(n+1)⌋ = A` and
`A % 10 = db f n`.  Then `diagonalReal f = f n` would force
`digit (diagonalReal f) n = digit (f n) n`, contradicting `db f n ≠ digit (f n) n`.

Sorry-free and axiom-free.  Uses only foundational axioms
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib

namespace CantorDiagonalizationOQ06OQ01

/-- The `n`-th decimal digit of a real number `r`, as an integer in `[0,10)`. -/
noncomputable def digit (r : ℝ) (n : ℕ) : ℤ := ⌊r * 10 ^ (n + 1)⌋ % 10

/-- The diagonal digit at position `n`: a value in `{1,2}` chosen to differ from the
`n`-th digit of `f n`. -/
noncomputable def db (f : ℕ → ℝ) (n : ℕ) : ℤ := if digit (f n) n = 1 then 2 else 1

/-- **Cantor's explicit diagonal real.**  Given an enumeration `f : ℕ → ℝ`, the digits
`db f n ∈ {1,2}` assemble into a real number in `[0,1]`. -/
noncomputable def diagonalReal (f : ℕ → ℝ) : ℝ := ∑' n, (db f n : ℝ) / 10 ^ (n + 1)

/-! ## Elementary facts about the diagonal digits -/

theorem db_eq (f : ℕ → ℝ) (n : ℕ) : db f n = 1 ∨ db f n = 2 := by
  unfold db; split_ifs <;> simp

theorem db_pos (f : ℕ → ℝ) (n : ℕ) : 0 < db f n := by
  rcases db_eq f n with h | h <;> rw [h] <;> norm_num

theorem db_le_two (f : ℕ → ℝ) (n : ℕ) : db f n ≤ 2 := by
  rcases db_eq f n with h | h <;> rw [h] <;> norm_num

/-- The diagonal digit differs from the `n`-th digit of `f n` — the heart of the
disagreement. -/
theorem db_ne_digit (f : ℕ → ℝ) (n : ℕ) : db f n ≠ digit (f n) n := by
  unfold db
  split_ifs with h
  · rw [h]; norm_num
  · exact fun hc => h hc.symm

/-! ## Summability -/

/-- A generic term bound: `db f m / 10^(i+1) ≤ 2 * (1/10)^(i+1)`, valid for any index `m`
appearing in the numerator. -/
theorem term_le' (f : ℕ → ℝ) (m i : ℕ) :
    (db f m : ℝ) / 10 ^ (i + 1) ≤ 2 * (1 / 10) ^ (i + 1) := by
  rw [div_pow, one_pow, mul_one_div]
  gcongr
  exact_mod_cast db_le_two f m

/-- Each term of the defining series is nonnegative. -/
theorem term_nonneg (f : ℕ → ℝ) (m i : ℕ) : 0 ≤ (db f m : ℝ) / 10 ^ (i + 1) := by
  apply div_nonneg
  · exact_mod_cast (db_pos f m).le
  · positivity

/-- The shifted geometric series `∑' i, 2 * (1/10)^(i+1)` is summable. -/
theorem summable_geo_shift : Summable (fun i : ℕ => 2 * (1 / 10 : ℝ) ^ (i + 1)) := by
  apply Summable.mul_left
  exact (summable_nat_add_iff 1).mpr
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- The defining series of `diagonalReal` is summable. -/
theorem summable_term (f : ℕ → ℝ) :
    Summable (fun k => (db f k : ℝ) / 10 ^ (k + 1)) := by
  apply Summable.of_nonneg_of_le (fun k => term_nonneg f k k) (fun k => term_le' f k k)
  exact summable_geo_shift

/-! ## The head/tail decomposition -/

/-- The integer head: `A f n = ∑_{i≤n} db f i * 10^(n-i)`.  This is an integer whose last
decimal digit is `db f n`. -/
noncomputable def headInt (f : ℕ → ℝ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), db f i * 10 ^ (n - i)

/-- The head sum over reals equals `(headInt f n : ℝ)`. -/
theorem head_real_eq (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (db f i : ℝ) / 10 ^ (i + 1)) * 10 ^ (n + 1)
      = (headInt f n : ℝ) := by
  rw [Finset.sum_mul, headInt]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by simp only [Finset.mem_range] at hi; omega
  have hpow : (10 : ℝ) ^ (n + 1) / 10 ^ (i + 1) = 10 ^ (n - i) := by
    rw [eq_comm, eq_div_iff (by positivity), ← pow_add]
    congr 1; omega
  rw [div_mul_eq_mul_div, mul_div_assoc, hpow]

/-- The `A % 10 = db f n` step: the last decimal digit of the head is `db f n`. -/
theorem headInt_emod (f : ℕ → ℝ) (n : ℕ) : headInt f n % 10 = db f n := by
  rw [headInt, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one]
  set S := ∑ i ∈ Finset.range n, db f i * 10 ^ (n - i) with hS
  have hdvd : (10 : ℤ) ∣ S := by
    rw [hS]
    apply Finset.dvd_sum
    intro i hi
    have hin : i < n := by simpa only [Finset.mem_range] using hi
    have he : n - i = (n - 1 - i) + 1 := by omega
    rw [he, pow_succ, ← mul_assoc]
    exact dvd_mul_left 10 (db f i * 10 ^ (n - 1 - i))
  obtain ⟨B, hB⟩ := hdvd
  rw [hB, add_comm, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (db_pos f n).le (by have := db_le_two f n; omega)

/-! ## The crux lemma -/

/-- **Crux:** the `n`-th digit of the diagonal real is exactly `db f n`. -/
theorem digit_diagonalReal (f : ℕ → ℝ) (n : ℕ) :
    digit (diagonalReal f) n = db f n := by
  have hsum := summable_term f
  -- Split the series at n+1: diagonalReal f = head + tail.
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun k => (db f k : ℝ) / 10 ^ (k + 1))
    (n + 1) hsum
  set tail := ∑' i, (db f (i + (n + 1)) : ℝ) / 10 ^ (i + (n + 1) + 1) with htail_def
  have hx : diagonalReal f =
      (∑ i ∈ Finset.range (n + 1), (db f i : ℝ) / 10 ^ (i + 1)) + tail := by
    rw [diagonalReal, htail_def]; exact hsplit.symm
  -- Multiply through by 10^(n+1).
  have hxmul : diagonalReal f * 10 ^ (n + 1)
      = (headInt f n : ℝ) + tail * 10 ^ (n + 1) := by
    rw [hx, add_mul, head_real_eq]
  set T := tail * 10 ^ (n + 1) with hT_def
  -- The scaled tail equals ∑' i, db f (i+n+1) / 10^(i+1).
  have hT_eq : T = ∑' i, (db f (i + (n + 1)) : ℝ) / 10 ^ (i + 1) := by
    rw [hT_def, htail_def, ← tsum_mul_right]
    apply tsum_congr
    intro i
    have hp : (10 : ℝ) ^ (i + (n + 1) + 1) = 10 ^ (i + 1) * 10 ^ (n + 1) := by
      rw [← pow_add]; congr 1; omega
    have h1 : (10 : ℝ) ^ (i + 1) ≠ 0 := by positivity
    have h2 : (10 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    rw [hp]; field_simp
  -- Tail is nonnegative.
  have hT_nonneg : 0 ≤ T := by
    rw [hT_eq]
    exact tsum_nonneg fun i => term_nonneg f (i + (n + 1)) i
  -- Tail is summable (comparison with geometric).
  have hT_summ : Summable (fun i => (db f (i + (n + 1)) : ℝ) / 10 ^ (i + 1)) :=
    Summable.of_nonneg_of_le (fun i => term_nonneg f (i + (n + 1)) i)
      (fun i => term_le' f (i + (n + 1)) i) summable_geo_shift
  -- Tail < 1.
  have hT_lt : T < 1 := by
    rw [hT_eq]
    calc ∑' i, (db f (i + (n + 1)) : ℝ) / 10 ^ (i + 1)
        ≤ ∑' i, 2 * (1 / 10 : ℝ) ^ (i + 1) :=
          Summable.tsum_le_tsum (fun i => term_le' f (i + (n + 1)) i) hT_summ summable_geo_shift
      _ = 2 * ∑' i, (1 / 10 : ℝ) ^ (i + 1) := by rw [tsum_mul_left]
      _ = 2 * ((∑' i, (1 / 10 : ℝ) ^ i) * (1 / 10)) := by
            congr 1
            rw [← tsum_mul_right]
            apply tsum_congr; intro i; rw [pow_succ]
      _ = 2 * ((1 - 1 / 10 : ℝ)⁻¹ * (1 / 10)) := by
            rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      _ < 1 := by norm_num
  -- Floor of x * 10^(n+1) is headInt f n.
  have hfloor : ⌊diagonalReal f * 10 ^ (n + 1)⌋ = headInt f n := by
    have hTfloor : ⌊T⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]; exact ⟨hT_nonneg, hT_lt⟩
    rw [hxmul, Int.floor_intCast_add, hTfloor, add_zero]
  rw [digit, hfloor, headInt_emod]

/-! ## The diagonal real differs from every listed real -/

/-- **Diagonal disagreement.**  The explicit real `diagonalReal f` is different from every
term `f n` of the enumeration, because their `n`-th decimal digits differ. -/
theorem diagonalReal_ne (f : ℕ → ℝ) (n : ℕ) : diagonalReal f ≠ f n := by
  intro hEq
  have hdig : digit (diagonalReal f) n = digit (f n) n := by rw [hEq]
  rw [digit_diagonalReal] at hdig
  exact db_ne_digit f n hdig

/-- **Cantor's constructive theorem:** no `f : ℕ → ℝ` is surjective, witnessed explicitly
by `diagonalReal f`. -/
theorem not_surjective_nat_real (f : ℕ → ℝ) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨n, hn⟩ := hf (diagonalReal f)
  exact diagonalReal_ne f n hn.symm

/-- The reals are uncountable, proved via the explicit diagonal witness (no appeal to
`Cardinal.not_countable_real`). -/
theorem not_exists_surjective_nat_real : ¬ ∃ f : ℕ → ℝ, Function.Surjective f :=
  fun ⟨f, hf⟩ => not_surjective_nat_real f hf

/-! ## Standard consequences, derived from the explicit diagonal

The two headline statements below are the textbook corollaries of Cantor's
diagonal argument.  We obtain them *from the bespoke construction above* — the
only input is `not_surjective_nat_real`, never `Cardinal.not_countable_real` —
so the entry's originality is preserved while it still delivers the expected
`Uncountable ℝ` conclusion in Mathlib's own vocabulary. -/

/-- **`ℝ` is uncountable** (`Uncountable` instance), obtained purely from the explicit
diagonal `diagonalReal`.  Were `ℝ` countable, `exists_surjective_nat` would supply a
surjection `ℕ → ℝ`, which `not_exists_surjective_nat_real` forbids.  No appeal to
`Cardinal.not_countable_real`. -/
theorem uncountable_real : Uncountable ℝ := by
  rw [← not_countable_iff]
  exact fun _ => not_exists_surjective_nat_real (exists_surjective_nat ℝ)

/-- **No countable type surjects onto `ℝ`.**  The diagonal argument scales from `ℕ`
to any countable index type `α`: a surjection `g : α → ℝ` with `α` countable would,
composed with a surjection `ℕ → α` (from `exists_surjective_nat`), yield a surjection
`ℕ → ℝ`; and if `α` is empty there is no surjection onto the non-empty `ℝ` at all.
Either way `not_surjective_nat_real` closes it.  So `ℝ` is not the surjective image of
any countable set — the general form of the uncountability statement. -/
theorem not_surjective_of_countable {α : Type*} [Countable α] (g : α → ℝ) :
    ¬ Function.Surjective g := by
  intro hg
  rcases isEmpty_or_nonempty α with hα | hα
  · exact (hg 0).elim (fun a _ => (IsEmpty.false a))
  · obtain ⟨e, he⟩ := exists_surjective_nat α
    exact not_surjective_nat_real (g ∘ e) (hg.comp he)

/-! ## The diagonal lives in the unit interval `(0,1)`

The construction above concludes `Uncountable ℝ`, but the diagonal `diagonalReal f`
built from digits in `{1,2}` in fact lands in the open unit interval `(0,1)` — it is
squeezed between `∑ 1/10^(n+1) = 1/9` and `∑ 2/10^(n+1) = 2/9`.  Recording this
strengthens the headline result: uncountability is already carried by an arbitrarily
small subinterval, and every statement below still routes through the bespoke
`diagonalReal`, never `Cardinal.not_countable_real`. -/

/-- The geometric majorant sums to `2/9`: `∑' i, 2·(1/10)^(i+1) = 2/9`. -/
theorem tsum_geo_shift : ∑' i : ℕ, 2 * (1 / 10 : ℝ) ^ (i + 1) = 2 / 9 := by
  calc ∑' i : ℕ, 2 * (1 / 10 : ℝ) ^ (i + 1)
      = ∑' i : ℕ, (2 * (1 / 10 : ℝ)) * (1 / 10 : ℝ) ^ i :=
        tsum_congr (fun i => by rw [pow_succ]; ring)
    _ = (2 * (1 / 10 : ℝ)) * ∑' i : ℕ, (1 / 10 : ℝ) ^ i := by rw [tsum_mul_left]
    _ = (2 * (1 / 10 : ℝ)) * (1 - 1 / 10)⁻¹ := by
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = 2 / 9 := by norm_num

/-- **The diagonal is strictly positive.**  `diagonalReal f > 0`: every term is
nonnegative and the `n = 0` term `db f 0 / 10 ≥ 1/10` is strictly positive. -/
theorem diagonalReal_pos (f : ℕ → ℝ) : 0 < diagonalReal f := by
  rw [diagonalReal]
  refine Summable.tsum_pos (summable_term f) (fun k => term_nonneg f k k) 0 ?_
  have h : (db f 0 : ℝ) / 10 ^ (0 + 1) = (db f 0 : ℝ) / 10 := by norm_num
  have hpos : (1 : ℝ) ≤ (db f 0 : ℝ) := by exact_mod_cast db_pos f 0
  rw [h]; positivity

/-- **The diagonal is strictly below `1`.**  `diagonalReal f ≤ 2/9 < 1`, since every
term is bounded by the geometric majorant `2·(1/10)^(n+1)` summing to `2/9`. -/
theorem diagonalReal_lt_one (f : ℕ → ℝ) : diagonalReal f < 1 := by
  have hle : diagonalReal f ≤ 2 / 9 := by
    rw [diagonalReal, ← tsum_geo_shift]
    exact Summable.tsum_mono (summable_term f) summable_geo_shift (fun k => term_le' f k k)
  linarith

/-- **The diagonal lies in the open unit interval.**  `diagonalReal f ∈ (0,1)`. -/
theorem diagonalReal_mem_Ioo (f : ℕ → ℝ) : diagonalReal f ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨diagonalReal_pos f, diagonalReal_lt_one f⟩

/-- **Cantor for the unit interval:** no `g : ℕ → (0,1)` is surjective, witnessed by the
diagonal of the underlying reals — which itself lies in `(0,1)`. -/
theorem not_surjective_nat_Ioo (g : ℕ → Set.Ioo (0 : ℝ) 1) : ¬ Function.Surjective g := by
  intro hg
  obtain ⟨n, hn⟩ := hg ⟨diagonalReal (fun m => (g m : ℝ)), diagonalReal_mem_Ioo _⟩
  have : diagonalReal (fun m => (g m : ℝ)) = (g n : ℝ) := congrArg Subtype.val hn.symm
  exact diagonalReal_ne (fun m => (g m : ℝ)) n this

/-- **The open unit interval `(0,1)` is uncountable**, proved from the explicit diagonal:
the diagonal of any listing lands in `(0,1)` yet differs from every listed real, so no
surjection `ℕ → (0,1)` exists.  A strengthening of `uncountable_real` — uncountability is
already carried by an arbitrarily small subinterval.  No appeal to
`Cardinal.not_countable_real`. -/
theorem uncountable_Ioo : Uncountable (Set.Ioo (0 : ℝ) 1) := by
  rw [← not_countable_iff]
  intro h
  have : Nonempty (Set.Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (Set.Ioo (0 : ℝ) 1)
  exact not_surjective_nat_Ioo e he

end CantorDiagonalizationOQ06OQ01
