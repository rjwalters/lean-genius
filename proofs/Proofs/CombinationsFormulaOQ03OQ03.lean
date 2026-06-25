/-
Combinations Formula OQ-03-OQ-03:
The Finite Rogers–Ramanujan (Schur) Identity via q-Gaussian Binomials

The parent entry `CombinationsFormulaOQ03` develops Gaussian (q-)binomial
coefficients `[n choose k]_q` over an arbitrary commutative ring, division-free,
via the q-Pascal recurrence. The seeker's open question asks whether the
**Rogers–Ramanujan identities** can be approached using that library.

The *analytic* Rogers–Ramanujan identity
  ∑_{n ≥ 0} q^{n²} / (q;q)_n = ∏_{n ≥ 0} 1 / ((1 - q^{5n+1})(1 - q^{5n+4}))
is an identity of formal power series / convergent q-series and is well beyond a
single formalization session (it needs infinite products and the theory of
`ℤ[[q]]`). This file instead formalizes the rigorous *finite* heart of the
identity — the object Schur (1917) introduced to prove Rogers–Ramanujan and
which converges termwise to the series side as `n → ∞`.

Define the **Schur sum** (a polynomial in q over any CommRing)

  S_n(q) = ∑_{j ≥ 0} q^{j²} · [n - j choose j]_q.

Main result (`schurSum_recurrence`): these satisfy the q-Fibonacci recurrence

  S_{n+2}(q) = S_{n+1}(q) + q^{n+1} · S_n(q),   S_0 = S_1 = 1.

This is exactly Schur's recurrence: as `n → ∞` the polynomials converge to the
Rogers–Ramanujan series `∑ q^{j²}/(q;q)_j`, and the recurrence is the finite
combinatorial mechanism underlying the identity. Specializing at `q = 1` the
recurrence becomes the Fibonacci recurrence, giving two corollaries:

  * `schurSum_at_one_eq_fib` :  S_n(1) = F_{n+1}   (Fibonacci numbers), and
  * `sum_choose_eq_fib`      :  ∑_{j} C(n-j, j) = F_{n+1}   (the classical
    diagonal-of-Pascal identity), recovered for free.

Everything is proved over an arbitrary `CommRing R`, with `0` sorries and
`0` axioms (the q-binomial library it builds on is itself `0`-axiom).

The engine is the parent's **second q-Pascal identity**
  [n+1 choose k+1]_q = q^{n-k} · [n choose k]_q + [n choose k+1]_q
(here proved unconditionally as `qBinom_pascal'_all`), applied termwise and
reindexed.
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic
import Proofs.CombinationsFormulaOQ03

namespace RogersRamanujanSchur

open QBinomialCoefficients

variable {R : Type*} [CommRing R]

-- ============================================================
-- Part I: Unconditional second q-Pascal identity
-- ============================================================

/-- **Unconditional second q-Pascal identity**:
    [a+1 choose k+1]_q = q^{a-k} · [a choose k]_q + [a choose k+1]_q,
    for *all* `a k : ℕ`.

    The parent `qBinom_pascal'` carries the hypothesis `k + 1 ≤ a + 1`. When
    `a < k` all three q-binomials vanish (`qBinom_eq_zero_of_lt`), so the
    identity degenerates to `0 = q^{a-k} · 0 + 0`. Removing the hypothesis lets
    us apply the identity termwise inside a `Finset` sum without threading a
    side condition through every summand. -/
theorem qBinom_pascal'_all (q : R) (a k : ℕ) :
    qBinom q (a + 1) (k + 1) = q ^ (a - k) * qBinom q a k + qBinom q a (k + 1) := by
  rcases le_or_gt k a with hk | hk
  · exact qBinom_pascal' q a k (by omega)
  · rw [qBinom_eq_zero_of_lt q (a + 1) (k + 1) (by omega),
        qBinom_eq_zero_of_lt q a k hk,
        qBinom_eq_zero_of_lt q a (k + 1) (by omega)]
    ring

-- ============================================================
-- Part II: The Schur sum
-- ============================================================

/-- The **Schur sum** `S_n(q) = ∑_{j} q^{j²} · [n - j choose j]_q`.

    The summation range `Finset.range (n + 1)` is a safe upper bound: the
    summand vanishes once `j > n - j` (the q-binomial `[n-j choose j]_q` is then
    `0`), so no nonzero term is omitted. At `q = 1` this is the diagonal sum
    `∑_j C(n-j, j)`, the `(n+1)`-st Fibonacci number. -/
def schurSum (q : R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range (n + 1), q ^ (j ^ 2) * qBinom q (n - j) j

@[simp] theorem schurSum_zero (q : R) : schurSum q 0 = 1 := by
  simp [schurSum]

@[simp] theorem schurSum_one (q : R) : schurSum q 1 = 1 := by
  simp [schurSum, Finset.sum_range_succ]

/-- Peeling the `j = 0` term of `S_{n+1}` and reindexing `j ↦ i+1`:
    `S_{n+1}(q) = (∑_{i < n+1} q^{(i+1)²} · [n - i choose i+1]_q) + 1`.
    Used to recognise the "second piece" produced by the q-Pascal split. -/
theorem schurSum_succ_peel (q : R) (n : ℕ) :
    schurSum q (n + 1) =
      (∑ i ∈ Finset.range (n + 1), q ^ ((i + 1) ^ 2) * qBinom q (n - i) (i + 1)) + 1 := by
  rw [schurSum, Finset.sum_range_succ']
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [Nat.succ_sub_succ])
  · simp

-- ============================================================
-- Part III: The finite Rogers–Ramanujan (Schur) recurrence
-- ============================================================

/-- **Finite Rogers–Ramanujan / Schur recurrence**:
    `S_{n+2}(q) = S_{n+1}(q) + q^{n+1} · S_n(q)`.

    This is Schur's (1917) recurrence for the polynomials whose `n → ∞` limit is
    the Rogers–Ramanujan series `∑_j q^{j²}/(q;q)_j`. The proof expands
    `S_{n+2}` over `Finset.range (n+3)`, peels the bottom (`j = 0`) and top
    (`j = n+2`, which vanishes) terms, then applies the unconditional second
    q-Pascal identity `qBinom_pascal'_all` to each remaining term. The split
    produces two sums: one is `S_{n+1}` (minus its peeled `j=0` term) and the
    other, after the exponent identity `(i+1)² + (n-i) - i = i² + (n+1)` (valid
    when the surviving q-binomial is nonzero), is `q^{n+1} · S_n`. -/
theorem schurSum_recurrence (q : R) (n : ℕ) :
    schurSum q (n + 2) = schurSum q (n + 1) + q ^ (n + 1) * schurSum q n := by
  -- Expand the left-hand side and peel the j = 0 term.
  rw [show schurSum q (n + 2) =
        ∑ j ∈ Finset.range (n + 3), q ^ (j ^ 2) * qBinom q (n + 2 - j) j from rfl,
      Finset.sum_range_succ']
  -- Peel the top term j = n+2 (it is 0: [0 choose n+2]_q = 0).
  rw [Finset.sum_range_succ]
  have htop : q ^ ((n + 1 + 1) ^ 2) * qBinom q (n + 2 - (n + 1 + 1)) (n + 1 + 1) = 0 := by
    rw [show n + 2 - (n + 1 + 1) = 0 from by omega, qBinom_zero_succ, mul_zero]
  -- The peeled j = 0 term equals 1.
  have hbot : q ^ ((0 : ℕ) ^ 2) * qBinom q (n + 2 - 0) 0 = 1 := by simp
  rw [htop, hbot, add_zero]
  -- Rewrite each surviving summand via the second q-Pascal identity.
  have hcongr : ∀ i ∈ Finset.range (n + 1),
      q ^ ((i + 1) ^ 2) * qBinom q (n + 2 - (i + 1)) (i + 1) =
        q ^ ((i + 1) ^ 2) * qBinom q (n - i) (i + 1) +
          q ^ (i ^ 2 + (n + 1)) * qBinom q (n - i) i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show n + 2 - (i + 1) = (n - i) + 1 from by omega, qBinom_pascal'_all q (n - i) i]
    rcases le_or_gt i (n - i) with hc | hc
    · -- the q-binomial survives; the exponents match exactly
      have hexp : (i + 1) ^ 2 + ((n - i) - i) = i ^ 2 + (n + 1) := by
        have hsq : (i + 1) ^ 2 = i ^ 2 + 2 * i + 1 := by ring
        omega
      calc
        q ^ ((i + 1) ^ 2) *
            (q ^ ((n - i) - i) * qBinom q (n - i) i + qBinom q (n - i) (i + 1))
            = q ^ ((i + 1) ^ 2 + ((n - i) - i)) * qBinom q (n - i) i +
                q ^ ((i + 1) ^ 2) * qBinom q (n - i) (i + 1) := by rw [pow_add]; ring
          _ = q ^ (i ^ 2 + (n + 1)) * qBinom q (n - i) i +
                q ^ ((i + 1) ^ 2) * qBinom q (n - i) (i + 1) := by rw [hexp]
          _ = q ^ ((i + 1) ^ 2) * qBinom q (n - i) (i + 1) +
                q ^ (i ^ 2 + (n + 1)) * qBinom q (n - i) i := by ring
    · -- the q-binomial [n-i choose i]_q vanishes; both extra terms are 0
      rw [qBinom_eq_zero_of_lt q (n - i) i (by omega)]
      ring
  rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib]
  -- Identify the two resulting sums with S_{n+1} and q^{n+1} · S_n.
  rw [schurSum_succ_peel]
  have hB : q ^ (n + 1) * schurSum q n =
      ∑ i ∈ Finset.range (n + 1), q ^ (i ^ 2 + (n + 1)) * qBinom q (n - i) i := by
    rw [schurSum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pow_add]; ring
  rw [hB]; ring

-- ============================================================
-- Part IV: Specialization at q = 1 — Fibonacci numbers
-- ============================================================

/-- **Specialization at q = 1**: `S_n(1) = F_{n+1}` (the `(n+1)`-st Fibonacci
    number). At `q = 1` the Schur recurrence `S_{n+2} = S_{n+1} + q^{n+1} S_n`
    becomes the Fibonacci recurrence `S_{n+2} = S_{n+1} + S_n` with
    `S_0 = S_1 = 1 = F_1 = F_2`. -/
theorem schurSum_at_one_eq_fib : ∀ n : ℕ, schurSum (1 : ℤ) n = (Nat.fib (n + 1) : ℤ)
  | 0 => by simp [Nat.fib_one]
  | 1 => by simp [schurSum_one, Nat.fib_add_two]
  | (n + 2) => by
    rw [schurSum_recurrence, one_pow, one_mul,
        schurSum_at_one_eq_fib (n + 1), schurSum_at_one_eq_fib n]
    have h : Nat.fib (n + 2 + 1) = Nat.fib (n + 1) + Nat.fib (n + 1 + 1) :=
      Nat.fib_add_two (n := n + 1)
    rw [h]; push_cast; ring

/-- **Classical diagonal-of-Pascal identity** `∑_{j} C(n-j, j) = F_{n+1}`,
    recovered as the `q = 1` reading of the Schur sum. The diagonal sums of
    Pascal's triangle are the Fibonacci numbers; here the identity falls out of
    `schurSum_at_one_eq_fib` together with `qBinom (1) = C`. -/
theorem sum_choose_eq_fib (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), Nat.choose (n - j) j = Nat.fib (n + 1) := by
  have h := schurSum_at_one_eq_fib n
  rw [schurSum] at h
  simp only [one_pow, one_mul, qBinom_at_one] at h
  exact_mod_cast h

-- ============================================================
-- Part V: Concrete verifications
-- ============================================================

section Verifications
variable (q : R)

/-- `S_2(q) = 1 + q`. -/
example : schurSum q 2 = 1 + q := by
  simp [schurSum, Finset.sum_range_succ, qBinom]

/-- `S_3(q) = 1 + q + q²`. -/
example : schurSum q 3 = 1 + q + q ^ 2 := by
  simp [schurSum, Finset.sum_range_succ, qBinom]; ring

/-- `S_4(q) = 1 + q + q² + q³ + q⁴`. -/
example : schurSum q 4 = 1 + q + q ^ 2 + q ^ 3 + q ^ 4 := by
  simp [schurSum, Finset.sum_range_succ, qBinom]; ring

/-- Fibonacci values: `S_5(1) = F_6 = 8`. -/
example : schurSum (1 : ℤ) 5 = 8 := by
  rw [schurSum_at_one_eq_fib]; decide

end Verifications

end RogersRamanujanSchur
