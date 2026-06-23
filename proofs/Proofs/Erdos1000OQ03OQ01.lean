import Mathlib

/-!
# The combinatorial characterization of Jordan's totient `J_k`

**Follow-up open question (`erdos-1000-oq-03-oq-01`).**  The gallery entry
`erdos-1000-oq-03` builds the divisor-sum / multiplicativity theory of **Jordan's
totient** `J_k` from its *Dirichlet-convolution* definition `J_k = μ * pow k`,
explicitly *deferring* the combinatorial counting definition.  This file closes
that gap: it proves that the convolution closed form really does **count tuples**.

Define
$$ C_k(n) \;=\; \#\bigl\{\, (a_0,\dots,a_{k-1}) \in (\mathbb{Z}/n)^k \;:\;
      \gcd(a_0,\dots,a_{k-1},n) = 1 \,\bigr\}. $$

## What this file proves (0 axioms, 0 sorries)

* `jordanCount_divisor_sum` : `∑_{d ∣ n} C_k(d) = n^k`
  — the Gauss-type divisor identity (generalizes `∑_{d∣n} φ(d) = n`), proved by a
  *bijective* fiberwise count: every tuple mod `n` scales uniquely from a
  jointly-coprime tuple mod `n/d`, where `d = gcd(a₀,…,a_{k-1},n)`.
* `jordanCount_eq_moebius_sum` : `C_k(n) = ∑_{d ∣ n} μ(d)·(n/d)^k`
  — the explicit **Jordan totient** closed form, obtained from the divisor sum by
  Möbius inversion.  This is exactly `(μ * pow k)(n)`, so the combinatorial count
  `C_k` agrees with the Dirichlet-convolution `J_k` of `erdos-1000-oq-03`.
* `jordanCount_one_eq_totient` : `C_1(n) = φ(n)` — recovers Euler's totient,
  confirming the count specializes correctly at `k = 1`.

The whole development rests on one elementary bijection plus Mathlib's Möbius
inversion (`ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`); no analysis.
-/

open Finset ArithmeticFunction

namespace Erdos1000OQ03OQ01

/-- The gcd of all coordinates of a tuple `a : Fin k → Fin n`, taken as naturals.
This is `gcd(a₀, …, a_{k-1})`; jointly coprime to `n` means `gcd(this, n) = 1`. -/
def gv {k n : ℕ} (a : Fin k → Fin n) : ℕ := univ.gcd (fun i => (a i).val)

/-- The set of `k`-tuples in `(ℤ/n)^k` whose coordinates are *jointly coprime* to
`n`, i.e. `gcd(a₀, …, a_{k-1}, n) = 1`. -/
def coprimeTuples (k n : ℕ) : Finset (Fin k → Fin n) :=
  univ.filter (fun a => Nat.Coprime (gv a) n)

/-- Jordan's totient as a count: `C_k(n) = #{ jointly-coprime k-tuples mod n }`. -/
def jordanCount (k n : ℕ) : ℕ := (coprimeTuples k n).card

/-- Scaling all coordinates by `d` multiplies the coordinate-gcd by `d`. -/
private lemma gcd_smul (k d : ℕ) (f : Fin k → ℕ) :
    univ.gcd (fun i => d * f i) = d * univ.gcd f := by
  simpa [normalize_eq] using
    Finset.gcd_mul_left (s := (univ : Finset (Fin k))) (f := f) (a := d)

/-- Dividing all coordinates (each a multiple of `d`) by `d` divides the gcd by `d`. -/
private lemma gcd_div (k d : ℕ) (f : Fin k → ℕ) (hd : 0 < d) (hdf : ∀ i, d ∣ f i) :
    univ.gcd (fun i => f i / d) = (univ.gcd f) / d := by
  have key : d * univ.gcd (fun i => f i / d) = univ.gcd f := by
    rw [← gcd_smul k d (fun i => f i / d)]
    exact Finset.gcd_congr rfl fun i _ => Nat.mul_div_cancel' (hdf i)
  rw [← key, Nat.mul_div_cancel_left _ hd]

/-- **Gauss-type divisor identity for Jordan's totient.**
`∑_{d ∣ n} C_k(d) = n^k`, the exact generalization of `∑_{d∣n} φ(d) = n`. -/
theorem jordanCount_divisor_sum (k : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, jordanCount k d = n ^ k := by
  classical
  -- content of a tuple: the gcd of its coordinates together with `n`.
  -- every content lands in `n.divisors`
  have hmaps : ∀ a ∈ (univ : Finset (Fin k → Fin n)),
      Nat.gcd (gv a) n ∈ n.divisors := by
    intro a _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hn.ne'⟩
  -- fiberwise count of all `n^k` tuples
  have hcard : (univ : Finset (Fin k → Fin n)).card
      = ∑ d ∈ n.divisors, (univ.filter (fun a => Nat.gcd (gv a) n = d)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  -- each fiber over `d` has exactly `C_k(n/d)` elements
  have hfiber : ∀ d ∈ n.divisors,
      (univ.filter (fun a : Fin k → Fin n => Nat.gcd (gv a) n = d)).card
        = jordanCount k (n / d) := by
    intro d hd
    obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
    rw [jordanCount]
    -- key per-tuple facts inside the fiber: `d ∣ (a i).val` for all `i`.
    have hdvd : ∀ a : Fin k → Fin n, Nat.gcd (gv a) n = d → ∀ i, d ∣ (a i).val := by
      intro a hca i
      have h1 : d ∣ gv a := by rw [← hca]; exact Nat.gcd_dvd_left _ _
      exact h1.trans (Finset.gcd_dvd (mem_univ i))
    refine Finset.card_bij'
      (i := fun a ha => fun i => (⟨(a i).val / d, ?_⟩ : Fin (n / d)))
      (j := fun b _ => fun i => (⟨d * (b i).val, ?_⟩ : Fin n))
      ?hi ?hj ?hl ?hr
    · -- bound: `(a i).val / d < n / d`
      have hca : Nat.gcd (gv a) n = d := (mem_filter.mp ha).2
      have : d * ((a i).val / d) < d * (n / d) := by
        rw [Nat.mul_div_cancel' (hdvd a hca i), hdmul]; exact (a i).isLt
      exact lt_of_mul_lt_mul_left this (Nat.zero_le d)
    · -- bound: `d * (b i).val < n`
      have : d * (b i).val < d * (n / d) := mul_lt_mul_of_pos_left (b i).isLt hdpos
      rwa [hdmul] at this
    · -- forward map lands in `coprimeTuples k (n/d)`
      intro a ha
      have hgcd : Nat.gcd (gv a) n = d := (mem_filter.mp ha).2
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      show Nat.Coprime (univ.gcd (fun i => (a i).val / d)) (n / d)
      rw [gcd_div k d (fun i => (a i).val) hdpos (hdvd a hgcd)]
      have hpos : 0 < Nat.gcd (gv a) n := hgcd ▸ hdpos
      have := Nat.coprime_div_gcd_div_gcd hpos
      rwa [hgcd] at this
    · -- backward map lands in the fiber `gcd = d`
      intro b hb
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      have hcop : Nat.gcd (univ.gcd (fun i => (b i).val)) (n / d) = 1 := (mem_filter.mp hb).2
      show Nat.gcd (univ.gcd (fun i => d * (b i).val)) n = d
      rw [gcd_smul k d (fun i => (b i).val)]
      have hkey : Nat.gcd (d * univ.gcd (fun i => (b i).val)) (d * (n / d))
          = d * Nat.gcd (univ.gcd (fun i => (b i).val)) (n / d) := Nat.gcd_mul_left _ _ _
      rw [hcop, mul_one, hdmul] at hkey
      exact hkey
    · -- left inverse: scaling back recovers `a`
      intro a ha
      have hca : Nat.gcd (gv a) n = d := (mem_filter.mp ha).2
      funext i
      exact Fin.ext (Nat.mul_div_cancel' (hdvd a hca i))
    · -- right inverse: dividing back recovers `b`
      intro b _
      funext i
      exact Fin.ext (Nat.mul_div_cancel_left _ hdpos)
  rw [Finset.card_univ, Fintype.card_fun] at hcard
  simp only [Fintype.card_fin] at hcard
  -- `n^k = ∑_{d|n} C_k(n/d) = ∑_{d|n} C_k(d)`
  rw [hcard, Finset.sum_congr rfl hfiber]
  exact (Nat.sum_div_divisors n (jordanCount k)).symm

/-- **The explicit Jordan-totient closed form, from Möbius inversion of the divisor
sum.**  `C_k(n) = ∑_{d ∣ n} μ(d)·(n/d)^k`, which is exactly `(μ * pow k)(n)` — so the
combinatorial count `C_k` coincides with the Dirichlet-convolution `J_k` of
`erdos-1000-oq-03`. -/
theorem jordanCount_eq_moebius_sum (k : ℕ) {n : ℕ} (hn : 0 < n) :
    (jordanCount k n : ℤ)
      = ∑ d ∈ n.divisors, (moebius d : ℤ) * (((n / d) ^ k : ℕ) : ℤ) := by
  have H : ∀ m, 0 < m → ∑ i ∈ m.divisors, (jordanCount k i : ℤ) = ((m ^ k : ℕ) : ℤ) := by
    intro m hm
    rw [← Nat.cast_sum, jordanCount_divisor_sum k hm]
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
      (f := fun i => (jordanCount k i : ℤ))
      (g := fun m => ((m ^ k : ℕ) : ℤ))).mp H n hn
  rw [← hinv, Nat.sum_divisorsAntidiagonal (fun p q => (moebius p : ℤ) • ((q ^ k : ℕ) : ℤ))]
  exact Finset.sum_congr rfl fun d _ => by simp

/-- **Euler recovery: `C_1(n) = φ(n)`.**  The `k = 1` count of integers coprime to
`n` is precisely Euler's totient, confirming `J_1 = φ`. -/
theorem jordanCount_one_eq_totient (n : ℕ) : jordanCount 1 n = Nat.totient n := by
  classical
  -- `gv` of a length-one tuple is just its single coordinate.
  have hgv : ∀ a : Fin 1 → Fin n, gv a = (a 0).val := by
    intro a
    rw [gv, Finset.univ_unique, Finset.gcd_singleton, normalize_eq]
    rfl
  rw [jordanCount, coprimeTuples, Nat.totient]
  refine Finset.card_bij' (fun a _ => (a 0).val)
    (fun x hx => fun _ => ⟨x, Finset.mem_range.mp (Finset.mem_filter.mp hx).1⟩) ?_ ?_ ?_ ?_
  · intro a ha
    have : Nat.Coprime (gv a) n := (mem_filter.mp ha).2
    rw [hgv] at this
    exact mem_filter.mpr ⟨Finset.mem_range.mpr (a 0).isLt, this.symm⟩
  · intro x hx
    have hc : Nat.Coprime n x := (mem_filter.mp hx).2
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [hgv]
    exact hc.symm
  · intro a _; funext i; fin_cases i; rfl
  · intro x _; rfl

end Erdos1000OQ03OQ01

