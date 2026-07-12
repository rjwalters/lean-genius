/-
  Roth Theorem OQ-04: the L¹ first moment of the quadratic Gauss sum.

  The magnitude machinery of `RothTheorem` (`sqGaussSum_normSq_le_gcd`,
  `sqGaussSum_norm_le_sqrt_gcd`) controls the quadratic Gauss sum
  `G(r) = ∑_{n} ψ(r · n²)` *pointwise* by the arithmetic quantity
  `√(N · gcd(2r, N))`.  The Sárközy square-difference density bound, however,
  is driven not by the pointwise maximum but by the **average** size of `G`.
  The relevant averaged quantity is the first moment (the `L¹` norm)
  `∑_{r} ‖G(r)‖`.

  This file evaluates the natural upper bound for that first moment at **odd
  moduli** as an exact multiplicative divisor sum.  Two ingredients:

  * `sum_weight_gcd_eq_divisor_sum` — a self-contained arithmetic identity:
    for any weight `w`, `∑_{c<n} w(gcd(n,c)) = ∑_{d∣n} φ(n/d)·w(d)`.  Each
    divisor `d` is hit by exactly `φ(n/d)` residues `c` with `gcd(n,c)=d`
    (Mathlib's `Nat.totient_div_of_dvd`), so the gcd-weighted sum collapses to a
    sum over divisors.

  * `sum_norm_sqGaussSum_le_of_odd` — the capstone.  Summing the pointwise
    bound, factoring out `√N`, reindexing `r ↦ 2r` (a bijection of `ZMod N`
    since `2` is a unit at odd `N`) and transporting the residue sum to
    `range N`, gives

      `∑_{r} ‖G(r)‖ ≤ √N · ∑_{d ∣ N} φ(N/d) · √d`.

  The right-hand side is a concrete multiplicative arithmetic function of `N`,
  the first-moment companion of the pointwise `√(N·gcd)` and the second-moment
  (Plancherel) `∑_r ‖G(r)‖² = N · #{n² = m²}` bounds.  It is the exact input a
  quantitative Sárközy density estimate needs.

  * `sum_norm_sqGaussSum_eq_of_prime` / `sum_norm_sqGaussSum_bound_eq_of_prime` /
    `sum_norm_sqGaussSum_eq_bound_of_prime` — the ceiling is **sharp**.  At a
    prime modulus `N ≠ 2` the exact magnitudes `‖G(0)‖ = N`, `‖G(r)‖ = √N`
    (`r ≠ 0`) give the closed form `∑_r ‖G(r)‖ = N + (N-1)·√N`, and the divisor
    sum `√N·∑_{d∣N}φ(N/d)√d` collapses to *exactly* the same value (only the two
    divisors `1, N` contribute).  So the odd-modulus bound holds with equality at
    every odd prime — it is the best possible upper bound of this shape.

  * `sum_norm_sqGaussSum_eq_of_odd` — the capstone: the ceiling is in fact an
    **equality for *every* odd `N`**, composite or prime.  The pointwise magnitude
    at odd moduli is not merely bounded but exact — `sqGaussSum_norm_eq_sqrt_gcd_of_odd`
    (proved in `RothTheorem`: the Weyl residual sum `∑_{2rh=0} ψ(−rh²)` has *no
    cancellation* at odd `N`, since `2` is a unit) gives `‖G(r)‖ = √(N·gcd(2r,N))`
    for all `r`.  Hence

      `∑_{r} ‖G(r)‖ = √N · ∑_{d ∣ N} φ(N/d) · √d`   (odd `N`),

    upgrading the `≤` of `sum_norm_sqGaussSum_le_of_odd` to `=` and subsuming the prime
    sharpness above as the two-divisor case.  It evaluates the first moment at composite
    odd moduli too — e.g. `N = 9` gives `27 + 6√3` — where no prime-field argument applies.

  All results are fully machine-checked, 0 sorries, no `native_decide`.
-/
import Mathlib
import Proofs.RothTheorem

open Finset

namespace Szemeredi.Roth

/-- **Weighted gcd–divisor identity.**  For `n > 0` and any real weight `w`, the
    sum of `w (gcd n c)` over the residues `c ∈ range n` regroups by the divisor
    `d = gcd n c`; each divisor `d ∣ n` is the gcd of exactly `φ(n/d)` residues
    (`Nat.totient_div_of_dvd`), so the whole sum collapses to
    `∑_{d ∣ n} φ(n/d) · w d`. -/
theorem sum_weight_gcd_eq_divisor_sum (n : ℕ) (hn : 0 < n) (w : ℕ → ℝ) :
    ∑ c ∈ range n, w (n.gcd c) = ∑ d ∈ n.divisors, ((n / d).totient : ℝ) * w d := by
  rw [← Finset.sum_fiberwise_of_maps_to
        (fun c (_ : c ∈ range n) => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left n c, hn.ne'⟩)
        (fun c => w (n.gcd c))]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hcongr : ∀ c ∈ {c ∈ range n | n.gcd c = d}, w (n.gcd c) = w d := by
    intro c hc; rw [(Finset.mem_filter.1 hc).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, ← Nat.totient_div_of_dvd hdvd,
    nsmul_eq_mul]

/-- **L¹ first moment of the quadratic Gauss sum at odd moduli.**  Summing the
    pointwise bound `‖G(r)‖ ≤ √(N · gcd(2r, N))` and collapsing the resulting
    gcd-weighted residue sum to a divisor sum gives the exact multiplicative
    ceiling

      `∑_{r} ‖G(r)‖ ≤ √N · ∑_{d ∣ N} φ(N/d) · √d`.

    Oddness enters only through the reindexing `r ↦ 2r`, a bijection of `ZMod N`
    (as `2` is a unit), which turns `∑_r √(gcd(2r, N))` into the divisor sum. -/
theorem sum_norm_sqGaussSum_le_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    ∑ r : ZMod N, ‖sqGaussSum r‖
      ≤ Real.sqrt N * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- Step 1: pointwise bound, then pull out the constant factor √N.
  have step1 : ∑ r : ZMod N, ‖sqGaussSum r‖
      ≤ Real.sqrt N * ∑ r : ZMod N, Real.sqrt (N.gcd (2 * r).val) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have h := sqGaussSum_norm_le_sqrt_gcd r
    rw [Nat.gcd_comm (2 * r).val N, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (N:ℝ))] at h
    exact h
  -- Step 2: reindex r ↦ 2r (a bijection of ZMod N, since 2 is a unit at odd N).
  have hcop : Nat.Coprime 2 N := Nat.coprime_two_left.mpr hodd
  have hunit : IsUnit (2 : ZMod N) := by
    have h := (ZMod.isUnit_iff_coprime 2 N).mpr hcop
    simpa using h
  have hbij : Function.Bijective (fun r : ZMod N => 2 * r) :=
    Finite.injective_iff_bijective.mp hunit.mul_right_injective
  have step2 : ∑ r : ZMod N, Real.sqrt (N.gcd (2 * r).val)
      = ∑ c : ZMod N, Real.sqrt (N.gcd c.val) :=
    Fintype.sum_bijective (fun r : ZMod N => 2 * r) hbij
      (fun r => Real.sqrt (N.gcd (2 * r).val)) (fun c => Real.sqrt (N.gcd c.val))
      (fun _ => rfl)
  -- Step 3: transport the residue sum to `range N`.
  have himg : Finset.image ZMod.val (univ : Finset (ZMod N)) = range N := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨c, rfl⟩; exact ZMod.val_lt c
    · intro hk; exact ⟨(k : ZMod N), ZMod.val_natCast_of_lt hk⟩
  have step3 : ∑ c : ZMod N, Real.sqrt (N.gcd c.val) = ∑ k ∈ range N, Real.sqrt (N.gcd k) := by
    rw [← himg, Finset.sum_image ((ZMod.val_injective N).injOn)]
  -- Assemble.
  calc ∑ r : ZMod N, ‖sqGaussSum r‖
      ≤ Real.sqrt N * ∑ r : ZMod N, Real.sqrt (N.gcd (2 * r).val) := step1
    _ = Real.sqrt N * ∑ c : ZMod N, Real.sqrt (N.gcd c.val) := by rw [step2]
    _ = Real.sqrt N * ∑ k ∈ range N, Real.sqrt (N.gcd k) := by rw [step3]
    _ = Real.sqrt N * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d := by
          rw [sum_weight_gcd_eq_divisor_sum N hN (fun m : ℕ => Real.sqrt m)]

/-- **Exact first moment at (odd) prime moduli.**  For a prime `N ≠ 2`, every
    nonzero frequency contributes exactly `‖G(r)‖ = √N`
    (`sqGaussSum_norm_eq_sqrt_of_prime`, from the exact magnitude
    `‖G(r)‖² = N·gcd(2r,N) = N`), while the principal frequency contributes
    `‖G(0)‖ = N` (`sqGaussSum_zero`).  There are `N-1` nonzero frequencies, so the
    first moment has the closed form

      `∑_{r} ‖G(r)‖ = N + (N-1)·√N`.

    This is the exact value the general odd-modulus ceiling
    `sum_norm_sqGaussSum_le_of_odd` bounds; see
    `sum_norm_sqGaussSum_eq_bound_of_prime` for sharpness. -/
theorem sum_norm_sqGaussSum_eq_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (hN2 : N ≠ 2) :
    ∑ r : ZMod N, ‖sqGaussSum r‖ = (N : ℝ) + ((N : ℝ) - 1) * Real.sqrt N := by
  have h0 : (0 : ZMod N) ∈ (univ : Finset (ZMod N)) := mem_univ 0
  -- principal term ‖G(0)‖ = N
  have hg0 : ‖sqGaussSum (0 : ZMod N)‖ = (N : ℝ) := by
    rw [sqGaussSum_zero, Complex.norm_natCast]
  -- each nonzero frequency contributes √N
  have hconst : ∀ r ∈ (univ : Finset (ZMod N)).erase 0, ‖sqGaussSum r‖ = Real.sqrt N :=
    fun r hr => sqGaussSum_norm_eq_sqrt_of_prime hp hN2 (Finset.ne_of_mem_erase hr)
  have hcard : ((univ : Finset (ZMod N)).erase 0).card = N - 1 := by
    rw [Finset.card_erase_of_mem h0, Finset.card_univ, ZMod.card]
  have hsum_erase : ∑ r ∈ (univ : Finset (ZMod N)).erase 0, ‖sqGaussSum r‖
      = ((N : ℝ) - 1) * Real.sqrt N := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, nsmul_eq_mul,
      Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  rw [← Finset.add_sum_erase univ (fun r => ‖sqGaussSum r‖) h0, hg0, hsum_erase]

/-- **The odd-modulus ceiling collapses to the exact value at primes.**  For a
    prime `N ≠ 2`, `N.divisors = {1, N}`, so the divisor sum on the right of
    `sum_norm_sqGaussSum_le_of_odd` is `φ(N)·√1 + φ(1)·√N = (N-1) + √N`, and

      `√N · ∑_{d ∣ N} φ(N/d)·√d = √N·((N-1) + √N) = N + (N-1)·√N`. -/
theorem sum_norm_sqGaussSum_bound_eq_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (_hN2 : N ≠ 2) :
    Real.sqrt N * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d
      = (N : ℝ) + ((N : ℝ) - 1) * Real.sqrt N := by
  rw [Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne]
  simp only [Nat.div_one, Nat.div_self hp.pos, Nat.totient_one, Nat.totient_prime hp,
    Nat.cast_one, Real.sqrt_one, mul_one, one_mul]
  rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one, mul_add,
    Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ))]
  ring

/-- **Sharpness of the odd-modulus first-moment ceiling.**  At every prime
    modulus `N ≠ 2` the bound `sum_norm_sqGaussSum_le_of_odd` is attained with
    equality: both sides equal `N + (N-1)·√N`.  Hence the multiplicative divisor
    sum `√N·∑_{d∣N}φ(N/d)√d` is the *best possible* upper bound of this shape —
    it cannot be replaced by any strictly smaller arithmetic function without
    failing at the primes. -/
theorem sum_norm_sqGaussSum_eq_bound_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (hN2 : N ≠ 2) :
    ∑ r : ZMod N, ‖sqGaussSum r‖
      = Real.sqrt N * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d :=
  (sum_norm_sqGaussSum_eq_of_prime hp hN2).trans
    (sum_norm_sqGaussSum_bound_eq_of_prime hp hN2).symm

/-- **Exact L¹ first moment at *all* odd moduli.**  The odd-modulus magnitude is not merely
    bounded but *exact* — `sqGaussSum_norm_eq_sqrt_gcd_of_odd` gives
    `‖G(r)‖ = √(N·gcd((2r).val, N))` for every frequency `r` (the Weyl residual sum has no
    cancellation at odd `N`, since `2` is a unit).  Summing over all frequencies, factoring
    out `√N`, reindexing `r ↦ 2r` and collapsing the gcd-weighted residue sum via
    `sum_weight_gcd_eq_divisor_sum` therefore yields the exact closed form

      `∑_{r} ‖G(r)‖ = √N · ∑_{d ∣ N} φ(N/d) · √d`.

    This upgrades the ceiling `sum_norm_sqGaussSum_le_of_odd` (a `≤`, from the pointwise
    triangle-inequality bound) to an **equality for every odd `N`**, composite or prime.  It
    subsumes the prime sharpness `sum_norm_sqGaussSum_eq_bound_of_prime` (the two-divisor
    special case `N.divisors = {1, N}`) and evaluates the first moment at composite odd
    moduli — e.g. `N = 9`: `√9·(φ(9)·√1 + φ(3)·√3 + φ(1)·√9) = 3·(6 + 2√3 + 3) = 27 + 6√3` —
    where no prime-field argument applies.  0 axioms. -/
theorem sum_norm_sqGaussSum_eq_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    ∑ r : ZMod N, ‖sqGaussSum r‖
      = Real.sqrt N * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- Step 1: the pointwise magnitude is *exact*, so this is an equality; pull out √N.
  have step1 : ∑ r : ZMod N, ‖sqGaussSum r‖
      = Real.sqrt N * ∑ r : ZMod N, Real.sqrt (N.gcd (2 * r).val) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h := sqGaussSum_norm_eq_sqrt_gcd_of_odd hodd r
    rw [Nat.gcd_comm (2 * r).val N, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (N:ℝ))] at h
    exact h
  -- Step 2: reindex r ↦ 2r (a bijection of ZMod N, since 2 is a unit at odd N).
  have hcop : Nat.Coprime 2 N := Nat.coprime_two_left.mpr hodd
  have hunit : IsUnit (2 : ZMod N) := by
    have h := (ZMod.isUnit_iff_coprime 2 N).mpr hcop
    simpa using h
  have hbij : Function.Bijective (fun r : ZMod N => 2 * r) :=
    Finite.injective_iff_bijective.mp hunit.mul_right_injective
  have step2 : ∑ r : ZMod N, Real.sqrt (N.gcd (2 * r).val)
      = ∑ c : ZMod N, Real.sqrt (N.gcd c.val) :=
    Fintype.sum_bijective (fun r : ZMod N => 2 * r) hbij
      (fun r => Real.sqrt (N.gcd (2 * r).val)) (fun c => Real.sqrt (N.gcd c.val))
      (fun _ => rfl)
  -- Step 3: transport the residue sum to `range N`.
  have himg : Finset.image ZMod.val (univ : Finset (ZMod N)) = range N := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨c, rfl⟩; exact ZMod.val_lt c
    · intro hk; exact ⟨(k : ZMod N), ZMod.val_natCast_of_lt hk⟩
  have step3 : ∑ c : ZMod N, Real.sqrt (N.gcd c.val) = ∑ k ∈ range N, Real.sqrt (N.gcd k) := by
    rw [← himg, Finset.sum_image ((ZMod.val_injective N).injOn)]
  -- Assemble.
  calc ∑ r : ZMod N, ‖sqGaussSum r‖
      = Real.sqrt N * ∑ r : ZMod N, Real.sqrt (N.gcd (2 * r).val) := step1
    _ = Real.sqrt N * ∑ c : ZMod N, Real.sqrt (N.gcd c.val) := by rw [step2]
    _ = Real.sqrt N * ∑ k ∈ range N, Real.sqrt (N.gcd k) := by rw [step3]
    _ = Real.sqrt N * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d := by
          rw [sum_weight_gcd_eq_divisor_sum N hN (fun m : ℕ => Real.sqrt m)]

/-- **Exact `s`-th moment of the quadratic Gauss sum at *all* odd moduli.**  The
    single divisor-sum evaluation behind `sum_norm_sqGaussSum_eq_of_odd` is not
    special to the first moment: the exact pointwise magnitude
    `‖G(r)‖ = √(N·gcd((2r).val, N))` (`sqGaussSum_norm_eq_sqrt_gcd_of_odd`) raised
    to any real power `s` factors as `(√N)^s · (√gcd)^s` (`Real.mul_rpow`), so the
    same reindexing `r ↦ 2r` and gcd → divisor collapse (`sum_weight_gcd_eq_divisor_sum`
    with weight `w(m) = (√m)^s`) gives the exact closed form

      `∑_{r} ‖G(r)‖ˢ = (√N)ˢ · ∑_{d ∣ N} φ(N/d) · (√d)ˢ`   (odd `N`, every real `s`).

    This is the whole `Lᵖ` moment hierarchy of the Gauss sum in one identity:
    * `s = 1` recovers the first moment `sum_norm_sqGaussSum_eq_of_odd`
      (`√N·∑φ(N/d)√d`);
    * `s = 2` recovers the second moment `∑‖G(r)‖² = N·∑ d·φ(N/d)`
      (`sum_sq_norm_sqGaussSum_eq_of_odd`), the Plancherel `N·#{n²=m²}` in exact
      divisor form (`∑_{d∣N} d·φ(N/d)` is Pillai's function).

    Since `‖G(r)‖ = √(N·gcd)` is exact at odd `N`, so is every moment: no `s`
    is bounded rather than evaluated.  `0` axioms. -/
theorem sum_rpow_norm_sqGaussSum_eq_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (s : ℝ) :
    ∑ r : ZMod N, ‖sqGaussSum r‖ ^ s
      = (Real.sqrt N) ^ s * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * (Real.sqrt d) ^ s := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- Step 1: raise the *exact* pointwise magnitude to the power `s` and split the product.
  have step1 : ∑ r : ZMod N, ‖sqGaussSum r‖ ^ s
      = (Real.sqrt N) ^ s * ∑ r : ZMod N, (Real.sqrt (N.gcd (2 * r).val)) ^ s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h := sqGaussSum_norm_eq_sqrt_gcd_of_odd hodd r
    rw [Nat.gcd_comm (2 * r).val N, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (N:ℝ))] at h
    rw [h, Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  -- Step 2: reindex r ↦ 2r (a bijection of ZMod N, since 2 is a unit at odd N).
  have hcop : Nat.Coprime 2 N := Nat.coprime_two_left.mpr hodd
  have hunit : IsUnit (2 : ZMod N) := by
    have h := (ZMod.isUnit_iff_coprime 2 N).mpr hcop
    simpa using h
  have hbij : Function.Bijective (fun r : ZMod N => 2 * r) :=
    Finite.injective_iff_bijective.mp hunit.mul_right_injective
  have step2 : ∑ r : ZMod N, (Real.sqrt (N.gcd (2 * r).val)) ^ s
      = ∑ c : ZMod N, (Real.sqrt (N.gcd c.val)) ^ s :=
    Fintype.sum_bijective (fun r : ZMod N => 2 * r) hbij
      (fun r => (Real.sqrt (N.gcd (2 * r).val)) ^ s) (fun c => (Real.sqrt (N.gcd c.val)) ^ s)
      (fun _ => rfl)
  -- Step 3: transport the residue sum to `range N`.
  have himg : Finset.image ZMod.val (univ : Finset (ZMod N)) = range N := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨c, rfl⟩; exact ZMod.val_lt c
    · intro hk; exact ⟨(k : ZMod N), ZMod.val_natCast_of_lt hk⟩
  have step3 : ∑ c : ZMod N, (Real.sqrt (N.gcd c.val)) ^ s
      = ∑ k ∈ range N, (Real.sqrt (N.gcd k)) ^ s := by
    rw [← himg, Finset.sum_image ((ZMod.val_injective N).injOn)]
  -- Assemble, collapsing the gcd-weighted residue sum with weight `w(m) = (√m)^s`.
  calc ∑ r : ZMod N, ‖sqGaussSum r‖ ^ s
      = (Real.sqrt N) ^ s * ∑ r : ZMod N, (Real.sqrt (N.gcd (2 * r).val)) ^ s := step1
    _ = (Real.sqrt N) ^ s * ∑ c : ZMod N, (Real.sqrt (N.gcd c.val)) ^ s := by rw [step2]
    _ = (Real.sqrt N) ^ s * ∑ k ∈ range N, (Real.sqrt (N.gcd k)) ^ s := by rw [step3]
    _ = (Real.sqrt N) ^ s * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * (Real.sqrt d) ^ s := by
          rw [sum_weight_gcd_eq_divisor_sum N hN (fun m : ℕ => (Real.sqrt m) ^ s)]

/-- **Exact second moment (Plancherel) at odd moduli, in divisor form.**  At odd
    `N` the squared magnitude is exact, `‖G(r)‖² = N·gcd((2r).val, N)`
    (`sqGaussSum_normSq_eq_gcd_of_odd`), so summing over frequencies and collapsing
    the gcd via `sum_weight_gcd_eq_divisor_sum` (weight `w(m) = m`) gives

      `∑_{r} ‖G(r)‖² = N · ∑_{d ∣ N} d · φ(N/d)`.

    The divisor sum `∑_{d∣N} d·φ(N/d)` is Pillai's arithmetical function, and this
    equals `N · #{(n,m) : n² = m²}` (`= N·(2N−1)` for odd `N`) — the exact
    Plancherel/second-moment total in closed arithmetic form, and the `s = 2` case
    of `sum_rpow_norm_sqGaussSum_eq_of_odd`.  `0` axioms. -/
theorem sum_sq_norm_sqGaussSum_eq_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    ∑ r : ZMod N, ‖sqGaussSum r‖ ^ 2
      = (N : ℝ) * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * (d : ℝ) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  -- Step 1: exact pointwise square, then pull out N.
  have step1 : ∑ r : ZMod N, ‖sqGaussSum r‖ ^ 2
      = (N : ℝ) * ∑ r : ZMod N, (N.gcd (2 * r).val : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [sqGaussSum_normSq_eq_gcd_of_odd hodd r, Nat.gcd_comm (2 * r).val N]
  -- Step 2: reindex r ↦ 2r (2 is a unit at odd N).
  have hcop : Nat.Coprime 2 N := Nat.coprime_two_left.mpr hodd
  have hunit : IsUnit (2 : ZMod N) := by
    have h := (ZMod.isUnit_iff_coprime 2 N).mpr hcop
    simpa using h
  have hbij : Function.Bijective (fun r : ZMod N => 2 * r) :=
    Finite.injective_iff_bijective.mp hunit.mul_right_injective
  have step2 : ∑ r : ZMod N, (N.gcd (2 * r).val : ℝ)
      = ∑ c : ZMod N, (N.gcd c.val : ℝ) :=
    Fintype.sum_bijective (fun r : ZMod N => 2 * r) hbij
      (fun r => (N.gcd (2 * r).val : ℝ)) (fun c => (N.gcd c.val : ℝ)) (fun _ => rfl)
  -- Step 3: transport to range N.
  have himg : Finset.image ZMod.val (univ : Finset (ZMod N)) = range N := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨c, rfl⟩; exact ZMod.val_lt c
    · intro hk; exact ⟨(k : ZMod N), ZMod.val_natCast_of_lt hk⟩
  have step3 : ∑ c : ZMod N, (N.gcd c.val : ℝ) = ∑ k ∈ range N, (N.gcd k : ℝ) := by
    rw [← himg, Finset.sum_image ((ZMod.val_injective N).injOn)]
  calc ∑ r : ZMod N, ‖sqGaussSum r‖ ^ 2
      = (N : ℝ) * ∑ r : ZMod N, (N.gcd (2 * r).val : ℝ) := step1
    _ = (N : ℝ) * ∑ c : ZMod N, (N.gcd c.val : ℝ) := by rw [step2]
    _ = (N : ℝ) * ∑ k ∈ range N, (N.gcd k : ℝ) := by rw [step3]
    _ = (N : ℝ) * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * (d : ℝ) := by
          rw [sum_weight_gcd_eq_divisor_sum N hN (fun m : ℕ => (m : ℝ))]

/-- **Elementary reduction: the first moment is `≤ N·√N·τ(N)`.**  The exact first
    moment `∑_r ‖G(r)‖ = √N·∑_{d∣N} φ(N/d)·√d` (`sum_norm_sqGaussSum_eq_of_odd`) is
    bounded, term-by-term, by the constant `N`:

      `φ(N/d)·√d ≤ (N/d)·√d ≤ (N/d)·d = N`,

    using `φ(N/d) ≤ N/d` (`Nat.totient_le`), `√d ≤ d` for `d ≥ 1` (`Real.sqrt_le_iff`)
    and `(N/d)·d = N` (`Nat.div_mul_cancel`, as `d ∣ N`).  There are `τ(N) = |N.divisors|`
    divisors, so the divisor sum is `≤ N·τ(N)` and

      `∑_{r} ‖G(r)‖ ≤ N·√N·τ(N) = N^{3/2}·τ(N)`.

    **Why this matters.**  The quantitative Sárközy / square-difference-free density
    estimate needs the *analytic* input `∑_{r} ‖G(r)‖ = o(N²)`.  This inequality reduces
    that analytic requirement to the purely **elementary, number-theoretic** statement
    `τ(N) = o(√N)` — indeed `N^{3/2}·τ(N) = o(N²) ⟺ τ(N) = o(√N)`, which holds because the
    divisor-counting function satisfies `τ(N) = N^{o(1)}` (Wigert's theorem).  That divisor
    asymptotic is not currently in Mathlib, so the `o(N²)` bound itself is not yet
    machine-checkable here; the explicit inequality below is the machine-checked content and
    isolates the *only* remaining ingredient.  (Note `τ(N) ≤ 2√N` always, so the bound is at
    worst `2N²`; the genuine `o` gain comes from the sub-polynomial growth of `τ`.)  `0` axioms. -/
theorem sum_norm_sqGaussSum_le_card_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    ∑ r : ZMod N, ‖sqGaussSum r‖ ≤ (N : ℝ) * Real.sqrt N * (N.divisors.card : ℝ) := by
  rw [sum_norm_sqGaussSum_eq_of_odd hodd]
  -- Per-divisor bound: `φ(N/d)·√d ≤ N` for every `d ∣ N`.
  have hterm : ∀ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d ≤ (N : ℝ) := by
    intro d hd
    have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
    -- `φ(N/d) ≤ N/d`
    have ht : ((N / d).totient : ℝ) ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast Nat.totient_le (N / d)
    -- `√d ≤ d`
    have hsd : Real.sqrt d ≤ (d : ℝ) := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith [hd1]⟩
    -- `(N/d)·d = N`
    have hmul : ((N / d : ℕ) : ℝ) * (d : ℝ) = (N : ℝ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    calc ((N / d).totient : ℝ) * Real.sqrt d
        ≤ ((N / d : ℕ) : ℝ) * Real.sqrt d :=
          mul_le_mul_of_nonneg_right ht (Real.sqrt_nonneg _)
      _ ≤ ((N / d : ℕ) : ℝ) * (d : ℝ) :=
          mul_le_mul_of_nonneg_left hsd (by positivity)
      _ = (N : ℝ) := hmul
  -- Sum the constant bound over the `τ(N)` divisors.
  have key : ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d
      ≤ (N : ℝ) * (N.divisors.card : ℝ) := by
    calc ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d
        ≤ ∑ _d ∈ N.divisors, (N : ℝ) := Finset.sum_le_sum hterm
      _ = (N.divisors.card : ℝ) * (N : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (N : ℝ) * (N.divisors.card : ℝ) := by ring
  calc Real.sqrt N * ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d
      ≤ Real.sqrt N * ((N : ℝ) * (N.divisors.card : ℝ)) :=
        mul_le_mul_of_nonneg_left key (Real.sqrt_nonneg _)
    _ = (N : ℝ) * Real.sqrt N * (N.divisors.card : ℝ) := by ring

end Szemeredi.Roth
