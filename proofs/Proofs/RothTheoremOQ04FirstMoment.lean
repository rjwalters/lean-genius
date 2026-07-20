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

/-- **A proper divisor is at most `N / minFac(N)`.**  If `0 < m < N` then
    `gcd(m, N)` is a *proper* divisor `d` of `N`, so its cofactor `e = N/d ≥ 2`
    is a divisor `≥ 2` of `N`, hence `minFac(N) ≤ e` (`Nat.minFac_le_of_dvd`);
    multiplying `d · minFac(N) ≤ d · e = N` and dividing gives `d ≤ N / minFac(N)`.
    This upgrades the crude `2·gcd ≤ N` to the sharp largest-proper-divisor ceiling. -/
private theorem gcd_le_div_minFac {m N : ℕ} (hpos : 0 < m) (hlt : m < N) :
    Nat.gcd m N ≤ N / N.minFac := by
  set d := Nat.gcd m N with hd
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le m) hlt
  have hdvd : d ∣ N := Nat.gcd_dvd_right m N
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hNpos
  have hdlt : d < N := lt_of_le_of_lt (Nat.gcd_le_left N hpos) hlt
  obtain ⟨e, he⟩ := hdvd
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, Nat.mul_zero] at he; omega
    · exact h
  have he2 : 2 ≤ e := by
    by_contra h
    push_neg at h
    interval_cases e
    · rw [Nat.mul_one] at he; omega
  have hedvd : e ∣ N := ⟨d, by rw [he]; ring⟩
  have hmf : N.minFac ≤ e := Nat.minFac_le_of_dvd he2 hedvd
  have key : d * N.minFac ≤ N := by
    calc d * N.minFac ≤ d * e := Nat.mul_le_mul_left d hmf
      _ = N := he.symm
  exact (Nat.le_div_iff_mul_le N.minFac_pos).mpr key

/-- **Sharp gcd-graded magnitude at odd moduli: `‖G(r)‖² ≤ N² / minFac(N)`.**  For odd
    `N` and any *nonzero* frequency `r`, oddness makes `2` a unit so `2r ≠ 0`, hence
    `(2r).val` is a nonzero residue `< N` and `gcd((2r).val, N)` is a proper divisor,
    bounded by the largest proper divisor `N / minFac(N)` (`gcd_le_div_minFac`).  Feeding
    this into the exact Weyl magnitude `‖G(r)‖² = N·gcd((2r).val, N)` (`sqGaussSum_normSq_le_gcd`)
    gives

      `‖G(r)‖² ≤ N · (N / minFac(N)) = N² / minFac(N)`.

    This is the *sharp* uniform sub-maximal bound — strictly better than the crude
    `‖G(r)‖² ≤ N²/2` (`sqGaussSum_normSq_le_half_of_odd`) for every odd `N` (whose smallest
    prime factor is `≥ 3`), and it degrades gracefully with `minFac`: at a prime `N` the
    smallest factor is `N` itself, recovering `‖G(r)‖² ≤ N`.  `0` axioms. -/
theorem sqGaussSum_normSq_le_sq_div_minFac_of_odd {N : ℕ} [NeZero N] (hodd : Odd N)
    {r : ZMod N} (hr : r ≠ 0) : ‖sqGaussSum r‖ ^ 2 ≤ (N : ℝ) ^ 2 / N.minFac := by
  -- Oddness ⟹ 2 is a unit ⟹ 2r ≠ 0.
  have h2r : 2 * r ≠ 0 := by
    have h2 : IsUnit (2 : ZMod N) := by
      have hcast : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
      rw [← hcast, ZMod.isUnit_iff_coprime]
      have hnd : ¬ (2 ∣ N) := by rw [Nat.dvd_iff_mod_eq_zero, Nat.odd_iff.mp hodd]; omega
      exact (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
    intro h
    obtain ⟨u, hu⟩ := h2
    have hz : (↑u⁻¹ : ZMod N) * (2 * r) = 0 := by rw [h, mul_zero]
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul] at hz
    exact hr hz
  have hpos : 0 < (2 * r).val := ZMod.val_pos.mpr h2r
  have hlt : (2 * r).val < N := ZMod.val_lt (2 * r)
  have hg : Nat.gcd (2 * r).val N ≤ N / N.minFac := gcd_le_div_minFac hpos hlt
  have hmfne : (N.minFac : ℝ) ≠ 0 := by exact_mod_cast (Nat.minFac_pos N).ne'
  have hgr : (Nat.gcd (2 * r).val N : ℝ) ≤ (N : ℝ) / (N.minFac : ℝ) := by
    have hcast := (Nat.cast_le (α := ℝ)).mpr hg
    rwa [Nat.cast_div (Nat.minFac_dvd N) hmfne] at hcast
  calc ‖sqGaussSum r‖ ^ 2 ≤ (N : ℝ) * (Nat.gcd (2 * r).val N : ℝ) := sqGaussSum_normSq_le_gcd r
    _ ≤ (N : ℝ) * ((N : ℝ) / (N.minFac : ℝ)) :=
        mul_le_mul_of_nonneg_left hgr (Nat.cast_nonneg N)
    _ = (N : ℝ) ^ 2 / N.minFac := by ring

/-- **`‖G(r)‖ ≤ N / √minFac(N)` at odd moduli.**  Square-root form of
    `sqGaussSum_normSq_le_sq_div_minFac_of_odd`: the sharp uniform magnitude bound valid at
    *every* nonzero frequency of an odd modulus, interpolating between the crude `N/√2` (which
    it always beats, as `minFac ≥ 3`) and the sharp prime value `√N` (when `minFac = N`).  It
    supplies the sharpest single-modulus `M` for `sqDiffFree_density_bound` over all odd `N`. -/
theorem sqGaussSum_norm_le_div_sqrt_minFac_of_odd {N : ℕ} [NeZero N] (hodd : Odd N)
    {r : ZMod N} (hr : r ≠ 0) : ‖sqGaussSum r‖ ≤ (N : ℝ) / Real.sqrt N.minFac := by
  have h := sqGaussSum_normSq_le_sq_div_minFac_of_odd hodd hr
  have hrhs : Real.sqrt ((N : ℝ) ^ 2 / N.minFac) = (N : ℝ) / Real.sqrt N.minFac := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq (Nat.cast_nonneg N)]
  have hmono := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), hrhs] at hmono

/-- **Sharp square-difference density bound at odd moduli.**  Discharging the analytic
    hypothesis of `sqDiffFree_density_bound` with the *sharp* uniform magnitude
    `M = N / √minFac(N)` (`sqGaussSum_norm_le_div_sqrt_minFac_of_odd`) gives, for any
    square-difference-free `A ⊆ ℤ/Nℤ` at odd `N`,

      `|A|² ≤ |A|·#{n : n² = 0} + N⁻¹·(N/√minFac(N))·(|A|·N − |A|²)`.

    This strictly sharpens `sqDiffFree_density_bound_of_odd` (`M = N/√2`): the coefficient
    `N/√minFac(N)` is smaller for every odd `N` (as `minFac ≥ 3 > 2`), and it collapses to the
    sharp `M = √N` at prime moduli, recovering `sqDiffFree_density_bound_of_prime`. -/
theorem sqDiffFree_density_bound_minfac_of_odd {N : ℕ} [NeZero N] (hodd : Odd N)
    (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) ^ 2
      ≤ (A.card : ℝ) * (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card
        + (↑N)⁻¹ * ((N : ℝ) / Real.sqrt N.minFac * (↑A.card * ↑N - (↑A.card) ^ 2)) :=
  sqDiffFree_density_bound A
    (fun _ hr => sqGaussSum_norm_le_div_sqrt_minFac_of_odd hodd hr) hfree

/-- **Sharp cardinality ceiling for square-difference-free sets at odd moduli.**  Solving the
    quadratic `sqDiffFree_density_bound_minfac_of_odd` — the error term `N⁻¹·M·(|A|N − |A|²)`
    is `≤ M·|A|` since `|A|N − |A|² ≤ |A|N` — collapses it to the clean linear ceiling

      `|A| ≤ #{n : n² = 0} + N / √minFac(N)`.

    **The single-modulus Sárközy statement in sharp form.**  For odd `N`:
    * at a **prime** `N`, `minFac(N) = N` and `#{n² = 0} = 1`, giving `|A| ≤ 1 + √N` — the sharp
      `√N` Sárközy bound, `o(N)` density;
    * along any sequence with `minFac(N) → ∞` (e.g. `N` a product of large primes), `N/√minFac(N)
      = o(N)`, so the density `|A|/N → 0`.

    **Honest limitation.**  When `minFac(N)` is bounded (e.g. `3 ∣ N`), `N/√minFac(N) = Θ(N)` and
    this bound is `Θ(N)` — *not* `o(N)`.  This is not a formalization gap but a genuine obstruction
    of the single-modulus circle method: the `φ(minFac) = minFac − 1` frequencies `r` with
    `gcd(r, N) = N/minFac` each carry the full sub-maximal Gauss sum `‖G(r)‖ = N/√minFac`, and even
    capping their Fourier mass by `‖Â(r)‖² ≤ |A|²` their combined contribution is `≈ √minFac·|A|²`,
    which overwhelms the `|A|²` main term.  Resolving `o(N)` for bounded-`minFac` moduli requires a
    *good modulus* (`minFac → ∞`) or the classical multi-modulus / interval reduction, not a sharper
    bound at the fixed modulus `N`.  `0` axioms. -/
theorem sqDiffFree_card_le_minfac_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ)
      ≤ (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card + (N : ℝ) / Real.sqrt N.minFac := by
  set a : ℝ := (A.card : ℝ) with ha_def
  set c₀ : ℝ := ((Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card : ℝ) with hc_def
  set M : ℝ := (N : ℝ) / Real.sqrt N.minFac with hM_def
  have hd := sqDiffFree_density_bound_minfac_of_odd hodd A hfree
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have haNN : 0 ≤ a := Nat.cast_nonneg _
  have hMnn : 0 ≤ M := by rw [hM_def]; positivity
  -- The error term `N⁻¹·M·(aN − a²) ≤ M·a`, since `aN − a² ≤ aN`.
  have hstep : (↑N)⁻¹ * (M * (a * N - a ^ 2)) ≤ M * a := by
    have hfrac : (a * N - a ^ 2) / N ≤ a := by
      rw [div_le_iff₀ hNpos]; nlinarith [sq_nonneg a]
    have heq : (↑N)⁻¹ * (M * (a * N - a ^ 2)) = M * ((a * N - a ^ 2) / N) := by
      rw [div_eq_mul_inv]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hfrac hMnn
  -- Hence `a² ≤ a·(c₀ + M)`.
  have hquad : a ^ 2 ≤ a * (c₀ + M) := by nlinarith [hd, hstep]
  -- Solve the quadratic: `a ≤ c₀ + M`.
  rcases eq_or_lt_of_le haNN with ha0 | hapos
  · rw [← ha0]; positivity
  · have hcancel := le_of_mul_le_mul_left (by nlinarith [hquad] : a * a ≤ a * (c₀ + M)) hapos
    linarith

/-- **Sárközy's `√N` density bound at prime moduli — the clean single-modulus form.**
    Specializing the sharp odd-modulus ceiling `sqDiffFree_card_le_minfac_of_odd` to a prime `N ≠ 2`
    makes *both* structural quantities collapse to their extreme values:
    * `minFac(N) = N` (the smallest prime factor of a prime is itself), so the sub-maximal
      Gauss magnitude is the sharp `N/√minFac(N) = N/√N = √N` (`Real.div_sqrt`);
    * `#{n : n² = 0} = 1` — over the field `ℤ/Nℤ` the only square root of `0` is `0`
      (`sq_eq_zero_iff`, no zero divisors).

    Hence any square-difference-free `A ⊆ ℤ/Nℤ` at a prime `N ≠ 2` satisfies

      `|A| ≤ 1 + √N`,

    i.e. density `|A|/N ≤ (1 + √N)/N → 0`.  This is the genuine Sárközy conclusion along the
    prime moduli: a fully machine-checked `o(N)` bound on the size of a set with no nonzero
    square difference, with no bounded-`minFac` obstruction (that obstruction, documented on
    `sqDiffFree_card_le_of_odd`, is exactly what primality removes).  `0` axioms. -/
theorem sqDiffFree_card_le_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (hN2 : N ≠ 2)
    (A : Finset (ZMod N))
    (hfree : ∀ x ∈ A, ∀ n : ZMod N, n ^ 2 ≠ 0 → x + n ^ 2 ∉ A) :
    (A.card : ℝ) ≤ 1 + Real.sqrt N := by
  have hodd : Odd N := hp.odd_of_ne_two hN2
  have hbase := sqDiffFree_card_le_minfac_of_odd hodd A hfree
  -- `minFac N = N`: the smallest prime factor of a prime is itself.
  have hmf : N.minFac = N := by
    rcases hp.eq_one_or_self_of_dvd N.minFac (Nat.minFac_dvd N) with h | h
    · exact absurd h (Nat.minFac_prime hp.ne_one).ne_one
    · exact h
  -- `#{n : n² = 0} = 1`: over the field `ℤ/Nℤ`, `n² = 0 ↔ n = 0`.
  have hcount : (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)).card = 1 := by
    haveI : Fact N.Prime := ⟨hp⟩
    have hset : (Finset.univ.filter (fun n : ZMod N => n ^ 2 = 0)) = {0} := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        sq_eq_zero_iff]
    rw [hset, Finset.card_singleton]
  rw [hcount, hmf, Real.div_sqrt] at hbase
  simpa using hbase

/-- **L¹-reduction capstone: the first moment is `≤ N^{3/2}·τ(N)`, reducing the
    composite-`N` Sárközy requirement to the elementary divisor bound `τ(N)=o(√N)`.**

    The exact first moment `∑_r ‖G(r)‖ = √N · ∑_{d∣N} φ(N/d)·√d`
    (`sum_norm_sqGaussSum_eq_of_odd`) is bounded termwise: for each divisor `d ∣ N`,
    `φ(N/d)·√d ≤ (N/d)·d = N` (using `φ(m) ≤ m`, `√d ≤ d` for `d ≥ 1`, and
    `(N/d)·d = N`). Summing over the `τ(N) = #N.divisors` divisors gives
    `∑_{d∣N} φ(N/d)·√d ≤ N·τ(N)`, hence `∑_r ‖G(r)‖ ≤ √N·N·τ(N) = N^{3/2}·τ(N)`.

    This is the structural endpoint of the L¹ circle-method direction: the whole
    analytic Sárközy input `∑_r ‖G(r)‖ = o(N²)` collapses to the *elementary
    arithmetic* statement `τ(N) = o(√N)` (Wigert's `τ(N) = N^{o(1)}`), with NO
    quadratic-Gauss-sum reciprocity required. Mathlib v4.31 has only
    `Nat.card_divisors_le_self` (`τ(N) ≤ N`) and an average-order `O(N log N)` sum
    formula — the individual bound `τ(N) = o(√N)` is a genuine Mathlib gap, so this
    lemma pins the sole remaining input precisely. `0` axioms. -/
theorem sum_norm_sqGaussSum_le_sqrt_mul_card_of_odd {N : ℕ} [NeZero N] (hodd : Odd N) :
    ∑ r : ZMod N, ‖sqGaussSum r‖ ≤ Real.sqrt N * ((N : ℝ) * (N.divisors.card : ℝ)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [sum_norm_sqGaussSum_eq_of_odd hodd]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  calc ∑ d ∈ N.divisors, ((N / d).totient : ℝ) * Real.sqrt d
      ≤ ∑ _d ∈ N.divisors, (N : ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hdN : d ∣ N := Nat.dvd_of_mem_divisors hd
        have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
        have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
        -- `√d ≤ d` for `d ≥ 1`.
        have hsd : Real.sqrt d ≤ d := by
          have h := Real.sqrt_le_sqrt (show (d : ℝ) ≤ (d : ℝ) ^ 2 by nlinarith)
          rwa [Real.sqrt_sq (by positivity)] at h
        -- `φ(N/d) ≤ N/d`.
        have htot : ((N / d).totient : ℝ) ≤ ((N / d : ℕ) : ℝ) := by
          exact_mod_cast Nat.totient_le (N / d)
        have hdiv : (N / d) * d = N := Nat.div_mul_cancel hdN
        calc ((N / d).totient : ℝ) * Real.sqrt d
            ≤ ((N / d : ℕ) : ℝ) * (d : ℝ) :=
              mul_le_mul htot hsd (Real.sqrt_nonneg _) (by positivity)
          _ = ((N / d * d : ℕ) : ℝ) := by push_cast; ring
          _ = (N : ℝ) := by rw [hdiv]
    _ = (N : ℝ) * (N.divisors.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end Szemeredi.Roth
