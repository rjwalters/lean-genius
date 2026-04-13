import Mathlib
import Proofs.KummerTheoremOQ01

/-!
# Kummer's Theorem for Multinomial Coefficients (OQ-01-OQ-01)

## Open Question

Can the p-adic valuation formula
  v_p(C(n; k₁,...,kₘ)) = total carries when adding k₁,...,kₘ in base p
be formally derived in Lean from:
1. **Binomial decomposition** (from OQ-01): `multinomial ks = ∏ C(acc+k, k)` over the scanl pairs
2. **Kummer's theorem** (Mathlib): `(C(n+k,k)).factorization p = #{carries when adding k and n in base p}`

## Answer: YES

The derivation is:
```
v_p(multinomial ks)
  = v_p(∏ C(acc+k, k))           [binomial decomposition, from OQ-01]
  = ∑ v_p(C(acc+k, k))           [factorization distributes over products]
  = ∑ #{carries at step (acc,k)} [Kummer, Nat.factorization_choose']
  = total carries                 [by definition]
```

The comment at the end of KummerTheoremOQ01.lean stating
"Full formalization requires base-p carry counting (not yet in Mathlib)"
is **outdated**: Mathlib 4.26.0 contains `Nat.factorization_choose'` in
`Mathlib.Data.Nat.Choose.Factorization`, which is precisely the carries
statement of Kummer's theorem.

## Summary Statistics

- Sorries: 0
- Axioms: 0
- Key Mathlib theorems:
  - `KummerMultinomial.multinomial_eq_prod_choose` (from OQ-01)
  - `Nat.factorization_mul` (factorization over products)
  - `Nat.factorization_choose'` (Kummer's theorem: factorization = carries)
  - `Nat.log_mono_right` (monotonicity of Nat.log)
-/

namespace KummerMultinomial

open Nat Finset

-- ============================================================================
-- Part I: Factorization Distributes Over List Products
-- ============================================================================

/-- The p-adic valuation of a product of nonzero naturals equals the sum
    of the individual p-adic valuations. -/
private lemma factorization_list_prod (l : List ℕ) (hl : ∀ x ∈ l, x ≠ 0) (p : ℕ) :
    l.prod.factorization p = (l.map (·.factorization p)).sum := by
  induction l with
  | nil => simp
  | cons n rest ih =>
    have hn : n ≠ 0 := hl n (List.mem_cons_self n rest)
    have hrest : rest.prod ≠ 0 :=
      List.prod_ne_zero (fun x hx => hl x (List.mem_cons_of_mem n hx))
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    rw [Nat.factorization_mul hn hrest, Finsupp.add_apply]
    congr 1
    exact ih (fun x hx => hl x (List.mem_cons_of_mem n hx))

-- ============================================================================
-- Part II: Partial Sum Bounds for Scanl Pairs
-- ============================================================================

/-- Every pair (acc, k) in `(scanl (·+·) init ks).zip ks` satisfies
    `acc + k ≤ init + ks.sum`. -/
private lemma scanl_zip_sum_le (ks : List ℕ) (init : ℕ) :
    ∀ pair ∈ (ks.scanl (· + ·) init).zip ks,
      pair.1 + pair.2 ≤ init + ks.sum := by
  induction ks generalizing init with
  | nil => simp
  | cons k rest ih =>
    simp only [List.scanl_cons, List.zip_cons_cons, List.mem_cons, List.sum_cons,
               Prod.mk.injEq]
    rintro ⟨a, b⟩ (⟨rfl, rfl⟩ | hmem)
    · omega
    · have h := ih (init + k) ⟨a, b⟩ hmem
      omega

/-- Every pair (acc, k) in the tail of `(scanl (·+·) 0 ks).zip ks` satisfies
    `acc + k ≤ ks.sum`. -/
private lemma scanl_zip_tail_sum_le (ks : List ℕ) :
    ∀ pair ∈ ((ks.scanl (· + ·) 0).zip ks).tail, pair.1 + pair.2 ≤ ks.sum := by
  cases ks with
  | nil => simp
  | cons k rest =>
    simp only [List.scanl_cons, Nat.zero_add, List.zip_cons_cons, List.tail_cons,
               List.sum_cons]
    intro pair hmem
    exact scanl_zip_sum_le rest k pair hmem

-- ============================================================================
-- Part III: The p-adic Valuation of Multinomial = Sum of Binomial Valuations
-- ============================================================================

/-- **Bridge theorem**: The p-adic valuation of `multinomial ks` equals the sum of
    the p-adic valuations of the binomial factors `C(acc+k, k)` at each scanl step.

    This is the key algebraic step: it combines the binomial decomposition from OQ-01
    with the fact that p-adic valuations distribute over products. -/
theorem multinomial_factorization_is_sum_of_binomial_factorizations
    (ks : List ℕ) (p : ℕ) :
    (multinomial ks).factorization p =
    (((ks.scanl (· + ·) 0).zip ks).tail.map
      (fun pair => (Nat.choose (pair.1 + pair.2) pair.2).factorization p)).sum := by
  -- Establish that all binomial factors are nonzero
  have hl : ∀ x ∈ (((ks.scanl (· + ·) 0).zip ks).tail.map
      (fun ⟨acc, k⟩ => Nat.choose (acc + k) k)), x ≠ 0 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨⟨acc, k⟩, _, rfl⟩ := hx
    exact (Nat.choose_pos (Nat.le_add_left k acc)).ne'
  -- Rewrite multinomial as product of binomials, then distribute factorization
  rw [multinomial_eq_prod_choose, factorization_list_prod _ hl, List.map_map]
  simp [Function.comp]

-- ============================================================================
-- Part IV: Kummer's Theorem for Multinomials
-- ============================================================================

/-- **Multinomial Kummer Theorem** (general form with bound hypothesis):

    The p-adic valuation of `multinomial ks` equals the total number of carries
    when successively adding the elements of `ks` in base `p`.

    At each step, adding `acc` and `k` produces carries counted by
    `{i ∈ Ico 1 b | p^i ≤ k mod p^i + acc mod p^i}`,
    matching Mathlib's `Nat.factorization_choose'`.

    The hypothesis `hb` ensures `b` is large enough for each step. -/
theorem multinomial_kummer (ks : List ℕ) (p b : ℕ) (hp : p.Prime)
    (hb : ∀ pair ∈ ((ks.scanl (· + ·) 0).zip ks).tail,
          Nat.log p (pair.1 + pair.2) < b) :
    (multinomial ks).factorization p =
    (((ks.scanl (· + ·) 0).zip ks).tail.map
      (fun pair =>
        ((Finset.Ico 1 b).filter
          (fun i => p ^ i ≤ pair.2 % p ^ i + pair.1 % p ^ i)).card)).sum := by
  rw [multinomial_factorization_is_sum_of_binomial_factorizations]
  congr 1
  apply List.map_congr_left
  intro pair hmem
  exact Nat.factorization_choose' hp (hb pair hmem)

/-- **Multinomial Kummer Theorem** (concrete form):

    Uses `b = Nat.log p ks.sum + 1`, which is always valid because every
    partial sum `acc + k` (for pairs in the scanl decomposition) satisfies
    `acc + k ≤ ks.sum`, giving `log p (acc + k) ≤ log p ks.sum < b`. -/
theorem multinomial_kummer_concrete (ks : List ℕ) (p : ℕ) (hp : p.Prime) :
    (multinomial ks).factorization p =
    (((ks.scanl (· + ·) 0).zip ks).tail.map
      (fun pair =>
        ((Finset.Ico 1 (Nat.log p ks.sum + 1)).filter
          (fun i => p ^ i ≤ pair.2 % p ^ i + pair.1 % p ^ i)).card)).sum :=
  multinomial_kummer ks p _ hp (fun pair hmem =>
    Nat.lt_succ_of_le (Nat.log_mono_right (scanl_zip_tail_sum_le ks pair hmem)))

-- ============================================================================
-- Part V: Concrete Verifications
-- ============================================================================

/-- φ_2(C(6; 1,2,3)) = 2. Multinomial(1,2,3) = 60, v_2(60) = 2.
    In base 2: adding 1 and 2 gives carry at position 1 (since 2^1 ≤ 2%2 + 1%2? No: 0+1=1<2).
    Actually: carry at i iff p^i ≤ k%p^i + acc%p^i. For step (1,2): 2 ≤ 2%2 + 1%2 = 0+1? No.
    For step (3,3): 2 ≤ 3%2 + 3%2 = 1+1 = 2 ≤ 2 ✓ (i=1), and 4 ≤ 3%4 + 3%4 = 3+3=6 ✓ (i=2).
    Total: 2 carries. v_2(60) = 2. ✓ -/
theorem multinomial_123_p2 :
    (multinomial [1, 2, 3]).factorization 2 = 2 := by native_decide

/-- The carries formula matches for [1,2,3] at p=2. -/
theorem multinomial_123_kummer_check :
    (multinomial [1, 2, 3]).factorization 2 =
    ((([1, 2, 3].scanl (· + ·) 0).zip [1, 2, 3]).tail.map
      (fun pair =>
        ((Finset.Ico 1 4).filter
          (fun i => 2 ^ i ≤ pair.2 % 2 ^ i + pair.1 % 2 ^ i)).card)).sum := by
  decide

/-- v_3(C(6; 1,2,3)) = 1. v_3(60) = 1.
    In base 3: step (1,2): 3 ≤ 2%3 + 1%3 = 2+1 = 3 ≤ 3 ✓ (i=1). One carry. ✓ -/
theorem multinomial_123_p3 :
    (multinomial [1, 2, 3]).factorization 3 = 1 := by native_decide

/-- Sanity check: multinomial [1,2,3] = 60. -/
theorem multinomial_123_value : multinomial [1, 2, 3] = 60 := by native_decide

-- ============================================================================
-- Summary Check
-- ============================================================================

#check @multinomial_factorization_is_sum_of_binomial_factorizations
#check @multinomial_kummer
#check @multinomial_kummer_concrete

end KummerMultinomial
