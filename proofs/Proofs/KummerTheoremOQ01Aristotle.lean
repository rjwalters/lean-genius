/-
  Aristotle targets for KummerTheoremOQ01 — multinomial coefficient decomposition.
  See KummerTheoremOQ01.lean for the main formalization.

  Primary target: `multinomial_eq_prod_choose` — the general binomial factorization
  identity showing multinomial ks = product of C(partial_sum + k, k) over all k.

  Proof strategy (backward list induction via List.reverseRecOn):

  Step 1: `factorial_dvd`
    (ks.map Nat.factorial).prod ∣ ks.sum.factorial
    Induction: k! * prod ∣ k! * sum! ∣ (k+sum)!

  Step 2: `multinomial_mul_factorial`
    multinomial ks * prod_factorial = sum_factorial
    Follows from Nat.div_mul_cancel + factorial_dvd.

  Step 3: `multinomial_append_singleton`
    multinomial (ks ++ [k]) = multinomial ks * C(sum(ks) + k, k)
    Both sides * prod_factorial * k! = (sum+k)! by the key identity.

  Step 4: `zip_scanl_append_singleton`
    zip (scanl 0 (ks ++ [k])) (ks ++ [k]) = zip (scanl 0 ks) ks ++ [(ks.sum, k)]
    The last pair is (ks.sum, k), giving factor C(ks.sum + k, k) in the product.
    Proof: scanl_append_singleton + zip_append (with |scanl ks| = |ks ++ [k]| = |ks|+1).

  Step 5: `rhs_append_singleton`
    The RHS scanl/zip/tail/prod picks up factor C(ks.sum + k, k) on appending [k].

  Step 6: `multinomial_eq_prod_choose`
    By List.reverseRecOn: base trivial; step uses steps 3 + 5 + IH.

  Key Mathlib lemmas:
  - Nat.factorial_mul_factorial_dvd_factorial_add : i! * j! ∣ (i+j)!
  - Nat.choose_mul_factorial_mul_factorial : C(n,k) * k! * (n-k)! = n!
  - List.zip_append : zip (l₁++r₁) (l₂++r₂) = zip l₁ l₂ ++ zip r₁ r₂ (|l₁| = |l₂|)
  - List.scanl_cons : scanl f b (a :: l) = [b] ++ scanl f (f b a) l
  - List.length_scanl : (scanl f b l).length = l.length + 1
-/
import Mathlib

namespace KummerMultinomialAristotle

open Nat List

/-- The multinomial coefficient n! / (k₁! · k₂! · ... · kₘ!) -/
noncomputable def multinomial (ks : List ℕ) : ℕ :=
  (ks.sum).factorial / (ks.map Nat.factorial).prod

/-- Product of factorials is always positive. -/
theorem prod_factorial_pos (ks : List ℕ) : 0 < (ks.map Nat.factorial).prod := by
  apply List.prod_pos
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨n, -, rfl⟩ := hx
  exact Nat.factorial_pos n

/-- The product of factorials divides the factorial of the sum.
    Induction: k! * prod(ks) ∣ k! * sum(ks)! ∣ (k + sum(ks))!. -/
theorem factorial_dvd (ks : List ℕ) :
    (ks.map Nat.factorial).prod ∣ ks.sum.factorial := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact (mul_dvd_mul_left k.factorial ih).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add k ks.sum)

/-- The multinomial coefficient is an integer: multinomial ks * prod_factorial = sum_factorial. -/
theorem multinomial_mul_factorial (ks : List ℕ) :
    multinomial ks * (ks.map Nat.factorial).prod = ks.sum.factorial := by
  simp only [multinomial]
  exact Nat.div_mul_cancel (factorial_dvd ks)

/-- Appending a singleton multiplies the multinomial by C(sum + k, k).
    Both sides times the denominator equal (sum + k)!. -/
theorem multinomial_append_singleton (ks : List ℕ) (k : ℕ) :
    multinomial (ks ++ [k]) = multinomial ks * Nat.choose (ks.sum + k) k := by
  have hprod : 0 < (ks.map Nat.factorial).prod * k.factorial :=
    Nat.mul_pos (prod_factorial_pos ks) (Nat.factorial_pos k)
  apply Nat.eq_of_mul_eq_mul_right hprod
  -- LHS * denom: use multinomial_mul_factorial on ks ++ [k]
  have lhs_eq : multinomial (ks ++ [k]) * ((ks.map Nat.factorial).prod * k.factorial) =
      (ks.sum + k).factorial := by
    have h := multinomial_mul_factorial (ks ++ [k])
    simp only [List.sum_append, List.sum_singleton, List.map_append, List.map_singleton,
               List.prod_append, List.prod_singleton, Nat.add_zero] at h
    linarith
  -- RHS * denom: C(sum+k,k) * k! * sum! = (sum+k)!  via choose_mul_factorial_mul_factorial
  have rhs_eq : multinomial ks * Nat.choose (ks.sum + k) k *
      ((ks.map Nat.factorial).prod * k.factorial) = (ks.sum + k).factorial := by
    have hchoose := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k ks.sum)
    simp only [Nat.add_sub_cancel] at hchoose
    -- hchoose : (ks.sum + k).choose k * k! * ks.sum! = (ks.sum + k)!
    calc multinomial ks * Nat.choose (ks.sum + k) k *
            ((ks.map Nat.factorial).prod * k.factorial)
        = Nat.choose (ks.sum + k) k * k.factorial *
            (multinomial ks * (ks.map Nat.factorial).prod) := by ring
      _ = Nat.choose (ks.sum + k) k * k.factorial * ks.sum.factorial := by
            rw [multinomial_mul_factorial]
      _ = (ks.sum + k).factorial := hchoose
  linarith

/-- foldl (·+·) b ks = b + ks.sum.
    Used to identify the accumulator at the end of scanl. -/
theorem foldl_add_eq (b : ℕ) (ks : List ℕ) : List.foldl (· + ·) b ks = b + ks.sum := by
  induction ks generalizing b with
  | nil => simp
  | cons k ks ih =>
    simp only [List.foldl_cons, List.sum_cons, ih]
    omega

/-- The general scanl append singleton lemma (with arbitrary initial accumulator).
    scanl (·+·) acc (ks ++ [k]) = scanl (·+·) acc ks ++ [acc + ks.sum + k] -/
theorem scanl_add_append (acc : ℕ) (ks : List ℕ) (k : ℕ) :
    (ks ++ [k]).scanl (· + ·) acc =
    ks.scanl (· + ·) acc ++ [acc + ks.sum + k] := by
  induction ks generalizing acc with
  | nil => simp
  | cons h t ih =>
    simp only [List.cons_append, List.scanl_cons, List.sum_cons]
    congr 1
    rw [ih (acc + h), show acc + h + t.sum + k = acc + (h + t.sum) + k from by omega]

/-- Generalized version of zip_scanl_append_singleton with arbitrary initial accumulator.
    By induction: cons case uses zip_cons_cons, then IH at (acc + h), then omega. -/
private theorem zip_scanl_append_singleton_gen (acc : ℕ) (ks : List ℕ) (k : ℕ) :
    ((ks ++ [k]).scanl (· + ·) acc).zip (ks ++ [k]) =
    (ks.scanl (· + ·) acc).zip ks ++ [(acc + ks.sum, k)] := by
  induction ks generalizing acc with
  | nil => simp
  | cons h t ih =>
    simp only [List.cons_append, List.scanl_cons, List.sum_cons, List.zip_cons_cons]
    congr 1
    rw [ih (acc + h), show acc + h + t.sum = acc + (h + t.sum) from by omega]

/-- The zip of (scanl 0 (ks ++ [k])) with (ks ++ [k]) decomposes as:
    zip (scanl 0 ks) ks ++ [(ks.sum, k)].
    Proved by specializing the generalized accumulator version at acc = 0. -/
theorem zip_scanl_append_singleton (ks : List ℕ) (k : ℕ) :
    ((ks ++ [k]).scanl (· + ·) (0 : ℕ)).zip (ks ++ [k]) =
    (ks.scanl (· + ·) 0).zip ks ++ [(ks.sum, k)] := by
  simpa using zip_scanl_append_singleton_gen 0 ks k

/-- The RHS scanl/zip/tail/prod expression picks up factor C(ks.sum + k, k) on appending [k].
    For ks = [], both sides equal 1.
    For ks ≠ [], the tail distributes and the extra pair contributes C(ks.sum + k, k). -/
theorem rhs_append_singleton (ks : List ℕ) (k : ℕ) :
    ((((ks ++ [k]).scanl (· + ·) (0 : ℕ)).zip (ks ++ [k])).tail.map
        (fun ⟨acc, j⟩ => Nat.choose (acc + j) j)).prod =
    (((ks.scanl (· + ·) (0 : ℕ)).zip ks).tail.map
        (fun ⟨acc, j⟩ => Nat.choose (acc + j) j)).prod *
    Nat.choose (ks.sum + k) k := by
  rw [zip_scanl_append_singleton]
  cases ks with
  | nil =>
    -- zip [] [] = [], so ([] ++ [(0, k)]).tail = [(0, k)].tail = []
    simp
  | cons h t =>
    -- zip (scanl 0 (h :: t)) (h :: t) starts with (0, h), non-empty
    -- tail distributes: (l ++ [x]).tail = l.tail ++ [x] when l ≠ []
    have hne : (List.scanl (· + ·) 0 (h :: t)).zip (h :: t) ≠ [] := by
      simp
    rw [List.tail_append_of_ne_nil hne]
    simp only [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

/-- Main theorem: multinomial ks = product of C(partial_sum + kᵢ, kᵢ) over all kᵢ in ks.
    Proved by backward induction (List.reverseRecOn) using:
    - multinomial_append_singleton: LHS step
    - rhs_append_singleton: RHS step -/
theorem multinomial_eq_prod_choose : ∀ (ks : List ℕ),
    multinomial ks =
      (((ks.scanl (· + ·) (0 : ℕ)).zip ks).tail.map
        (fun ⟨acc, k⟩ => Nat.choose (acc + k) k)).prod := by
  intro ks
  induction ks using List.reverseRecOn with
  | nil => simp [multinomial]
  | append_singleton ks k ih =>
    rw [multinomial_append_singleton, ih, rhs_append_singleton]

end KummerMultinomialAristotle
