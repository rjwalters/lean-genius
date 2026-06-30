/-
# Vajda's Identity (the bilinear master identity for `Nat.fib`)

Vajda's identity states that for the Fibonacci numbers `F` and all `n, i, j`,

  `F_{n+i}·F_{n+j} − Fₙ·F_{n+i+j} = (−1)ⁿ · Fᵢ·Fⱼ`.

It is the common generalization of **all three** classical bilinear Fibonacci
identities, and unlike the signed Catalan/d'Ocagne forms it is *fully additive*
in its indices — no `Nat` subtraction appears anywhere:

* **Cassini** is `i = j = 1`:    `F_{n+1}² − Fₙ·F_{n+2} = (−1)ⁿ`.
* **Catalan** (`catalan_aux` of the parent file) is `i = j = r`:
    `F_{n+r}² − Fₙ·F_{n+2r} = (−1)ⁿ·Fᵣ²`.
* **d'Ocagne (shift form)** is `j = 1`:
    `F_{n+i}·F_{n+1} − Fₙ·F_{n+i+1} = (−1)ⁿ·Fᵢ`.

The parent entry (`CassiniIdentityOQ01OQ01`) proved Catalan, and its docstring
noted that "Mathlib records neither Catalan's identity nor the general
Vajda/d'Ocagne bilinear identities for `Nat.fib`". This file supplies exactly
that missing master identity, from which Catalan is recovered as the diagonal
`i = j = r` case.

## Proof

The proof is a single bilinear expansion, with no second induction beyond the
one already inside Cassini. Writing `A = Fₙ`, `B = F_{n+1}`, we expand each of
`F_{n+i}`, `F_{n+j}`, `F_{n+i+j}` by Mathlib's **addition formula** `Nat.fib_add`
(`F_{m+k+1} = Fₘ·F_k + F_{m+1}·F_{k+1}`). All the cross terms collapse, leaving

  `LHS = F_i·F_j · (B² − A·B − A²) = F_i·F_j · (−1)ⁿ`,

where the last step is Cassini in the normalized form `cassini_sub` proved by the
parent file. We reuse `cassini_sub` directly via `import`.

The same Vajda identity is also proved elsewhere in the gallery
(`FibonacciIdentitiesOQ01OQ02OQ01.fib_vajda_gap`) by a two-step induction on `j`
off d'Ocagne's identity. This file gives the *independent, non-inductive*
derivation native to the Cassini lineage: one addition-formula expansion against
the imported Cassini core, no induction beyond the one already inside Cassini.

No axioms, no `native_decide`, no sorries.
-/
import Mathlib
import Proofs.CassiniIdentityOQ01OQ01

namespace CassiniIdentityOQ01OQ01OQ01

open CassiniIdentityOQ01OQ01 (cassini_sub)

/-- **Vajda's identity.**
`F_{n+i}·F_{n+j} − Fₙ·F_{n+i+j} = (−1)ⁿ · Fᵢ·Fⱼ`, for all `n i j : ℕ`.

This is the bilinear master identity for `Nat.fib`: it specializes to Cassini
(`i = j = 1`), Catalan (`i = j = r`), and the d'Ocagne shift identity (`j = 1`).
The index arithmetic is entirely additive, so no `Nat` subtraction is needed.

The proof expands the three Fibonacci values by the addition formula
`Nat.fib_add` and collapses the cross terms with Cassini (`cassini_sub`). -/
theorem vajda (n i j : ℕ) :
    (Nat.fib (n + i) : ℤ) * Nat.fib (n + j) - Nat.fib n * Nat.fib (n + i + j)
      = (-1) ^ n * (Nat.fib i : ℤ) * Nat.fib j := by
  cases i with
  | zero =>
    -- `i = 0`: both sides vanish (`F₀ = 0`, and `F_{n}·F_{n+j}` cancels).
    simp only [Nat.add_zero, Nat.fib_zero, Nat.cast_zero, mul_zero, zero_mul]
    ring
  | succ s =>
    cases j with
    | zero =>
      -- `j = 0`: symmetric vanishing.
      simp only [Nat.add_zero, Nat.fib_zero, Nat.cast_zero, mul_zero]
      ring
    | succ t =>
      -- Normalize the three indices into `· + 1` shape for `Nat.fib_add`.
      have ei : n + (s + 1) = n + s + 1 := by ring
      have ej : n + (t + 1) = n + t + 1 := by ring
      -- `ei` first rewrites `n + (s+1) ↦ n + s + 1` everywhere, including inside the
      -- `F_{n+i+j}` argument, so `eij` must match that already-normalized form.
      have eij : n + s + 1 + (t + 1) = n + (s + t + 1) + 1 := by ring
      rw [ei, ej, eij]
      -- Addition-formula expansions of the three Fibonacci values.
      have hI : (Nat.fib (n + s + 1) : ℤ)
          = Nat.fib n * Nat.fib s + Nat.fib (n + 1) * Nat.fib (s + 1) := by
        exact_mod_cast Nat.fib_add n s
      have hJ : (Nat.fib (n + t + 1) : ℤ)
          = Nat.fib n * Nat.fib t + Nat.fib (n + 1) * Nat.fib (t + 1) := by
        exact_mod_cast Nat.fib_add n t
      have hIJ : (Nat.fib (n + (s + t + 1) + 1) : ℤ)
          = Nat.fib n * Nat.fib (s + t + 1) + Nat.fib (n + 1) * Nat.fib (s + t + 2) := by
        exact_mod_cast Nat.fib_add n (s + t + 1)
      -- Addition-formula expansions of the two combined inner indices.
      have hsum1 : (Nat.fib (s + t + 1) : ℤ)
          = Nat.fib s * Nat.fib t + Nat.fib (s + 1) * Nat.fib (t + 1) := by
        exact_mod_cast Nat.fib_add s t
      have hsum2 : (Nat.fib (s + t + 2) : ℤ)
          = Nat.fib s * Nat.fib (t + 1) + Nat.fib (s + 1) * Nat.fib (t + 2) := by
        have : s + t + 2 = s + (t + 1) + 1 := by ring
        rw [this]; exact_mod_cast Nat.fib_add s (t + 1)
      -- `F_{t+2} = F_t + F_{t+1}` to eliminate the stray `F_{t+2}`.
      have ht2 : (Nat.fib (t + 2) : ℤ) = Nat.fib t + Nat.fib (t + 1) := by
        exact_mod_cast (Nat.fib_add_two (n := t))
      -- Cassini supplies `B² − A·B − A² = (−1)ⁿ`.
      have hcas := cassini_sub n
      rw [hI, hJ, hIJ, hsum1, hsum2, ht2]
      linear_combination (Nat.fib (s + 1) : ℤ) * Nat.fib (t + 1) * hcas

/-! ### Specializations: Vajda recovers the classical bilinear identities -/

/-- **Cassini** is Vajda at `i = j = 1`: `F_{n+1}² − Fₙ·F_{n+2} = (−1)ⁿ`. -/
theorem vajda_cassini (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) = (-1) ^ n := by
  have h := vajda n 1 1
  simp only [Nat.fib_one, Nat.cast_one, mul_one] at h
  have e : n + 1 + 1 = n + 2 := by ring
  rw [e] at h
  linear_combination h

/-- **Catalan (subtraction-free form)** is Vajda at `i = j = r`:
`F_{n+r}² − Fₙ·F_{n+2r} = (−1)ⁿ·Fᵣ²`. This is exactly the parent file's
`catalan_aux`, here obtained as a corollary of the more general `vajda`. -/
theorem vajda_catalan (n r : ℕ) :
    (Nat.fib (n + r) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2 * r)
      = (-1) ^ n * (Nat.fib r : ℤ) ^ 2 := by
  have h := vajda n r r
  have e : n + r + r = n + 2 * r := by ring
  rw [e] at h
  linear_combination h

/-- **d'Ocagne shift identity** is Vajda at `j = 1`:
`F_{n+i}·F_{n+1} − Fₙ·F_{n+i+1} = (−1)ⁿ·Fᵢ`. -/
theorem vajda_docagne (n i : ℕ) :
    (Nat.fib (n + i) : ℤ) * Nat.fib (n + 1) - Nat.fib n * Nat.fib (n + i + 1)
      = (-1) ^ n * (Nat.fib i : ℤ) := by
  have h := vajda n i 1
  simp only [Nat.fib_one, Nat.cast_one, mul_one] at h
  linear_combination h

/-! ### Numerical sanity checks -/

/-- `n = 2, i = 1, j = 3`: `F₃·F₅ − F₂·F₆ = 2·5 − 1·8 = 2 = (−1)²·F₁·F₃`. -/
theorem vajda_2_1_3 :
    (Nat.fib 3 : ℤ) * Nat.fib 5 - Nat.fib 2 * Nat.fib 6
      = (-1) ^ 2 * (Nat.fib 1 : ℤ) * Nat.fib 3 := by
  have := vajda 2 1 3
  norm_num at this ⊢

/-- `n = 3, i = 2, j = 2`: `F₅² − F₃·F₇ = 25 − 2·13 = −1 = (−1)³·F₂²`
(the Catalan instance `catalan_5_2` of the parent, via the diagonal of Vajda). -/
theorem vajda_3_2_2 :
    (Nat.fib 5 : ℤ) * Nat.fib 5 - Nat.fib 3 * Nat.fib 7
      = (-1) ^ 3 * (Nat.fib 2 : ℤ) * Nat.fib 2 := by
  have := vajda 3 2 2
  norm_num at this ⊢

end CassiniIdentityOQ01OQ01OQ01
