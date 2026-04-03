# Knowledge: erdos-433-incomplete-01

## Problem Summary

Erdős #433: Prove g(k,n) ~ n²/(k-1). SOLVED by Dixmier 1990. The lean file had >15 compilation errors preventing any progress; this session fixed all of them.

## Session 2026-04-03 (Session 1) - Fix compilation errors, create Aristotle companion

**Mode**: FRESH
**Outcome**: progress — all compilation errors fixed, Aristotle file created

### What I Did

- Fixed all >15 compilation errors in `Erdos433Problem.lean`
- Created new `Erdos433Aristotle.lean` companion file with 4 sorries for Aristotle
- Both files now compile successfully (verified via docker build)

### Key Findings

- **Root cause of notation bug**: `notation "G(\" A \")\"` caused Lean's lexer to treat escaped quotes inside a string literal, producing "unterminated string" error at line 251. Fixed with three-token notation: `notation "G(" A ")" => frobeniusNumber A`
- **`IsCoprime` name conflict**: Mathlib defines `IsCoprime` as a predicate on ring elements. Renamed to `SetGCDOne`.
- **`g` definition syntax**: `{G(A) | A : Finset ℕ // ...}` is invalid Lean 4 (parses `//` as a comment). Fixed to `{v : ℕ | ∃ A : Finset ℕ, ... ∧ v = G(A)}`.
- **`omega` can't close nonlinear ℕ goals directly**: For identities like `(n-2)*(n-2+1)-1 = n²-3n+1`, use `obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩` to eliminate ℕ subtraction, then expand products to `m*m + linear` form so omega treats `m*m` as an atom.
- **`Nat.sub_sub`** is universally valid in ℕ: combines `a - b - c = a - (b+c)` without preconditions.
- **`schur_bound`**: `a * b - a - b < a * b` is nonlinear; omega fails. Proved with `calc` using `Nat.sub_le` and `Nat.sub_lt`.
- **`AsymptoticFormula`**: Need explicit type annotations `(n ^ 2 : ℝ)` and `(g k n : ℝ)` to avoid coercion ambiguity.
- **`Finset.card_insert_of_not_mem` deprecated**: Use `Finset.card_insert_of_notMem` (camelCase).

### Files Modified

- `proofs/Proofs/Erdos433Problem.lean` — fixed all compilation errors; 1 sorry remains (g_two)
- `proofs/Proofs/Erdos433Aristotle.lean` — new Aristotle companion; 4 sorries for Aristotle

### Sorries Remaining

**Erdos433Problem.lean:**
- `g_two` (line 195): main theorem g(2,n) = n²-3n+1. Requires showing {n-1,n} achieves the max in the sSup. HARD — needs upper bound over all 2-element subsets + sSup attainment argument.

**Erdos433Aristotle.lean (for Aristotle):**
- `coprime_pred_self`: Nat.Coprime (n-1) n. Should be in Mathlib.
- `frobenius_ub_pair`: a*b - a - b ≤ n²-3n+1 for 1 ≤ a ≤ n-1, 1 ≤ b ≤ n. nlinarith should work.
- `frobenius_bound_int`: Same bound in ℤ. nlinarith with cast.
- `finset_gcd_pred_self`: ({n-1,n} : Finset ℕ).gcd id = 1.

### Next Steps

1. Check Aristotle results after overnight job
2. Integrate Aristotle solutions for the 4 companion sorries
3. Work on g_two: key challenge is sSup argument (showing {n-1,n} achieves the supremum)
