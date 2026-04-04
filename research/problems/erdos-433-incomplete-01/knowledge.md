# Knowledge: erdos-433-incomplete-01

## Problem Summary

Erdős #433: Prove g(k,n) ~ n²/(k-1). SOLVED by Dixmier 1990. **STATUS: COMPLETE** — all sorries proved, g_two theorem proved for n≥3, both Lean files compile cleanly. PR #9157.

## Session 2026-04-03 (Session 2) - Prove all sorries, complete g_two

**Mode**: FRESH (continuing)
**Outcome**: completed — all 5 sorries eliminated, both files build

### What I Did

- Proved `coprime_pred_self` by lifting to ℤ, using `dvd_sub` on gcd divisibility
- Proved `frobenius_bound_int` via `nlinarith` with 4 Positivstellensatz witnesses
- Proved `frobenius_ub_pair` via `rcases le_or_lt` on ℕ underflow + `zify` + `linarith`
- Proved `finset_gcd_pred_self` via `Finset.gcd_dvd` for each element + `Nat.dvd_gcd` + coprimality
- Proved `every_mem_num_sem_01`: rewrote `Finset.univ` for `↥{0,1}` to explicit pair `{⟨0,_⟩, ⟨1,_⟩}`, then `sum_insert`/`sum_singleton` + `norm_num`
- Proved `frobenius_zero_one`: G({0,1}) = 0 from `every_mem_num_sem_01`
- Proved `g_two` upper bound: `csSup_le`; for each 2-element subset, apply Sylvester-Frobenius then `frobenius_ub_pair`; handle a=0 or b=0 degenerate cases via `frobenius_zero_one`
- Proved `g_two` lower bound: `dixmier_lower_bound 2 n` + `dixmier_k2_arith` arithmetic identity

### Key Findings

- **`Finset.sum_coe_sort` fails with lambdas**: Both `rw` (pattern `?f ↑i` can't match lambdas) and `simp only` (goal has `a.val` not `↑a` form) fail. Workaround: rewrite `Finset.univ` for the subtype finset to an explicit element set, then use `sum_insert`/`sum_singleton`.
- **`Finset.gcd_insert` takes no proof argument**: calling `Finset.gcd_insert (by simp)` gives "function expected". Use `Finset.gcd_dvd` instead.
- **`GCDMonoid.gcd ≠ Nat.gcd` definitionally**: Can't use `simp [coprime_pred_self]` after `gcd_insert`/`gcd_singleton`. Use `Nat.dvd_gcd` + `Finset.gcd_dvd` approach instead.
- **`subst h` direction**: `h : x = a` (both locals) may substitute `a := x`, making `a` unknown. Use `rw [h]` instead of `subst h` or `rcases ... with rfl`.
- **`zify [side_conds]`**: Much more reliable than `push_cast` for ℕ subtraction with known bounds. Pass the bound proof as a side condition directly.

### Files Modified

- `proofs/Proofs/Erdos433Aristotle.lean` — all 4 sorries filled
- `proofs/Proofs/Erdos433Problem.lean` — g_two sorry filled, helpers added

### PR

https://github.com/rjwalters/lean-genius/pull/9157

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
