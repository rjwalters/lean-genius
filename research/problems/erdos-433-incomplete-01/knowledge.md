# Knowledge: erdos-433-incomplete-01

## Problem Summary

Erdős #433: Prove g(k,n) ~ n²/(k-1). SOLVED by Dixmier 1990. **STATUS: COMPLETE** — all sorries proved, g_two theorem proved for n≥3, both Lean files compile cleanly. PR #9185.

## Session 2026-04-03 (Session 3) - Prove g_two, complete all sorries

**Mode**: FRESH (continuing)
**Outcome**: completed — g_two sorry eliminated, both files have 0 sorries

### What I Did

- Added `import Proofs.Erdos433Aristotle` to `Erdos433Problem.lean`
- Proved `frobenius_zero_one` (G({0,1}) = 0): key insight is `hempty` stated in terms of `NumericalSemigroup` (not unfolded) so `simp only [frobeniusNumber, hempty, csSup_empty, bot_eq_zero]` rewrites cleanly; `Finset.sum_coe_sort` converts subtype sum to ordinary sum then `simp [sum_insert, sum_singleton]` closes it
- Proved `g_two` upper bound via `csSup_le` + Sylvester-Frobenius + `frobenius_ub_pair`; degenerate cases (a=0 or b=0) handled via `frobenius_zero_one`
- Proved `g_two` lower bound via witness `{n-1,n}` using `pair_subset_range`, `pair_card`, `finset_gcd_pred_self`, `frobenius_pair_max`
- Concluded by `le_antisymm (csSup_le ... hbound) (le_csSup ... hmem)`

### Key Findings

- **`hempty` simp pattern match**: After `simp only [frobeniusNumber, NumericalSemigroup]` the goal has `∉` form (`{n | n ∉ {n | ∃ ...}}`). If `hempty` is stated using `¬∃` form, `simp only [hempty]` fails with "pattern not found". Fix: state `hempty` at the `NumericalSemigroup` abstraction level, then unfold in the final `simp only [frobeniusNumber, hempty, ...]`.
- **`Finset.sum_coe_sort` works**: Converts `∑ a : ↑{0,1}, f a` to `∑ a ∈ {0,1}, f ⟨a,_⟩`. After rewrite, `simp [sum_insert, sum_singleton]` handles the if-then-else arithmetic.

### Files Modified

- `proofs/Proofs/Erdos433Problem.lean` — g_two sorry eliminated, frobenius_zero_one helper added

### PR

https://github.com/rjwalters/lean-genius/pull/9185

## Session 2026-04-03 (Session 2) - Prove 4 Aristotle companion sorries

**Mode**: FRESH (continuing)
**Outcome**: progress — all 4 Aristotle companion sorries proved, g_two still pending

### What I Did

- Proved `coprime_pred_self`: `Nat.dvd_sub` on gcd divisibility, then `Nat.dvd_one`
- Proved `frobenius_bound_int`: `nlinarith` with 3 `mul_nonneg` witnesses (Positivstellensatz)
- Proved `frobenius_ub_pair`: `n = m+3` substitution to clear ℕ subtraction; `by_cases` on `a+b ≤ a*b`; positive case uses `(a-1)*(b-1)-1` factoring + `nlinarith`
- Proved `finset_gcd_pred_self`: `simp only [gcd_insert, gcd_singleton, id, normalize_eq]` then `exact coprime_pred_self`

### Key Findings

- **`Nat.dvd_sub` not `dvd_sub'`**: The Mathlib 4 name uses `Nat.dvd_sub` (not `dvd_sub'`).
- **`Int.natCast_nonneg` not `Int.coe_nat_nonneg`**: Updated naming in recent Mathlib.
- **`normalize_eq` is key**: Makes `Nat.gcd` and `GCDMonoid.gcd` compatible in `finset_gcd_pred_self`.

### Files Modified

- `proofs/Proofs/Erdos433Aristotle.lean` — all 4 sorries filled

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

## Session 2026-04-04 (Session 2) - Prove all 4 Aristotle companion sorries manually

**Mode**: REVISIT
**Outcome**: progress — all 4 sorries in Erdos433Aristotle.lean proved; PR #9185 created

### What I Did

- Proved all 4 sorries in `Erdos433Aristotle.lean` manually (Aristotle wasn't needed)
- Fixed two API issues: `Nat.dvd_sub'` (use `Nat.dvd_sub`), `Int.coe_nat_nonneg` (use `Int.natCast_nonneg`)
- Built with docker to verify 0 compilation errors
- Committed and created PR #9185

### Key Findings

- **`coprime_pred_self`**: `Nat.coprime_succ_self` absent in this Mathlib. Proved from first principles: any common divisor of n-1 and n divides their difference = 1. Use `Nat.dvd_sub` (NOT `Nat.dvd_sub'`).
- **`frobenius_bound_int`**: Cast `han : a ≤ n-1` via `simp only [Nat.cast_sub (show 1 ≤ n by omega)]`. Use `Int.natCast_nonneg a` for non-negativity (NOT `Int.coe_nat_nonneg`). `nlinarith` with three `mul_nonneg` product certificates closes it.
- **`frobenius_ub_pair`**: Substitute `n = m+3` first so RHS `n²-3n+1` becomes `m*m+3*m+1` (no ℕ subtraction to cast). Split on `a + b ≤ a * b`: positive case uses `(a-1)*(b-1)-1` factoring + nlinarith; negative case is `omega`.
- **`finset_gcd_pred_self`**: `simp only [Finset.gcd_insert, Finset.gcd_singleton, id, normalize_eq]` reduces goal to `Nat.gcd (n-1) n = 1`, closed by `coprime_pred_self`.

### Files Modified

- `proofs/Proofs/Erdos433Aristotle.lean` — all 4 sorries eliminated (PR #9185 pending)

### Sorries Remaining

**Erdos433Problem.lean:**
- `g_two` (line 195): 1 sorry remains. Strategy identified (see below) but not yet implemented.

### g_two Proof Strategy

The proof `g 2 n = n^2-3n+1` requires:

**Lower bound** (`n^2-3n+1 ≤ g 2 n`): Via `le_csSup`. Witness A = {n-1, n}.
- A ⊆ range(n+1): `pair_subset_range`; A.card = 2: `pair_card`
- SetGCDOne A: `finset_gcd_pred_self`
- G(A) = n^2-3n+1: `sylvester_frobenius (n-1) n ... (coprime_pred_self n ...)` + `frobenius_pair_max`

**Upper bound** (`g 2 n ≤ n^2-3n+1`): Via `csSup_le`. For each A with card=2, A ⊆ range(n+1), gcd=1:
- Extract a,b with A = {a,b} using `Finset.card_eq_two`
- Both a,b ≤ n from `Finset.mem_range`
- If a,b ≥ 1: `sylvester_frobenius` + `frobenius_ub_pair` (WLOG a < b so a ≤ n-1)
- If a = 0: gcd(0,b) = b = 1, so A = {0,1}. G({0,1}) = sSup ∅ = 0 ≤ n^2-3n+1

**Hard remaining piece for {0,1} case**: Show `NumericalSemigroup ({0,1} : Finset ℕ) = Set.univ`. Every m is representable: take `coeffs ⟨1,_⟩ = m, coeffs ⟨0,_⟩ = 0`. Need to compute `∑ a : ↑{0,1}, coeffs a * a.val = m` using `Finset.sum_attach` + `Finset.sum_insert`/`Finset.sum_singleton`.

**Also needed**: `import Proofs.Erdos433Aristotle` at top of Problem file.

### Next Steps

1. Implement `g_two` proof using the strategy above
2. Handle `G({0,1}) = 0` via `NumericalSemigroup {0,1} = Set.univ`
3. Use `Finset.sum_attach` then `simp [Finset.sum_insert, Finset.sum_singleton]` for the sum computation
