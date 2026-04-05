# Knowledge Base: bezout-identity-oq-01-oq-01

**Problem**: Formalize Stein's binary GCD algorithm and prove it equals Nat.gcd.

---

## Session 2026-04-04 (Session 1) — Stein's Binary GCD Proved

**Mode**: FRESH
**Outcome**: completed

### What I Did

- Defined `binaryGcd : ℕ → ℕ → ℕ` (Stein's algorithm) using `if-then-else` with `termination_by a + b`
- Proved `gcd_sub_right`: `Nat.gcd a (b-a) = Nat.gcd a b` when a ≤ b via `Nat.gcd_rec` + `Nat.add_mod_right`
- Proved `gcd_odd_sub_half`: gcd(a, (b-a)/2) = gcd(a, b) when both odd with a ≤ b
- Proved `binaryGcd_eq_gcd`: main correctness theorem via recursive proof with `termination_by a + b`
- Proved properties: `binaryGcd_comm`, `binaryGcd_dvd_left`, `binaryGcd_dvd_right`, `dvd_binaryGcd`
- Proved `bezout_via_binaryGcd`: Bezout identity via Int.gcdA/gcdB

### Key Findings

- **`simp only [binaryGcd]` loops**: The auto-generated simp equation for recursive `def` can loop.
  Fix: use `unfold binaryGcd` for one definitional step, then `split_ifs`, then make recursive calls via the theorem itself (with `termination_by`).
- **`rw [ha]` where ha : a = 2*(a/2)**: rewrites `a` inside `a/2` too, causing unexpected goals.
  Fix: use `conv_rhs => rw [show a = 2*(a/2) from by omega]` to rewrite only in the RHS.
- **`gcd_sub_right` via modular arithmetic**: `(b-a) % a = b % a` when a ≤ b. Proved via `Nat.add_mod_right`: `conv_rhs => rw [← Nat.sub_add_cancel h, Nat.add_mod_right]`.
- **`Nat.dvd_sub'` does not exist** in Lean 4 Mathlib. Use the divisibility-based proof via `Nat.dvd_add` instead.
- **`congr 1` on Nat.cast equality**: For `(Nat.gcd a b : ℤ) = ↑(Int.gcd ↑a ↑b)`, `congr 1` closes the goal by definitional equality (Int.gcd ↑a ↑b reduces definitionally to Nat.gcd a b). Remove any simp after.
- **`termination_by a + b` for recursive theorem**: Works exactly like for definitions — the proof is itself well-founded recursive with `decreasing_by all_goals simp_wf; omega`.
- **Bezout corollary**: `(Int.gcd_eq_gcd_ab x y).symm : ↑(x.gcd y) = x * gcdA x y + y * gcdB x y`. Use `congr 1` to equate the Nat/Int gcd casts.

### Files Modified

- `proofs/Proofs/BezoutIdentityOQ01OQ01.lean` (created)
  - 5 proved lemmas, 4 proved theorems, 4 properties, 1 Bezout corollary
  - 0 sorries, 0 axioms

### Next Steps

- No open questions remain. This fully closes bezout-identity-oq-01-oq-01.
- Potential follow-up: binary extended GCD (computing Bezout coefficients directly using the binary algorithm)
