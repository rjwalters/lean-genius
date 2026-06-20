# Knowledge Base: euler-totient-oq-05

Insights accumulated during research on this problem.

---

## Problem Understanding

Euler's theorem `a^φ(n) ≡ 1 (mod n)` for `gcd(a,n)=1`, framed directly through the
totient `φ` (distinct from the Carmichael-`λ` entry oq-01 and the abstract
group-exponent derivation in lagrange-theorem-oq-07). The emphasis is the
**exponent-reduction corollary** `a^k ≡ a^(k mod φ(n))`, which the sibling entries
do not state and which is the arithmetic basis of modular exponentiation / RSA.

---

## Session 2026-06-19 — COMPLETED (verified, axiom-free)

**Mode:** fresh · **Outcome:** shipped `Proofs/EulerTotientOQ05.lean` (7 theorems, 113 lines, 0 axioms)

### What I did
- `euler_theorem` — `a.Coprime n → a^φ(n) ≡ 1 [MOD n]`, restating `Nat.ModEq.pow_totient`.
- `pow_mod_totient` — exponent reduction `a^k ≡ a^(k % φ n) [MOD n]`, the ModEq reading
  of `Nat.pow_totient_mod` (the `% n` arithmetic form IS `Nat.ModEq` definitionally).
- `pow_congr_of_modEq_totient` — `k ≡ j [MOD φ n] ⟹ a^k ≡ a^j [MOD n]` via a 3-step calc
  through the reduced exponents.
- `pow_add_totient` — `a^(k+φ n) ≡ a^k [MOD n]` (`Nat.pow_add_totient_mod_eq`); the period
  of `k ↦ a^k mod n` divides `φ(n)`.
- `fermat_little` — `a^(p-1) ≡ 1 [MOD p]` for prime `p`, via `rw [← Nat.totient_prime hp]`.
- `euler_units` — `u^φ(n) = 1` in `(ZMod n)ˣ` (`ZMod.pow_totient`, the Lagrange/`pow_card`
  statement since `|(ZMod n)ˣ| = φ(n)`).
- `euler_theorem_via_units` — bridge re-deriving the ℕ-ModEq form from the unit-group form
  via `ZMod.unitOfCoprime`.
- Concrete `decide` checks (3^φ(10), 2^φ(9), 7^100 reduction mod 12) — axiom-free.

### Key findings (technique notes)
- `Nat.pow_totient_mod hn h : a^k % n = a^(k%φn) % n` is **definitionally** `Nat.ModEq n
  (a^k) (a^(k%φn))`, so `pow_mod_totient` is a direct term restatement.
- `rw` on a `Nat.ModEq` hypothesis fails (it is a `def`, not syntactic `Eq`); extract
  `have : k%φn = j%φn := hkj` first.
- ℕ↔units bridge as one `rw` chain: `ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one,
  ← ZMod.coe_unitOfCoprime, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one`.
- Use `decide` (not `native_decide`) on the concrete checks to avoid `Lean.ofReduceBool`.

### Verification
- `lake env lean Proofs/EulerTotientOQ05.lean` → exit 0, no errors.
- `#print axioms` on `euler_theorem`, `pow_mod_totient`, `fermat_little`,
  `euler_theorem_via_units` → `[propext, Classical.choice, Quot.sound]` (foundational only).

### Files modified
- `proofs/Proofs/EulerTotientOQ05.lean` (new, verified)
- `proofs/Proofs.lean` (import)
- `src/data/proofs/euler-totient-oq-05/{meta,annotations}.json` (gallery entry)
- `src/data/research/problems/euler-totient-oq-05.json` (knowledge)

### Next steps
- RSA correctness `m^(ed) ≡ m (mod n)` for `ed ≡ 1 (mod φ(n))`, incl. `gcd(m,n)>1` via CRT.
- Carmichael sharpening `a^λ(n) ≡ 1` with a base of exact order `λ(n)` (overlaps oq-01).

---

## Dead Ends

- First attempt at `euler_theorem_via_units` used `simpa [hu] using congrArg …`, but the
  `@[simp]` lemma `ZMod.pow_totient` collapsed the hypothesis to `True` before it could be
  used. Replaced with the explicit `rw` chain above.
