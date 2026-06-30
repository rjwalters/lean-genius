/-
# Axiom-free CRT worked examples on composite coprime moduli (OQ-05-OQ-01)

The sibling entry **chinese-remainder-constructive-oq-05** removed the root CRT
entry's `native_decide` from its two headline worked examples (Sunzi `x = 23`
mod `105` and the four-moduli `x = 53` mod `210`), packaging the argument into a
reusable two-modulus certificate

    `crt_pair_iff : Coprime m n → N < m*n → N % m = a → N % n = b →
        ∀ x < m*n, (x % m = a ∧ x % n = b) ↔ x = N`

whose only axioms are the ordinary foundational `propext / Classical.choice /
Quot.sound`.  Every numeric check there is a kernel `decide` / `omega`, never the
compiler-trusting `native_decide` (which would inject `Lean.ofReduceBool`).

This entry continues that programme on the remaining advertised worked examples,
which use **composite (non-prime) coprime moduli** — the regime where a careless
`native_decide` is most tempting because `decide` on `Nat.Coprime` unfolds a `gcd`:

* `crt_17_mod_20`   : over `0 ≤ x < 20 = 4·5`,   `x ≡ 1 (4) ∧ x ≡ 2 (5)  ↔ x = 17`.
* `crt_135_mod_143` : over `0 ≤ x < 143 = 11·13`, `x ≡ 3 (11) ∧ x ≡ 5 (13) ↔ x = 135`.

Both are one-line instances of `crt_pair_iff`, so they inherit its axiom profile.
We also reprove the small `x = 8` mod `15` example that the list-based sibling
`...OQ04OQ02` discharges with `native_decide`, here entirely kernel-checked.

Finally we extend the certificate to **three pairwise-coprime moduli**

    `crt_triple_iff : Coprime m n → Coprime m p → Coprime n p → N < m*n*p →
        N % m = a → N % n = b → N % p = c →
        ∀ x < m*n*p, (x % m = a ∧ x % n = b ∧ x % p = c) ↔ x = N`

— the genuinely new infrastructure of this file (the sibling stopped at two
moduli) — and exercise it on a fresh composite-modulus example `x = 11` mod `60`.

`#print axioms` on every theorem below lists only `propext`, `Classical.choice`,
`Quot.sound`: no `native_decide`, no `Lean.ofReduceBool`, no `sorry`, no `axiom`.
-/
import Mathlib
import Proofs.ChineseRemainderConstructiveOQ05

namespace ChineseRemainderConstructiveOQ05OQ01

open ChineseRemainderConstructiveOQ05

/- ## Composite-modulus worked examples via the two-modulus certificate -/

/-- **`17` mod `20`, axiom-free.** The moduli `4` and `5` are coprime but not
prime; over `0 ≤ x < 20` the congruences `x ≡ 1 (mod 4)` and `x ≡ 2 (mod 5)`
hold *iff* `x = 17`.  A direct instance of `crt_pair_iff` — no `native_decide`. -/
theorem crt_17_mod_20 (x : ℕ) (hx : x < 20) :
    (x % 4 = 1 ∧ x % 5 = 2) ↔ x = 17 :=
  crt_pair_iff (by decide) (by decide) (by decide) (by decide) x hx

/-- **`135` mod `143`, axiom-free.** With the coprime composite range `143 = 11·13`,
over `0 ≤ x < 143` the congruences `x ≡ 3 (mod 11)` and `x ≡ 5 (mod 13)` hold
*iff* `x = 135`.  Again a single application of `crt_pair_iff`. -/
theorem crt_135_mod_143 (x : ℕ) (hx : x < 143) :
    (x % 11 = 3 ∧ x % 13 = 5) ↔ x = 135 :=
  crt_pair_iff (by decide) (by decide) (by decide) (by decide) x hx

/-- **`8` mod `15`, axiom-free.** The list-based sibling `...OQ04OQ02` proves the
analogous `example_8_mod3_mod5` with `native_decide`; here the same fact is a
kernel-checked instance of `crt_pair_iff` over `15 = 3·5`. -/
theorem crt_8_mod_15 (x : ℕ) (hx : x < 15) :
    (x % 3 = 2 ∧ x % 5 = 3) ↔ x = 8 :=
  crt_pair_iff (by decide) (by decide) (by decide) (by decide) x hx

/- ## A reusable axiom-free three-modulus certificate -/

/-- **Three-modulus CRT certificate, axiom-free.** For pairwise coprime moduli
`m, n, p` and a witness `N < m*n*p` matching all three residues, over the range
`0 ≤ x < m*n*p` the three congruences hold *iff* `x = N`.

This extends the sibling's two-modulus `crt_pair_iff` by folding in the third
modulus with `Nat.modEq_and_modEq_iff_modEq_mul`, using `m·n` coprime to `p`
(`Nat.Coprime.mul`).  Like the pair version it certifies existence and uniqueness
in one `iff` and uses only kernel `omega`, never `native_decide`. -/
theorem crt_triple_iff {m n p N : ℕ}
    (hmn : Nat.Coprime m n) (hmp : Nat.Coprime m p) (hnp : Nat.Coprime n p)
    (hN : N < m * n * p) {a b c : ℕ}
    (ha : N % m = a) (hb : N % n = b) (hc : N % p = c)
    (x : ℕ) (hx : x < m * n * p) :
    (x % m = a ∧ x % n = b ∧ x % p = c) ↔ x = N := by
  constructor
  · rintro ⟨hxa, hxb, hxc⟩
    have em : x ≡ N [MOD m] := by unfold Nat.ModEq; omega
    have en : x ≡ N [MOD n] := by unfold Nat.ModEq; omega
    have ep : x ≡ N [MOD p] := by unfold Nat.ModEq; omega
    have emn : x ≡ N [MOD m * n] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hmn).mp ⟨em, en⟩
    have hmnp : Nat.Coprime (m * n) p := hmp.mul_left hnp
    have emnp : x ≡ N [MOD m * n * p] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hmnp).mp ⟨emn, ep⟩
    have hxmod : x % (m * n * p) = N % (m * n * p) := emnp
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hN] at hxmod
    exact hxmod
  · rintro rfl
    exact ⟨ha, hb, hc⟩

/-- **`11` mod `60`, axiom-free.** A fresh three-modulus example on the pairwise
coprime composite range `60 = 3·4·5`: over `0 ≤ x < 60` the congruences
`x ≡ 2 (mod 3)`, `x ≡ 3 (mod 4)`, `x ≡ 1 (mod 5)` hold *iff* `x = 11`.  A direct
instance of `crt_triple_iff`. -/
theorem crt_11_mod_60 (x : ℕ) (hx : x < 60) :
    (x % 3 = 2 ∧ x % 4 = 3 ∧ x % 5 = 1) ↔ x = 11 :=
  crt_triple_iff (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) x hx

end ChineseRemainderConstructiveOQ05OQ01
