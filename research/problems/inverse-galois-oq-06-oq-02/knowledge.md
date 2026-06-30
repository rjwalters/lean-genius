# Knowledge Base: inverse-galois-oq-06-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The A₅ realizability entry rests on a single axiom `three_dvd_gal_card`. The
mod-7 Dedekind route to eliminate it has two halves:

1. **Algebraic input** (THIS slug): `q mod 7` = distinct irreducibles of degree
   `(1,1,3)`, squarefree (7 unramified).
2. **Dedekind implication** (sibling `inverse-galois-a5-oq-01`): factor type ⟹
   Frobenius cycle type ⟹ `3 ∣ |Gal|`. Mathlib gap.

Sibling `inverse-galois-oq-06-oq-01` had established only the *shape* of the
factorization and that the cubic has no roots — not irreducibility/squarefree.

---

## Insights

- A degree-3 polynomial over a field with no root is irreducible:
  `Polynomial.irreducible_of_degree_le_three_of_not_isRoot`
  `(hdeg : p.natDegree ∈ Finset.Icc 1 3) (hnot : ∀ x, ¬ IsRoot p x)`.
  First goal closes by `rw [natDegree_eq]; decide`; second is exactly the
  no-roots fact reused from the sibling.
- Coprimality of distinct linear factors: `isCoprime_X_sub_C_of_isUnit_sub`
  needs `IsUnit (a - b)`; over a field use `isUnit_iff_ne_zero.mpr (by decide)`.
- Coprimality of linear vs cubic: `Irreducible.isRelPrime_iff_not_dvd` +
  `Polynomial.dvd_iff_isRoot` reduces `¬ (X - C a) ∣ cubic` to `eval a cubic ≠ 0`.
- Squarefree of a product of pairwise-coprime squarefrees:
  `squarefree_mul_iff : Squarefree (x*y) ↔ IsRelPrime x y ∧ Squarefree x ∧ Squarefree y`
  (note: `IsRelPrime`, not `IsCoprime`; convert with `IsCoprime.isRelPrime`).
  `IsCoprime.mul_left` builds `IsCoprime (a*b) c` from the two coprimalities.
- Non-association of equal-degree monic factors: `eq_of_monic_of_associated`
  forces equality, then evaluate at 0 (`congrArg (eval 0)`) and `decide`.
  Different degrees: `natDegree_le_of_dvd` both ways + `omega`.

---

## Packaging completeness (iter 3)

- A "factor type" theorem that lists irreducibles + degrees + distinctness +
  squarefreeness is **incomplete** unless it ALSO carries the factorization
  identity `q.map(ℤ→𝔽ₚ) = f₁·f₂·f₃`. Without it the statement is about an
  arbitrary product, not about `q mod p`. The mod-11 packaging already had this
  conjunct; the mod-7 one did not — fixed by re-exporting
  `q_ℤ_mod7_factorization` through the local factor defs.
- Restating an identity proved with `(X - C 5)` in terms of a `noncomputable def
  linFactor5 := X - C 5`: use `show <goal with X - C 5>; exact <lemma>`. The
  `show` succeeds by defeq (regular defs unfold during `isDefEq`); no `rw`/`simp`
  unfolding of the def is needed.

---

## Part (B): the permutation-group consequence (iter 3 / Cycle file)

Dedekind's conclusion at `p = 7` factors into two independent halves:

- **(A) Frobenius ↔ factorization** — the genuine number-theory gap (Frobenius
  at an unramified `𝔭 | 7` acts with cycle type equal to the factorization
  degrees). Owned by sibling `inverse-galois-a5-oq-01`
  (`InverseGaloisA5Dedekind.exists_gal_order_three`, still a sorry).
- **(B) cycle type ⟹ order ⟹ divisibility** — pure group theory, now fully
  machine-checked in `InverseGaloisOQ06OQ02Cycle.lean` (0-axiom/0-sorry).

`InverseGaloisOQ06OQ02Cycle.lean` content:

- `frob113 : Perm (Fin 5) := swap 2 3 * swap 2 4` — explicit `(1,1,3)`
  permutation (3-cycles 2,3,4; fixes 0,1 = the two linear-factor roots).
- `Equiv.Perm.isThreeCycle_swap_mul_swap_same (ab) (ac) (bc)` proves
  `IsThreeCycle (swap a b * swap a c)`; the three distinctness args over
  `Fin 5` close by `decide`. Fixed points `frob113 0 = 0`, `frob113 1 = 1`
  also by `decide` (kernel `decide`, NOT `native_decide` — stays 0-axiom).
- `Equiv.Perm.IsThreeCycle.orderOf : orderOf g = 3` (via `lcm_cycleType` +
  `cycleType = {3}`).
- Bridges:
  - `three_dvd_card_of_orderOf_three` — finite group, order-3 elt ⟹ `3 ∣ card`
    via `orderOf_dvd_card`.
  - `three_dvd_natCard_of_isThreeCycle_mem` — `H ≤ Perm α` containing a 3-cycle
    ⟹ `3 ∣ Nat.card H` via `Subgroup.orderOf_dvd_natCard` (no `Fintype` needed,
    uses `Nat.card`).
  - `dedekind_consequence_113` — the packaged part-(B) statement with the
    cycle-type hypothesis explicit, making the residual gap (A) visible.

This does **not** discharge `three_dvd_gal_card`; it verifies the deterministic
half so the only remaining gap is the Frobenius ↔ factorization correspondence.

---

## Dead Ends

- `isCoprime_of_irreducible_of_not_associated` does NOT exist in Mathlib 4.26.
  Use the `Irreducible.isRelPrime_iff_not_dvd` / `dvd_iff_isRoot` route instead.
- `squarefree_mul_iff` is phrased with `IsRelPrime`, not `IsCoprime` — calling
  `IsCoprime.squarefree_mul_iff` fails; convert first.

---

## Gap characterization (iter 5 / GapChar file)

`InverseGaloisOQ06OQ02GapChar.lean` records that the lone open axiom of the A₅
entry has **no slack**: given the constraints `InverseGaloisA5` already proves
(`5 ∣ |q.Gal|`, `|q.Gal| ∣ 60`, `≠ 15`, `≠ 30`),

  `three_dvd_card_iff_card_eq_60 : 3 ∣ |q.Gal| ↔ |q.Gal| = 60`.

So `three_dvd_gal_card` is *exactly* as strong as the A₅-realizability target
`q_gal_card`, neither weaker nor stronger. Forward direction
`card_eq_60_of_three_dvd` is the `q_gal_card` divisor argument
(`Nat.Coprime.mul_dvd_of_dvd_of_dvd` to get `15 ∣ |Gal|`, then
`gal_card_dvd_60_proved` bounds the cofactor `k ∣ 4`, `interval_cases k`) with
the axiom replaced by an explicit hypothesis — so it is **independent of
`three_dvd_gal_card`** (verified by `#print axioms`).

Capstone `card_eq_60_of_exists_galAction_threeCycle` chains the inlined
deterministic-half bridge (injective `galActionHom` ⟹ `orderOf σ = 3` ⟹
`orderOf_dvd_card`) into the forward direction: a **single** Galois automorphism
acting on the five roots as a 3-cycle (the Frobenius at 7) forces the full
`|q.Gal| = 60`. This is the sharpest statement of the residual mod-7 input.

### HONESTY CORRECTION (important)

These GapChar theorems are **NOT** `0-axiom`/`propext-Classical-Quot only`.
`#print axioms` shows they inherit **`Lean.ofReduceBool` + `Lean.trustCompiler`**
from the A₅ constraint lemmas `gal_card_dvd_60_proved`, `gal_card_ne_15`,
`gal_card_ne_30`, all of which are discharged by `native_decide`. The earlier
sibling files (`Cycle`, `GalBridge`) avoided this only because they never pull in
those constraint lemmas — they touch just `galActionHom` + `orderOf_dvd_card`.
The honest claim is therefore narrower: GapChar removes dependence on the **open**
axiom `three_dvd_gal_card`, replacing it with a hypothesis, while carrying the
same `native_decide` trust base as the underlying A₅ entry. Do not call it
axiom-free.

(`five_dvd_gal_card` IS clean — propext/Classical.choice/Quot.sound only. The
`native_decide` lives in the divisibility-bound and order-exclusion lemmas.)
