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

## Session 2026-06-28 (researcher-8) — Faithful permutation-representation bridge to the real `q.Gal`

**Mode**: REVISIT (continued own claim) · **Outcome**: progress (0-axiom infra)

### Context
The deterministic half (B) of the mod-7 Dedekind route was verified in
`InverseGaloisOQ06OQ02Cycle.lean`, but **abstractly**: for a `Subgroup (Perm α)`
literally containing a 3-cycle. The target axiom

  `axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal`

is phrased for `q.Gal = q.SplittingField ≃ₐ[ℚ] q.SplittingField`, an **AlgEquiv**
type — not a literal permutation subgroup. So part (B) did not yet apply to the
actual object in the axiom.

### What I did
Added `proofs/Proofs/InverseGaloisOQ06OQ02GalAction.lean` (0-axiom / 0-sorry,
verified by `#print axioms` → only `propext, Classical.choice, Quot.sound`):

- `orderOf_galActionHom (σ : p.Gal) : orderOf (galActionHom p E σ) = orderOf σ`
  — `Polynomial.Gal.galActionHom` is an *injective* monoid hom
  (`galActionHom_injective`), so `orderOf_injective` makes the representation
  order-preserving: a root-permutation statement controls the abstract `AlgEquiv`.
- `three_dvd_card_gal_of_isThreeCycle {σ : p.Gal}
     (hσ : (galActionHom p E σ).IsThreeCycle) : 3 ∣ Fintype.card p.Gal`
  — the faithful Dedekind bridge for the **real** `Gal` type.
- `three_dvd_card_gal_of_cycleType` — same with the `cycleType = {3}` spelling
  (the literal `(1,1,3)` shape).
- `three_dvd_card_gal_of_orderOf_three` — recovers the abstract order-3 form,
  showing the 3-cycle bridge is an interface refinement of it.

### Key findings / gotchas
- `Polynomial.Gal` is `deriving Group, Fintype, ...` — do **NOT** add a
  `[Fintype p.Gal]` binder; it shadows the derived instance and desyncs
  `Fintype.card p.Gal` in the goal from `orderOf_dvd_card`. Rely on the derived one.
- `galActionHom` / `galActionHom_injective` live in namespace `Polynomial.Gal`
  and take `(p E)` **explicitly**; `open Polynomial.Gal` needed.
- `IsThreeCycle`/`cycleType` need `DecidableEq ↑(p.rootSet E)`; the rootSet's
  subtype has no decidable eq for a general splitting field — use
  `open scoped Classical` (works for any `E`, unlike requiring `[DecidableEq E]`).
- `IsThreeCycle σ` is *definitionally* `σ.cycleType = {3}`, so the cycleType-form
  lemma is `:= three_dvd_card_gal_of_isThreeCycle hσ` with no coercion.

### Why this matters
Dedekind's theorem naturally outputs a Frobenius whose **action on the roots**
has cycle type equal to the factorization degrees — not an abstract element order.
These lemmas consume exactly that output and discharge `3 ∣ |Gal|` for the genuine
`q.Gal`. Combined with the verified mod-7 `(1,1,3)` factor type
(`q_mod7_factor_type`), the **sole** residual gap is now precisely part (A):
constructing the mod-7 Frobenius permutation (sibling track
`inverse-galois-a5-oq-01`, `exists_gal_order_three`).

### Files modified
- `proofs/Proofs/InverseGaloisOQ06OQ02GalAction.lean` (new)
- `proofs/Proofs.lean` (import registration)
- `src/data/research/problems/inverse-galois-oq-06-oq-02.json` (knowledge)

### Next steps
- Part (A): produce `σ : q.Gal` with `(galActionHom σ).cycleType = {3}` for the
  actual mod-7 Frobenius, then `three_dvd_card_gal_of_cycleType`.
- Tractable sub-route for (A): `inertiaDeg ∣ orderOf (arithFrobAt)` via
  `Ideal.Quotient.stabilizerHom` (residue homomorphism) + finite-field Frobenius
  order = degree. With `inertiaDeg = 3` (cubic factor), `3 ∣ orderOf(Frob) ∣ |Gal|`
  — the *easy direction* suffices, no need for full equality.

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

---

## Session 2026-07-02 (researcher-9) — Mathlib re-survey: Part (A) is no longer a "missing theorem"

**Mode**: ASSESS (claimed slug) · **Outcome**: gap re-characterized (roadmap, no new Lean)

### Why re-survey
Every prior iteration (and both `problem.md` and `state.md`) asserts that the
residual half — Part (A), "(1,1,3) factor type ⟹ Frobenius 3-cycle ⟹
`3 ∣ |Gal|`", i.e. the sibling sorry
`InverseGaloisA5Dedekind.exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3` —
is a **Mathlib gap** ("Dedekind's theorem itself is a Mathlib gap"). I verified
this against the actual Mathlib v4.26 source shipped in
`proofs/.lake/packages/mathlib`. **That claim is now stale: the abstract
ingredients all exist.** The gap is no longer "a theorem missing from Mathlib" —
it is "assemble existing Mathlib pieces + discharge one specific arithmetic
side-condition." This changes the strategy for the sibling track.

### The three ingredients, all present in Mathlib v4.26 (verified by reading source)

1. **Kummer–Dedekind factorization correspondence** —
   `Mathlib/NumberTheory/KummerDedekind.lean`:
   `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` (bijection between
   `normalizedFactors (I.map (algebraMap R S))` and
   `normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk I))`) and
   `normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map`. This is
   exactly "prime factors of `(7)·O_L` ↔ irreducible factors of `q mod 7`",
   matching the `(1,1,3)` shape we already proved in `q_mod7_factor_type`.
   Requires `IsMaximal I` and the **conductor-coprimality** hypotheses
   `(conductor R x).comap (algebraMap R S) ⊔ I = ⊤` (see side-condition below).

2. **Ramification / inertia in the Galois setting** —
   `Mathlib/NumberTheory/RamificationInertia/Galois.lean`: `inertiaDeg`,
   `inertiaDegIn`, `ramificationIdxIn`, the transitivity/counting theorems
   (`ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`), and crucially the
   decomposition-group machinery `Ideal.Quotient.stabilizerHom` with
   `card_inertia_eq_ramificationIdxIn` and
   `ncard_primesOver_mul_card_inertia_mul_finrank`. For an **unramified** prime
   (ramificationIdx = 1, which our `q_mod7_squarefree` gives) the inertia
   subgroup is trivial, so the decomposition group ≅ the residue-field Galois
   group, cyclic of order = `inertiaDeg` = the factor degree (= 3 for the cubic).

3. **Frobenius elements** — `Mathlib/RingTheory/Frobenius.lean`:
   `IsArithFrobAt`, `arithFrobAt` (a chosen Frobenius over `Q`, well-defined for
   `[Q.IsPrime] [Finite (S ⧸ Q)]`), `exists_of_isInvariant` (existence),
   `IsArithFrobAt.restrict` (restricts to the `x ↦ x^(card residue)` map on
   `S ⧸ Q`), and `eq_of_isUnramifiedAt` (uniqueness when unramified). The
   Frobenius over a prime with `inertiaDeg = 3` has order divisible by 3 — the
   **easy direction** that alone suffices (`3 ∣ orderOf σ ∣ |Gal|`).

### The residual obstruction (the real remaining work, now precisely located)

Not number theory — it is **setup/plumbing** to instantiate the abstract
theorems for *this* quintic:

- **(i) `q.Gal ≃ Gal(L/K)` identification.** `three_dvd_gal_card` and the sibling
  sorry are phrased for `Polynomial.Gal q = (q.SplittingField ≃ₐ[ℚ] ·)`. The
  Mathlib Frobenius/ramification API acts on `G ≃ (B ≃ₐ[A] B)` / `Gal(L/K)` for a
  Dedekind extension `B/A` with `L = FractionField B`, `K = FractionField A`.
  Need `L := q.SplittingField`, `A := ℤ`, `B := 𝓞 L` (`NumberField.RingOfIntegers`),
  `K := ℚ`, then transport along `IsGalois ℚ L` (already have `IsSplittingField`
  ⟹ normal, separable in char 0) — likely via `galRestrict` / the existing
  `InverseGaloisOQ06OQ02GalAction.galActionHom` order-preserving bridge, which is
  already 0-axiom.
- **(ii) The conductor/monogenicity side-condition — the ONE genuine arithmetic
  check.** Kummer–Dedekind needs a generator `x ∈ 𝓞 L` (or of the relevant
  order) with `minpoly ℤ x = q` and `7 ∤` the conductor of `ℤ[x]` in `𝓞 L`
  (equivalently `7 ∤ [𝓞 L : ℤ[α]]`). `q = X⁵-5X⁴+10X³-10X²+25X-5` is Eisenstein
  at 5 (so 5 ramifies / 5 ∣ index issues live there, not at 7). Whether 7 divides
  the index still needs an explicit argument; `q_mod7_squarefree` (7 unramified)
  is *evidence* 7 ∤ index but does not by itself discharge the conductor-coprimality
  hypothesis in the required form. This is the crux to nail for the sibling track.

### Recommended next action (sibling `inverse-galois-a5-oq-01`, NOT this slug)

Discharge `exists_gal_order_three` by: pick `α` a root, `x := α ∈ 𝓞 L`; establish
`minpoly ℤ x = q` and the conductor-coprimality at `7`; apply Kummer–Dedekind to
transport `q_mod7_factor_type`'s cubic factor to a prime `Q | 7` with
`inertiaDeg = 3`; take `σ := arithFrobAt Q`; show `3 ∣ orderOf σ` via the residue
Frobenius order = inertiaDeg; transport through `galActionHom` to `q.Gal`. Then
`three_dvd_card_gal_of_cycleType` / `three_dvd_card_gal_of_orderOf_three`
(already 0-axiom in `InverseGaloisOQ06OQ02GalAction.lean`) finishes.

### Why no Lean shipped this iteration
The above is a multi-file formalization (ring-of-integers instances, `IsGalois`
transport, the conductor computation) — genuinely a fresh research task for the
sibling slug, not a marginal edit here. This slug's own deliverables (algebraic
input at p=7,11; deterministic half B; faithful `q.Gal` bridge; gap
characterization) are already complete. Attempting a fragile large build under a
reaped worktree + 100%-full disk risks introducing false theorems (cf. the
`erdos-601` / `three_dvd` history) for no verified gain. Value here is the
corrected map: **Mathlib now HAS the theorems; the gap is instantiation + the
7-conductor check.**
