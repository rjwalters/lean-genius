# abel-ruffini-galois-extensions-oq-10 — Knowledge

## Problem

**Regular inverse Galois problem (RIGP) for $S_n$ and $A_n$.**
Hilbert (1892) proved every $S_n$ (and via specialization $A_n$) is realizable as
$\mathrm{Gal}(L/\mathbb{Q})$. The *regular* IGP asks for a **regular** extension
$L/\mathbb{Q}(t_1,\dots,t_m)$ (equivalently $\mathbb{Q}$ algebraically closed in $L$,
i.e. the cover is geometrically connected) with $\mathrm{Gal}(L/\mathbb{Q}(t))\cong G$.
The problem card cites Thompson's rigidity criterion (1984) and Belyi's three‑point
covers (1979) — but those are the machinery for the **general** RIGP. For the two
specific groups named here, $S_n$ and $A_n$, RIGP has a **classical, elementary
resolution** via the *generic polynomial*, and that resolution is what is formalizable
in today's Mathlib.

## Summary

**Central finding (Session 1, ORIENT).** Both the $S_n$ and the $A_n$ halves of RIGP
reduce to the **same** Mathlib construction: Artin's fixed‑field theorem applied to the
permutation action on the rational function field $\mathbb{Q}(x_1,\dots,x_n)$.

- $S_n$ acts faithfully on $F := \mathbb{Q}(x_1,\dots,x_n)$ by permuting the variables.
- The fixed field $F^{S_n}$ is the field of **symmetric** rational functions
  $\mathbb{Q}(e_1,\dots,e_n)$ (elementary symmetric functions), which is purely
  transcendental over $\mathbb{Q}$ — hence $\mathbb{Q}$ is algebraically closed in it,
  so the extension $F/F^{S_n}$ is **regular**. This is the generic $S_n$ extension and
  *is* the standard RIGP‑for‑$S_n$ proof.
- Artin ⟹ $F/F^{S_n}$ is finite Galois with $\mathrm{Gal}\cong S_n$ and
  $[F:F^{S_n}] = n!$.
- $A_n \le S_n$ acts on the same $F$; Artin gives $F/F^{A_n}$ Galois with group $A_n$,
  where $F^{A_n} = \mathbb{Q}(e_1,\dots,e_n)(\sqrt{\mathrm{disc}})$ (still purely
  transcendental over $\mathbb{Q}$, so regular). This is RIGP for $A_n$.

So **the Belyi/rigidity machinery in the problem card is unnecessary for $S_n$ and
$A_n$**; the elementary generic‑polynomial route suffices and is Mathlib‑reachable.

## The exact Mathlib API path

The abstract engine is already in Mathlib (`Mathlib/FieldTheory/Fixed.lean`), for any
finite group $G$ acting **faithfully** on a field $F$:

| Mathlib declaration | Gives |
|---|---|
| `FixedPoints.subfield G F : Subfield F` | the fixed field $F^G$ |
| `instance : Normal (FixedPoints.subfield G F) F` | normality |
| `instance : Algebra.IsSeparable (FixedPoints.subfield G F) F` | separability |
| `instance : FiniteDimensional (FixedPoints.subfield G F) F` | finiteness ⟹ `IsGalois` |
| `FixedPoints.finrank_eq_card [Fintype G] [FaithfulSMul G F]` | $[F:F^G] = \lvert G\rvert$ |
| `FixedPoints.toAlgAutMulEquiv [Finite G] [FaithfulSMul G F] : G ≃* (F ≃ₐ[F^G] F)` | **the Galois‑group isomorphism** |

`toAlgAutMulEquiv` is the headline: it produces $G \cong \mathrm{Gal}(F/F^G)$ as a group
isomorphism, directly realizing $G$ as a Galois group. Instantiating $G = S_n$ (or $A_n$)
and $F = \mathbb{Q}(x_1,\dots,x_n)$ gives the theorem.

## The single infrastructure gap

Mathlib does **not** ship a `MulSemiringAction (Equiv.Perm (Fin n)) (MvPolynomial (Fin n) ℚ)`
(symmetric polynomials are defined pointwise as `∀ e, rename e p = p`, not as fixed
points of an action). So the only missing piece is:

**Build the permutation action on $F = \mathrm{FractionRing}(\mathrm{MvPolynomial}\,(\mathrm{Fin}\,n)\,\mathbb{Q})$.**

All the ingredients exist:

1. `MvPolynomial.renameEquiv ℚ e : MvPolynomial (Fin n) ℚ ≃ₐ[ℚ] MvPolynomial (Fin n) ℚ`
   for `e : Fin n ≃ Fin n`, with functoriality lemmas `renameEquiv_refl`,
   `renameEquiv_trans` (`Mathlib/Algebra/MvPolynomial/Rename.lean`).
2. Extend each `renameEquiv ℚ e` to the fraction field with
   `IsFractionRing.ringEquivOfRingEquiv` (or the algebra version
   `IsFractionRing.fieldEquivOfAlgEquiv`, `Mathlib/RingTheory/Localization/FractionRing.lean`).
3. Assemble a monoid hom `Equiv.Perm (Fin n) →* RingAut F` and turn it into an action via
   `MulSemiringAction.compHom` (`RingAut R` acts on `R` by
   `Mathlib/Algebra/Ring/Action/End.lean`).
4. Faithfulness `FaithfulSMul (Equiv.Perm (Fin n)) F`: reduces to faithfulness on
   `MvPolynomial` (`rename` sends `X i ↦ X (e i)`, injective on the generators), which
   embeds in `F`.

**Size estimate:** ~120–180 lines, all standard API — a clean **BUILD** target, not a
blocker. The only real proof obligations are the two monoid‑hom functoriality proofs
(map_one/map_mul for the extension) and faithfulness.

## Infrastructure Assessment

- **Needed:** perm `MulSemiringAction` on `FractionRing (MvPolynomial (Fin n) ℚ)` +
  faithfulness. **Decision: BUILD** (~150 lines).
- **NOT needed:** Belyi maps, Thompson rigidity, Hilbert irreducibility, algebraic
  geometry of covers. (Those are for RIGP of *general* groups; irrelevant to $S_n$/$A_n$.)
- **Regularity ("R" in RIGP):** an extra observation that $F^{S_n}=\mathbb{Q}(e_1,\dots,e_n)$
  and $F^{A_n}=\mathbb{Q}(e)(\sqrt{\mathrm{disc}})$ are purely transcendental over
  $\mathbb{Q}$, so $\mathbb{Q}$ is algebraically closed in them. Formalizing the
  *regularity* claim itself is a secondary target (Mathlib has limited "regular
  extension" API); the core Galois‑group realization does not depend on it.

## Relation to existing gallery work

- `AbelRuffiniGaloisExtensionsOQ01.lean` already realizes **$S_5$** concretely and
  *unconditionally* over $\mathbb{Q}$ via the specific quintic $X^5-4X+2$
  (`galEquivS5 : (X⁵−4X+2).Gal ≃* Equiv.Perm (Fin 5)`). That is the *specialized*
  (ordinary IGP) picture for one $n$; the present roadmap gives the **generic/regular**
  picture for **all $n$** simultaneously via the function field.
- The 68‑file `AbelRuffini*` family supplies solvability/`Equiv.Perm` lemmas but the
  fixed‑field route here is self‑contained on top of `Mathlib/FieldTheory/Fixed.lean`.

## Status

- **Phase:** ORIENT (feasibility + full API‑cited roadmap; no verified Lean committed).
- **Build/verify blackout:** Docker build unavailable and Aristotle MCP returns 404
  ("Resource not found") this session, so no new `.lean` was added to the built
  `proofs/Proofs/` glob (avoids risking gallery CI with unverifiable code). A design
  draft lives at `GenericSnAnRealization.draft.lean` in this directory (non‑globbed).

## Sessions

### Session 2026-07-04 (Session 1) — ORIENT

**Mode:** FRESH · **Outcome:** progress (ORIENT roadmap)

**What I did**
- Surveyed the `AbelRuffini*` family (68 files); confirmed OQ‑01 realizes $S_5$
  concretely but no generic/all‑$n$ or $A_n$ realization exists.
- Read `Mathlib/FieldTheory/Fixed.lean`; identified `FixedPoints.toAlgAutMulEquiv`,
  `finrank_eq_card`, and the `Normal`/`IsSeparable`/`FiniteDimensional` instances as the
  complete abstract Artin engine.
- Reduced **both** $S_n$ and $A_n$ RIGP to one construction (perm action on
  $\mathbb{Q}(x_1,\dots,x_n)$ + Artin), and pinned the *single* missing piece to the
  perm `MulSemiringAction` on the fraction field (~150 lines, all API present:
  `renameEquiv`, `IsFractionRing.ringEquivOfRingEquiv`/`fieldEquivOfAlgEquiv`,
  `MulSemiringAction.compHom`, `RingAut` action).
- Noted the **regularity** observation (fixed fields purely transcendental over
  $\mathbb{Q}$) that makes these *regular* realizations, resolving the "R" in RIGP.

**Key findings**
- The Belyi/Thompson‑rigidity framing on the problem card is a red herring for the
  specific groups $S_n,A_n$; they have the elementary generic‑polynomial resolution.
- Artin's fixed‑field theorem in current Mathlib is strong enough to realize *any* finite
  group acting faithfully on a field — the whole difficulty is producing the concrete
  faithful action, here the variable‑permutation action on rational functions.

**Files**
- `research/problems/abel-ruffini-galois-extensions-oq-10/knowledge.md` (this file)
- `research/problems/abel-ruffini-galois-extensions-oq-10/GenericSnAnRealization.draft.lean`
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-10.json` (knowledge fields)

**Next steps**
1. When build/Aristotle access returns: implement `permToAutF` (monoid hom
   `Perm (Fin n) →* RingAut F`) and `FaithfulSMul`, then state `realizeSn`/`realizeAn`
   via `toAlgAutMulEquiv`; promote the draft into `proofs/Proofs/` and build.
2. Prove `[F:F^{S_n}] = n!` via `finrank_eq_card` + `Fintype.card_perm`.
3. Secondary: formalize regularity ($\mathbb{Q}$ algebraically closed in the fixed field)
   to upgrade "IGP" to "RIGP" explicitly.

### Session 2026-07-04 (Session 2) — ACT → COMPLETED

**Mode:** REVISIT (continuing Session 1 ORIENT) · **Outcome:** completed (verified, 0 sorry / 0 axiom)

**What I did**
- Promoted the Session-1 roadmap to a built proof: `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ10.lean` (157 lines), verified via Docker (`✔ Built ... (0 sorries)`).
- Found a cleaner path than the draft's hand-rolled `permAutF`/`permToAutF`: Mathlib already ships the **bundled** monoid hom `IsFractionRing.fieldEquivOfAlgEquivHom : (B ≃ₐ[A] B) →* (L ≃ₐ[K] L)` *with* an injectivity lemma. Composing it with `renamePermHom : Perm (Fin n) →* (P ≃ₐ[ℚ] P)` (built from `renameEquiv_refl`/`renameEquiv_trans`) killed the two `map_one`/`map_mul` sorries **and** both faithfulness sorries at once.
- Key instance realization: take the base fraction field `K = ℚ` itself (valid since `IsFractionRing ℚ ℚ` for a field), so the action lands in `F ≃ₐ[ℚ] F`, which carries the tautological faithful `AlgEquiv.applyMulSemiringAction`. `Algebra ℚ F` and `IsScalarTower ℚ P F` resolve as global instances (`FractionRing` transitivity).
- Applied Artin (`FixedPoints.toAlgAutMulEquiv`, `finrank_eq_card`) to get `realizeSn`, `realizeAn`, `isGalois_Sn/An`, `finrank_Sn = n!`, `finrank_An = |Aₙ|`.

**Two build-fix deltas (both mechanical)**
- `map_mul'`: `e * f` and `Equiv.trans f e` are propositionally but not defeq-equal ⟹ close with `congrArg (renameEquiv ℚ) (Equiv.ext fun _ => rfl)`.
- `renamePermHom_injective`: apply `MvPolynomial.X_injective` explicitly (the `simpa`-close hit a `↑`-coercion mismatch on the `Fin n` goal).

**Files**
- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ10.lean` (new, verified)
- `src/data/proofs/abel-ruffini-galois-extensions-oq-10/meta.json` (new gallery entry, status verified)
- draft `GenericSnAnRealization.draft.lean` removed (superseded by the built file)

**Scope honesty**
- Formalized: the **Galois-group realization** of Sₙ and Aₙ (isomorphism to `Gal` of the generic extension) + degrees. NOT separately formalized: the *regularity* claim (ℚ algebraically closed in the fixed field) that upgrades "IGP" to "RIGP" — a genuine optional follow-up; Mathlib has limited "regular extension" API.

**Next steps (optional follow-ups)**
1. Formalize regularity: `IsAlgClosed`-in / `algebraicClosure ℚ ∩ F^{Sₙ} = ℚ`, using that `F^{Sₙ} = ℚ(e₁,…,eₙ)` is purely transcendental.
2. Identify `F^{Sₙ}` explicitly with `ℚ(e₁,…,eₙ)` via `MvPolynomial.symmetricSubalgebra` / fundamental theorem of symmetric polynomials.
