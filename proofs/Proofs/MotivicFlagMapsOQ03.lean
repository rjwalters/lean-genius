import Proofs.MotivicFlagMaps

/-!
# Motivic Measures: Realization Functors out of K₀(Var)

This file lays down the **S2-A axiom-free core** of the realization-functor
framework scoped by `motivic-flag-maps-oq-03`:

  * `MotivicMeasure K R` — a ring homomorphism `K.carrier →+* R` together
    with a tagged image of the Lefschetz motive `K.L`.
  * `main_identity_propagates` — the BEMSV identity
    `[Ω²_β(Fl_{n+1})] = [GL_n × A^a]` propagates through any realization.
  * `annihilate_of_lefschetz_eq_one` — if `μ.lefschetz = 1`, then `μ` kills
    every `(K.L − 1)`-multiple. Combined with the S2-D divisibility
    `(K.L − 1) ∣ motivicClassBasedMaps K n β` (for `n ≥ 1`, in the parent
    file), this gives Euler-characteristic vanishing in the realization.

## Scope decisions

- **No realization instances** in this iteration. Constructing the
  Euler-characteristic ring hom (Bittner 2004) or the F_q point-counting
  ring hom (Grothendieck trace formula) requires Mathlib infrastructure
  that does not exist. Each instance would axiomatise existence + L-image
  for **+2 axioms each**. Deferred to S2-A2 (Euler) and S2-B (F_q).
- **+0 axioms in this file.** The S2-A PREP estimated `+4 axioms` for the
  two concrete realizations; landing only the structure + propagations
  keeps the framework axiom-free.

## Corrections incorporated from the S2c PREP audit (PR #18631)

- Use `import Proofs.MotivicFlagMaps` (the parent already pulls in
  `Mathlib`); do **not** cite the deprecated `Mathlib.Algebra.Ring.Hom.Basic`.
- Defer all `[Fact q.Prime]` / `Field (ZMod q)` synthesis questions to S2-B.
- Use direct `μ.toRingHom` projections in proofs (avoid the
  `CoeFun`-`rw [map_mul]` interaction noted in S2c PREP §4). The `CoeFun`
  instance is kept as user-facing sugar but is **not** used in any proof
  body in this file.

## Predecessors (all merged on `main`)

| Phase    | PR     | Researcher    | Date       |
|----------|--------|---------------|------------|
| S1 OBSERVE | #18299 | researcher-10 | 2026-05-12 |
| S2 PREP    | #18401 | researcher-6  | 2026-05-13 |
| S2-A PREP  | #18457 | researcher-6  | 2026-05-13 |
| S2 ACT     | #18524 | researcher-11 | 2026-05-13 |
| S2b PREP   | #18574 | researcher-4  | 2026-05-13 |
| S2c PREP   | #18631 | researcher-4  | 2026-05-13 |

## References

- Bryan–Elek–Manners–Salafatinos–Vakil (2025), arXiv:2601.07222.
- Parent file `Proofs.MotivicFlagMaps` — axiomatized BEMSV identity
  `motivic_class_flag_maps` plus the S2 ACT divisibility lemma
  `L_minus_one_dvd_motivicClassBasedMaps`.
-/

namespace MotivicFlagMaps

variable {k : Type*} [Field k]

/--
A **motivic measure** is a ring homomorphism out of the Grothendieck ring
of varieties, parametrised by the image of the Lefschetz motive `L = [A¹]`.

Concrete realizations of `K₀(Var_k)` all fit this pattern:

| Realization               | Target `R`    | `lefschetz` | `k`                                |
|---------------------------|---------------|-------------|------------------------------------|
| Euler characteristic      | `ℤ`           | `1`         | char-0 field (e.g. `ℂ`)            |
| Point count over `F_q`    | `ℤ`           | `q`         | `ZMod q` with `[Fact q.Prime]`     |
| Hodge–Deligne `E`-poly    | `ℤ[u,v]`     | `u·v`       | `ℂ`, smooth proper varieties only  |
| Poincaré polynomial       | `ℤ[t]`        | `t²`        | when the motive is pure Tate       |

The structure is **axiom-free**: it merely packages a ring hom together
with the value `μ K.L = lefschetz`. Concrete instances live in
downstream files (see scope decisions above).
-/
structure MotivicMeasure (K : GrothendieckRingVar k) (R : Type*) [CommRing R] where
  /-- The underlying ring homomorphism. -/
  toRingHom : K.carrier →+* R
  /-- The image of the Lefschetz motive `K.L`. -/
  lefschetz : R
  /-- The defining identity `μ K.L = lefschetz`. -/
  lefschetz_eq : toRingHom K.L = lefschetz

namespace MotivicMeasure

variable {K : GrothendieckRingVar k} {R : Type*} [CommRing R]

/-- Convenience coercion: write `μ x` instead of `μ.toRingHom x`.

This is **user-facing sugar only**. Proof bodies in this file use
`μ.toRingHom` directly to avoid the `CoeFun`/`rw [map_*]` fragility
noted in PR #18631 §4. -/
instance : CoeFun (MotivicMeasure K R) (fun _ => K.carrier → R) :=
  ⟨fun μ => μ.toRingHom⟩

/-- `μ K.L = μ.lefschetz` (as a `@[simp]` lemma — the `lefschetz_eq` field
in `simp`-friendly form). -/
@[simp]
lemma toRingHom_L (μ : MotivicMeasure K R) :
    μ.toRingHom K.L = μ.lefschetz :=
  μ.lefschetz_eq

/-- **Propagation 1 (`main_identity_propagates`).**

For any motivic measure `μ`, the BEMSV identity propagates from `K₀(Var)`
into the target ring:

  μ ⟦Ω²_β(Fl_{n+1})⟧ = μ ⟦GL_n × A^a⟧.

This is a one-line consequence of the axiomatized identity
`motivic_class_flag_maps` in `Proofs.MotivicFlagMaps`: any ring hom maps
equals to equals. -/
theorem main_identity_propagates
    (μ : MotivicMeasure K R) (n : ℕ) (hn : n ≥ 1)
    (β : HomologyClass n) (hβ : β.positive) :
    μ.toRingHom (motivicClassBasedMaps K n β) =
      μ.toRingHom (motivicClassGLnAffine K n (computeA β)) := by
  rw [motivic_class_flag_maps K n hn β hβ]

/-- **Propagation 2 (`annihilate_of_lefschetz_eq_one`).**

If `μ.lefschetz = 1`, then `μ` annihilates every `(K.L − 1)`-multiple in
`K.carrier`. The "Euler-characteristic vanishing" mechanism: any
realization sending `L ↦ 1` factors through the augmentation
`K.carrier / (K.L − 1)`. -/
theorem annihilate_of_lefschetz_eq_one
    (μ : MotivicMeasure K R) (hL : μ.lefschetz = 1)
    {x : K.carrier} (hx : (K.L - 1) ∣ x) :
    μ.toRingHom x = 0 := by
  obtain ⟨y, hy⟩ := hx
  rw [hy, map_mul, map_sub, map_one, μ.lefschetz_eq, hL]
  ring

/-- **Headline payoff: Euler-characteristic vanishing for moduli of based maps.**

Combining `S2-D` (`(K.L − 1) ∣ motivicClassBasedMaps K n β` for `n ≥ 1`,
proved in the parent file as `L_minus_one_dvd_motivicClassBasedMaps`)
with Propagation 2 above: every motivic measure with `μ.lefschetz = 1`
annihilates the class of `Ω²_β(Fl_{n+1})`.

Specialising `μ` to the Euler-characteristic realisation (`lefschetz = 1`),
this says `χ(Ω²_β(Fl_{n+1})) = 0` for `n ≥ 1` — recovering a classical
fact via the BEMSV motivic identity. The realization instance is
axiomatised separately in S2-A2. -/
theorem motivicClassBasedMaps_eq_zero_of_lefschetz_eq_one
    (μ : MotivicMeasure K R) (hL : μ.lefschetz = 1)
    (n : ℕ) (hn : n ≥ 1) (β : HomologyClass n) (hβ : β.positive) :
    μ.toRingHom (motivicClassBasedMaps K n β) = 0 :=
  μ.annihilate_of_lefschetz_eq_one hL
    (L_minus_one_dvd_motivicClassBasedMaps K n hn β hβ)

end MotivicMeasure

/-!
## S3: Universal witnesses — the hypothesis class is nonempty (axiom-free)

Every theorem above is conditional on a `MotivicMeasure K R`, and the
headline additionally assumes `μ.lefschetz = 1`. Since concrete
realizations (Euler characteristic, `F_q` point counts) are deferred by
design (+2 axioms each), **no instance of `MotivicMeasure` existed
anywhere in this development** — leaving the adversarial gap that the
headline vanishing theorem could be vacuously true.

This section closes that gap with **+0 axioms** via the canonical
universal witness: for any `c : K.carrier`, the quotient map

  `K.carrier →+* K.carrier ⧸ span {K.L − c}`

is a motivic measure sending `L` to the image of `c`. At `c = 1` this is
the *universal Euler-characteristic realization* — the augmentation
quotient through which every `lefschetz = 1` measure factors (proved
below as `factorThroughAugmentation`) — and it discharges the headline
hypothesis unconditionally (`universal_euler_vanishing`).

Degenerate models are permitted: for a `K` in which `K.L − 1` is a unit
the quotient is the zero ring and the vanishing is trivial. That is
unavoidable at this level of abstraction — `GrothendieckRingVar` is an
abstract interface — and harmless: for the *true* `K₀(Var_k)` the
augmentation quotient is the universal Euler-characteristic target, and
every concrete `lefschetz = 1` realization factors through it, so the
factorization theorem transfers the vanishing to every such realization.
-/

namespace MotivicMeasure

variable (K : GrothendieckRingVar k)

/-- **S3-A. The augmentation measure at `c`.** The quotient map
`K.carrier →+* K.carrier ⧸ span {K.L − c}` packaged as a `MotivicMeasure`
with `lefschetz` = image of `c`. This is the universal measure sending
`L ↦ c`, and the first `MotivicMeasure` instance constructed in this
development — axiom-free, for every model `K` and every `c`. -/
def augmentation (c : K.carrier) :
    MotivicMeasure K (K.carrier ⧸ Ideal.span {K.L - c}) where
  toRingHom := Ideal.Quotient.mk (Ideal.span {K.L - c})
  lefschetz := Ideal.Quotient.mk (Ideal.span {K.L - c}) c
  lefschetz_eq := Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton_self _)

/-- At `c = 1` the augmentation measure satisfies the headline hypothesis
`lefschetz = 1` on the nose. -/
@[simp]
lemma augmentation_one_lefschetz :
    (augmentation K 1).lefschetz = 1 :=
  map_one (Ideal.Quotient.mk (Ideal.span {K.L - 1}))

/-- **S3-B. Nonvacuity of the headline.** For every model `K` there is a
motivic measure with `lefschetz = 1`, so the hypothesis of
`motivicClassBasedMaps_eq_zero_of_lefschetz_eq_one` is satisfiable. -/
theorem nonempty_lefschetz_one :
    ∃ μ : MotivicMeasure K (K.carrier ⧸ Ideal.span {K.L - 1}),
      μ.lefschetz = 1 :=
  ⟨augmentation K 1, augmentation_one_lefschetz K⟩

variable {R : Type*} [CommRing R]

/-- **S3-C. Universal property of the augmentation quotient.** Every
motivic measure with `lefschetz = 1` factors through the `c = 1`
augmentation quotient: the induced ring hom on `K.carrier ⧸ (L − 1)`. -/
def factorThroughAugmentation (μ : MotivicMeasure K R)
    (hL : μ.lefschetz = 1) :
    (K.carrier ⧸ Ideal.span {K.L - 1}) →+* R :=
  Ideal.Quotient.lift _ μ.toRingHom fun _ ha =>
    μ.annihilate_of_lefschetz_eq_one hL (Ideal.mem_span_singleton.mp ha)

/-- The factorization identity: `factorThroughAugmentation μ hL ∘ mk = μ`.
So the augmentation measure is initial among `lefschetz = 1` measures. -/
@[simp]
lemma factorThroughAugmentation_mk (μ : MotivicMeasure K R)
    (hL : μ.lefschetz = 1) (x : K.carrier) :
    factorThroughAugmentation K μ hL
      ((augmentation K 1).toRingHom x) = μ.toRingHom x :=
  rfl

/-- **S3-D. Unconditional universal Euler-characteristic vanishing.**
The class of `Ω²_β(Fl_{n+1})` vanishes in the augmentation quotient
`K₀(Var)/(L − 1)` for all `n ≥ 1` — no realization hypothesis at all.
This upgrades the headline from a conditional statement (for every
measure with `lefschetz = 1` …) to a concrete identity in a concrete
ring; the conditional version is recovered by applying
`factorThroughAugmentation`. -/
theorem universal_euler_vanishing (n : ℕ) (hn : n ≥ 1)
    (β : HomologyClass n) (hβ : β.positive) :
    Ideal.Quotient.mk (Ideal.span {K.L - 1})
      (motivicClassBasedMaps K n β) = 0 :=
  motivicClassBasedMaps_eq_zero_of_lefschetz_eq_one (augmentation K 1)
    (augmentation_one_lefschetz K) n hn β hβ

end MotivicMeasure

end MotivicFlagMaps
