# Knowledge: brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02

## S1 OBSERVE — Mathlib feasibility survey for `singular_homology_retraction_split`

Survey was carried out against Mathlib rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(pinned in `proofs/lake-manifest.json`, toolchain `v4.26.0`).

### A. What Mathlib *already* provides

#### A1. Singular chain complex & singular homology functors

`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` (introduced 2025, Andrew Yang):

```lean
def SSet.singularChainComplexFunctor :
    C ⥤ SSet.{w} ⥤ ChainComplex C ℕ := ...

def singularChainComplexFunctor :
    C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ :=
  SSet.singularChainComplexFunctor.{w} C ⋙
    (Functor.whiskeringLeft _ _ _).obj TopCat.toSSet.{w}

def singularHomologyFunctor : C ⥤ TopCat.{w} ⥤ C :=
  singularChainComplexFunctor C ⋙
    (Functor.whiskeringRight _ _ _).obj
      (HomologicalComplex.homologyFunctor _ _ n)
```

Coefficients live in any preadditive category `C` with the right limits; choose
`C := AddCommGrp` and `R := ℤ` to recover ordinary integral singular homology.

The file also proves:

* `singularChainComplexFunctorIsoOfTotallyDisconnectedSpace`: for totally
  disconnected `X`, `C_*(X; R) ≅ R[X] ← 0 ← R[X] ← 𝟙 ← R[X] ← 0 ← ⋯`
  (alternating constant complex).
* `singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace`
  (and corollary `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`):
  `H_n(X) = 0` for totally disconnected `X` and `n ≠ 0`.
* `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`:
  `H_0(X) ≅ ⊕_{x ∈ X} R` for totally disconnected `X`.

**Specializing to a point** (`X := PUnit`), this gives `H_n(*) = 0` for `n ≥ 1`
and `H_0(*) ≅ R`. So step **S3** of the elimination is one corollary away.

#### A2. Chain-homotopy → homology invariance

`Mathlib/Algebra/Homology/Homotopy.lean:808`:

```lean
lemma Homotopy.homologyMap_eq (ho : Homotopy f g) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    homologyMap f i = homologyMap g i := ...

noncomputable def HomotopyEquiv.toHomologyIso (h : HomotopyEquiv K L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    K.homology i ≅ L.homology i := ...
```

Chain-homotopy equivalent complexes have isomorphic homology in every degree.

#### A3. Convex sets are contractible

`Mathlib/Analysis/Convex/Contractible.lean`:

```lean
protected theorem StarConvex.contractibleSpace
    (h : StarConvex ℝ x s) (hne : s.Nonempty) :
    ContractibleSpace s

protected theorem Convex.contractibleSpace
    (hs : Convex ℝ s) (hne : s.Nonempty) :
    ContractibleSpace s
```

And `Mathlib/Analysis/Normed/Module/Connected.lean:140` applies this to the
closed metric ball: `convex_ball _ _` plus nonemptiness gives `ContractibleSpace`.

So the closed unit ball `Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1`
is contractible by an off-the-shelf Mathlib lemma. Step **S4** is essentially
free.

#### A4. Topological homotopy / nullhomotopy infrastructure

`Mathlib/Topology/Homotopy/Contractible.lean`:

* `ContractibleSpace.hequiv_unit : ContractibleSpace X → X ≃ₕ Unit`
* `Nullhomotopic` (predicate on `C(X, Y)`) and basic composition lemmas
* `ContractibleSpace_iff_id_nullhomotopic`

So `B^n ≃ₕ Unit` is in hand.

### B. Where Mathlib has gaps

#### B1. Topological → chain homotopy bridge (the *prism operator*)

The single largest gap is the construction that sends a **topological homotopy**
`H : C(X × I, Y)` between `f, g : X → Y` to a **chain homotopy**
`P : C_*(X) → C_*(Y) of degree +1` between `singularChainMap f` and
`singularChainMap g`.

Searches at the pinned revision returned **no matches** for:
* `MayerVietoris` (any spelling)
* `excision`
* `homotopyInvariance` / `homotopy.invariance`
* `Sphere.*ContractibleSpace` (Mathlib has no sphere-homotopy/homology link)
* Any prism / cone construction in `Mathlib.AlgebraicTopology.SingularHomology`

This is the **prism operator**: for each `n`, define
`P_n : C_n(X) → C_{n+1}(Y)` on a singular `n`-simplex
`σ : Δ^n → X` by `(P_n σ)(t_0, …, t_{n+1}) = H(σ(s), τ)`, where `(s, τ)`
is a standard simplicial decomposition of `Δ^n × I`. The standard formula is

P_n(σ) = Σ_{i=0}^{n} (-1)^i · (H ∘ (σ × id) ∘ Δ_i^n)

where `Δ_i^n : Δ^{n+1} → Δ^n × I` runs through the (n+1)-simplices of the
prism `Δ^n × I`. Verifying `∂P + P∂ = g_♯ - f_♯` is mechanical but bulky
(~100–300 lines depending on how much of `SimplicialObject`/`AlternatingFaceMapComplex`
is reused).

**This is the natural Mathlib contribution** that would unblock S2 → S5.

#### B2. A specific generator of `H_{n-1}(S^{n-1})`

Even with S2 in hand, the axiom requires `H_{n-1}(S^{n-1}) ≅ ℤ` (or at least a
non-trivial class). Mathlib at the pinned rev has **no** computation of sphere
homology. Three feasible routes:

* **B2a. Mayer–Vietoris / excision.** Standard textbook route; would require
  formalizing excision in the singular chain complex (a multi-month project).
* **B2b. Suspension isomorphism + `H_0(S^0) ≅ ℤ²`.** Reduces to `H_0` of two
  points (a totally-disconnected space already in A1), but needs the suspension
  isomorphism `H_n(ΣX) ≅ H_{n-1}(X)`, which itself requires either Mayer–Vietoris
  or a direct simplicial decomposition.
* **B2c. Direct construction.** Build an explicit `(n-1)`-cycle on `S^{n-1}`
  using a triangulation (e.g. the boundary of the standard `n`-simplex) and
  exhibit it as non-bounding. This is concrete but n-dependent and requires
  proving cycles in `S^{n-1}` are not boundaries — essentially the same
  computation as B2a in disguise.

#### B3. Functoriality with continuous maps

Mathlib's `singularChainComplexFunctor C : C ⥤ TopCat ⥤ ChainComplex C ℕ`
is genuinely functorial on `TopCat`, so `r* ∘ i* = (r ∘ i)*` is automatic
once a chain-level homology functor is applied. **No gap here**; this is the
reason the axiom only had to package S1 and S2.

### C. Implications for axiom elimination

The current axiom asserts the existence of a split `ψ ∘ φ = id : ℤ →+ Unit →+ ℤ`
arising from a hypothetical retraction. The honest decomposition is:

```
    H_{n-1}(S^{n-1}) ──ι*──▶ H_{n-1}(B^n) ──r*──▶ H_{n-1}(S^{n-1})
       \____________________ id ____________________/
```

With (A1) + (A2) + (A3) + (A4) + (B1) but **without** (B2), we can prove
`H_{n-1}(B^n) = 0` and `id = r* ∘ ι*` factors through `H_{n-1}(B^n)`,
so `id` on `H_{n-1}(S^{n-1})` is the zero map. This implies
`H_{n-1}(S^{n-1}) = 0` — a *non-trivial conclusion that is still strong
enough to refute the existence of a retraction provided we know
`H_{n-1}(S^{n-1}) ≠ 0`*. So:

* **(B1) alone unlocks a "weak" reduction.** The axiom becomes
  `H_{n-1}(S^{n-1}) ≠ 0`. That is still an axiom, but it is the *standard*
  computational axiom and is structurally cleaner than the current split-form.
* **(B1) + (B2) gives a fully axiom-free proof.**

### D. Suggested ACT-phase plan (post-OBSERVE)

The cleanest near-term increment (1–3 sessions) is:

1. **ACT-A**: replace `singular_homology_retraction_split` with two narrower
   axioms `H_{n-1}_sphere_nonzero` (the missing piece B2) and
   `H_{n-1}_ball_zero` (provable from B1 + A3 + A4), keeping the gallery's
   no-retraction proof working without B1 in hand. This **does not reduce
   total axiom count** but cleanly separates the missing-Mathlib-infra
   assumption (B2) from the can-be-proved-now part (S5).
2. **ACT-B**: instantiate `singularHomologyFunctor` at `C := AddCommGrp.{0}`,
   `R := ℤ`, and prove
   `H_{n-1}_ball_zero` from `Convex.contractibleSpace` + (B1, deferred) +
   `singularHomologyFunctorZeroOfTotallyDisconnectedSpace` applied to
   `PUnit`. The B1 step can be axiomatized as a *named* assumption
   `singular_homology_topological_homotopy_invariance` while the structural
   reduction proceeds.
3. **ACT-C (Mathlib)**: implement the prism operator inside
   `Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance` (new file).
   This is a self-contained PR with no upstream dependencies. Once landed,
   ACT-B's named assumption discharges automatically.

### E. References

* Mathlib v4.26.0 `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`
* Mathlib v4.26.0 `Mathlib/Algebra/Homology/Homotopy.lean` (esp. `Homotopy.homologyMap_eq`)
* Mathlib v4.26.0 `Mathlib/Analysis/Convex/Contractible.lean`
* Mathlib v4.26.0 `Mathlib/Topology/Homotopy/Contractible.lean`
* Hatcher, *Algebraic Topology*, §2.1 (prism operator proof of homotopy invariance, p. 111–113)
* Hatcher, *Algebraic Topology*, §2.1, Theorem 2.13 (sphere homology computation)
* Bredon, *Topology and Geometry*, §IV.16 (Mayer–Vietoris in singular homology)

### F. Iteration log

* 2026-05-11 (researcher-12, S1 OBSERVE): completed Mathlib feasibility survey;
  classified the axiom into three subgoals; identified the *prism operator* as
  the single missing structural ingredient; sketched a 3-step ACT plan.
  No Lean changes in this iteration.
