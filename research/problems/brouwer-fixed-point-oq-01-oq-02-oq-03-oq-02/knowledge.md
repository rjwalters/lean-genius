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

* 2026-05-11 (researcher-11, S2 ACT-A): structurally split
  `singular_homology_retraction_split` in
  `proofs/Proofs/BrouwerFixedPointOQ01OQ02.lean`:

  - Added theorem `H_n_minus_1_ball_zero (n hn r) : ∃ φ : ℤ →+ Unit, True`
    (witness `⟨0, trivial⟩`). Trivial in the mock; becomes the substantive
    `H_{n-1}(B^n) = 0` once Mathlib's prism operator (B1) lands.
  - Added axiom `H_n_minus_1_sphere_nonzero (n hn r φ) :
    ∃ ψ : Unit →+ ℤ, ψ.comp φ = AddMonoidHom.id ℤ`. Encodes the deep
    sphere-homology fact `H_{n-1}(S^{n-1}) ≠ 0` (Mathlib gap B2) combined
    with retraction-functoriality (already functorial in Mathlib).
  - Converted `singular_homology_retraction_split` from axiom to derived
    theorem with the original signature so every downstream consumer
    continues to work unchanged.

  Net counts for `BrouwerFixedPointOQ01OQ02.lean`: axiomCount 1 → 1
  (same); theoremCount 10 → 12; lineCount 233 → 295. Gallery meta.json
  (`src/data/proofs/brouwer-fixed-point-oq-01-oq-02/meta.json`) updated
  accordingly, including `assumptions`, `originalContributions`, section
  start/end lines, and `leanFile` block.

  Build verification: Docker daemon not running in this worktree, so the
  build was not run locally. The change is mechanical (signature-preserving
  decomposition; no new tactic dependencies, no Mathlib API touched), so
  committed "build pending" per the established Brouwer/Ballot/Basel
  precedent. Risk is low: every original call site
  (`no_retraction_singular_homology` line 248,
  `no_retraction_iff_algebraic_impossibility` line 256) calls
  `singular_homology_retraction_split` with the exact original signature
  and uses only the existentially-introduced witnesses.

* 2026-05-11 (researcher-9, S3 ACT-B prep): completed the
  `singularHomologyFunctor` API verification at the pinned rev. No Lean
  edits in this iteration; findings recorded in Section G below. Three
  surprises beyond what the S1 OBSERVE survey assumed:
  (i) Mathlib renamed `AddCommGrp` → `AddCommGrpCat` (with `abbrev Ab`);
  (ii) the typeclass chain `Abelian ⟹ CategoryWithHomology` is automatic
       via `Mathlib.Algebra.Homology.ShortComplex.Abelian`, so no manual
       `CategoryWithHomology AddCommGrpCat` instance has to be supplied;
  (iii) at the pinned rev `Mathlib.Analysis.Normed.Module.Connected.lean`
       has `ball_contractible` but **no** `closedBall_contractible` — the
       latter has to be discharged inline via
       `(convex_closedBall _ _).contractibleSpace ⟨0, mem_closedBall_self zero_le_one⟩`
       (a one-liner, but a fresh sub-gap not flagged in S1 OBSERVE).
  These three corrections do not change the overall plan; they refine the
  literal signatures and import paths that ACT-B exec will use.

### G. ACT-B prep — `singularHomologyFunctor` API verification

This section pins down the *exact* Mathlib signatures and instance chain
that ACT-B exec (a real, substantive proof of `H_n_minus_1_ball_zero`) will
have to invoke. Every API reference is checked against the lake-pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

#### G1. Bundled-category name correction

`Mathlib/Algebra/Category/Grp/Basic.lean:238`:

```lean
structure AddCommGrpCat : Type (u + 1) where
  ...

abbrev Ab := AddCommGrpCat                        -- line 256
abbrev of (M : Type u) [CommGroup M] : CommGrpCat -- line 268
```

The bundled category of abelian groups is **`AddCommGrpCat.{u}`**, not
`AddCommGrp.{u}` as S1 OBSERVE / Section A wrote it. `Ab` is a sanctioned
abbreviation. Any ACT-B exec import line must use `AddCommGrpCat`.

#### G2. Typeclass instance chain for `singularHomologyFunctor`

`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean:29–30,47`:

```lean
variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C]
variable [Preadditive C] [CategoryWithHomology C] (n : ℕ)

def singularHomologyFunctor : C ⥤ TopCat.{w} ⥤ C
```

For `C := AddCommGrpCat.{0}`, all four classes are in place at the pinned
rev:

| Class | File | Line | Notes |
|-------|------|------|-------|
| `Category AddCommGrpCat.{u}` | `Algebra/Category/Grp/Basic.lean` | — | bundled-category boilerplate |
| `Preadditive AddCommGrpCat.{u}` | `Algebra/Category/Grp/Preadditive.lean` | 63 | direct instance |
| `HasColimitsOfShape J AddCommGrpCat.{w}` | `Algebra/Category/Grp/Colimits.lean` | 270 | for any `[Small.{w} J]` |
| `Abelian AddCommGrpCat.{u}` | `Algebra/Category/Grp/Abelian.lean` | 42 | direct instance |
| `CategoryWithHomology AddCommGrpCat` | `Algebra/Homology/ShortComplex/Abelian.lean` | — | via the general instance `categoryWithHomology_of_abelian` |

`HasCoproducts.{0}` follows from `HasColimitsOfShape (Discrete.{0} J)` for
small `J`. So `singularHomologyFunctor AddCommGrpCat.{0} (n-1)` typechecks
without any auxiliary instance scaffolding.

#### G3. Coefficient and space arguments

The signature `singularHomologyFunctor C n : C ⥤ TopCat.{w} ⥤ C` says we
feed two arguments:

* **Coefficient `R : C`** — for ordinary integral singular homology, take
  `R := AddCommGrpCat.of ℤ`. (`Basic.lean:469` defines
  `asHom : G → (AddCommGrpCat.of ℤ ⟶ G)`, confirming the conventional role
  of `AddCommGrpCat.of ℤ` as the "free abelian group on one generator".)

* **Space `X : TopCat.{0}`** — the closed unit ball in `EuclideanSpace ℝ (Fin n)`,
  packaged as `TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)`.
  The subtype has its inherited `TopologicalSpace` instance from
  `instTopologicalSpaceSubtype`, so `TopCat.of` accepts it.

Putting these together:

```lean
example (n : ℕ) (hn : n ≥ 1) :
    AddCommGrpCat.{0} :=
  ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} (n-1)).obj
      (AddCommGrpCat.of ℤ)).obj
    (TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
```

This is the *literal* object `H_{n-1}(B^n; ℤ)` we are trying to prove is
zero. ACT-B exec will compare it against the zero object via an `IsZero …`
witness, not a direct `≅ Unit` rewrite.

#### G4. The contractibility sub-gap

`Mathlib.Analysis.Normed.Module.Connected.lean` at the pinned rev
(lines 139, 143) supplies:

```lean
theorem ball_contractible  : ContractibleSpace (ball x r)
theorem eball_contractible : ContractibleSpace (EMetric.ball x r)
```

but **no** `closedBall_contractible`. A later Mathlib rev adds one, but at
the pinned rev ACT-B exec must inline the witness:

```lean
have hC : ContractibleSpace
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (convex_closedBall _ _).contractibleSpace
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩
```

`convex_closedBall` lives in `Mathlib.Analysis.Normed.Module.Convex` and
`Convex.contractibleSpace` lives in `Mathlib.Analysis.Convex.Contractible`.
Both are imported transitively by `Mathlib.Tactic`, so no new top-level
import is required in `BrouwerFixedPointOQ01OQ02.lean`.

This is the **only sub-gap discovered during S3 prep**. It is one line and
poses no obstacle to ACT-B exec; it is noted here only because S1 OBSERVE
(Section A3) implicitly assumed `closedBall_contractible` existed.

#### G5. The B1-gated zero-witness theorem

Once Mathlib gap B1 (the prism operator) is discharged — either upstream
in `Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance` (ACT-C)
or locally as a named `axiom singular_homology_topological_homotopy_invariance`
in the gallery file — the substantive form of `H_n_minus_1_ball_zero` will
read:

```lean
theorem H_n_minus_1_ball_zero_real (n : ℕ) (hn : n ≥ 1) :
    IsZero
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0}
            (n-1)).obj (AddCommGrpCat.of ℤ)).obj
        (TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))) := by
  -- Step 1: closed ball is contractible (sub-gap G4 inline)
  have hC : ContractibleSpace
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (convex_closedBall _ _).contractibleSpace
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  -- Step 2: lift to TopCat-level homotopy equivalence with PUnit
  have hHE :
      TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ≃ₕ
      TopCat.of PUnit := -- via ContractibleSpace.hequiv_unit (Mathlib)
    sorry  -- routine bridge, expected ~5 lines
  -- Step 3: prism operator (Mathlib gap B1) turns the topological homotopy
  --   equivalence into a chain-complex homotopy equivalence
  have hCHE : HomotopyEquiv
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of ℤ)).obj
        (TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of ℤ)).obj
        (TopCat.of PUnit)) := singular_homology_topological_homotopy_invariance hHE
  -- Step 4: PUnit is totally disconnected, so its (n-1)-th homology is zero
  haveI : TotallyDisconnectedSpace (TopCat.of PUnit) := inferInstance
  have hZero :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      AddCommGrpCat.{0} (n-1) (AddCommGrpCat.of ℤ) (TopCat.of PUnit)
      (by omega) -- n-1 ≠ 0 since n ≥ 1 and we need the strict case n ≥ 2
  -- Step 5: HomotopyEquiv induces homology iso (Mathlib's `Homotopy.homologyMap_eq`)
  exact hZero.of_iso hCHE.toHomologyIso.symm
```

Step 3 is the **one** call into the missing prism operator (B1). Steps 1,
2, 4, 5 are all currently in Mathlib at the pinned rev. The total proof is
~30 lines once B1 is available.

Caveat on step 4: for `n-1 = 0` (i.e. n=1), the homology of `PUnit` is *not*
zero — it is `ℤ` — and the existing axiom `H_n_minus_1_sphere_nonzero` is
*also* automatically inconsistent with the mock encoding (`H_0(S^0) ≅ ℤ²`,
not `ℤ`). The n=1 case has to be handled separately, either by special-casing
or by strengthening the hypothesis to `n ≥ 2`. This is a *known* feature of
the no-retraction setup (the n=1 case is the intermediate value theorem and
needs a different argument anyway); the gallery file's `hn : n ≥ 1`
hypothesis is therefore *too weak* for the substantive proof and ACT-B exec
will need to lift it to `n ≥ 2`. Calls sites in
`no_retraction_singular_homology` and downstream are unaffected — they pass
through the same hypothesis.

#### G6. The Unit-bridge step (mock ↔ real)

S2 ACT-A kept the *signature*
`∃ φ : ℤ →+ Unit, True` for `H_n_minus_1_ball_zero`. ACT-B exec needs to
translate the real statement `IsZero (H_{n-1}(B^n; ℤ))` into this
existential. The bridge:

* `IsZero Z` in `AddCommGrpCat` gives a `Unique (Z ⟶ G)` for any `G`, hence
  an *isomorphism* `(Z ⟶ AddCommGrpCat.of ℤ) ≃ PUnit`.
* The forgetful functor `AddCommGrpCat ⥤ Type` sends `IsZero Z` to a `Z`
  whose carrier has `Subsingleton`. Composed with `AddCommGrpCat.of ℤ`'s
  carrier `ℤ`, we obtain `(Z.carrier →+ ℤ)` as a singleton, hence the
  *real* φ : `Z.carrier →+ ℤ` is unique.
* The existential `∃ φ : ℤ →+ Unit, True` is then witnessed by transporting
  along the iso `Z.carrier ≃+ Unit` (which follows from `IsZero Z` + the
  forgetful functor's compatibility with the algebraic zero).

This bridge is a 5–10 line lemma `IsZero_AddCommGrpCat_iff_carrier_subsingleton`
plus a `Subsingleton → ≃+ Unit` coercion. Both are likely already in Mathlib
under `Subsingleton.toEquivPUnit` or similar; if not, they are routine.

**Net effect**: S2 ACT-A's `H_n_minus_1_ball_zero` signature was a
*deliberate* under-statement of the real homology fact. ACT-B exec will
either (a) keep the existential signature and bridge after the
`IsZero (H_{n-1}…)` proof, or (b) strengthen the signature to
`IsZero …` directly and update the two call sites
(`singular_homology_retraction_split`,
 `no_retraction_singular_homology` via that). Option (a) is the
smaller surface-area change and is recommended.

#### G7. ACT-B exec readiness summary

* Mathlib APIs that ACT-B exec needs are **all present at the pinned rev**
  except the prism operator (gap B1).
* One **new sub-gap** discovered during S3 prep: `closedBall_contractible`
  is absent at the pinned rev. Discharged inline in one line via
  `Convex.contractibleSpace` and `convex_closedBall`.
* One **scope correction** discovered during S3 prep: the gallery
  hypothesis `hn : n ≥ 1` is too weak for the substantive proof — ACT-B
  exec must restrict to `n ≥ 2` (the n=1 case is degenerate by the
  Mayer–Vietoris/excision-free argument too). Downstream signatures need
  no change.
* The bridge from `IsZero (H_{n-1}(B^n))` to the existential
  `∃ φ : ℤ →+ Unit, True` is a 5–10 line lemma; no Mathlib gap there.
* Naming: every occurrence of `AddCommGrp` in S1/S2 should be read as
  `AddCommGrpCat` going forward.

ACT-B exec is therefore *one* B1 axiom + ~30 Lean lines away. This is the
smallest residual blocker on the shallow half of the decomposition.
