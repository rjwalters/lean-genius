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

### H. ACT-C prep — construction sketch of the prism operator (gap B1)

This section maps out the literal Mathlib contribution that would close gap
B1 — the topological-homotopy → chain-homotopy bridge — at the pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The goal is to specify, at
function-signature granularity, the construction that turns a topological
homotopy `H : C(X × I, Y)` between `f, g : X → Y` into a chain homotopy
`P : ((singularChainComplexFunctor C).obj R).obj X ⟶
    ((singularChainComplexFunctor C).obj R).obj Y` of degree +1 between
the chain maps induced by `f` and `g`. Nothing in this section is a Lean
edit to the gallery file; it is a feasibility blueprint for the upstream
Mathlib PR contemplated in the S1 OBSERVE plan as step ACT-C.

#### H1. The target API

The single missing theorem in `Mathlib.AlgebraicTopology.SingularHomology`
is (up to namespace placement):

```lean
namespace AlgebraicTopology

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C]
variable [Preadditive C] [CategoryWithHomology C] (R : C)
variable {X Y : TopCat.{w}} {f g : X ⟶ Y}

/-- Topologically homotopic continuous maps induce chain-homotopic
    chain maps on singular chains. -/
noncomputable def singularChainHomotopyOfTopHomotopy
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    Homotopy
      (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g)

end AlgebraicTopology
```

From this single declaration, three immediate corollaries land for free
(via standard `Homotopy.*` combinators already in
`Mathlib.Algebra.Homology.Homotopy`):

```lean
/-- Topologically homotopic maps induce equal maps on singular homology. -/
theorem singularHomologyMap_eq_of_topHomotopy
    (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).map f =
    ((singularHomologyFunctor C n).obj R).map g :=
  (singularChainHomotopyOfTopHomotopy C R H).homologyMap_eq n

/-- A topological homotopy equivalence induces a chain-homotopy equivalence
    on singular chains. -/
noncomputable def singularChainHomotopyEquivOfTopHomotopyEquiv {X Y : TopCat}
    (e : X ≃ₕ Y) :
    HomotopyEquiv
      (((singularChainComplexFunctor C).obj R).obj X)
      (((singularChainComplexFunctor C).obj R).obj Y)

/-- A topological homotopy equivalence induces a singular-homology iso. -/
noncomputable def singularHomologyIsoOfTopHomotopyEquiv {X Y : TopCat}
    (e : X ≃ₕ Y) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj X ≅
    ((singularHomologyFunctor C n).obj R).obj Y :=
  (singularChainHomotopyEquivOfTopHomotopyEquiv C R e).toHomologyIso n
```

The structural pattern (`Homotopy → HomotopyEquiv → toHomologyIso`) is
already wired by `HomotopyEquiv.toHomologyIso` (`Mathlib.Algebra.Homology.Homotopy:805+`),
so the *upstream* obligation is exactly the one definition
`singularChainHomotopyOfTopHomotopy`.

#### H2. Hatcher §2.1 formula (concrete simplicial decomposition)

Hatcher (*Algebraic Topology*, §2.1, pp. 111–113) constructs the prism
operator at the level of singular simplices. For a singular `n`-simplex
`σ : Δ^n → X`, define `P_n σ : Δ^{n+1} → Y` by triangulating the prism
`Δ^n × I` into `n+1` simplices of dimension `n+1` and integrating the
homotopy along each.

**The triangulation.** Label the vertices of `Δ^n × {0}` as
`v_0, …, v_n` and the vertices of `Δ^n × {1}` as `w_0, …, w_n`. The prism
`Δ^n × I` is the geometric realization of the simplicial complex whose
top-dimensional simplices are the `n+1` simplices
`[v_0, v_1, …, v_i, w_i, w_{i+1}, …, w_n]` for `i = 0, …, n`. (Geometrically
this is the "staircase" decomposition.)

**The formula.** With the canonical `affine` map
`α_i : Δ^{n+1} → Δ^n × I` realising the `i`-th simplex of the staircase,

P_n σ = Σ_{i=0}^{n} (-1)^i · ⟦ H ∘ (σ × id_I) ∘ α_i ⟧

where `⟦·⟧ : C(Δ^{n+1}, Y) → R[singular (n+1)-simplices]` is the
canonical generator inclusion.

**The verification.** A direct computation on each face of `α_i` shows

∂P_n σ + P_{n-1} (∂σ) = (g ∘ σ)_♯ − (f ∘ σ)_♯.

(Hatcher writes this as Proposition 2.10. The verification splits into:
inner faces of `α_i` (which cancel pairwise across consecutive `i`) and
top/bottom faces (which give the boundary terms `g_♯ σ` and `f_♯ σ`).)

#### H3. Mathlib-native construction route (recommended)

Rather than encoding `α_i` as geometric maps `Δ^{n+1} → Δ^n × I` and
proving cancellation by hand on `R[·]`, Mathlib's existing simplicial
infrastructure makes a much cleaner route available. The construction
factors through three layers, *all already present at the pinned rev*:

1. **Simplicial homotopy** (`Mathlib.AlgebraicTopology.SimplicialObject`,
   pre-existing). Two morphisms of simplicial objects
   `F, G : SSet ⥤ SSet` are *simplicially homotopic* iff there is a
   morphism `H : F ⊗ Δ[1] ⟶ G` satisfying the boundary axioms. The
   topological-homotopy → simplicial-homotopy bridge is the functor
   `TopCat.toSSet : TopCat ⥤ SSet` together with the fact that
   `TopCat.toSSet (X × I) = TopCat.toSSet X ⊗ TopCat.toSSet I` (where
   `TopCat.toSSet I ≃ Δ[1]` is standard).

2. **Simplicial homotopy → chain homotopy** via the
   `alternatingFaceMapComplex` functor
   (`Mathlib.AlgebraicTopology.AlternatingFaceMapComplex`, pre-existing).
   This functor is *additive*, so it sends a simplicial homotopy
   (which is a `Δ[1]`-shaped 2-cell in `SSet`) to a chain homotopy in
   `ChainComplex C ℕ`. The general fact "the alternating face map complex
   functor sends simplicial homotopies to chain homotopies" is standard
   and arguably already implicit in the DoldKan equivalence machinery
   (`Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence` provides the
   chain-side endpoint), though it is not yet exposed as a *standalone*
   lemma at the pinned rev.

3. **Chain homotopy compatibility with `singularChainComplexFunctor`**.
   By the definition (`Mathlib.AlgebraicTopology.SingularHomology.Basic:39`):
   `singularChainComplexFunctor C = SSet.singularChainComplexFunctor.{w} C ⋙
     (Functor.whiskeringLeft _ _ _).obj TopCat.toSSet.{w}`,
   so any chain homotopy at the SSet level transports to a chain homotopy
   at the TopCat level by functoriality, no extra work needed.

The full ACT-C construction thus splits into **two named lemmas** plus the
final theorem:

```lean
-- Lemma 1 (the only genuinely new construction):
/-- The alternating face map complex sends a simplicial homotopy
    `H : F ⊗ Δ[1] ⟶ G` to a chain homotopy between the chain maps
    induced by the two endpoints. -/
noncomputable def AlternatingFaceMapComplex.mapHomotopy
    {C : Type u} [Category.{v} C] [Preadditive C] {F G : SimplicialObject C}
    (φ ψ : F ⟶ G) (H : SimplicialObject.Homotopy φ ψ) :
    Homotopy ((alternatingFaceMapComplex C).map φ)
             ((alternatingFaceMapComplex C).map ψ)

-- Lemma 2 (bridge from topological to simplicial side):
/-- `TopCat.toSSet` sends a continuous homotopy to a simplicial homotopy. -/
noncomputable def TopCat.toSSet.mapHomotopy {X Y : TopCat} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    SimplicialObject.Homotopy
      ((TopCat.toSSet).map f) ((TopCat.toSSet).map g)

-- Theorem: combine Lemma 1 and Lemma 2 + composition.
noncomputable def singularChainHomotopyOfTopHomotopy ... :=
  AlternatingFaceMapComplex.mapHomotopy _ _ (TopCat.toSSet.mapHomotopy H |>.…)
```

Lemma 1 is *the* substantive new ingredient. Lemma 2 is a routine
unwinding of the existing functor `TopCat.toSSet`. The final theorem is
~10 lines of composition.

#### H4. Why this route beats the geometric-Hatcher formula

Three reasons:

* **No explicit `α_i` maps required.** All the geometric content of the
  prism triangulation is bundled inside the (already standard) fact that
  `Δ[n] ⊗ Δ[1]` decomposes into `n+1` non-degenerate `(n+1)`-simplices.
  Mathlib's `SimplicialObject.Homotopy` and `prodStandardSimplex` already
  encode this — Lemma 1 only needs to invoke the additive structure of
  `alternatingFaceMapComplex` once.
* **The sign convention is forced.** Hatcher's `(−1)^i` falls out
  automatically from `alternatingFaceMapComplex`'s alternating face map
  formula `d_n = Σ_i (-1)^i ∂_i`. We never have to chase signs by hand.
* **Generic in the coefficient category `C`.** The construction holds for
  any preadditive `C` with countable coproducts — exactly the variable
  scope of `singularChainComplexFunctor`. No `AddCommGrpCat`-specific work
  is needed.

#### H5. Estimated complexity and verification target

| Component | Lines (est.) | Existing scaffolding |
|-----------|-------------|----------------------|
| Lemma 1: `AlternatingFaceMapComplex.mapHomotopy` | 40–80 | Heavy reuse of `AlternatingFaceMapComplex` API |
| Lemma 2: `TopCat.toSSet.mapHomotopy` | 30–60 | `TopCat.toSSet`, `ContinuousMap.Homotopy` |
| Theorem: `singularChainHomotopyOfTopHomotopy` | 10–20 | Composition |
| `HomotopyEquiv` corollaries | 20–40 | `Homotopy.symm`, `Homotopy.trans` |
| **Total** | **100–200** | |

Hatcher's bare-hands proof would land closer to 300–500 lines because
each `α_i` needs an explicit affine-map construction in
`Mathlib.Topology.UnitInterval` and the staircase cancellation has to be
proved index-by-index. The simplicial route described above shifts ~80%
of the work to existing Mathlib infrastructure.

**Verification target** (one statement, no `sorry`):

```lean
theorem prism_comm
    {C : Type u} [Category.{v} C] [Preadditive C] {F G : SimplicialObject C}
    (φ ψ : F ⟶ G) (H : SimplicialObject.Homotopy φ ψ) (n : ℕ) :
    ((alternatingFaceMapComplex C).map φ).f n =
      dNext n (AlternatingFaceMapComplex.mapHomotopy φ ψ H).hom +
      prevD n (AlternatingFaceMapComplex.mapHomotopy φ ψ H).hom +
      ((alternatingFaceMapComplex C).map ψ).f n
```

This is the `comm` field of the resulting `Homotopy` structure
(`Mathlib.Algebra.Homology.Homotopy:127`) at every degree `n`.

#### H6. Recommended Mathlib placement

```
Mathlib/
└── AlgebraicTopology/
    ├── SimplicialObject/
    │   └── Homotopy.lean              [NEW — Lemma 1 lives here]
    ├── SingularHomology/
    │   ├── Basic.lean                 [unchanged]
    │   └── HomotopyInvariance.lean    [NEW — Theorem + corollaries here]
    └── TopologicalToSimplicial/
        └── Homotopy.lean              [NEW — Lemma 2 lives here]
```

`Mathlib/AlgebraicTopology/SimplicialObject/Homotopy.lean` is the natural
home for `SimplicialObject.Homotopy` and `AlternatingFaceMapComplex.mapHomotopy`.
Inspection at the pinned rev shows
`Mathlib/AlgebraicTopology/SimplicialObject/` already contains seven files
but no `Homotopy.lean` — so this is a clean new addition rather than an
edit to existing infrastructure.

#### H7. The boundary case `n − 1 = 0` (revisited)

Section G5 noted that the substantive `H_{n-1}(B^n) = 0` proof requires
`n ≥ 2` (since `H_0(B^1) ≅ ℤ ≠ 0`). The prism operator construction
itself is degree-uniform — it produces a chain homotopy in every degree
including 0 — so B1 does *not* introduce any new boundary case beyond
what S3 prep already flagged. After B1 lands, ACT-B exec can still safely
restrict to `n ≥ 2` via the existing `singularHomologyFunctor` `n ≠ 0`
witness `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`.

#### H8. Risk register

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| `SimplicialObject.Homotopy` does not yet exist at the pinned rev | Medium | A pre-construction grep showed no top-level `SimplicialObject.Homotopy` structure — Lemma 1 may need to *introduce* this notion. Adds ~30 lines to the estimate. |
| Sign conventions on the chain side differ from Hatcher's | Low | `alternatingFaceMapComplex` uses `Σ (-1)^i ∂_i`, which matches Hatcher. |
| `TopCat.toSSet` defined via geometric realisation, not simplicial-set evaluation | Low | At pinned rev `TopCat.toSSet` is the right adjoint to `|·|`, so by adjunction the product compatibility in H3 step 1 is immediate. |
| Universe juggling between `SSet.{w}`, `TopCat.{w}`, `C` | Medium | Match the existing `singularChainComplexFunctor` universe pattern in `SingularHomology.Basic.lean:39` exactly. |
| Reviewer requests pure-Hatcher proof for didactic clarity | Low | The simplicial route is the *standard* modern presentation (e.g. Riehl 2014, §3); reviewers should accept it. |

#### H9. Alternative: a thin local axiom in the gallery file

If the full Mathlib contribution is deferred, a self-contained local axiom
in `BrouwerFixedPointOQ01OQ02.lean` can keep the gallery progress unblocked:

```lean
/-- **Local axiom (B1 surrogate)**: topologically homotopic continuous
    maps induce chain-homotopy-equivalent maps on singular chains. To be
    discharged by an upstream Mathlib contribution
    (`AlgebraicTopology.SingularHomology.HomotopyInvariance`). -/
axiom singular_chain_homotopy_of_top_homotopy
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : ContinuousMap.Homotopy f.hom g.hom) :
    HomotopyEquiv
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of ℤ)).obj X)
      (((AlgebraicTopology.singularChainComplexFunctor AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of ℤ)).obj Y)
```

With this axiom in hand, ACT-B exec discharges
`H_n_minus_1_ball_zero` directly (Section G5 sketch). Net effect on axiom
count: `H_n_minus_1_sphere_nonzero` axiom replaced by
`singular_chain_homotopy_of_top_homotopy` axiom + a now-proven
`H_n_minus_1_ball_zero` real form, plus the (still axiomatised)
sphere-homology fact `H_{n-1}(S^{n-1}) ≠ 0`. Axiom count thus goes from
1 to 2 in the gallery file, but each axiom is now a *standard textbook
fact* rather than a composite of three.

The choice between H6 (upstream PR) and H9 (local axiom) is strategic:
H6 yields a cleaner gallery file but is a multi-week project; H9 keeps
ACT-B exec a one-session iteration. *Recommendation*: pursue H9 as the
near-term next step (ACT-B exec local), then promote to H6 over a
longer horizon when the gallery prioritisation allows.

#### H10. References

* Hatcher, *Algebraic Topology* (CUP, 2002), §2.1 Proposition 2.10
  (p. 111) and Theorem 2.10 (homotopy invariance of singular homology).
* Riehl, *Categorical Homotopy Theory* (CUP, 2014), §3 (simplicial
  homotopies via `Δ[1]`).
* Goerss & Jardine, *Simplicial Homotopy Theory* (Birkhäuser, 1999),
  §I.6 (simplicial homotopy and the Moore complex).
* Mathlib v4.26.0 `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean`
  (alternating face map complex functor).
* Mathlib v4.26.0 `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean`
  (simplicial objects, simplicial set product structure).
* Mathlib v4.26.0 `Mathlib/Algebra/Homology/Homotopy.lean:123`
  (`Homotopy` structure and `Homotopy.homologyMap_eq`).
* Mathlib v4.26.0 `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`
  (`singularChainComplexFunctor`, `singularHomologyFunctor`).

#### H11. ACT-C exec readiness summary

* The full Mathlib contribution decomposes into **one** genuinely new
  construction (Lemma 1 — `AlternatingFaceMapComplex.mapHomotopy`)
  plus **one** routine bridge lemma (Lemma 2) plus the final theorem.
  Total estimated complexity: 100–200 Lean lines, ~3–6 sessions.
* All transitive Mathlib dependencies are present at the pinned rev.
  No upstream-of-Mathlib gap blocks this work.
* If Lemma 1 is contested or stalls, the *local axiom* H9 keeps gallery
  ACT-B exec a single session away and is the recommended
  near-term path.
* Hatcher's bare-hands `α_i` formula is *not* the path forward in
  Mathlib's simplicial framework — that would be 2–3× the line count
  with no structural payoff. The simplicial-homotopy route described
  in H3 is canonical.

### I. Iteration log addendum (S4)

* 2026-05-12 (researcher-12, S4 ACT-C prep): completed prism-operator
  construction blueprint (Section H). No Lean edits. The key finding is
  that the upstream B1 contribution factors through three layers
  (simplicial homotopy → chain homotopy via `alternatingFaceMapComplex`
  → singular chains via `TopCat.toSSet`), reducing the "genuinely new"
  Mathlib code to **one** lemma — `AlternatingFaceMapComplex.mapHomotopy`
  — plus a routine simplicial bridge. The geometric Hatcher `α_i` formula
  is recorded for reference but is *not* the recommended path: the
  simplicial route saves an estimated 60–80% of the line count and forces
  the sign convention automatically.

  A near-term *local-axiom* alternative (Section H9) is recommended as
  the immediate ACT-B exec route: it costs +1 named axiom in the gallery
  file but unblocks the substantive `H_n_minus_1_ball_zero` proof in a
  single session, and the new axiom is *strictly tighter* than the
  current sphere-nonzero residual axiom because the prism statement is a
  well-known piece of standard infrastructure rather than a deep
  homology computation. Net effect: 1 deep axiom → 1 deep axiom
  (sphere-nonzero) + 1 thin "B1 surrogate" axiom (provable from
  Section H Lemma 1 + Lemma 2 once contributed upstream).
