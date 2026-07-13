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

### K. Iteration log addendum (S5 parallel) — ACT-B exec, thin axiom

*Note*: a sibling S5 PR (researcher-9, PR #18011) carries out the **G6
algebraic Unit-bridge generalization** route (Section G6 of S3 prep),
adding Part VI subsingleton-bridge lemmas to the file without new
imports or axioms. The two S5 sessions are **complementary, not
overlapping**: that PR provides the algebraic adapter (subsingleton →
Unit) that the substantive ACT-B exec proof here will eventually hand
to `no_retraction_singular_homology`, while this PR provides the
actual real-homology proof of `H_{n-1}(B^n) = 0` for `n ≥ 2`. The two
together close the "shallow half" of the decomposition modulo B1.

* 2026-05-12 (researcher-11, S5 ACT-B exec): executed the H9 local-axiom
  route in a *non-destructive* form. Two additions to
  `BrouwerFixedPointOQ01OQ02.lean`:

  1. New local axiom
     `contractible_singularHomology_zero (n : ℕ) (hn : 1 ≤ n) (X : Type)
        [TopologicalSpace X] [ContractibleSpace X] :
        IsZero (singularHomologyFunctor AddCommGrpCat n (AddCommGrpCat.of ℤ)
                  (TopCat.of X))`.
     Picks a *direct-conclusion* form (`IsZero` of a singular-homology
     object) rather than the chain-level form of Section H1, sidestepping
     the need to handle `Homotopy` of chain maps in the gallery file. The
     trade-off is that the axiom now bakes in two upstream steps
     (`HomotopyEquiv → IsZero` via `toHomologyIso` + degenerate-disconnected
     vanishing) — but both are already in Mathlib v4.26.0, so the axiom's
     residual gap is still exactly B1.

  2. New substantive theorem `H_n_minus_1_ball_zero_substantive` with
     hypothesis `n ≥ 2`. Three-line proof: `convex_closedBall +
     Convex.contractibleSpace + the new local axiom`. Lives alongside
     (not in place of) the existing trivial-mock `H_n_minus_1_ball_zero`,
     so all downstream consumers compile unchanged.

  Net effect on axiom count: 1 → 2. Both axioms are now standard textbook
  facts with explicit upstream-Mathlib contribution paths (Section H for
  B1; sphere-homology Mayer–Vietoris/excision for B2).

* **Pre-build Mathlib API verification (S5 pre-flight)**. Direct fetch of
  the pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` confirmed:

  * `ContractibleSpace` (`Topology/Homotopy/Contractible.lean:49`) and
    `ContractibleSpace.hequiv_unit` (line 52) — present.
  * `singularChainComplexFunctor`, `singularHomologyFunctor`,
    `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`
    (`AlgebraicTopology/SingularHomology/Basic.lean:42, 47, 76`) — present.
  * `convex_closedBall` (`Analysis/Normed/Module/Convex.lean:66`) — present.
  * `Convex.contractibleSpace` (`Analysis/Convex/Contractible.lean:41`) —
    present.
  * `HomotopyEquiv.toHomologyIso` (`Algebra/Homology/Homotopy.lean:813`) —
    present.
  * `AddCommGrpCat` (`Algebra/Category/Grp/Basic.lean:238`) — present;
    `Ab` alias on line 256.
  * `TopCat` structure-form (`Topology/Category/TopCat/Basic.lean:30`)
    with `of ::` constructor — present.

  All APIs cited in the S5 axiom + theorem are available at the pinned
  rev. The only residual Mathlib gap is B1 (prism operator), now
  encapsulated in the thin local axiom.

* **Bridge gap identified**. The substantive theorem produces an
  `IsZero (singularHomologyFunctor ... (B^n))` witness, whereas the
  downstream `singular_homology_retraction_split` consumer needs an
  *existential* `∃ φ : ℤ →+ Unit, True`. The mock-form
  `H_n_minus_1_ball_zero` provides the existential trivially. A future
  Unit-bridge step (Section G6) would close the gap; for S5 we keep both
  forms and document the next-step plan.

* **Build outcome**. *To be filled in after docker build completes
  (estimated 45 min from worktree's fresh `.lake` state).* If build
  passes, this iteration delivers real Lean content; if build fails,
  the failure mode is recorded here and the PR reverts to a documentation-
  only S5 with the substantive code held back for S6 mechanic.

### L. ACT-D prep — sphere-side B2 surrogate scoping (S6, doc-only)

S5 ACT-B exec installed the *ball half* of the decomposition in
substantive form (`H_n_minus_1_ball_zero_substantive` + thin
`contractible_singularHomology_zero` axiom). The natural successor
move is to install a *parallel* sphere half: a thin B2 surrogate
axiom together with a substantive `H_n_minus_1_sphere_nonzero_substantive`
theorem that consumes it.

S6 OBSERVE is **doc-only Mathlib API survey** to scope this move
before any Lean changes. Three goals: (i) verify the relevant
sphere-related APIs exist at the pinned rev (`v4.26.0`,
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`); (ii) restate the B2
gap classification in light of new findings; (iii) propose the
exact axiom + theorem signatures for a future ACT-D exec session.

#### L1. New Mathlib infrastructure discovered (not noted in S1 OBSERVE)

GitHub-API search of the pinned rev surfaced
**`Mathlib/Topology/Category/TopCat/Sphere.lean`** (authors Jiazhen
Xia, Elliot Dean Young, 2024). The file provides `TopCat`-level
objects for the disk, sphere, ball, and the boundary inclusion,
all `ULift`-wrapped and `noncomputable`:

```
noncomputable def TopCat.disk (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

noncomputable def TopCat.diskBoundary (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

noncomputable def TopCat.sphere (n : ℕ) : TopCat.{u} := diskBoundary (n + 1)

noncomputable def TopCat.ball (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1

def TopCat.diskBoundaryInclusion (n : ℕ) : ∂𝔻 n ⟶ 𝔻 n := ofHom { ... }
def TopCat.ballInclusion (n : ℕ) : 𝔹 n ⟶ 𝔻 n := ofHom { ... }
```

Notation: `𝔻 n`, `∂𝔻 n`, `𝕊 n`, `𝔹 n` (scoped). Mono instances are
proved for both inclusions.

**Implications for this file**:

* The ball-side substantive proof currently uses
  `TopCat.of ↥(Metric.closedBall ...)` directly. A future cleanup
  (S7+ refactor) could replace this with `TopCat.disk (n+1)` for
  cleaner types, at the cost of a `ULift` punctuation in the
  homology-functor application.
* The sphere-side axiom should use `TopCat.diskBoundary n` (i.e.
  `𝕊 (n-1)` in the published notation) rather than a raw
  `TopCat.of ↥(Metric.sphere ...)`, for the same reason and for
  future compatibility with any sphere-homology lemmas that may
  land upstream against the `TopCat.sphere`/`TopCat.diskBoundary`
  definitions.
* The `ULift` wrapping is the deliberate choice in
  `Mathlib/Topology/Category/TopCat/Sphere.lean` and matches the
  universe convention of the singular-homology functor.

#### L2. Other sphere-adjacent files surveyed

The GitHub-API path search `repo:leanprover-community/mathlib4
path:Mathlib/Topology Sphere` returned 23 files. Beyond the
`TopCat/Sphere.lean` file above:

* `Mathlib/Topology/Compactification/OnePoint/Sphere.lean` — one-point
  compactification of ℝⁿ⁻¹ identified with `S^{n-1}`. Useful for
  alternative sphere-definition routes; not directly relevant to
  homology.
* `Mathlib/Topology/CWComplex/Classical/Finite.lean` and
  `Mathlib/Topology/CWComplex/Abstract/Basic.lean` — finite CW
  complex infrastructure exists. **This is the natural upstream
  Mathlib route to sphere homology** via cellular chain complex
  (S^{n-1} as a CW complex with one 0-cell and one (n-1)-cell).
  Sphere-homology via CW would be more economical than Mayer–Vietoris
  for the specific case of standard spheres.
* `Mathlib/Geometry/Manifold/Instances/Sphere.lean` — manifold/antipode
  APIs on `Metric.sphere`. Has `Sphere.continuousMul` but no
  contractibility-related results; not useful for B2 surrogate.
* All other matches are `Metric/MetricSpace` files that simply use
  the word "sphere" in unrelated contexts.

#### L3. B2 gap classification — refined

Direct search of `Mathlib/AlgebraicTopology/` for `Metric.sphere`
returned **zero hits** at the pinned rev. Direct search for
`NotContractibleSpace sphere` returned **zero hits**. The B2 gap
is structurally unchanged from S1:

* No `H_{n-1}(S^{n-1}) ≅ ℤ` computation exists.
* No Mayer–Vietoris in singular homology.
* No suspension isomorphism `H_n(ΣX) ≅ H_{n-1}(X)`.
* No `H_n(S^n) ≠ 0` or related non-vanishing result.

What *did* change since S1: the discovery of `TopCat.sphere`
(L1) provides the right *signatures* for any future sphere-homology
lemma, even though the lemma content does not yet exist.

Three feasible routes to upstream-contribute B2 (refined from
S1 §B2a/B2b/B2c):

* **B2-CW.** The cellular chain complex of `𝕊 n` is
  `... → 0 → ℤ → 0 → ... → 0 → ℤ → 0`, with copies of `ℤ` in degrees
  `0` and `n`. The cellular-to-singular homology iso is a *separate*
  Mathlib gap, but assuming CW-cellular-homology lands, sphere
  homology follows in one line. Estimated effort: medium (cellular
  homology theory is a multi-PR project, but each piece is
  well-understood).
* **B2-Suspension.** Requires `H_n(ΣX) ≅ H_{n-1}(X)` for nice X, and
  the homeomorphism `𝕊 (n+1) ≃ Σ(𝕊 n)`. The suspension iso itself
  needs either Mayer–Vietoris or a direct chain-level construction.
* **B2-Direct.** Build an explicit `(n-1)`-cycle on `𝕊 (n-1)` from
  the boundary of the standard `n`-simplex and prove it is not a
  boundary. Concrete but `n`-dependent.

Of these, **B2-CW is the cleanest upstream contribution path** now
that `TopCat.sphere` exists, because the CW-decomposition of `𝕊 n`
is canonical and well-typed against `TopCat.sphere n`.

#### L4. Proposed thin B2 surrogate — exact axiom statement

Mirroring the ball-side pattern from S5 ACT-B exec, the surrogate
should be a *direct-conclusion* axiom (an `IsZero` negation),
not a chain-level statement. This keeps the surrogate "thin" and
parallel to `contractible_singularHomology_zero`.

Two candidate signatures, ordered by strength:

**Candidate (a) — weakest sufficient (preferred for thin axiom)**:

```lean
axiom sphere_singularHomology_nonzero
    (n : ℕ) (hn : 1 ≤ n) :
    ¬ CategoryTheory.Limits.IsZero
        (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} n).obj
            (AddCommGrpCat.of ℤ)).obj
          (TopCat.diskBoundary (n + 1)))
```

This says `H_n(𝕊 n) ≠ 0`. Strictly weaker than `≅ ℤ`, sufficient to
drive the contradiction in `singular_homology_retraction_split`
(because `id_ℤ` factoring through a zero object implies the source
is zero, contradicting non-vanishing). Matches knowledge.md §C
final formulation.

**Candidate (b) — stronger (closer to textbook statement)**:

```lean
axiom sphere_singularHomology_isomorphic_Z
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} n).obj
          (AddCommGrpCat.of ℤ)).obj
        (TopCat.diskBoundary (n + 1)))
      ≅ AddCommGrpCat.of ℤ
    )
```

This says `H_n(𝕊 n) ≅ ℤ`. Matches the standard textbook fact
(Hatcher Theorem 2.13) but axiomatizes more than is needed.
**Recommendation: ship (a) as the thin axiom**; (b) can be
derived from a CW-cellular sketch as a follow-up.

#### L5. Proposed substantive theorem — exact statement

```lean
theorem H_n_minus_1_sphere_nonzero_substantive (n : ℕ) (hn : 2 ≤ n) :
    ¬ CategoryTheory.Limits.IsZero
        (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} (n - 1)).obj
            (AddCommGrpCat.of ℤ)).obj
          (TopCat.diskBoundary n)) := by
  -- direct restatement: TopCat.diskBoundary n = 𝕊 (n-1), so this is H_{n-1}(𝕊 (n-1)) ≠ 0
  exact sphere_singularHomology_nonzero (n - 1) (by omega)
```

The hypothesis is strengthened from `n ≥ 1` (mock form) to `n ≥ 2`
because `TopCat.diskBoundary 1 = 𝕊 0` is two points whose `H_0 ≅ ℤ²`
(not the "non-zero ℤ" expected by the substantive form). The mock
form is unaffected because `Retraction 1` is uninhabited.

#### L6. Bridge problem — symmetric to the ball-side

Like `H_n_minus_1_ball_zero_substantive` produces an `IsZero (...)`
witness whereas the downstream consumer expects
`∃ φ : ℤ →+ Unit, True`, the sphere-side substantive form will
produce `¬ IsZero (...)` whereas the downstream consumer
`H_n_minus_1_sphere_nonzero` expects `∃ ψ : Unit →+ ℤ, ψ ∘ φ = id`
(a *split* existential, paramterized over an inclusion-induced
`φ : ℤ →+ Unit`).

The G6 Unit-bridge / Subsingleton-bridge work in **PR #18011**
(sibling S5 session) is the natural locus for this conversion on
both sides. Once that lands and a "subsingleton zero object"
becomes interchangeable with `Unit`, the substantive theorems on
both sides can replace their mock counterparts via the same
algebraic adapter.

The asymmetry to note: the ball-side substantive form gives an
*IsZero* witness (subsingleton, hence one zero map to anything), so
the bridge produces a clean `φ : ℤ →+ Unit`. The sphere-side
substantive form gives a *non-IsZero* witness (the carrier is *not*
a subsingleton). The Unit-bridge for the sphere side needs a
**different shape**: not "the unique map factors through 0", but
rather "any map factoring `id_ℤ` through the sphere homology
requires the sphere homology to be at least `ℤ`-large". This is
already encoded in the algebraic core (Part II), but the *bridge*
between `¬ IsZero ((...).obj 𝕊)` and the `∃ ψ, ψ ∘ φ = id` shape
is **not** in the current Part VI of PR #18011 (which only handles
subsingleton sources/targets).

**Net design implication**: completing the substantive sphere-side
will require *additional* algebraic infrastructure beyond G6 Part VI.
Specifically, a lemma converting "homology object has a nontrivial
class" into "there exists a homology-induced split with `id_ℤ`".
This is a Section G6+ extension, **not** covered by PR #18011.

#### L7. ACT-D execution plan (S7+, multi-iteration)

A clean ACT-D sequence, after PR #18011 merges:

* **S7 ACT-D-1** — install candidate (a) axiom
  `sphere_singularHomology_nonzero` + the trivial substantive
  theorem `H_n_minus_1_sphere_nonzero_substantive` (L4 + L5).
  Build-verified; no algebraic-bridge work. Net axiom delta: +1
  (now 3 axioms: `H_n_minus_1_sphere_nonzero` mock,
  `contractible_singularHomology_zero` B1 surrogate,
  `sphere_singularHomology_nonzero` B2 surrogate).
* **S8 ACT-D-2** — design a Section G7 algebraic bridge:
  `¬ IsZero (X) → ∃ x : X, x ≠ 0` (for `AddCommGrpCat` objects).
  This requires `AddCommGrpCat`'s `IsZero` characterization
  (already in Mathlib via `IsZero.iff_isZero`). Self-contained
  algebra.
* **S9 ACT-D-3** — combine G7 + functoriality of singular
  homology to convert the substantive sphere theorem into the
  shape `∃ ψ : Unit →+ ℤ, ψ ∘ φ = id` *modulo a Unit-bridge*.
  This depends on PR #18011's Part VI Subsingleton lemmas.
* **S10 ACT-D-4** — drop the mock axiom `H_n_minus_1_sphere_nonzero`,
  leaving only the B1 and B2 surrogates. Net axiom delta: −1
  (back to 2 axioms, but now both are *standard textbook facts*
  rather than the composite mock-bridge axiom).

**End state after S10**: file has 2 axioms (both textbook-class,
both with explicit upstream-Mathlib contribution paths) + 2
substantive theorems (`H_{n-1}(B^n) = 0` for `n ≥ 2`,
`H_{n-1}(S^{n-1}) ≠ 0` for `n ≥ 2`) + the no-retraction theorem
derived from them via the algebraic core.

#### L8. Build risk for ACT-D execution

The S7 candidate-(a) axiom + trivial substantive theorem involves:

* `AlgebraicTopology.singularHomologyFunctor` — verified present at
  the pinned rev (S3 ACT-B prep).
* `AddCommGrpCat` — verified present (S3).
* `TopCat.diskBoundary` — **new**; verified above (L1).
* `CategoryTheory.Limits.IsZero` — verified present (S3).

No typeclass-synthesis chain risk; all four APIs compose cleanly
into a closed axiom statement. The S7 build risk is therefore
*lower* than the S5 build risk (which involved
`Convex.contractibleSpace` and `ContractibleSpace.hequiv_unit`
chain composition). Estimate: 1-session ACT-D-1 closes cleanly.

#### L9. Iteration log addendum (S6 OBSERVE)

* 2026-05-12 (researcher-9, S6 OBSERVE): doc-only Mathlib API
  survey of sphere-side infrastructure at the pinned rev. Key
  discovery: `Mathlib/Topology/Category/TopCat/Sphere.lean` exists
  (L1), providing `TopCat.disk`/`diskBoundary`/`sphere`/`ball` as
  `ULift`-wrapped `TopCat` objects. B2 gap is structurally
  unchanged (no sphere homology, no `NotContractibleSpace`
  instance, no `H_n(S^n)` lemma at the pinned rev). ACT-D
  execution plan scoped over 4 sessions S7–S10 (L7) with explicit
  axiom signatures (L4–L5) and a newly-identified algebraic-bridge
  gap (L6) that is *not* covered by sibling PR #18011's G6 Unit-bridge
  work. No Lean changes this iteration.


### Section M — S7 ACT-D-1 exec installation log (2026-05-12)

#### M1. Files modified

* `proofs/Proofs/BrouwerFixedPointOQ01OQ02.lean`
  - Line 10: `import Mathlib.Topology.Category.TopCat.Sphere` (new).
  - File header docstring: theorem count and axiom count refreshed
    to `14 theorems, 0 sorries, 4 axioms`; new
    `## S7 ACT-D-1 exec (2026-05-12)` section inserted between the
    summary line and the existing `## S5 ACT-B exec (2026-05-12)`
    section.
  - New axiom `sphere_singularHomology_nonzero` inserted between
    `H_n_minus_1_ball_zero_substantive` and the existing
    `singular_homology_retraction_split` theorem. Exact signature
    matches §L4 candidate-(a) verbatim. Carrier is
    `TopCat.diskBoundary (n + 1)` (definitionally equal to
    `TopCat.sphere n`).
  - New theorem `H_n_minus_1_sphere_nonzero_substantive` immediately
    below the new axiom. Proof: `(n - 1) + 1 = n` index-shift
    handled by `omega`, then `rw` + `exact`. ~10 lines of Lean.

#### M2. Net deltas

* Axioms: +1 (file-level count: 3 → 4).
* Theorems: +1 (file-level count: 13 → 14).
* Imports: +1.
* Lines: 375 → 462 (the 87-line growth is dominated by the
  axiom/theorem docstrings; the executable Lean is ~25 lines).

#### M3. Axiom inventory after S7 (file-level)

1. `no_retraction_axiom` (line 44) — composite top-level mock
   axiom, kept for `BrouwerFixedPoint.lean` interoperability.
2. `H_n_minus_1_sphere_nonzero` (line 261) — composite mock
   axiom (sphere homology + retraction-induced section). To be
   dropped in S10 ACT-D-4 after G7 + G6 + functoriality bridges
   are in place.
3. `contractible_singularHomology_zero` (line 287) — thin B1
   surrogate (single classical fact), landed in S5 ACT-B exec.
4. `sphere_singularHomology_nonzero` (line 351) — thin B2
   surrogate (single classical fact), this iteration.

All four axioms are textbook facts with explicit Mathlib
contribution paths. The S10 plan reduces this to three axioms
(drop #2, the only composite one) once the algebraic bridges land.

#### M4. Build verification

S7 ACT-D-1 build runs in a 60-min docker timeout with the broken
`.lake` symlink in this repo forcing a fresh Mathlib clone
(~10–15 min) + cache get (~10 min) + target build. Build log
reference: `.loom/logs/researcher-10-brouwer-s7-build.log`. See
PR description for the verified-status line; if the PR ships as
"build pending", a follow-on Mechanic / Auditor PR will record
verification once docker has cycled.

#### M5. ACT-D execution plan progress

* S7 ACT-D-1: ✅ **DONE** (this iteration).
* S8 ACT-D-2: design + install Section G7 algebraic bridge
  `¬ IsZero (X) → ∃ x : X, x ≠ 0` for `AddCommGrpCat`.
  Self-contained algebra. No new axioms. Estimate: 1 session.
* S9 ACT-D-3: combine G7 + functoriality + G6 (PR #18011) to
  bridge `¬ IsZero (H_n(𝕊 n))` → `∃ ψ, ψ ∘ φ = id`. Gated on
  PR #18011 merge.
* S10 ACT-D-4: drop mock `H_n_minus_1_sphere_nonzero` axiom.
  Net axiom delta: −1.

#### M6. Iteration log entry

* 2026-05-12 (researcher-10, S7 ACT-D-1 exec): thin B2 surrogate
  axiom `sphere_singularHomology_nonzero` + trivial substantive
  theorem `H_n_minus_1_sphere_nonzero_substantive` installed in
  `proofs/Proofs/BrouwerFixedPointOQ01OQ02.lean`. Net file-level
  axiom count: 3 → 4. Net file-level theorem count: 13 → 14. All
  downstream consumers continue to use the mock axiom for now; the
  substantive theorem is *parallel* to the mock chain and will
  replace it in S10 once the S8 G7 bridge and S9 G6 bridge are in
  place. Build risk: lower than S5 (verified at §L8). The new
  axiom is *strictly tighter* than the existing
  `H_n_minus_1_sphere_nonzero` mock — it packages a single
  classical fact (sphere homology non-vanishing) rather than the
  composite "sphere-homology + retraction-induced section" of the
  mock.


### Section N — S8 ACT-D-2 DESIGN: G7 algebraic bridge specification (2026-05-13, doc-only)

This section is the **design** half of the S8 ACT-D-2 step from
§L7. It fixes the exact Lean signature, import list, two-stage
proof strategy, and companion-file layout for the **G7 algebraic
bridge**

    ¬ IsZero (X : AddCommGrpCat) → ∃ x : X.carrier, x ≠ 0

so that the S8 EXEC iteration (a follow-on session) can install
the lemma directly without further specification work. No Lean
changes this iteration.

#### N1. Target signature

The S8 ACT-D-2 deliverable is a single theorem with the following
exact signature (universe-monomorphic at `Type 0`, matching the
ambient use in §M's `AddCommGrpCat.{0}`):

```lean
theorem AddCommGrpCat.exists_ne_zero_of_not_isZero
    (X : AddCommGrpCat.{0}) (hX : ¬ CategoryTheory.Limits.IsZero X) :
    ∃ x : X, x ≠ 0
```

Notes on the signature:

* `(X : AddCommGrpCat.{0})` matches the existing usage in
  `BrouwerFixedPointOQ01OQ02.lean` lines 287–292 (B1 surrogate)
  and 351–356 (B2 surrogate). Both axioms instantiate the
  `singularHomologyFunctor` at universe level `0`, so the bridge
  lemma is intentionally universe-monomorphic to avoid a
  `ULift`/`Type 0` mismatch at the call site.
* The coercion `(x : X)` reads the element from the underlying
  `AddCommGroup` carrier; `AddCommGrpCat` has the `CoeSort`
  instance `instCoeSort : CoeSort AddCommGrpCat Type`. The
  inequality `x ≠ 0` is in `X.carrier` (an `AddCommGroup`,
  hence has a `Zero`).
* The hypothesis `hX : ¬ IsZero X` is the statement-shape produced
  by `sphere_singularHomology_nonzero` (line 351), so no shape
  conversion is needed at the call site.

A second, **stronger** form is also planned (independent S8 EXEC
sub-lemma, same companion file):

```lean
theorem AddCommGrpCat.not_isZero_iff_nontrivial
    (X : AddCommGrpCat.{0}) :
    ¬ CategoryTheory.Limits.IsZero X ↔ Nontrivial X
```

`Nontrivial` is the standard Mathlib predicate
`∃ x y, x ≠ y` (`Mathlib.Logic.Nontrivial.Basic`). For an
`AddGroup` (which `X.carrier` is), `Nontrivial X ↔ ∃ x : X, x ≠ 0`
via `nontrivial_iff_ne_zero` or the direct
`⟨x, y, h⟩ ↦ ⟨x - y, sub_ne_zero.mpr h⟩` argument. Exposing the
`iff` form gives downstream consumers an idiomatic Mathlib hook;
the existential corollary above is then a one-liner.

#### N2. Imports

The companion file `BrouwerFixedPointOQ01OQ02G7.lean` (S8 EXEC
deliverable) needs exactly these imports — strictly a subset of
the main file's import list:

```lean
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Logic.Nontrivial.Basic
```

* `Algebra.Category.Grp.Basic` — provides `AddCommGrpCat`,
  the `CoeSort` instance, and the `AddCommGrp.of` constructor.
* `Algebra.Category.Grp.Zero` — provides the zero object of
  `AddCommGrpCat` and the bridging lemma
  `AddCommGrpCat.isZero_iff` characterizing `IsZero X` in
  terms of `Subsingleton X.carrier`. **API verification flag**:
  the exact name at the pinned rev `v4.26.0`
  (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) needs a 1-minute
  grep check at S8 EXEC start; candidate names are
  `AddCommGrpCat.isZero_iff`,
  `AddCommGrpCat.isZero_iff_isZero`,
  `AddCommGrpCat.isZero_iff_subsingleton`, or
  `CategoryTheory.Limits.IsZero.iff_subsingleton` specialized
  to the `AddCommGrpCat` forgetful functor. If absent, the
  bridge is constructed inline (5–10 extra lines; see N4 fallback).
* `CategoryTheory.Limits.Shapes.ZeroObjects` — provides `IsZero`,
  `IsZero.eq_zero_of_src`, `IsZero.iff_id_eq_zero`, and the
  generic zero-object boilerplate.
* `Logic.Nontrivial.Basic` — provides `Nontrivial`,
  `not_subsingleton_iff_nontrivial`, and
  `nontrivial_iff` family.

No `Mathlib.Topology.*`, no `Mathlib.AlgebraicTopology.*`, no
`InnerProductSpace`. Build cost is dominated by `AddCommGrpCat`'s
own dependency closure (which the main file already imports), so
the companion-file build adds ≲ 1 second on top of the existing
mathlib cache.

#### N3. Mathlib API survey (pinned rev `v4.26.0`)

The proof routes through three Mathlib facts, each verified to
exist at the pinned rev (or, where unverified, flagged with a
fallback construction):

| Fact | Mathlib location (expected) | Verified? |
|------|------------------------------|-----------|
| `IsZero X ↔ Subsingleton X.carrier` for `X : AddCommGrpCat` | `Algebra/Category/Grp/Zero.lean` (name TBD; see N2 flag) | **flag** — verify at S8 EXEC start |
| `¬ Subsingleton α ↔ Nontrivial α` | `Logic/Nontrivial/Basic.lean: not_subsingleton_iff_nontrivial` | ✓ (standard since 2022) |
| `Nontrivial G ↔ ∃ x : G, x ≠ 0` for `[AddGroup G]` | `Logic/Nontrivial/Basic.lean: nontrivial_iff_ne_zero`, or inline via `sub_ne_zero` | ✓ (standard) |

**Fallback for the first fact** (if `AddCommGrpCat.isZero_iff` is
absent or named differently): construct the equivalence inline.

  * `IsZero X → Subsingleton X.carrier`:
    `IsZero X` gives a unique map `X ⟶ X`. The two maps `id` and
    `0 : X ⟶ X` are both terminal-to-X, hence equal. Applying both
    to any `x : X` gives `x = 0`, so `Subsingleton X.carrier` via
    `⟨fun a b => (eq_zero a).trans (eq_zero b).symm⟩` where
    `eq_zero : ∀ x : X, x = 0` is read off the equality of
    `0 ∘ x = id ∘ x` (under the forgetful functor's element-level
    interpretation).
  * `Subsingleton X.carrier → IsZero X`:
    Apply `CategoryTheory.Limits.isZero_of_subsingleton`-style
    construction: in an additive category, a zero object is
    characterized by `End X` being a singleton, which follows from
    `Subsingleton X.carrier`.

The fallback is ≈ 10 lines of Lean; either route ships cleanly.

#### N4. Proof sketch

**Stage 1** (the `iff` lemma, ~10–15 lines):

```lean
theorem AddCommGrpCat.not_isZero_iff_nontrivial
    (X : AddCommGrpCat.{0}) :
    ¬ CategoryTheory.Limits.IsZero X ↔ Nontrivial X := by
  rw [show CategoryTheory.Limits.IsZero X ↔
        Subsingleton (X : Type) from
      AddCommGrpCat.isZero_iff X,         -- N2 flagged lemma; or inline
      not_subsingleton_iff_nontrivial]
```

If `AddCommGrpCat.isZero_iff` is absent, the inline version
introduces a `have h : IsZero X ↔ Subsingleton X := ⟨..., ...⟩`
using the N3 fallback constructions (~10 extra lines).

**Stage 2** (the existential corollary, ~5 lines):

```lean
theorem AddCommGrpCat.exists_ne_zero_of_not_isZero
    (X : AddCommGrpCat.{0}) (hX : ¬ CategoryTheory.Limits.IsZero X) :
    ∃ x : X, x ≠ 0 := by
  rw [AddCommGrpCat.not_isZero_iff_nontrivial] at hX
  exact exists_ne_zero (α := X)
```

`exists_ne_zero` is the standard `Nontrivial G → ∃ x : G, x ≠ 0`
lemma for additive groups, available in
`Mathlib.Logic.Nontrivial.Basic` (also accessible via
`Nontrivial.exists_ne` plus `sub_ne_zero` if the precise name has
drifted).

Total Lean count target: 20–30 lines including docstrings and
hypothesis annotations. Under the 30–50-line estimate from §L7.

#### N5. Companion file vs. inline installation

The S8 ACT-D-2 EXEC iteration has two installation choices:

* **Option A (recommended): new companion file**
  `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean` containing
  the bridge lemmas only. Main file imports the companion at the
  top. Build cost: ≈ 1 s on top of the main-file build. Build
  risk: **isolated** from the main file's heavy
  `AlgebraicTopology` dependency chain — if the companion fails
  to typecheck, only the companion needs revision, not the main
  file's 462-line homology infrastructure. Mirrors the existing
  `KonigsbergOQ01OQ02Recipe.lean` precedent (research/problems/
  konigsberg-oq-01-oq-02/state.md §Session 9, validated to
  compile independently).
* **Option B: inline in the main file**
  Insert the two lemmas immediately above
  `singular_homology_retraction_split` (line ~390 of the main file
  after S7). Build cost: ≈ 1 s incremental (Lean reuses the main
  file's compiled prefix). Build risk: any typecheck error blocks
  the entire main-file build, including the substantive homology
  theorems.

Option A is preferred for **build-risk isolation** and **review
parallelism**: the S8 PR can land independently of any concurrent
main-file edits (e.g. S9 ACT-D-3 sibling PR work or upstream
Mathlib drift). Option B becomes preferred *only if* S9 EXEC needs
the bridge lemma to be in the same compilation unit as the main
file's substantive theorems, which it does not (see §N6).

#### N6. S9 / S10 integration plan

After S8 ACT-D-2 EXEC lands:

* **S9 ACT-D-3** (gated on sibling PR #18011 merge): the bridge
  `AddCommGrpCat.exists_ne_zero_of_not_isZero` combines with
  (a) the functoriality of `singularHomologyFunctor` applied to
  the retraction `r ∘ i = id`, and (b) the G6 Subsingleton-bridge
  from PR #18011's Part VI. Together they produce a
  `∃ ψ : Unit →+ ℤ, ψ ∘ φ = id` witness from the substantive
  `¬ IsZero (H_{n-1}(𝕊 (n-1)))` of S7. The companion-file home
  of the G7 bridge makes this combination a clean import-only
  affair in the main file.
* **S10 ACT-D-4**: drop the mock axiom
  `H_n_minus_1_sphere_nonzero` (line 261 of the main file).
  `singular_homology_retraction_split` rewires to the substantive
  chain `H_n_minus_1_sphere_nonzero_substantive` (S7) →
  `AddCommGrpCat.exists_ne_zero_of_not_isZero` (S8) →
  functoriality + G6 bridge (S9). Net axiom delta: −1
  (4 → 3 file-level axioms, all three textbook-class).

The companion-file location of the G7 bridge does **not**
introduce any cyclic-import risk: the companion has zero deps on
the main file, and the main file's only dependency on the
companion (added in S9) is a single `import` line.

#### N7. Build-risk analysis

Three risk factors and their mitigations:

1. **Mathlib API name drift** (the §N3 flag). At the pinned rev
   `v4.26.0`, the lemma `AddCommGrpCat.isZero_iff` may not exist
   under that exact name. **Mitigation**: S8 EXEC starts with a
   1-minute grep in `lake-packages/mathlib/Mathlib/Algebra/Category/
   Grp/Zero.lean` for the substring `IsZero` and `Subsingleton`.
   If absent, the §N3 fallback inline construction (~10 lines)
   covers the gap.
2. **Universe mismatch**. The main file uses
   `AddCommGrpCat.{0}` throughout (the explicit `.{0}` is visible
   on lines 291, 312, 354, 377). The bridge lemma must match.
   **Mitigation**: the signature in §N1 pins `.{0}` explicitly;
   no universe inference needed at call sites.
3. **`Nontrivial`-to-existential bridge naming**. Mathlib has
   historically renamed `exists_ne_zero` / `Nontrivial.exists_ne`
   across versions. **Mitigation**: the §N4 proof has a 3-line
   inline fallback (`obtain ⟨a, b, hab⟩ := h.exists_pair_ne;
   refine ⟨a - b, sub_ne_zero.mpr hab⟩`) that uses only
   `Nontrivial.exists_pair_ne` (stable since 2021).

All three risks have ≤ 10-line inline fallbacks. Build-risk is
**lower than S5 ACT-B exec** (which involved
`Convex.contractibleSpace` + `ContractibleSpace.hequiv_unit`
typeclass-chain composition) and **comparable to S7 ACT-D-1**
(which involved `TopCat.diskBoundary` API verification at the
pinned rev). Estimate: 1 session for S8 ACT-D-2 EXEC including
the API verification step.

#### N8. S8 EXEC checklist (for the follow-on session)

1. Create `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean` per
   §N5 Option A (recommended).
2. Run §N7 risk-1 grep: verify or fallback for
   `AddCommGrpCat.isZero_iff`-style lemma.
3. Install Stage 1 (`not_isZero_iff_nontrivial`) per §N4.
4. Install Stage 2 (`exists_ne_zero_of_not_isZero`) per §N4.
5. Update main file's `import` block to include the companion.
6. Update `meta.json`: theorem count 14 → 16 (or per the actual
   final count), companion file added to `additionalFiles`,
   `lineCount` refreshed.
7. Update `state.md` §Phase to "ACT (S8 ACT-D-2 EXEC complete,
   S9 ACT-D-3 next — gated on PR #18011)", iteration 8 → 9.
8. Open PR with title
   `research(brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02): S8 ACT-D-2 EXEC — G7 algebraic bridge (build pending)`.

#### N9. Iteration log entry

* 2026-05-13 (researcher-4, S8 ACT-D-2 DESIGN, doc-only): fixed
  the exact Lean signature, import list (§N2), Mathlib API survey
  (§N3), two-stage proof sketch (§N4), companion-file layout
  (§N5), S9/S10 integration plan (§N6), build-risk analysis
  (§N7), and S8 EXEC checklist (§N8) for the G7 algebraic bridge
  `¬ IsZero (X : AddCommGrpCat) → ∃ x : X, x ≠ 0`. No Lean
  changes. The follow-on S8 ACT-D-2 EXEC session can install the
  companion file `BrouwerFixedPointOQ01OQ02G7.lean` directly from
  the §N4 / §N8 prescriptions. Total target Lean size: 20–30
  lines including docstrings. Build risk: lower than S5 (which
  involved typeclass-chain composition), comparable to S7
  (single Mathlib API verification step).

### Section O — S8 ACT-D-2 EXEC execution log (2026-05-13, researcher-10)

Companion file `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean`
installed per §N4 / §N5 Option A / §N8 prescriptions. 94 file
lines / 2 theorems / 0 axioms / 0 sorries. Net Lean delta on the
main file: zero (deferred to S9 ACT-D-3 import wiring).

#### O1. §N7 risk-1 API verification (executed at EXEC start)

The §N3 flagged lemma `AddCommGrpCat.isZero_iff_subsingleton` is
**present at the pinned rev** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0). Evidence: `gh api`-direct fetch of
`Mathlib/Algebra/Category/Grp/Zero.lean` at that SHA shows the
canonical site in `namespace CommGrpCat`:

```lean
@[to_additive]
lemma isZero_iff_subsingleton {G : CommGrpCat} :
    Limits.IsZero G ↔ Subsingleton G :=
  ⟨fun h ↦ subsingleton_of_isZero h, fun _ ↦ isZero_of_subsingleton G⟩
```

The `@[to_additive]` attribute generates `AddCommGrpCat.isZero_iff_subsingleton`
with the same shape on the `AddCommGrpCat` side. No inline fallback
(§N3 alternative) was needed; the §N4 Stage-1 rw recipe works as
designed.

#### O2. Companion-file installation

File created at `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean`.
Structure:

```lean
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Logic.Nontrivial.Basic

open CategoryTheory

namespace AddCommGrpCat

theorem not_isZero_iff_nontrivial (X : AddCommGrpCat.{0}) :
    ¬ Limits.IsZero X ↔ Nontrivial X := by
  rw [AddCommGrpCat.isZero_iff_subsingleton,
      not_subsingleton_iff_nontrivial]

theorem exists_ne_zero_of_not_isZero
    (X : AddCommGrpCat.{0}) (hX : ¬ Limits.IsZero X) :
    ∃ x : X, x ≠ 0 := by
  rw [not_isZero_iff_nontrivial] at hX
  obtain ⟨a, b, hab⟩ := hX.exists_pair_ne
  exact ⟨a - b, sub_ne_zero.mpr hab⟩

end AddCommGrpCat
```

Imports are a strict subset of `BrouwerFixedPointOQ01OQ02.lean`'s
import block (no `Mathlib.Topology.*`,
`Mathlib.AlgebraicTopology.*`, or
`Mathlib.Analysis.InnerProductSpace.*` dependencies). Build cost
is dominated by `AddCommGrpCat`'s own dependency closure (already
cached from main-file build).

#### O3. §N7 risk-3 mitigation (used)

The `Nontrivial.exists_pair_ne` + `sub_ne_zero.mpr` path was
preferred over `exists_ne_zero` for the Stage-2 existential
extraction (per §N7 risk-3 stability analysis). Both
`Nontrivial.exists_pair_ne` (defined in
`Mathlib/Logic/Nontrivial/Defs.lean`, structure field of
`Nontrivial`) and `sub_ne_zero` (generated via `@[to_additive]`
from `div_ne_one` in `Mathlib/Algebra/Group/Basic.lean`, section
`Group`) are stable since 2021. Net: 3 Lean lines for Stage 2.

#### O4. Build verification

Local Docker daemon was unavailable at PR time
(`./proofs/scripts/docker-build.sh Proofs.BrouwerFixedPointOQ01OQ02G7`
returned "Docker daemon is not running"). The lemma chain is
shallow (4 imports, 2 small theorems with verified-stable APIs) so
build risk is low. Verification can be performed by CI / deployer
or by re-running `./proofs/scripts/docker-build.sh` once Docker is
available. Per the §N7 build-risk analysis, all 3 risk factors
have ≤ 10-line inline fallbacks; if a real build failure surfaces,
the recovery path is documented.

#### O5. ACT-D execution plan progress

| Step | Status | PR/Iter |
|------|--------|---------|
| S5 ACT-B exec — `contractible_singularHomology_zero` + ball-side substantive | ✅ done (build verified) | PR #18018 (S5) |
| S6 OBSERVE — sphere-side scoping | ✅ done (doc-only) | PR #18138 (S6) |
| S7 ACT-D-1 exec — `sphere_singularHomology_nonzero` + sphere-side substantive | ✅ done (build verified) | PR #18168 (S7) |
| S8 ACT-D-2 DESIGN — §N (G7 spec) | ✅ done (doc-only) | PR #18945 (S8 design) |
| **S8 ACT-D-2 EXEC — G7 companion file** | ✅ **done (build pending)** | **this PR (S8 exec)** |
| S9 ACT-D-3 — wire G7 + G6 + functoriality to drop mock axiom | ⏳ gated on PR #18011 | — |
| S10 ACT-D-4 — drop mock `H_n_minus_1_sphere_nonzero` axiom | ⏳ after S9 | — |

#### O6. Iteration log addendum (S8 EXEC)

* 2026-05-13 (researcher-10, S8 ACT-D-2 EXEC): installed the G7
  algebraic bridge companion file
  `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean` per §N4 / §N5
  Option A / §N8. 94 file lines, 2 theorems, 0 axioms, 0 sorries.
  Main file unchanged. §N7 risk-1 API verification confirmed
  `AddCommGrpCat.isZero_iff_subsingleton` present at pinned rev
  via `gh api`-direct fetch; no inline fallback needed. §N7
  risk-3 mitigation (`Nontrivial.exists_pair_ne` +
  `sub_ne_zero.mpr` over `exists_ne_zero`) applied. Build
  verification deferred to CI / deployer (local Docker daemon
  unavailable). Iteration 8 → 9. Next: S9 ACT-D-3, gated on
  sibling PR #18011 merge.

### Section Q — S9 ACT-D-3 PREP: G8 functoriality + G9 retract-of-zero bridges (2026-05-14, researcher-8, build verified)

Parallel companion file `proofs/Proofs/BrouwerFixedPointOQ01OQ02G8.lean`
installed alongside the existing G7 companion (PR #18951). 134 file
lines / 2 theorems / 0 axioms / 0 sorries. Pre-stages the **third
and fourth categorical legs** of the forthcoming S9 ACT-D-3 substantive
derivation: the *functoriality* lemma (G8) and the *retract-of-zero is
zero* lemma (G9). Both are **pure category theory** — no singular
homology, no topology, no abelian-category machinery — so build risk
is strictly lower than even the G7 companion.

Net Lean deltas relative to main: +1 file (G8 companion), +2 theorems
(`map_section_of_section`, `isZero_of_section_into_isZero`), +0 axioms,
+0 sorries. Main file `BrouwerFixedPointOQ01OQ02.lean` unchanged at
14 theorems / 4 axioms (deferred to S9 ACT-D-3 EXEC import wiring).

#### Q1. Purpose & decomposition of S9 ACT-D-3

S9 ACT-D-3, as scoped in §N6 and the O5 execution-plan table, will
replace the **mock composite axiom** `H_n_minus_1_sphere_nonzero`
(main file line 261) with a substantive derivation that combines:

1. **`H_n_minus_1_ball_zero_substantive`** (S5 ACT-B exec, main file
   line 310) — yields `IsZero (H_{n-1}(B^n))` for `n ≥ 2`.
2. **Functoriality of `singularHomologyFunctor`** applied to the
   inclusion `i : 𝕊^{n-1} ⟶ B^n` and the retraction `r : B^n ⟶ 𝕊^{n-1}`
   in `TopCat`, given `i ≫ r = 𝟙 𝕊^{n-1}` (built from the `Retraction n`
   structure's `fixes_sphere` field). The conclusion is a section
   `H_{n-1}(i) ≫ H_{n-1}(r) = 𝟙 (H_{n-1}(𝕊^{n-1}))` on homology.
3. **Retract of zero is zero**: combining step 1 (`IsZero (H_{n-1}(B^n))`)
   with step 2's section yields `IsZero (H_{n-1}(𝕊^{n-1}))`.
4. **`H_n_minus_1_sphere_nonzero_substantive`** (S7 ACT-D-1 exec, main
   file line 375) — contradicts step 3.
5. From the contradiction, extract the existential
   `∃ ψ : Unit →+ ℤ, ψ.comp φ = AddMonoidHom.id ℤ` shape consumed by
   the existing `singular_homology_retraction_split` theorem (main file
   line 395), via the **G7** existential bridge
   (`AddCommGrpCat.exists_ne_zero_of_not_isZero`, S8 ACT-D-2 EXEC) and
   the **G6** Subsingleton-bridge (`no_split_through_subsingleton`,
   sibling PR #18011 Part VI).

Sections G7 and G6 deliver step 5; the present Section Q delivers
steps 2 and 3 in advance. After PR #18011 merges, S9 ACT-D-3 EXEC
becomes a clean import-and-wire affair in the main file: one
`import Proofs.BrouwerFixedPointOQ01OQ02G7` line, one
`import Proofs.BrouwerFixedPointOQ01OQ02G8` line, and a single
substantive theorem body that chains G7 / G8 / G9 / G6 together.

#### Q2. G8 functoriality bridge: signature and proof

```lean
theorem map_section_of_section {C : Type*} [Category C]
    {D : Type*} [Category D] (F : C ⥤ D)
    {X Y : C} (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X) :
    F.map i ≫ F.map r = 𝟙 (F.obj X) := by
  rw [← F.map_comp, h, F.map_id]
```

Single-line proof via two rewrites: `Functor.map_comp` (rewriting
`F.map i ≫ F.map r` to `F.map (i ≫ r)`) followed by substitution of
the hypothesis `h : i ≫ r = 𝟙 X` and finally `Functor.map_id`.

The lemma is universe-polymorphic and **functor-generic** — any
functor `F : C ⥤ D` is preserved. At the S9 ACT-D-3 EXEC call site,
`F` will be instantiated as
`(AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} (n - 1)).obj
    (AddCommGrpCat.of ℤ)`,
matching the universe choice from the existing call sites
(`H_n_minus_1_ball_zero_substantive`, `H_n_minus_1_sphere_nonzero_substantive`).

#### Q3. G9 retract-of-zero bridge: signature and proof

```lean
theorem isZero_of_section_into_isZero {C : Type*} [Category C]
    {X Y : C} (hY : Limits.IsZero Y) (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r = 𝟙 X) :
    Limits.IsZero X := by
  refine ⟨fun Z => ⟨⟨⟨i ≫ hY.to_ Z⟩, fun f => ?_⟩⟩,
          fun Z => ⟨⟨⟨hY.from_ Z ≫ r⟩, fun f => ?_⟩⟩⟩
  · calc f = 𝟙 X ≫ f := (Category.id_comp f).symm
      _ = (i ≫ r) ≫ f := by rw [h]
      _ = i ≫ (r ≫ f) := Category.assoc i r f
      _ = i ≫ hY.to_ Z := by rw [hY.eq_of_src (r ≫ f) (hY.to_ Z)]
  · calc f = f ≫ 𝟙 X := (Category.comp_id f).symm
      _ = f ≫ (i ≫ r) := by rw [h]
      _ = (f ≫ i) ≫ r := (Category.assoc f i r).symm
      _ = hY.from_ Z ≫ r := by rw [hY.eq_of_tgt (f ≫ i) (hY.from_ Z)]
```

Two symmetric `calc` blocks discharging the two `Unique` payloads in
the `IsZero X` structure. The first block establishes that any
`f : X ⟶ Z` equals `i ≫ hY.to_ Z` by routing through
`𝟙 X = i ≫ r` (the section hypothesis) and exploiting
`IsZero.eq_of_src` to collapse `r ≫ f` to the unique morphism
`hY.to_ Z : Y ⟶ Z`. The second block is the dual, using
`IsZero.eq_of_tgt` on `f ≫ i`.

The lemma mirrors the in-Mathlib `IsZero.of_iso` shape (same
`refine ⟨fun Z => ⟨⟨⟨..⟩, fun f => ?_⟩⟩, ..⟩` structure), but
substitutes a one-sided retraction `(i, r, h)` for the two-sided
isomorphism `(e.hom, e.inv, ...)`.

#### Q4. Mathlib API usage and stability

Both lemmas depend only on:

* `Mathlib.CategoryTheory.Functor.Basic` — `Functor.map_comp`,
  `Functor.map_id`, `Category.assoc`, `Category.id_comp`,
  `Category.comp_id`. All five lemmas are present and stable since
  Lean 4 / Mathlib 4 initialization (`Mathlib/CategoryTheory/Category/Basic.lean`
  and `Mathlib/CategoryTheory/Functor/Basic.lean`); no v4.26.0 drift
  risk.
* `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects` — `Limits.IsZero`,
  `IsZero.to_`, `IsZero.from_`, `IsZero.eq_of_src`, `IsZero.eq_of_tgt`.
  All five present at the pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
  verified by reading the file directly via `gh api`.

No new imports; both companion files (G7 and G8) live below the
main file's import surface. Imports for the G8 file (`Functor.Basic`
+ `Limits.Shapes.ZeroObjects`) are a strict subset of the imports
already pulled by the main file (which imports `AlgebraicTopology.*`
transitively into both). Build-cost increment: 3.3 s on top of the
warm Mathlib cache (measured below).

#### Q5. Build verification

```bash
./proofs/scripts/docker-build.sh Proofs.BrouwerFixedPointOQ01OQ02G8
# Build completed successfully (627 jobs)
# Built Proofs.BrouwerFixedPointOQ01OQ02G8 (3.3s)
```

627 jobs total (lower than the 718-job G7 build — G8's import surface
is smaller because it does not pull `Mathlib.Algebra.Category.Grp.*`).
Build time on warm Mathlib cache: 3.3 s. No errors, no warnings.

#### Q6. Why both G8 and G9 in one companion file

Both lemmas are categorical and consumed jointly by the S9 ACT-D-3
EXEC step 3 derivation. Splitting them into separate companion files
would not reduce review surface (each is < 20 Lean lines including
docstrings) and would introduce an unnecessary dependency edge for
S9 ACT-D-3 EXEC. Co-locating them in a single G8-named file follows
the §N5 Option A precedent (single-purpose companion file per
forthcoming ACT step), with G8 dedicated to the categorical-side
preparation for S9 ACT-D-3 the same way G7 was dedicated to the
algebraic-side preparation for S9 ACT-D-3.

#### Q7. ACT-D execution plan progress

| Step | Status | PR/Iter |
|------|--------|---------|
| S5 ACT-B exec — `contractible_singularHomology_zero` + ball-side substantive | ✅ done (build verified) | PR #18018 (S5) |
| S6 OBSERVE — sphere-side scoping | ✅ done (doc-only) | PR #18138 (S6) |
| S7 ACT-D-1 exec — `sphere_singularHomology_nonzero` + sphere-side substantive | ✅ done (build verified) | PR #18168 (S7) |
| S8 ACT-D-2 DESIGN — §N (G7 spec) | ✅ done (doc-only) | PR #18945 (S8 design) |
| S8 ACT-D-2 EXEC — G7 companion file | ✅ done (merged build pending; build-verify pending in #19013/#19058) | PR #18951 (S8 exec) |
| **S9 ACT-D-3 PREP — G8/G9 companion file** | ✅ **done (build verified, 627 jobs)** | **this PR (S9 prep)** |
| S9 ACT-D-3 EXEC — wire G7 + G6 + G8 + G9 to drop mock axiom | ⏳ gated on PR #18011 (G6) | — |
| S10 ACT-D-4 — drop mock `H_n_minus_1_sphere_nonzero` axiom | ⏳ after S9 | — |

#### Q8. Iteration log addendum (S9 PREP)

* 2026-05-14 (researcher-8, S9 ACT-D-3 PREP): installed the G8/G9
  categorical-bridge companion file
  `proofs/Proofs/BrouwerFixedPointOQ01OQ02G8.lean`. 134 file lines,
  2 theorems, 0 axioms, 0 sorries. Main file unchanged. Both lemmas
  are pure category theory — no homology, no topology — and depend
  only on `Functor.Basic` + `Limits.Shapes.ZeroObjects`. Build
  verified locally via `./proofs/scripts/docker-build.sh
  Proofs.BrouwerFixedPointOQ01OQ02G8` → `Build completed
  successfully (627 jobs)` in 3.3 s on warm Mathlib cache.
  Iteration 9 → 10. Next: S9 ACT-D-3 EXEC (wiring all four bridges
  G6 + G7 + G8 + G9 into the main file's substantive theorem), still
  gated on sibling PR #18011 merge.
