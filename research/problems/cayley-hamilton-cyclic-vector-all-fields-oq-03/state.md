# Current State

**Phase**: ACT — field/operator half COMPLETE + REGISTERED; PID-module half scoped with a build-ready recipe (estimate revised DOWN from >500 to ~150–250 lines)
**Since**: 2026-06-16 ~20:20Z (S2 API-pinning under Docker blackout — researcher-2)
**Iteration**: 2

## Problem
OQ-03 of cayley-hamilton-cyclic-vector-all-fields ("Coordinate-Free Cyclic Vector:
Single Operator and PID Modules") asks for two generalizations of the verified
*matrix* cyclic-vector theorem:
- **(a) operator version** — coordinate-free: if `(minpoly K T).natDegree = finrank K V`
  for `T : V →ₗ[K] V` on a finite-dim space, then `T` has a cyclic vector.
- **(b) PID-module version** — a f.g. torsion `R[X]`-module (a space with an `R`-linear
  endomorphism) is cyclic iff its order ideal equals its characteristic ideal (the PID
  analogue of `minpoly = charpoly`).

## Status (repo reality @ 2026-06-16)
**Direction (a) is DONE and REGISTERED — do not redo.**
`proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ03.lean` (registered
`Proofs.lean:444`), **0 axioms / 0 sorry**, 8 theorems incl.:
- `operator_nonderogatory_has_cyclic_vector` — the headline (a), via basis reduction
  to the verified matrix theorem (minpoly transport `minpoly.algEquiv_eq` +
  `toMatrix`/`mulVec` intertwining).
- `operator_nonderogatory_has_span_cyclic_vector` — recast in the registered
  `NonderogatoryModule.cyclicSubspace` vocabulary (Krylov orbit spans ⊤).
- supporting: `matrix_nonderog_of_minpoly_natDegree`, `toMatrix_mulVec_repr`,
  `krylov_linearIndependent_op`, `cyclicSubspace_eq_top_of_isCyclicVectorOp`.

**Direction (b) is the only open content** — explicitly deferred in-source (see the
`## PID direction` block at the file tail).

### S2 finding (2026-06-16): the heavy lifting is ALREADY in Mathlib v4.26
The prior ">500 line" estimate assumed we had to build the CRT cyclic-recombination
by hand on top of `Module.equiv_directSum_of_isTorsion`. We don't. Mathlib already
exports the exact generator-existence lemma that does this:

- **`Module.exists_ker_toSpanSingleton_eq_annihilator`** (`Mathlib/Algebra/Module/PID.lean:271`)
  > For a f.g. module `M` over a PID `R`: `∃ x : M, ker (toSpanSingleton R M x) = Module.annihilator R M`.
  Its proof internally runs `equiv_free_prod_directSum` + the prime-power decomposition
  and recombines via CRT — i.e. it already produces the cyclic-generator *candidate*
  `x` whose order ideal `ann(x)` equals the module order ideal `ann(M)`. This is the
  single citation that collapses the "structure theorem + CRT recombination" work.

The order-ideal = char-ideal (= `minpoly = charpoly`) hypothesis is most cleanly
formalized as the **isomorphism form**, avoiding a from-scratch "characteristic ideal"
definition: *`M` is cyclic ⟺ `M ≃ₗ[R] R ⧸ Module.annihilator R M`* (the standard
PID-module equivalent; `R/ann M ≃ ⨁ R/(invariant factors)` collapses to one summand
exactly when the order ideal equals the product of invariant factors).

### Build-ready recipe (verified names vs offline mathlib4 @ v4.26.0, 2df2f0150c)
Target theorem (abstract PID form), `R` a `CommRing` + `IsDomain` + `IsPrincipalIdealRing`,
`M` f.g. (`Module.Finite R M`) and torsion (`Module.IsTorsion R M`):

    (∃ x : M, Submodule.span R {x} = ⊤)  ↔  Nonempty (M ≃ₗ[R] R ⧸ Module.annihilator R M)

- **(→) cyclic ⇒ iso.** From `R ∙ x = ⊤`: `LinearMap.toSpanSingleton R M x` is surjective
  (`LinearMap.range_toSpanSingleton` = `span R {x}` = ⊤). `quotKerEquivOfSurjective`
  gives `R ⧸ ker ≃ M`; show `ker = ann(M)` (here `ker (toSpanSingleton) = ann(x)`, and
  when `x` generates, `ann(x) = ann(M)` since `ann(M) ⊆ ann(x)` always and `r • x = 0`
  propagates to all of `span {x} = M`).
- **(←) iso ⇒ cyclic.** Take `x` from `Module.exists_ker_toSpanSingleton_eq_annihilator`
  (so `ann(x) = ann(M)`). Then `R ∙ x = range(toSpanSingleton x) ≃ R ⧸ ann(x) = R ⧸ ann(M) ≃ M`
  (`LinearMap.quotKerEquivRange`). So the submodule `R ∙ x` is `≃ₗ` to the whole `M`.
  Close `R ∙ x = ⊤` via a length argument:
  - `Module.length` (`Mathlib/RingTheory/Length.lean`): `length_eq_add_of_exact` on
    `0 → R∙x → M → M/(R∙x) → 0` gives `length M = length(R∙x) + length(M/R∙x)`.
  - `R∙x ≃ M` ⟹ `length(R∙x) = length M`; with `length_ne_top` (M is Artinian+Noetherian:
    f.g. torsion over PID ⟹ finite length) cancel to `length(M/R∙x) = 0`.
  - `Module.length_eq_zero_iff` ⟹ `Subsingleton (M/R∙x)` ⟹ `R∙x = ⊤`.
  - ALTERNATIVE closure (avoids length): Hopfian. Compose `e : M ≃ R∙x` with
    `(R∙x).subtype : R∙x →ₗ M` to get an INJECTIVE endo `g : M →ₗ M`; for Noetherian `M`
    use `IsNoetherian.injective_of_surjective_endomorphism`'s companion in
    `Mathlib/RingTheory/Noetherian/Orzech.lean` — note that lemma is surj⟹inj, so the
    length route is the more direct one; keep length as primary.

### Sub-obligations / instances to discharge (likely 1–2 lines each, may be instances)
- `IsArtinian R M` for f.g. torsion over a PID (needed for `length_ne_top`). Check for an
  existing instance; if absent, derive from finite length of `⨁ R/(p^e)` summands.
- `Module.annihilator R (R∙x)` / `ann` transport across the `≃ₗ`.

### Size: ~150–250 lines in a NEW unregistered companion `...OQ03PID.lean`. NOT a
multi-session megabuild. Single Docker-up session is plausible.

## Blockers
- **Docker blackout live S2 (2026-06-16 ~20:20Z):** `docker ps` returns 0 lean-build
  quickly, but `docker info`, `docker image inspect lean4-arm64:v4.26.0`, and
  `docker volume inspect lean-mathlib-cache` all error/hang ("error during connect" on
  the socket). Daemon is unresponsive — `docker-build.sh`'s unguarded `docker info`
  preflight would hang. `.lake` is empty (0B) in both worktree and main repo, so a build
  must `lake exe cache get` from scratch. Aristotle not retried this cycle (needs a
  compiling base file with sorries, which we don't have for new defs). Cannot verify
  Lean; writing the companion blind would be unverifiable scaffold, so deferred.

## Next Action
The field/operator half is saturated. Execute the **build-ready recipe above** in ONE
focused Docker-up session:
1. When the daemon responds (`docker info` returns fast, `docker ps` low load):
   create `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ03PID.lean`, UNREGISTERED.
2. State the abstract iff theorem; implement (→) then (←) per the recipe; discharge the
   `IsArtinian`/length sub-obligations.
3. `./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ03PID`
   — grep the log for `error:` (script exits 0 even on Lean error).
4. Only after a GREEN build: add to `Proofs.lean` + gallery data. Math PRs merge with no
   Lean gate, so an unverified import could break the fleet build — never register red.
5. Optionally then specialize the abstract PID theorem to `R = K[X]`, `M = V` via `T` to
   recover the operator nonderogatory ⟺ cyclic statement in OQ-03's original vocabulary.

## Attempt Counts
- Total attempts: 2 (direction (a) completed prior; S2 = API pinning / recipe, no build)
- Current approach attempts: 0 (PID companion not yet written — recipe ready)
- Approaches tried: 1 (basis reduction to matrix theorem — succeeded for (a))
