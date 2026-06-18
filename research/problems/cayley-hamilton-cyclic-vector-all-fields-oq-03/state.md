# Current State

**Phase**: ACT — directions (a) operator forward + (b) PID both COMPLETE + REGISTERED (`Proofs.lean:453/454`, 0 sorry/0 axiom). Operator CONVERSE companion `…OQ03Converse.lean` written + ON main (#25622) but UNREGISTERED + NEVER built green; S8 (this session) completed a full offline bearer/namespace/defeq audit → it is one-shot register-ready, build is the only gate. operator↔K[X] bridge still recipe-only (S6).
**Since**: 2026-06-16 (S3 gallery annotation re-anchor under triple blackout — researcher-8)
**Iteration**: 7

## S6 (2026-06-18, researcher-2): PID file build-readiness RE-CONFIRMED + operator↔K[X] bridge recipe (the real remaining content)

**Status reality check.** The PID companion `CayleyHamiltonCyclicVectorAllFieldsOQ03PID.lean`
written in S5 is now **MERGED to origin/main via PR #25497** (commit `6549be30187`), 0 sorry / 0
axiom — but it is **still UNREGISTERED in `Proofs.lean` and has never been built**. So the only
gating step for direction (b) remains a single green `docker-build.sh` run + registration.

**Independent build-readiness audit (this session, vs offline pin `2df2f0150c` = v4.26.0).**
Re-verified every external bearer the merged file references, with exact file:line, AND checked the
tactic steps are sound:
- `LinearMap.toSpanSingleton` `Span/Basic.lean:702` (`@[simps!]` ⇒ `toSpanSingleton_apply` exists);
  `range_toSpanSingleton` `:751`.
- `LinearMap.quotKerEquivOfSurjective` / `quotKerEquivRange` `Isomorphisms.lean:45/39`.
- `LinearMap.range_eq_top` `Submodule/Range.lean:95`.
- `Module.annihilator` / `Module.mem_annihilator` `Ideal/Maps.lean:820/822`; `(annihilator).IsTwoSided`
  instance `:825` (needed for the next lemma).
- `Ideal.Quotient.span_singleton_one (I) [I.IsTwoSided] : Submodule.span A {(1 : A⧸I)} = ⊤`
  `Ideal/Quotient/Operations.lean:483`.
- `Module.exists_ker_toSpanSingleton_eq_annihilator [Module.Finite R M]` `Algebra/Module/PID.lean:273`
  (in `namespace Module`; `variable (R M)` is explicit at `:254`, so the file's named-arg call
  `(R := R) (M := M)` is correct).
The `smul_comm` step is fine (`CommRing R ⇒ SMulCommClass R R M`). **No bearer or tactic-soundness
issue found — the file should build green on first try.** (Only residual risk, as S5 flagged: the
`rw [hx] at e` type-rewrite inside the equiv type in `exists_injective_quotient_annihilator_hom`.)

**Operator↔K[X] bridge — now a build-ready recipe, not a vague "optionally specialize".**
S5's step 4 ("specialize R:=K[X], M:=V") is the genuine remaining *content* of OQ-03 (it's what the
problem literally asks: recognize the matrix theorem as an instance of the PID structure theorem via
`V` as a `K[X]`-module). The infrastructure is all in Mathlib at pin and far lighter than the old
"heavy AEval bridge" gap estimate:
- **`Module.AEval' T`** (`Algebra/Polynomial/Module/AEval.lean`): `V` with `X` acting as `T`, for
  `T : Module.End K V` (= `V →ₗ[K] V`). Canonical equiv `AEval'.of T : V ≃ₗ[K] AEval' T` (`:198`);
  `AEval'.X_pow_smul_of : Xⁿ • of v = of ((T^n) • v)` (`:205`);
  instance `Module.Finite K[X] (AEval' T)` when `FiniteDimensional K V` (`:93/211`).
- **`Module.span_minpoly_eq_annihilator (T) : Ideal.span {minpoly K T} = Module.annihilator K[X] (AEval' T)`**
  (`LinearAlgebra/AnnihilatingPolynomial.lean:166`) — the linchpin: identifies the K[X]-annihilator
  with the minpoly ideal, so "order ideal = char ideal" becomes literally `minpoly K T`.
- **Worked template: `FieldTheory/Galois/NormalBasis.lean:38-58`** uses *exactly* this combo
  (`exists_ker_toSpanSingleton_eq_annihilator K[X] (AEval' …)` + `span_minpoly_eq_annihilator` +
  `AEval'.X_pow_smul_of`) to build a cyclic generator. Mirror it.

Draft statements for a new companion `…OQ03Bridge.lean` (imports
`Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ03PID` to reuse `cyclic_iff_nonempty_equiv_quotient_annihilator`):

    -- Corollary of the merged PID theorem + span_minpoly_eq_annihilator (LOW risk: ~2 rewrites,
    -- watch the quotient-type motive when rewriting ann → span{minpoly}).
    theorem aeval_cyclic_iff_equiv_quot_minpoly (T : V →ₗ[K] V) [FiniteDimensional K V] :
        (∃ w : Module.AEval' T, Submodule.span K[X] {w} = ⊤) ↔
          Nonempty (Module.AEval' T ≃ₗ[K[X]] K[X] ⧸ Ideal.span {minpoly K T})

    -- Orbit dictionary (HARDER: the genuinely new lemma; transfer span ⊤ across AEval'.of using
    -- X_pow_smul_of so K[X]·of(v) = of(K-span{Tⁿv})). This is the right Aristotle target once the
    -- MCP 404 clears.
    theorem aeval_cyclic_iff_krylov_span_top (T : V →ₗ[K] V) [FiniteDimensional K V] :
        (∃ w : Module.AEval' T, Submodule.span K[X] {w} = ⊤) ↔
          (∃ v : V, Submodule.span K (Set.range fun n : ℕ => (T ^ n) v) = ⊤)

Composing the two recovers OQ-03's headline "T nonderogatory (minpoly = charpoly) ⟺ T has a cyclic
vector" in the K[X]-module vocabulary, completing the conceptual ask of the problem.

**Blackout this session:** BOTH `docker info` (rc=124, daemon unresponsive, load ~19) AND Aristotle
MCP `prove` (`Resource not found`, 404) are down — could not build or auto-prove, so deliberately did
NOT blind-commit the bridge `.lean` (the orbit dictionary needs build iteration). Recipe above is the
ready artifact for the next Docker-up / Aristotle-up session.

## S5 (2026-06-17, researcher-9): PID half WRITTEN — proof simplified, structure-theorem/length machinery ELIMINATED

**Key correction to S2/S4's recipe: the (⇐) direction needs NO IsArtinian / Module.length /
structure-theorem cancellation.** The headline equivalence

    (∃ x, Submodule.span R {x} = ⊤)  ↔  Nonempty (M ≃ₗ[R] R ⧸ Module.annihilator R M)

holds over **any commutative ring** (no PID hypothesis). Reason: `R ⧸ I` is *always* cyclic
(generated by `1` — `Ideal.Quotient.span_singleton_one`), so an iso `M ≃ R ⧸ ann(M)` transports
that generator straight back. The S4 "crux risk" (constructing `IsArtinian R M` for f.g. torsion
over a PID via the structure theorem) is moot — it was only needed for a length argument the proof
doesn't use.

**Written:** `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ03PID.lean` (committed this session,
UNREGISTERED, 165 lines, 0 sorry / 0 axiom). Contents:
- `ker_toSpanSingleton_eq_annihilator_of_span_eq_top` — `ker(r↦r•x) = ann(M)` when `x` generates.
- `exists_span_eq_top_of_equiv` — cyclicity transfers along any `M ≃ₗ N`.
- `cyclic_iff_nonempty_equiv_quotient_annihilator` — **headline (⟺), any comm ring.**
- `exists_injective_quotient_annihilator_hom` — PID: canonical injective `R⧸ann ↪ M` via
  `Module.exists_ker_toSpanSingleton_eq_annihilator` + `quotKerEquivRange` (the only place the PID
  hyp is used; "largest invariant factor always sits inside M").
- `cyclic_iff_canonical_candidate_spans` — PID restatement.

**Every lemma name + signature verified against offline mathlib4 pin `2df2f0150c` (v4.26.0)** before
writing: `LinearMap.{toSpanSingleton,toSpanSingleton_apply(@[simps!]-generated),range_toSpanSingleton,
quotKerEquivOfSurjective,quotKerEquivRange,range_eq_top}`, `Module.{annihilator,mem_annihilator,
exists_ker_toSpanSingleton_eq_annihilator}`, `Ideal.Quotient.span_singleton_one` (needs `I.IsTwoSided`
— auto for CommRing, `Ideal/Defs.lean:113`), `Submodule.{mem_span_singleton,mem_top}`. CommRing gives
`SMulCommClass R R M` for the `smul_comm` step.

**Build NOT run this session — host contention (11 lean-build containers, load ~18, ≤2-container
good-citizen rule; docker-build.sh does a fresh mathlib clone per run).** File is unregistered so it
cannot break the fleet build. Aristotle MCP still returns 404.

**Next Docker-light session (≤2 containers):**
1. `./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ03PID` — grep log for `error:`.
2. Likely-fragile spots if red (all high-level, should be robust): the `rw [hx] at e` type-rewrite in
   `exists_injective_quotient_annihilator_hom` (rewriting `ker f → ann` inside the equiv type — if the
   motive complains, transport via `LinearEquiv.trans`/`Submodule.Quotient.equiv` instead); the
   `simpa using h` reducing `(range.subtype.comp e) a = ... b` to `↑(e a)=↑(e b)`.
3. On GREEN: register in `Proofs.lean`, add gallery dir `src/data/proofs/cayley-hamilton-cyclic-vector-all-fields-oq-03-pid/`
   (status verified, badge mathlib — delegates the deep generator-existence to Mathlib's PID structure thm).
4. Optionally specialize `R := K[X]`, `M := V` to recover OQ-03's operator "nonderogatory ⟺ cyclic" form.

## S4 (2026-06-17, researcher-11): PID recipe bearer RE-CONFIRM + crux risk pinpointed (offline source now available)
**Corrects S3's "no usable offline mathlib source".** The standalone checkout
`/Users/rwalters/GitHub/mathlib4` is at the exact pin (`2df2f0150c` = v4.26.0). Re-audited the
S2 build-ready recipe against it — **every bearer still resolves**, with exact file:line:
- `Module.exists_ker_toSpanSingleton_eq_annihilator` — `Mathlib/Algebra/Module/PID.lean:273` (the
  linchpin: produces the cyclic-generator candidate `x` with `ker(toSpanSingleton x) = ann(M)`).
- `LinearMap.toSpanSingleton` `Span/Basic.lean:702`, `range_toSpanSingleton` `:751`,
  `ker_toSpanSingleton` `:816`, range≃`R∙x` equiv `:854`.
- `Module.length_eq_add_of_exact` `RingTheory/Length.lean:153`, `Module.length_eq_zero_iff` `:49`,
  `Module.length_ne_top [IsArtinian][IsNoetherian]` `:106`.
- `Module.mem_annihilator` `RingTheory/Ideal/Maps.lean:822`.

**CRUX RISK SHARPENED (the real remaining work, not a freebie).** The (←) length argument needs
`[IsArtinian R M]`, and **Mathlib has NO direct lemma `f.g. torsion over a PID ⟹ IsArtinian /
IsFiniteLength`** at pin. The only route is `isFiniteLength_iff_isNoetherian_isArtinian`
(`RingTheory/FiniteLength.lean:73`), so `IsArtinian R M` must itself be CONSTRUCTED (via the
structure theorem `Module.equiv_directSum_of_isTorsion` → each `R ⧸ (pⁱ)` summand is Artinian →
`isArtinian_of_quotient_of_artinian` `Artinian/Module.lean:256` + `isArtinian_prod`/`pi`). This is
the genuine ≥30-LOC sub-obligation hidden inside the recipe's "discharge the IsArtinian/length
sub-obligations" bullet — it needs build iteration, not a one-citation close.

**Build reality this session:** Docker daemon UP, but host **heavily contended** (load avg ~29,
8 concurrent `lean-build` containers). docker-build.sh does a fresh mathlib clone per run (~minutes);
the PID file needs multiple such cycles. Per the ≤2-container good-citizen rule, did NOT run the
multi-cycle iteration into a load-29 host racing 8 peers, and did NOT blind-write the finicky
IsArtinian-dependent proof (role + file both warn). Aristotle `prove` still **404**. Released.
**Next clean Docker-up (≤2 containers) session:** write the PID file, building the `IsArtinian R M`
instance FIRST (the structure-theorem route above), then the length close — budget for ~5+ build cycles.

## S3 (2026-06-16, researcher-8): gallery annotation re-anchor (verifiable, blackout-safe)
Resolver `validate` reported 1/6 misaligned: `chcv-oq03-ann-main` ("Main Theorem:
Basis Reduction and Pullback") was anchored at startLine 141 — an empty line before
the SECTION III divider comment, no Lean construct there. The annotation describes
`operator_nonderogatory_has_cyclic_vector` (line 172). Re-anchored its range to
168–214 (doc-comment start through theorem body) → resolver now 6/6 valid.
**No Lean edits** (file is registered in `Proofs.lean:447`; editing it is Docker-gated).
Triple blackout reconfirmed this session: Docker `docker run alpine` rc=124; Aristotle
MCP `prove` returns 404 "Resource not found"; no usable offline mathlib source
(`.lake/packages/mathlib` is a circular/broken symlink in both worktree and main repo)
so no offline name-audit possible. Direction (b) PID companion deliberately NOT written
blind — the build-ready recipe below remains the next Docker-up action.

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

## S7 (2026-06-18, researcher-2): CONVERSE companion written — closes the operator biconditional
**Both directions (a) operator and (b) PID are now DONE + REGISTERED** (OQ03 + OQ03PID
on main, 0 sorry / 0 axiom, PR #25497 + #25552). S6's last open nextStep (register PID)
is complete. Re-scoping the problem, the genuine remaining gap was that the OQ03 headline
**operator** theorem is **forward-only** (`operator_nonderogatory_has_cyclic_vector` and
its span recast `operator_nonderogatory_has_span_cyclic_vector` only give
nonderogatory ⟹ cyclic). The headline is an *iff* ("minpoly = charpoly ⟺ cyclic vector"),
so the converse was missing at the operator level.

**Wrote `CayleyHamiltonCyclicVectorAllFieldsOQ03Converse.lean`** (UNREGISTERED, cannot
break the fleet build):
- `span_cyclic_implies_nonderogatoryOp` — `cyclicSubspace T v = ⊤ ⟹ (minpoly K T).natDegree = finrank K V`.
- `nonderogatoryOp_iff_exists_span_cyclic` — the full biconditional, composing the
  forward capstone with the new converse.

**Proof (all names audited vs offline pin 2df2f0150c):**
- Orbit containment from the registered `NonderogatoryModule.cyclicSubspace_le_minpoly_degree`
  (CayleyHamiltonMinpolyOQ05OQ01OQ03.lean:243): for `k ≥ d`, `Tᵏ v ∈ span{Tⁱ v : i < d}`.
  ⟹ `cyclicSubspace ≤ W := span{Tⁱ v : i<d}`; with `hv` gives `W = ⊤`.
- `finrank K V ≤ d` via `finrank_range_le_card` (Dimension/Constructions.lean:453) + `finrank_top` (Finrank.lean:139).
- `d ≤ finrank K V` via `LinearMap.minpoly_dvd_charpoly` + `LinearMap.charpoly_natDegree` (Charpoly/Basic.lean:99,78).
- Integrality: `IsIntegral.of_finite K T` (End K V is a finite K-algebra).

**Build reality:** Docker daemon UP but host heavily contended (10 `lean-build` containers,
~6.7 of 7.65 GiB VM) — building now would risk OOM-ing peers, against the good-citizen
≤2–3 container rule. Background watcher `/tmp/r2-oq03converse-build.sh` builds the file once
the host frees up and writes `/tmp/r2-oq03converse-build.done`.

**Next action:** On GREEN — register `Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ03Converse`
in `Proofs.lean`, add the converse/iff to the gallery entry, and confirm the headline iff is
stated. On RED — fix the flagged tactic step (math + every lemma name are sound; any failure
is a tactical mismatch, not a missing result).

## S8 (2026-06-18, researcher-6): CONVERSE companion FULLY offline-audited → one-shot register-ready; S7 watcher was killed mid-clone (never built)

**Reality reconciled.** Top-of-file Phase header was stale ("PID still UNREGISTERED") — both
`OQ03` and `OQ03PID` are registered (`Proofs.lean:453/454`). The S7 background watcher
`/tmp/r2-oq03converse-build.sh` **started but was killed (`Terminated: 15`) mid mathlib-clone**;
no `/tmp/r2-oq03converse-build.done` exists and the watcher process is dead — so the Converse file
has **never actually built green**. It IS committed to `origin/main` (via #25622) but is **absent
from `Proofs.lean`** (not in the fleet build), so its compilation status was unverified going into
this session.

**Full offline audit vs pin `2df2f0150c` (= v4.26.0, `/Users/rwalters/GitHub/mathlib4`).** Audited
every bearer in `CayleyHamiltonCyclicVectorAllFieldsOQ03Converse.lean` (5208 B, 2 theorems,
0 sorry/0 axiom) — names, namespaces, AND the two definitional `rfl`s:

Project-local (registered, present):
- `IsNonderogatoryOp` def — `OQ03.lean:100` ✓
- `operator_nonderogatory_has_span_cyclic_vector` — `OQ03.lean:280` ✓
- `NonderogatoryModule.cyclicSubspace` (def) + `cyclicSubspace_le_minpoly_degree`
  — `CayleyHamiltonMinpolyOQ05OQ01OQ03.lean:243`; signature
  `(T)(hT:IsIntegral K T)(v)(∀ k, (minpoly K T).natDegree ≤ k → (T^k)v ∈ span K (range fun i:Fin … ))`
  EXACTLY matches the call `… T hint v k (by omega)` (the `by_cases ¬k<d` branch gives `d ≤ k`). ✓

Mathlib (all resolve at pin, namespaces confirmed):
- `IsIntegral.of_finite` — `RingTheory/IntegralClosure/Algebra/Basic.lean:64` (needs `Module.Finite K (End K V)`, auto from `FiniteDimensional`). ✓
- `finrank_range_le_card {ι}[Fintype ι](b:ι→M) : (Set.range b).finrank R ≤ Fintype.card ι`
  — `LinearAlgebra/Dimension/Constructions.lean:453`; `rw [Fintype.card_fin]` ⇒ `≤ d`. ✓
- `finrank_top : finrank R (⊤:Submodule R M) = finrank R M` — `Dimension/Finrank.lean:139`
  (the `IntermediateField.finrank_top` homonyms are `protected`, so no clash with `open Polynomial` only). ✓
- `Set.finrank s := finrank R (span R s)` — `Constructions.lean:442` ⇒ the line-82 `rfl`
  `finrank K (span K (range f)) = (range f).finrank K` holds by definitional unfold. ✓
- `LinearMap.minpoly_dvd_charpoly` — `Charpoly/Basic.lean:99` (in `namespace LinearMap`, 41–135). ✓
- `LinearMap.charpoly_natDegree` (`[Nontrivial R][StrongRankCondition R]`, both hold for a field)
  — `Charpoly/Basic.lean:78`; `: f.charpoly.natDegree = finrank R M`. ✓
- `LinearMap.charpoly_monic` (⇒ `.ne_zero`) — `Charpoly/Basic.lean:74`. ✓
- `Polynomial.natDegree_le_of_dvd (h1:p∣q)(h2:q≠0) : p.natDegree ≤ q.natDegree`
  — `Algebra/Polynomial/Degree/Domain.lean:61` (in `namespace Polynomial`, 27–98). ✓

**Verdict: no bearer/namespace/`rfl`/signature issue found.** Residual risk is only the standard
`set W …`/`set d …` + `exact` defeq unification (the lemma's span output unifying with the `let`-bound
`W`) — low, idiomatic. The file should build green on first try; registration is the SOLE remaining
gate. The next session can skip re-auditing and go straight to build → register → gallery.

**Build blackout this session:** host load **68 on 28 cores, 14 `lean-build` containers** — far above
the load-30 / ≤2–3-container good-citizen rule. Deliberately did NOT build or relaunch a watcher
(a watcher that may never fire under sustained saturation is not a deliverable, and the prior one was
already reaped). Aristotle MCP not needed (file is sorry-free). Did NOT blind-write the S6 bridge
(its orbit-dictionary `aeval_cyclic_iff_krylov_span_top` needs build iteration — prior sessions
correctly avoided committing it unverified).

**Gallery note (for the eventual register session, not fixed here — it is an auditor concern and
the entry is accurate-to-its-file):** `src/data/proofs/cayley-hamilton-cyclic-vector-all-fields-oq-03/meta.json`
is scoped to `OQ03.lean` (status `formalized`/badge `wip`); its `assumptions` still say
"Build-pending verification" and frame the PID half as "an explicit open gap, not formalized here."
The PID half is now done+registered in the separate `OQ03PID.lean` (which has NO gallery dir). When
the Converse lands, revisit whether this entry should become `verified` and whether PID/converse
deserve their own entries.
