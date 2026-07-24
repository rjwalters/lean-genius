# Knowledge Base: cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-03

## Session 2026-07-22 (researcher-1) — MASA capstone: C(T) is a maximal abelian subalgebra of minimal dimension

New file `CayleyHamiltonCyclicVectorAllFieldsOQ02OQ03Masa.lean` (139 lines, namespace
`EndCyclicCommutant`, imports `...OQ02OQ03Frobenius`). VERIFIED clean Docker build
(v4.31.0); all four theorems `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(0 axioms / 0 sorries). Coordinate-free lift of the matrix MASA file (OQ02OQ02Masa):

- `end_self_mem_centralizer` — T ∈ C(T) (trivial).
- `end_centralizer_isMaximalCommutative` — for ANY T (no cyclic vector, no finite
  dimension): a commutative subalgebra A ⊇ C(T) equals C(T). Formal argument: a ∈ A
  commutes with T ∈ C(T) ⊆ A.
- `end_centralizer_mul_comm_of_cyclic` — commutativity in subalgebra-MEMBERSHIP form
  (route through `end_centralizer_eq_adjoin` + `Algebra.adjoin_singleton_eq_range_aeval`
  + `AlgHom.mem_range`, then `obtain ⟨p, rfl⟩` and `map_mul`/`mul_comm`).
- `end_centralizer_isMasa_of_cyclic` — CAPSTONE: C(T) is commutative ∧ maximal among
  commutative subalgebras ∧ dim_K C(T) = dim_K V (leg 3 = `finrank_centralizer_eq_of_cyclic`).

### Node status after this session
The Module.End lift (this node's stated objective) is COMPLETE and fully rounded out:
both inclusions, subalgebra equality C(T)=K[T], commutativity, Frobenius dimension
equality, evaluation isomorphism C(T) ≃ₗ[K] V, minpoly degree = dim V, and now the
MASA characterization. The ONLY remaining direction is the deep converse
(dim C(T)=n ⟹ cyclic), a structured blocker (needs rational-canonical-form /
invariant-factor infrastructure absent from Mathlib v4.31). Pool status set to
COMPLETED — future work should target the converse as its own problem if RCF infra lands.

### Adversarial notes on the completion claim
- The masa maximality leg is deliberately hypothesis-free (holds for every T); the
  claim of interest for cyclic T is the CONJUNCTION with commutativity + dimension.
- `IsEndCyclicVector` is the degree-< n annihilator-free definition (matches the
  matrix parent), not "Krylov span = ⊤"; the two agree in finite dimension via
  `endKrylov_linearIndependent` (n independent Krylov vectors span).
- No circularity: the masa file consumes only already-#print-verified pieces of this
  node and the general lower bound `CyclicCommutantConverse.endK_centralizer_bound`.

## Session 2026-07-20 (researcher-1) — centralizer = K[T] as a subalgebra equality

Added `end_centralizer_eq_adjoin` to `CayleyHamiltonCyclicVectorAllFieldsOQ02OQ03.lean`
(namespace `EndCyclicCommutant`, Section IV Consequences):

```
Subalgebra.centralizer K ({T} : Set (Module.End K V)) = Algebra.adjoin K {T}
```

for a cyclic endomorphism `T` (hyp `IsEndCyclicVector T v`). Host-verified (this
file is `import Mathlib`-only): compiles, `#print axioms` = `[propext,
Classical.choice, Quot.sound]` (0 sorry / 0 axiom).

This packages the two already-proven inclusions into one canonical statement that
gallery/Mathlib consumers can cite directly:
- `⊆` (needs cyclic vector): `commuting_end_is_polynomial` — a commuting endo is a
  polynomial in `T`.
- `⊇` (trivial): `aeval_end_commute` — every polynomial in `T` commutes with `T`.

### Reusable Lean recipe
- `Algebra.adjoin_singleton_eq_range_aeval` rewrites `Algebra.adjoin K {T}` to
  `(aeval T).range`; range membership is then the anonymous `⟨p, hp.symm⟩`.
- `Subalgebra.mem_centralizer_iff` unfolds `A ∈ Subalgebra.centralizer K s` to
  `∀ g ∈ s, g * A = A * g`; for a singleton, feed `Set.mem_singleton T` /
  `Set.mem_singleton_iff`.
- **Gotcha:** `subst hg` on `hg : g = T` eliminates `T` (not `g`), so later
  references to `T` fail with "unknown identifier"; use `rw [hg]` to rewrite
  `g → T` in the goal instead.

### State of this OQ node
The core lift to `Module.End` is now complete: `commuting_end_is_polynomial`
(centralizer ⊆ K[T]), `aeval_end_commute` (⊇), the Frobenius dimension equality
`finrank_centralizer_eq_of_cyclic`, and now the subalgebra equality. The one
remaining open direction is the **hard converse** (`dim C(T) = n ⟹ T has a cyclic
vector`), which requires rational canonical form / module structure theory and is
not session-sized.

## Session 2026-07-20 (researcher-1) — Frobenius EQUALITY dim C(T) = dim V for cyclic endomorphisms

New file `CayleyHamiltonCyclicVectorAllFieldsOQ02OQ03Frobenius.lean` (namespace `EndCyclicCommutant`,
imports `...OQ02OQ03` + `...OQ02OQ01`). VERIFIED clean Docker build (v4.31.0); all three theorems
depend only on `[propext, Classical.choice, Quot.sound]` (0 axioms / 0 sorries, `#print axioms`).

Sharpens the general Frobenius LOWER bound (`CyclicCommutantConverse.endK_centralizer_bound`:
`dim_K V ≤ dim_K C(φ)` for every φ, already proven via PID primary decomposition) to an EQUALITY
in the cyclic case:

- `commuting_end_eq_of_apply_eq` — two operators commuting with T that agree on a cyclic vector v
  are equal. (They agree on the whole Krylov basis {Tᵏv} since A·Tᵏv = Tᵏ·Av; `Basis.ext`.)
  = injectivity of the evaluation map A ↦ A·v on the centralizer.
- `finrank_centralizer_le_of_cyclic` — dim C(T) ≤ dim V, via that injective K-linear eval map
  `↥(toSubmodule (centralizer K {T})) →ₗ[K] V`, `LinearMap.finrank_le_finrank_of_injective`.
- `finrank_centralizer_eq_of_cyclic` — dim C(T) = dim V (`le_antisymm` of the two bounds).

This is the minimal-centralizer / nonderogatory edge of the triangle nonderogatory ⟺ cyclic ⟺
C(T)=K[T], lifted to the coordinate-free Module.End setting (the matrix analogue lived in oq-02-oq-01).

### Findings / reuse
- The recorded next-step "endomorphism Frobenius bound dim C(T) ≥ finrank V" was ALREADY DONE in
  general form as `CyclicCommutantConverse.endK_centralizer_bound` (OQ02OQ01) — reused directly as the ≥ half.
- `commuting_end_is_polynomial` (OQ02OQ03) NOT needed for the ≤ half; the injective-evaluation route
  is more elementary (no polynomial coordinates), only needing the Krylov basis.

### Gotchas (v4.31)
- `Subalgebra.mem_toSubmodule` takes the subalgebra `S` EXPLICITLY: `(Subalgebra.mem_toSubmodule S).mp h`
  (not `(Subalgebra.mem_toSubmodule).mp`, which parses `.mp` on the ∀-expr → "Invalid field mp").
- `Subalgebra.mem_centralizer_iff K` gives `T * A = A * T`; need `.symm` for `A * T = T * A`.
- `Module.finrank K ↥(Subalgebra.toSubmodule S) = Module.finrank K S` by `rfl`.

### Remaining open
- Last edge: centralizer = K[T] (or dim C(T)=n) IMPLIES cyclic vector — the converse completing the triangle.
- Optionally: C(T) = K[T] as an equality of subalgebras in Module.End.

---


Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-07-20 (researcher-1) — triage: tractable layer SATURATED; converse is deep [no change shipped]

Triaged the sole remaining open edge — the **converse** "dim C(T) = finrank V (or C(T) = K[T])
⟹ T cyclic" (the last edge of the cyclic ⟺ C(T)=K[T] ⟺ dim C(T)=n triangle). The two forward
directions and the subalgebra equality `end_centralizer_eq_adjoin` are all DONE (file is
0-sorry/0-axiom, 225 lines). The converse is the nonderogatory characterization, which needs
invariant-factor / rational-canonical-form module theory over K[X] — **searched Mathlib v4.31:
no usable `IsCyclic`/nonderogatory/`minpoly = charpoly ⟹ cyclic` characterization exists**. The
Frobenius `≥` bound is `endK_centralizer_bound` (OQ02OQ01), but the equality-forces-cyclic
direction has no elementary route: `dim C(T) = n` does not imply `dim K[T] = n` directly (only
`dim K[T] = deg minpoly ≤ n`), so the shortcut through `K[T]` fails; genuine structure theory is
required. **BLOCKED (needs materially new mechanism: K[X]-module invariant-factor infra).**
Standing down — no filler shipped. See [[reference-researcher-depthfirst-tier-serves-completed]].

## Session 2026-07-21 (researcher-1-4) — evaluation ISOMORPHISM C(T) ≃ₗ[K] V

**Mode**: build on the Frobenius dimension equality. **Outcome**: progress — 1 def + 1 theorem
(+ 1 def + 1 @[simp] apply lemma), axiom-free (`#print axioms` = `[propext, Classical.choice,
Quot.sound]`). Verified BOTH Docker (`docker-build.sh ...OQ02OQ03Frobenius`, exit 0, 8582 jobs)
and host (`lake env lean` after rebuilding the parent olean chain). File 149→205 lines.

Added to `CayleyHamiltonCyclicVectorAllFieldsOQ02OQ03Frobenius.lean` (Section IV):

- `centralizerEval (T v) : ↥(toSubmodule (centralizer K {T})) →ₗ[K] V`, `A ↦ A·v`.
- `centralizerEval_injective` — injective at a cyclic vector (wraps `commuting_end_eq_of_apply_eq`).
- **`centralizerEvalEquiv (T v hcyc) : C(T) ≃ₗ[K] V`** — the headline: evaluation at a cyclic
  vector is a K-linear ISOMORPHISM of the centralizer onto the whole space. Built via
  `LinearMap.linearEquivOfInjective` (injective + `finrank_centralizer_eq_of_cyclic` equal-dim
  ⟹ bijective). Strengthens the dimension EQUALITY to a canonical equivalence and re-derives it
  as a corollary. It is the K-linear shadow of "V is a free rank-1 module over K[T]=C(T)".
- `centralizerEvalEquiv_apply` `@[simp]`: `e A = (A:End) v` (`rfl`).

### Reusable Lean recipe
- `LinearMap.linearEquivOfInjective f hf hdim : V ≃ₗ[K] V₂` (in
  `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`) turns an injective map between
  equal-finrank finite-dim spaces into an equiv; the `@[simp] linearEquivOfInjective_apply`
  makes the apply lemma `rfl`.
- `finrank_centralizer_eq_of_cyclic` (a `Subalgebra.centralizer` finrank) feeds `hdim`
  directly — `finrank K S = finrank K (↥(toSubmodule S))` is `rfl`.
- Host verify of a `Proofs.*`-importing file needs the WHOLE parent olean chain fresh
  (`incompatible header` on any pre-v4.31 olean): build bottom-up with
  `lake env lean Proofs/X.lean -o .lake/build/lib/lean/Proofs/X.olean`. Docker build does NOT
  persist compatible host oleans. Chain here: Minpoly…WIP04 → CyclicVectorAllFields →
  {OQ01OQ01, OQ02} → OQ02OQ01, OQ02OQ03.

### State of this OQ node (BLOCKED at elementary layer)
The Module.End lift is complete: centralizer=K[T] (`end_centralizer_eq_adjoin`), commutativity
(`end_commutant_commutative`), dimension equality (`finrank_centralizer_eq_of_cyclic`), and now
the evaluation isomorphism (`centralizerEvalEquiv`). The one remaining direction is the deep
converse `dim C(T)=n ⟹ T cyclic`, which needs rational-canonical-form / invariant-factor
infrastructure ABSENT from Mathlib v4.31 — registered as a structured blocker
(reopen: "materially new mechanism required"). Natural adjacent results (minpoly degree = n)
are also gated: `Algebra.adjoin.powerBasis` requires `CommRing S`, which `Module.End K V` is not.
STAND DOWN at the elementary layer for this node.

## Session 6 (2026-07-24, researcher-2): algebra capstone — C(T) ≃ₐ[K] K[X]/(μ_T), χ_T = μ_T

New file `CayleyHamiltonCyclicVectorAllFieldsOQ02OQ03Quotient.lean` (4 theorems, 1 def,
0 axioms, 0 sorries; `#print axioms` = propext/Classical.choice/Quot.sound on all five).

- **`end_charpoly_eq_minpoly_of_cyclic`**: `T.charpoly = minpoly K T` for cyclic `T` — the
  nonderogatory EQUALITY, sharpening the degree identity from Session 4. Six lines:
  `minpoly.dvd` on Cayley–Hamilton (`LinearMap.aeval_self_charpoly`) + both monic +
  degrees agree ⟹ `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`.
- **`centralizerQuotientAlgEquiv : K[X] ⧸ span {minpoly K T} ≃ₐ[K] centralizer K {T}`** —
  the headline: the commutant is the polynomial quotient algebra, not merely a
  `dim V`-dimensional space. First isomorphism theorem for `aeval T`.
- `centralizerQuotientAlgEquiv_mk_coe` `@[simp]`: the equiv is induced by evaluation
  (`mk p ↦ p(T)`), proved by `simp` on the composite.
- `finrank_quotient_span_minpoly_of_cyclic`: `dim K[X]/(μ_T) = dim V` (Frobenius equality
  transported through the equiv's `toLinearEquiv.finrank_eq`).

### Reusable Lean recipe (quotient-algebra presentation of a commutant)
- Mathlib has ALL the glue: `minpoly.ker_aeval_eq_span_minpoly` (kernel of `aeval` is the
  span of the minpoly, unconditional over a field), `AlgHom.ker_rangeRestrict`,
  `AlgHom.rangeRestrict_surjective`, `Ideal.quotientKerAlgEquivOfSurjective` (first iso
  theorem for algebras), `Ideal.quotientEquivAlgOfEq` + `Subalgebra.equivOfEq` for
  transporting the two endpoint equalities. Note `ker_aeval_eq_span_minpoly` lands in
  `K[X] ∙ μ` form — bridge to `Ideal.span {μ}` with `Ideal.submodule_span_eq`.
- The cyclic hypothesis enters ONLY at the final subalgebra equality
  (`end_centralizer_eq_adjoin`); everything upstream is generic. The Session-5 gate note
  ("adjoin.powerBasis needs CommRing S") is bypassed entirely — no power basis needed.
- `LinearMap.charpoly_natDegree` takes the map explicitly (`T.charpoly_natDegree`), not
  as an instance-implicit trailing argument.
