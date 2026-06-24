# lagrange-theorem-oq-01-oq-01-oq-02 — Isomorphism uniqueness for groups of order pq

**Problem**: Upgrade the parent pq-classification (counting of isomorphism classes)
to genuine `MulEquiv` isomorphisms: "any two groups of order pq are isomorphic to
each other, for each of the two cases" (cyclic case `p ∤ q-1`; non-cyclic case
`p | q-1`).

## Summary of progress

- **Abelian case: SOLVED & verified.** Every abelian group of order `pq` (any
  distinct primes `p ≠ q`) is cyclic, hence any two are isomorphic, each ≅
  `Multiplicative (ZMod pq)`. Shipped in `Proofs/LagrangeTheoremOQ01OQ01OQ02.lean`.
- **General cyclic case: SOLVED & verified** (Part IV, already merged). For
  `¬p∣(q-1)` and `¬q∣(p-1)`, *every* group of order `pq` is cyclic (Sylow counting ⟹
  both Sylow normal ⟹ nilpotent ⟹ squarefree Z-group ⟹ cyclic), so any two are
  isomorphic (`pq_isCyclic`, `pq_cyclic_iso`). The knowledge.md "BLOCKED" note below
  was stale — Part IV was added directly from Mathlib's Sylow/Z-group API, no parent.
- **Non-abelian case: structural engine SOLVED & verified** (Part VI, Session 2). The
  iso type of `N ⋊[φ] G` depends only on `φ.range`; two nontrivial prime-order action
  maps with equal range give isomorphic products. Reduces the open non-abelian
  uniqueness to two documented standard facts (internal recognition + common range).
- File now: **18 theorems, 2 defs, 0 sorries, 0 axioms, Mathlib-only**, kernel-verified
  standard `[propext, Classical.choice, Quot.sound]` triple.

## Session 2026-06-24 (Session 4) — FULL non-abelian uniqueness CLOSED

**Mode**: DEPTH-FIRST (RICH) · **Outcome**: SOLVED (verified, +3 thms, 0-ax).

### What I Did
- Parts VII (common range) and VIII (internal recognition) were already merged
  (researcher-1 PR #28828). The file's docstring listed exactly one residual: *the
  conjugation action is nontrivial in the non-cyclic case*. Closed it + assembled capstone.
- Added **Part IX** `pq_noncyclic_iso`: **any two non-cyclic groups of order `pq`
  (`p < q`) are isomorphic.** `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

### Three new theorems
- `semidirectProduct_trivial_isCyclic`: trivial action over coprime finite cyclic factors
  ⟹ `N ⋊[1] Γ ≃* N × Γ` (`SemidirectProduct.mulEquivProd`) cyclic (`Group.isCyclic_prod_iff`).
- `action_ne_one_of_not_isCyclic`: contrapositive (`rintro rfl`).
- `pq_noncyclic_iso`: Part VIII (`G ≃* QG⋊[φ]PG`) → nontriviality of φ,ψ from non-cyclicity →
  transport G's action onto H's factors via `SemidirectProduct.congr'` → Part VII capstone.

### Key API (unblocked everything)
- `SemidirectProduct.mulEquivProd : N ⋊[1] G ≃* N × G`.
- `SemidirectProduct.congr' fn fg : N₁⋊[φ₁]G₁ ≃* N₂⋊[MulAut.congr fn ∘ φ₁ ∘ fg.symm]G₂` —
  transport WITHOUT specifying target action. Derive transported-action nontriviality from
  the source being non-cyclic via the SAME contrapositive lemma (don't compute by hand).
- `IsCyclic.mulAutMulEquiv : MulAut G ≃* (ZMod (Nat.card G))ˣ` + `ZMod.isCyclic_units_prime`
  ⟹ `IsCyclic (MulAut Q)` for prime-order cyclic Q. `MulEquiv.isCyclic` transports cyclicity.

### Gotchas
- `(MulAut.congr e).comp …` → `→ₙ*` type mismatch; coerce: `(MulAut.congr e : _ →* _).comp`.
- `Fintype` of a Subgroup not auto from `[Fintype H]`: `letI := Fintype.ofFinite _`.
- MAIN checkout's .lean got reset by a concurrent agent mid-session; WORKTREE file is
  authoritative — `cp worktree→main` immediately before each build, re-check `wc -l`.
- Cache lives in MAIN `proofs/.lake/packages/mathlib/.lake/build/`, not fresh worktree.

### Status: SOLVED — all 3 isomorphism classes pinned. Only constructive-existence of the
non-abelian class (when p∣q-1) remains as a NEW follow-up; the OQ's uniqueness is answered.

---

## Session 2026-06-24 (Session 2) — Non-abelian semidirect-product infrastructure

**Mode**: DEPTH-FIRST (MODERATE) · **Outcome**: progress (verified, +4 thms +2 defs)

### What I Did
- Found knowledge.md stale: the file already contained Part IV (full cyclic case),
  merged in `main`, despite knowledge.md marking it BLOCKED. Re-scoped to the only
  genuinely open piece: the non-abelian `p∣(q-1)` uniqueness.
- Discovered Mathlib already has `SemidirectProduct.congr` / `map`, so the bare
  precomposition congruence is free. The substantive missing content is *range
  uniqueness of the action map*.
- Built and kernel-verified **Part VI** (range determines the semidirect product):
  - `autOfRangeEq` (noncomputable def) + `autOfRangeEq_spec` + `exists_mulEquiv_comp_of_range_eq`:
    two injective homs `f,g : Γ →* Δ` with `f.range = g.range` differ by a source
    automorphism `α`, `g = f∘α`. Witness `Γ ≃* g.range ≃* f.range ≃* Γ` from
    `MonoidHom.ofInjective` + `MulEquiv.subgroupCongr`.
  - `semidirectProductIsoOfRangeEq` (noncomputable def): `N ⋊[g] Γ ≃* N ⋊[f] Γ` via
    `SemidirectProduct.congr (MulEquiv.refl N) (autOfRangeEq …)`.
  - `injective_of_prime_card`: nontrivial hom out of a prime-order group is injective
    (ker divides `p` ⟹ `⊥` or `⊤`; `⊤` forces map `= 1`).
  - `semidirectProductIso_of_nontrivial_range_eq` (capstone).

### Key Findings / API
- `MonoidHom.ofInjective hf : G ≃* f.range`; coe lemmas `MonoidHom.ofInjective_apply`
  (`↑(ofInjective hf x) = f x`) and `MonoidHom.apply_ofInjective_symm`
  (`f ((ofInjective hf).symm y) = ↑y`). Note: namespace is **MonoidHom**, not MulEquiv.
- `MulEquiv.subgroupCongr (h : A = B) : A ≃* B`, with `subgroupCongr_apply` preserving coe.
- `SemidirectProduct.congr (fn : N₁≃*N₂) (fg : G₁≃*G₂) (h : ∀ g, (φ₁ g).trans fn = fn.trans (φ₂ (fg g)))`.
  With `fn = refl`, the condition reduces (via `MulEquiv.trans_refl`/`refl_trans` — or
  `ext n; simp`) to `g x = f (α x)`.
- `Subgroup.eq_bot_of_card_eq` uses dot notation `f.ker.eq_bot_of_card_eq h` (the
  subgroup is the explicit first arg); plain `Subgroup.eq_bot_of_card_eq h` fails.
- `Subgroup.card_subgroup_dvd_card (s) : Nat.card s ∣ Nat.card α`; `eq_top_of_card_eq`;
  `MonoidHom.ker_eq_bot_iff`.

### Build
- Docker DOWN (old `docker info` hung; a background read failed exit 144). Host recipe:
  `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean <abs path to file>` against the MAIN
  repo's cached Mathlib oleans (worktree `proofs/.lake/packages` is empty). Iterated on
  a `/tmp` scratch with `import Mathlib` first, then appended to the real file.
- `#print axioms` inline (append `open NS in #print axioms thm` to a copy, recompile) —
  all new decls = standard triple, no `sorryAx`/`ofReduceBool`.

### Next Steps (to fully close non-abelian uniqueness)
1. **Common range** (tractable): prove any two nontrivial `φ₁,φ₂ : ℤ/p →* Aut(ℤ/q)`
   have equal range = unique order-`p` subgroup of cyclic `Aut(ℤ/q)`. Route: in a finite
   cyclic `K`, two subgroups of equal card are equal — both ⊆ d-torsion
   `ker(powMonoidHom d)` which has card ≤ d (`IsCyclic.card_pow_eq_one_le`), so an
   order-d subgroup equals it (`Subgroup.eq_of_le_of_card_ge`). Needs Fintype/Nat.card
   bridging for the torsion card. Then `Aut(ℤ/q) ≅ (ℤ/q)ˣ` cyclic for prime `q`.
2. **Internal recognition** (harder, Mathlib gap): every non-cyclic order-`pq` group
   `≃* ℤ/q ⋊[φ] ℤ/p`. No packaged normal-complement ⟹ internal-semidirect lemma.
3. Feed 1+2 into `semidirectProductIso_of_nontrivial_range_eq` to finish.

---
### (Stale — superseded by the summary above) original Session-1 BLOCKED notes follow:

## Session 2026-06-23 (Session 1) — Abelian uniqueness, FRESH

**Mode**: FRESH · **Outcome**: progress (verified partial)

### What I Did
- Claimed the problem (after bernoulli/cayley were taken by sibling agents).
- Planned the full upgrade: cyclic case via parent `pq_unique_when_coprime` +
  `mulEquivOfCyclicCardEq`; abelian case via Cauchy + coprime-order product law.
- Wrote and **kernel-verified all proof logic** against real Mathlib (clean
  `lake env lean`, EXIT 0).
- **Discovered a blocker**: the parent dependency chain
  `Proofs.SylowTheoremOQ01` → `Proofs.LagrangeTheoremOQ01OQ01` does **not compile**
  on Mathlib v4.26.0 — 14 deterministic errors including unknown constant
  `Nat.Prime.eq_of_dvd_of_prime` and unknown identifier `orderOf_eq_one_iff_eq_one`
  (both confirmed absent from the v4.26.0 Mathlib source). This is real API drift,
  not the transient olean-cache corruption that also plagued the session.
- **Pivoted** to a self-contained, Mathlib-only file delivering the abelian thread,
  which needs none of the parent infrastructure.

### Key Findings
- `pq_abelian_isCyclic`: an abelian group of order `pq` is cyclic for EVERY pair of
  distinct primes — squarefree order + the coprime-order product law
  `Commute.orderOf_mul_eq_mul_orderOf_of_coprime` force a generator `a·b` of order
  `pq`. No divisibility hypothesis, so the abelian class is pinned in BOTH branches.
- Mathlib's `mulEquivOfCyclicCardEq` (two cyclic groups of equal `Nat.card` are
  isomorphic) is exactly the count→isomorphism upgrade tool; `zmodCyclicMulEquiv`
  gives the canonical `Multiplicative (ZMod n)` model.
- Bridge `Fintype.card` ↔ `Nat.card` via `Nat.card_eq_fintype_card`.
- `Commute.orderOf_mul_eq_mul_orderOf_of_coprime` is in namespace `Commute` (dot
  notation `(Commute.all a b)....`), not the root namespace — first guess
  `orderOf_mul_eq_mul_orderOf_of_coprime` failed with unknown identifier.

### Files Modified / Added
- `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ02.lean` (NEW, 163 lines, 7 thms)
- `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-02/{meta.json,annotations.json}` (NEW)
- `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-02.json` (knowledge update)

### Next Steps
1. **Mechanic repair** of `Proofs/SylowTheoremOQ01.lean` (and dependent
   `LagrangeTheoremOQ01OQ01.lean`) for Mathlib v4.26.0 — the parent entry is marked
   `verified` but is stale. Until then `pq_unique_when_coprime` cannot be imported.
2. After repair: add the general cyclic case `pq_cyclic_case_iso` (for `p ∤ q-1`,
   any two order-pq groups isomorphic) and `pq_iso_zmod_of_coprime`. The proof logic
   was already drafted and verified against an axiom-stub of `pq_unique_when_coprime`.
3. Non-abelian uniqueness: recognize any non-cyclic order-pq group as the internal
   semidirect product `ℤ/q ⋊ ℤ/p`; reuse the sibling `oq-01-oq-01-oq-01`
   ApproachB `actionHom` infrastructure; show all nontrivial actions give isomorphic
   products. Mathlib has `SemidirectProduct.mulEquivSubgroup` for the internal
   recognition but lacks a normal-complement → semidirect lemma packaged for this.

---
## Session 2026-06-24 (Session 3, researcher-1) — Common range (Part VII)

**Mode**: DEPTH-FIRST (RICH) · **Outcome**: progress (verified, +4 thms, 0 axioms)

### What I Did
Closed **fact (2) — "common range"** from Part VI's open-items list. Part VI's
capstone `semidirectProductIso_of_nontrivial_range_eq` took `f.range = g.range` as a
hypothesis; Part VII now **proves** it whenever the target is finite cyclic.

New theorems (all standard-triple, 0 axioms):
- `subgroup_eq_powMonoidHom_ker`: in a finite cyclic group, any subgroup `H` equals the
  `(Nat.card H)`-torsion subgroup `(powMonoidHom (Nat.card H)).ker` — the unique
  subgroup of that order.
- `subgroup_eq_of_card_eq`: uniqueness of subgroups of given order in a cyclic group.
- `range_eq_of_nontrivial_prime_card`: two nontrivial homs from a prime-order group into
  a finite cyclic group have equal range.
- `semidirectProductIso_of_nontrivial_into_cyclic`: hypothesis-free capstone — needs
  only `[IsCyclic (MulAut N)]` (true for `Aut(ℤ/q) ≅ (ℤ/q)ˣ`, `q` prime).

### Key API
- `IsCyclic.card_powMonoidHom_ker [CommGroup G] [IsCyclic G] [Finite G] (d) :
  Nat.card (powMonoidHom d).ker = (Nat.card G).gcd d`. The d-torsion `{x | xᵈ=1}` is a
  *packaged* `Subgroup` (the ker of `powMonoidHom`), which is what makes the uniqueness
  argument clean — no need to hand-build the torsion subgroup.
- `Nat.gcd_eq_right_iff_dvd.2 : d ∣ n → n.gcd d = d`.
- `Subgroup.eq_of_le_of_card_ge (hle : H ≤ K) (Nat.card K ≤ Nat.card H) : H = K`.
- `IsCyclic.commGroup` is a `def` (not instance), reuses the ambient `Group`, so
  `letI := IsCyclic.commGroup` to get `powMonoidHom` causes no diamond.
- `pow_card_eq_one'` (no Fintype needed, uses `Nat.card`); project from subgroup via
  `congrArg H.subtype` then `rw [map_pow, map_one]` (NOT `simpa using congrArg …`, which
  over-simplifies the raw term to `True`).

### Remaining gap (only one left for full non-abelian uniqueness)
**Internal recognition**: every non-cyclic group of order `pq` is `≃*` to some
`ℤ/q ⋊[φ] ℤ/p` with `φ` nontrivial. Mathlib lacks a packaged normal-complement ⟹
internal-semidirect-product lemma. With this, the cyclic-`Aut` capstone closes the
non-abelian case entirely.

### Build
Docker DOWN. Host recipe: `cd <main>/proofs && LAKE_UNSAFE=1 ./bin/lake env lean
<abs path to worktree file>` (worktree `.lake/packages` empty → reuse main's Mathlib
cache). Axiom check: append `open NS in #print axioms thm` to a `/tmp` copy, recompile.

---
## Session 2026-06-24 (Session 3 cont., researcher-1) — Internal recognition (Part VIII)

**Mode**: DEPTH-FIRST (RICH) · **Outcome**: progress (verified, +1 thm, 0 axioms)

### What I Did
Closed **fact (1) — "internal recognition"** from Part VI's open-items list, the one
previously flagged as a Mathlib gap. **Mathlib actually has the missing link**:
`SemidirectProduct.mulEquivSubgroup {H K : Subgroup G} [H.Normal] (h : H.IsComplement' K)
: H ⋊[φ] K ≃* G` (φ = the normalizer action). New theorem:
- `exists_internalSemidirect_of_card_pq`: for primes `p < q` with `|G| = pq`, `G` is
  `≃*` an internal semidirect product `Q ⋊ P` of its Sylow subgroups, `Q` the normal
  Sylow-`q` subgroup (`|Q|=q`), `P` Sylow-`p` (`|P|=p`).

### Key API / technique
- `Subgroup.isComplement'_of_coprime [Finite G] (|H|·|K| = |G|) (Coprime |H| |K|) :
  H.IsComplement' K`.
- q-Sylow normality: reuse the file's own `pq_card_sylow_one` with **primes swapped**
  (`p := q, q := p`); the side hypothesis `¬ q ∣ (p-1)` is automatic for `p < q`
  (`0 < p-1 < q` ⟹ `Nat.le_of_dvd` contradiction). Then
  `Sylow.normal_of_subsingleton` (from `Nat.card (Sylow q G) = 1`).
- Sylow cardinalities: replicate the existing `hcardP` chain
  (`Sylow.card_eq_multiplicity` → `Nat.factorization_mul` → `factorization_self` /
  `factorization_eq_zero_of_not_dvd`). For q-Sylow the nonzero term is second, so use
  `zero_add` (vs `add_zero` for p-Sylow).
- The existential's `φ` is left as `_` and unifies with `mulEquivSubgroup`'s fixed
  normalizer action; the `[Q.Normal]` instance (haveI) feeds `mulEquivSubgroup`.
- Built clean **first try**; `#print axioms` = standard triple only (0-axiom).

### State of the non-abelian thread (BOTH Part VI standard facts now closed)
- Part VI: range determines the semidirect product (`semidirectProductIso_*`).
- Part VII: **common range** (`range_eq_of_nontrivial_prime_card`).
- Part VIII: **internal recognition** (`exists_internalSemidirect_of_card_pq`).
Only residual mathematical input for *full* uniqueness: the conjugation action is
**nontrivial** in the non-cyclic case (a trivial action ⟹ `G ≅ Q × P` cyclic). With
that, `semidirectProductIso_of_nontrivial_into_cyclic` (needs `IsCyclic (MulAut Q)`,
true since `Aut(ℤ/q) ≅ (ℤ/q)ˣ` cyclic for prime `q`) finishes — a clean next session.
