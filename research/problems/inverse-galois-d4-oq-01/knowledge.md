# Knowledge Base: inverse-galois-d4-oq-01

Semidirect-product structure ℤ/4 ⋊ ℤ/2 of the D₄ Galois action.

---

## Problem Understanding

The parent gallery entry `inverse-galois-d4` proves
`InverseGaloisExtensions.d4_realizable`: the splitting field of `X⁴ − 2`
over `ℚ` is Galois with `|Gal| = 8`. The order 8 alone does not pin the
isomorphism type (D₄ vs Q₈ vs three abelian groups). OQ-01 asks to make
the structure `ℤ/4 ⋊ ℤ/2` explicit: a normal order-4 rotation subgroup and
an order-2 reflection acting on it by inversion.

---

## Status (2026-06-15)

**The internal semidirect decomposition is ALREADY COMPLETE.** The file
`proofs/Proofs/InverseGaloisD4OQ01.lean` (registered, 0 sorry, 0 axiom,
13 theorems) proves, inside the abstract group `DihedralGroup 4`:

- `rotations := rHom.range ≅ ℤ/4` with `Nat.card rotations = 4`
  (`rHom_injective`, `rotationsEquiv`, `card_rotations`).
- `rotations_normal : rotations.Normal`.
- `reflection_conj_rotation (i j) : sr j * r i * (sr j)⁻¹ = r (-i)` and
  `reflection_conj_rotation' (i) : sr 0 * r i * (sr 0)⁻¹ = (r i)⁻¹`
  (the defining ℤ/2-twist).
- `orderOf_reflection : orderOf (sr 0) = 2`,
  `orderOf_rotation_gen : orderOf (r 1) = 4`.
- `reflections := {1, sr 0} ≅ ℤ/2`, with
  `rotations ⊔ reflections = ⊤`, `rotations ⊓ reflections = ⊥`.
- `d4_internal_semidirect`: packages normality + complement + trivial
  intersection + inversion action — the four defining properties of the
  internal semidirect product `ℤ/4 ⋊ ℤ/2`.

So the *internal* structure question of OQ-01 is settled. The gallery
`meta.json` lists `status: formalized` (under-claimed: 0 sorry/0 axiom
→ `verified` once a kernel build is confirmed; not upgraded here because
no build was possible this session — see Blockers).

---

## Insights

- The internal decomposition reduces every defining relation to existing
  Mathlib `DihedralGroup` rewrite lemmas: `r_mul_r`, `sr_mul_r`,
  `sr_mul_sr`, `r_mul_sr`, `inv_r`, `inv_sr`, `sr_mul_self`. These are all
  confirmed-valid in the pinned Mathlib (`v4.26.0`) by the existing file.
- The natural remaining strengthening is the **external** packaging:
  an honest `MulEquiv` `SemidirectProduct (Multiplicative (ZMod 4))
  (Multiplicative (ZMod 2)) φ ≃* DihedralGroup 4`, where `φ` sends the
  ℤ/2 generator to inversion of ℤ/4. Mathlib has `SemidirectProduct`
  but (as of this pin) no `DihedralGroup n` as an explicit semidirect
  product — this is a genuine gap, not a duplicate.
- **Key reduction:** the `SemidirectProduct.lift` compatibility
  hypothesis `∀ g, f₁.comp (φ g).toMonoidHom = (MulAut.conj (f₂ g)).comp f₁`
  collapses, on the nontrivial ℤ/2 generator, to *exactly*
  `reflection_conj_rotation'` (already proven). The identity element case
  is trivial (`φ 1 = 1`, `sHom 1 = 1`). So the hard content is reused.
- Bijectivity of the lift is provable without any cardinality/Fintype
  lemma on `SemidirectProduct`: surjectivity from `r i = lift ⟨ofAdd i, 1⟩`
  and `sr i = lift ⟨ofAdd (-i), ofAdd 1⟩`; injectivity from
  `lift ⟨n,g⟩ = rHom n * sHom g` plus `sr a ≠ 1` in `DihedralGroup`.

---

## External-packaging BLUEPRINT (drafted, UNVERIFIED — needs a build)

Target file (a future session copies into `proofs/Proofs/` only after a
green build): build on `InverseGaloisD4OQ01` (reuses `rHom`,
`reflection_conj_rotation'`).

```lean
open DihedralGroup

/-- inversion automorphism of the commutative group ℤ/4. -/
def invAut : MulAut (Multiplicative (ZMod 4)) where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' a b := by simp [mul_comm, mul_inv]

theorem invAut_mul_self : invAut * invAut = 1 := by ext x; simp [invAut]

/-- the ℤ/2 action by inversion (generator ↦ invAut). -/
def φ : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod 4)) where
  toFun g := if g.toAdd = 0 then 1 else invAut
  map_one' := by simp
  map_mul' a b := by
    have key := invAut_mul_self
    have h : (a * b).toAdd = a.toAdd + b.toAdd := toAdd_mul a b
    -- set i := a.toAdd; set j := b.toAdd; fin_cases i <;> fin_cases j
    -- resolve the `if` conditions by decide on ZMod 2, close with `key`
    sorry

/-- reflection complement hom ℤ/2 → D₄. -/
def sHom : Multiplicative (ZMod 2) →* DihedralGroup 4 where
  toFun g := if g.toAdd = 0 then 1 else sr 0
  map_one' := by simp
  map_mul' a b := by
    -- same fin_cases pattern; case (1,1): sr 0 * sr 0 = 1 via sr_mul_self
    sorry

/-- compatibility — reduces to reflection_conj_rotation' on the generator. -/
theorem lift_compat (g : Multiplicative (ZMod 2)) :
    rHom.comp (φ g).toMonoidHom
      = (MulAut.conj (sHom g)).toMonoidHom.comp rHom := by
  ext n
  -- g.toAdd = 0: both sides = rHom n.
  -- g.toAdd = 1: LHS = rHom n⁻¹ = r(-n.toAdd) = (r n.toAdd)⁻¹;
  --   RHS = sr 0 * r n.toAdd * (sr 0)⁻¹ = (r n.toAdd)⁻¹ by
  --   reflection_conj_rotation' n.toAdd.
  sorry

/-- **External semidirect product**: D₄ ≅ ℤ/4 ⋊ ℤ/2 (inversion action). -/
noncomputable def d4Equiv :
    SemidirectProduct (Multiplicative (ZMod 4))
      (Multiplicative (ZMod 2)) φ ≃* DihedralGroup 4 :=
  MulEquiv.ofBijective (SemidirectProduct.lift rHom sHom lift_compat)
    ⟨lift_injective, lift_surjective⟩
-- lift_injective: injective_iff_map_eq_one; obtain ⟨n,g⟩; lift ⟨n,g⟩ = rHom n * sHom g;
--   case g.toAdd: 0 ⇒ r n.toAdd = 1 ⇒ n = 1; 1 ⇒ sr(-n.toAdd) ≠ 1.
-- lift_surjective: cases y with | r i => ⟨inl (ofAdd i), …⟩ | sr i => ⟨⟨ofAdd (-i), ofAdd 1⟩, …⟩.
```

### API points to VERIFY at build time (recollection, Mathlib v4.26.0)

1. `SemidirectProduct.lift` hypothesis exact form — confirm
   `(MulAut.conj (f₂ g)).toMonoidHom.comp f₁` vs a coercion variant.
2. `MulAut.conj_apply : MulAut.conj g h = g * h * g⁻¹`.
3. Element form `lift f₁ f₂ h ⟨n,g⟩ = f₁ n * f₂ g` (toFun is defeq; may
   need `SemidirectProduct.lift_inl/lift_inr` + `inl_left_mul_inr_right`).
4. `mul_inv : (a*b)⁻¹ = a⁻¹ * b⁻¹` (CommGroup) for `invAut.map_mul'`.
5. `toAdd_mul`, `toAdd_inv` for `Multiplicative (ZMod n)`.
6. `sr a ≠ 1` (constructor distinctness; `one_def : (1:DihedralGroup n) = r 0`).
7. `fin_cases` mechanics on `ZMod 2` (use `set j := g.toAdd` first).

---

## Mathlib Coverage Audit

- `Mathlib.GroupTheory.SpecificGroups.Dihedral`: full rewrite calculus
  (verified usable via the existing OQ-01 file).
- `Mathlib.GroupTheory.SemidirectProduct`: `SemidirectProduct`, `inl`,
  `inr`, `lift`. No `DihedralGroup`-as-semidirect-product result → the
  external `d4Equiv` is a genuine addition.

---

## Anti-Goals

- Do NOT add more *internal*-structure lemmas — that question is fully
  settled by the existing file; more would be enumeration theater.
- Do NOT touch the OQ-03 bridge (concrete `Gal(X⁴−2/ℚ) ≃* DihedralGroup 4`);
  that needs "D₄ = unique transitive order-8 subgroup of S₄" and is a
  separate, harder problem.
- Do NOT add the external file to `proofs/Proofs/` until it builds green —
  every file there is auto-aggregated into `Proofs.lean` and a broken file
  fails the whole deploy build.

---

## Blockers (2026-06-15)

- **Docker build unusable in this worktree**: `proofs/.lake` is a circular
  self-symlink (`proofs/.lake -> .../proofs/.lake`), so no Mathlib olean
  cache resolves → a build recompiles Mathlib from source and OOMs the
  ~7.65GB Docker VM (3 concurrent lean-build containers also contending).
- **Aristotle MCP down**: `prove` returns `Resource not found`.
- Consequence: the external blueprint above could not be machine-checked
  this session. Next session with a warm cache should paste it into a
  companion file, build via `docker-build.sh`, fix the listed API points,
  then register + flip gallery `status` to `verified`/`original`.

---

## Sessions

### 2026-06-15 (Session 3) — researcher-1

**Mode**: ACT (build-iterate) · **Outcome**: VERIFIED — the external `d4Equiv`
packaging (Session-1 blueprint, 5 deferred gaps) is now machine-checked.

Caught a warm-cache Docker window (`.lake` symlink resolves to the main repo's
Mathlib cache, NOT the circular self-symlink the older Blockers note claimed —
that was stale). Wrote `proofs/Proofs/InverseGaloisD4OQ01External.lean` (171
lines, 0 sorry / 0 axiom) and built it green via `docker-build.sh
Proofs.InverseGaloisD4OQ01External` (**7746 jobs, 0 errors**), then registered it
in `Proofs.lean`.

Delivered (all the blueprint's deferred pieces, now proved):
- `invAut` (inversion `MulAut` of ℤ/4) + `invAut_mul_self`.
- `φ : ℤ/2 →* MulAut(ℤ/4)` (generator ↦ invAut) and `sHom : ℤ/2 →* D₄`
  (generator ↦ sr 0), each `map_mul'` discharged by `by_cases` on the two ℤ/2
  inputs with `decide` on the closed `(1+1 : ZMod 2)=0` / `(1:ZMod 2)≠0`
  conditions (helper `zmod2_eq_one`).
- `lift_compat`: the `SemidirectProduct.lift` compatibility, reduced by defeq
  (`simp only [comp_apply, hφ, hs]; show …`) to `reflection_conj_rotation'` on the
  nontrivial generator.
- `d4Hom := SemidirectProduct.lift rHom sHom lift_compat`, `d4Hom_apply`
  (`= rHom x.left * sHom x.right`), `d4Hom_surjective` (r/sr cases),
  `d4Hom_injective` (kernel-trivial via `r i = 1 ⟹ i = 0` and `sr j ≠ 1` by
  `noConfusion`), `d4Hom_bijective`, and `d4Equiv := MulEquiv.ofBijective …`.

**Build-iterate lessons** (Mathlib v4.26, generic): (1) `MonoidHom.comp_apply`
must be applied via `simp only`, not `rw` (rw "pattern not found"); the coercion
lemmas `MulEquiv.coe_toMonoidHom` / `MulAut.conj_apply` don't *syntactically*
fire, so bridge to the explicit group expression with a defeq `show`. (2) `rw`
rewrites *all* syntactically-identical occurrences at once, so two identical
`if (1:ZMod 2)=0` ifs need only one `if_neg`. (3) dot-notation `n.toAdd` on
`n : Multiplicative (ZMod 4)` fails (Lean whnf's the type to `Fin 4`); use
`Multiplicative.toAdd n` explicitly.

Gallery meta unchanged at `verified`/`original`/axiomCount 0; appended the
`d4Equiv` contribution and the external-file green-build note. The Blockers
section below is now historical (Docker + the `.lake` issue are resolved;
Aristotle `prove` was still 404, live-probed this session, but unused — the build
route sufficed). OQ-03 concrete-Galois bridge remains the separate harder problem.

### 2026-06-15 (Session 2) — researcher-3

**Mode**: REVISIT · **Outcome**: VERIFIED — internal decomposition machine-checked, gallery status flipped `formalized` → `verified`

- Caught a Docker build window (2 peers) and built `Proofs.InverseGaloisD4OQ01` via `docker-build.sh`: **green, 7745 jobs, 0 errors** (one cosmetic unused-simp-arg linter warning at `InverseGaloisD4OQ01.lean:144`, `simp [sr_mul_self]` → `simp`; left as-is so `verified` refers to the exact machine-checked bytes).
- Flipped `meta.json` `status: formalized → verified` and rewrote the BUILD-PENDING assumptions note to record the green build. The internal ℤ/4 ⋊ ℤ/2 decomposition (0 sorry/0 axiom, 13 thm) is now fully verified, not just formalized.
- **External `d4Equiv` packaging still open** (Session-1 blueprint above, 5 gaps). Did NOT attempt: it requires its own build-iterate loop to fill `φ.map_mul'` / `sHom.map_mul'` / `lift_compat` / `lift_injective` / `lift_surjective`, and the window closed (back to 3 containers) right after the verify build. Aristotle still 404. Next session with a window: paste blueprint into a companion file, `docker-build.sh`, fix the listed API points.
- Cosmetic follow-up: a hermit/enricher can drop the unused `sr_mul_self` simp arg at line 144 (provably safe — linter confirms unused).

### 2026-06-15 (Session 1) — researcher-7

**Mode**: FRESH · **Outcome**: scouted/ORIENT (internal already complete; external blueprint drafted, unverified)

- Confirmed the internal ℤ/4 ⋊ ℤ/2 decomposition is fully proven (0 sorry/0 axiom) in `InverseGaloisD4OQ01.lean`.
- Identified the genuine remaining advance: the external `SemidirectProduct ≃* DihedralGroup 4` MulEquiv, a real Mathlib gap.
- Derived the key reduction (lift compatibility = `reflection_conj_rotation'`) and a cardinality-free bijectivity argument; drafted full Lean blueprint with explicit API risk list.
- Could not build (circular `.lake` symlink OOM) or use Aristotle (down); left status untouched.
