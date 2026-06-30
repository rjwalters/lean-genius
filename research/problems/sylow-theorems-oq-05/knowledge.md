# Knowledge Base: sylow-theorems-oq-05

Problem: **Formalize the transfer homomorphism G → P/[P,P] and the Sylow subgroup connection.**

---

## Problem Understanding

The transfer (Verlagerung) homomorphism `transfer ϕ : G →* A` is built from a left
transversal of a finite-index subgroup `H ≤ G` and a homomorphism `ϕ : H →* A` into an
abelian group `A`. The instance the problem asks for takes `A = P/[P,P]` for a Sylow
`p`-subgroup `P`, giving the map `G → P/[P,P]` underlying the focal-subgroup theorem.

**Mathlib status (proofs/.lake/.../GroupTheory/Transfer.lean):**
- HAS: `MonoidHom.transfer`, `diff`, `transferCenterPow`, `transferSylow`,
  Burnside's normal p-complement theorem (`ker_transferSylow_isComplement'`),
  `IsCyclic.isComplement'`.
- LACKS: naturality of `transfer` in `ϕ`; the abelianization target `G → P/[P,P]`;
  any `focalSubgroup` / focal-subgroup theorem.

---

## Insights

- **`diff` is literally a finite product `∏_{q∈G/H} ϕ⟨…⟩`.** Hence the transfer is
  *natural in its coefficient homomorphism*: for `ψ : A →* B`,
  `transfer (ψ.comp ϕ) = ψ.comp (transfer ϕ)` (`transfer_comp`). Proof of the diff
  version is `unfold diff; rw [map_prod]; rfl`. This is the engine for everything.
- **G → P/[P,P] is the universal abelian transfer.** Since `A` abelian ⇒ every
  `ϕ : H → A` factors through `Abelianization.of`, naturality forces
  `transfer ϕ = (Abelianization.lift ϕ).comp (transferAb H)`
  (`transfer_eq_lift_comp_transferAb`). `transferAb H := transfer Abelianization.of`.
- **Universality is a kernel statement:** `ker(transferAb H) ≤ ker(transfer ϕ)` for
  all `ϕ` (`transferAb_ker_le`) — it is the finest abelian transfer.
- **Mathlib's `transferCenterPow` is one instance** of the factorization:
  `transferCenterPow G = (Abelianization.lift id).comp (transferAb (center G))`.

## Dead Ends

- **Direct factorization of Burnside's `transferSylow` through `transferAb`**
  (for an abelian Sylow) **times out at `whnf` even at 2,000,000 heartbeats.**
  `transferSylow` equips `↥P` with an ad hoc `CommGroup.ofIsMulCommutative` instance
  that does not reduce against the subgroup's group structure — a genuine instance
  diamond. The universal property is therefore stated abstractly
  (`transferSylowAb_universal`) and the clean concrete factorization is demonstrated
  on the **center**, whose `CommGroup` instance is canonical. Resolving this diamond
  is left as an open question.

## Verification

- Verified single-file via `lake env lean Proofs/SylowTheoremsOQ05.lean` against the
  prebuilt `.lake` (Docker daemon down). EXIT=0.
- `#print axioms` on all 6 theorems + 2 defs: only `propext`, `Classical.choice`,
  `Quot.sound`. No `sorryAx`, no `Lean.ofReduceBool`, no `native_decide`.
- Status: **verified / original**, 0 axioms, 0 sorries. 157 lines.

## Session 2026-06-25 (Session 1) — FRESH

**Outcome:** completed (verified, 0-axiom, original).
Built `Proofs/SylowTheoremsOQ05.lean`: `diff_comp`, `transfer_comp`, `transferAb`,
`transfer_eq_lift_comp_transferAb`, `transferAb_ker_le`, `transferSylowAb`,
`transferSylowAb_universal`, `transferCenterPow_eq_lift_comp_transferAb`.
Gallery entry `src/data/proofs/sylow-theorems-oq-05/` (meta + annotations).
Registered module in `proofs/Proofs.lean`.

### Next Steps
- Formalize the focal-subgroup theorem (image of `transferSylowAb P` = `P/(P∩[G,G])`).
- Resolve the CommGroup instance diamond to connect to Burnside's `transferSylow`.
