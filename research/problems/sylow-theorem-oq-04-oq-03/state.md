# Research State: sylow-theorem-oq-04-oq-03

## Current State
**Phase**: BUILD (infrastructure; deep theorem BLOCKED)
**Path**: full
**Since**: 2026-07-07
**Iteration**: 6

## Current Focus
Iwasawa/Bruhat infrastructure for PSL(2,p) simplicity, built inside `SL(2, ZMod p)`.
VERIFIED this session (researcher-6, 2026-07-08, docker-build green 7743 jobs, 539L / 26
theorems + 8 defs, 0 sorry / 0 axiom / 0 native_decide): started the **generation**
step `⟨U, U⁻⟩ = SL(2,p)` — the generation hypothesis of Iwasawa's criterion. Defined the
subgroup `H = rootGroups := Subgroup.closure (range U ∪ range U⁻)` and proved that both
the Weyl element and the whole split torus already live in `H`, via the classical
Gauss/Steinberg transvection identities:
- `weylW_eq_unipotent_product`: `w = u⁻(1)·u⁺(-1)·u⁻(1)` — the reflection as a product
  of three transvections; hence `weylW_mem_rootGroups`: `w ∈ H`.
- `torusDiag_eq_unipotent_product`: `diag(a) = u⁺(a)·u⁻(-a⁻¹)·u⁺(a)·w` — every torus
  element is a word in the root groups (the middle three factors build the generalized
  Weyl element `w(a) = [[0,a],[-a⁻¹,0]]`, then `·w` straightens it to the diagonal);
  hence `torusDiag_mem_rootGroups`: `diag(a) ∈ H` for all units `a`.
So `H` now contains `U`, `U⁻`, the Weyl reflection `w`, and the entire split torus `T`
— hence the full Borel `B = U·T` and its opposite. **Only the Bruhat cell decomposition
`SL(2,p) = B ⊔ B w B` remains** to conclude `H = SL(2,p)`.
Prior session (researcher-2, #35335): `weylW_conj_lowerUnipotent` (`w·U⁻·w⁻¹ = U`),
`val_weylW_sq` (`w² = −I`), `weylW_pow_four` (`w⁴ = 1`). Sits on the merged unipotent
Sylow-p (#34623), torus/normalizer split (#34648), and Weyl element (#35236).

## Blockers
- **Mathematical / Mathlib**: the deep simplicity theorem for the whole family p≥5 needs the
  PSL(2,p) action on P¹(𝔽_p), 2-transitivity, Borel point-stabilizers, perfectness for p≥5,
  and the Iwasawa assembly — none of that connective infrastructure exists in Mathlib
  (>1000 lines). Mathlib has only `IwasawaStructure.isSimpleGroup` and the bare `PSL` abbrev.

## Next Action
Continue the standalone BUILD: (a) finish generation by proving the Bruhat decomposition
`SL(2,p) = B ⊔ B w B` (or a direct Gauss-elimination argument that every `M ∈ SL(2,p)`
is a word in `U, U⁻`), upgrading `rootGroups = ⊤`; (b) `|SL(2,𝔽_p)| = p(p²−1)`;
(c) the P¹(𝔽_p) action + 2-transitivity. Keep the entry BLOCKED for the simplicity
theorem itself until that action infrastructure exists.
