# S38 (researcher-2 / researcher-86494, 2026-06-18) — ACT: thirteenth partial quotient a₁₂ = 8

**Phase:** ACT (extend the verified CF prefix by one partial quotient).
Frontier before this session: `cbrt3_a1 … cbrt3_a11` are merged and
build-verified in `CubeRoot3IrrationalOQ04.lean`; the next term `a₁₂` had its
two-sided convergent bounds prepared in `Cbrt3Helpers` (S13/S14a) but no
assembled floor theorem.

## Deliverable

`cbrt3_a12 : ⌊1 / (… - 5)⌋ = (8 : ℤ)` — the thirteenth partial quotient of the
simple CF of `∛3`, extending the OEIS A002945 prefix to
`a₀..a₁₂ = [1,2,3,1,4,1,5,1,1,6,2,5,8]`.

Mechanical clone of the merged/verified `cbrt3_a11`: start from the tighter
12th/13th convergent sandwich `597449/414248 < ∛3 < 1865358/1293367` (both
axiom-free in `Cbrt3Helpers`), propagate the rational interval through the
eleven CF maps `x ↦ 1/(x - aᵢ)`. The twelfth tail lands in
`x₁₂ ∈ (3/25, 1/8)`, so `1/x₁₂ ∈ (8, 25/3) ⊂ (8, 9)`, forcing the floor to `8`.
Every step is `linarith` over exact rationals — no new tactic/API surface beyond
what `cbrt3_a11` already uses (`lt_div_iff₀`, `div_lt_iff₀`, `le_div_iff₀`,
`Int.floor_lt`, `Int.le_floor`).

## Offline certification

`verify_a12_floor.py` (exact `fractions.Fraction`): cubes verify
`lo³ < 3 < hi³`; every `x_k` strictly positive; final reciprocal interval
`(8, 25/3) ⊂ (8, 9)`. The printed per-level `(lo, hi)` pairs are byte-equal to
the bounds in the Lean proof (deep-tail bounds `8/41, 90/41, 581/90, …`
reproduce `cbrt3_a11`'s, an independent consistency check). PASS.

## Build status

**BUILD-PENDING — Docker blackout this session** (`docker run` rc=124,
`docker image inspect lean4-arm64:v4.26.0` → socket connect error). The proof
ships as an **orphan file** `CubeRoot3IrrationalOQ04A12.lean`, **UNREGISTERED**
in `Proofs.lean`, so it cannot affect the gallery build closure. Same pattern as
the S35/S36b Stream orphan (which compiled clean on first post-blackout build).

**Next action (Docker-up):**
`./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04A12`; on success
fold `cbrt3_a12` into `CubeRoot3IrrationalOQ04.lean` immediately after
`cbrt3_a11`, drop the orphan, and bump the verified prefix a₁₁ → a₁₂. The S15a
bounds for `a₁₃ = 3` (`6193523/4294349 < ∛3 < 1865358/1293367`) are already in
`Cbrt3Helpers`, so `cbrt3_a13` is the natural follow-on by the same recipe.
