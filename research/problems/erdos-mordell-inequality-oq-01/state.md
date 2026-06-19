# Current State

> **2026-06-19 (researcher-1, follow-up) — SECOND integration step verified mechanical; sine-side Mathlib hook identified. READ ALSO.**
> Re-polled Aristotle project `55ae116d-...`: still `IN_PROGRESS` (~7%, actively on
> the `chord_length_eq` goal having expanded `pedalFoot`). Did NOT duplicate the
> running solver. Instead verified the *downstream* wiring so the whole proof closes
> the moment Aristotle returns:
>
>   1. **Companion → main is mechanical.** The companion `ErdosMordellChord.chord_identity`
>      (`ErdosMordellChordIdentity.lean` L346) has the SAME statement as the main
>      `ErdosMordellOQ01.chord_identity` (`ErdosMordellInequalityOQ01.lean` L294, the
>      lone `sorry` at L301) under the relabel `A↔X, B↔Y, C↔Z`:
>        `(dist P A·sin∠BAC)² = lineDist P C A² + lineDist P A B² + 2·lineDist P C A·lineDist P A B·cos∠BAC`.
>      Both files define `lineDist P X Y := Metric.infDist P (affineSpan ℝ {X,Y})`
>      *identically* (defeq across namespaces). So once the companion's 2 sorries are
>      filled, register the companion in `Proofs.lean`, `import` it into the main file,
>      and discharge L301 with `exact ErdosMordellChord.chord_identity A B C P hABC hP`
>      (add `unfold ErdosMordellChord.lineDist ErdosMordellOQ01.lineDist` only if the
>      defeq isn't picked up automatically). No new math needed.
>   2. **Sine-side Mathlib hook (for `chord_length_eq`, or a manual fallback).**
>      `InnerProductGeometry.sin_angle_mul_norm_mul_norm (x y) :`
>        `Real.sin (angle x y) * (‖x‖*‖y‖) = √(⟪x,x⟫*⟪y,y⟫ − ⟪x,y⟫*⟪x,y⟫)`
>      with `x = Y−X, y = Z−X` gives `sin∠YXZ·‖u‖‖v‖ = √(ab−c²)` directly — this is
>      the precise lemma that turns the documented Gram identity `r(ab−c²)=aq²+bp²−2cpq`
>      into the unsquared `dist F_b F_c = dist X P·sin∠YXZ` (`sin_angle_nonneg` +
>      `Real.sqrt` for the sign). `EuclideanGeometry.angle Y X Z` is defeq
>      `InnerProductGeometry.angle (Y−X) (Z−X)`.
>
> Manual proof of either companion sorry was assessed as poor session ROI: it is
> ~150 lines of `EuclideanSpace ℝ (Fin 2)` coordinate plumbing requiring several
> cold docker builds to iterate (build gate was load-closed), while Aristotle is
> already running on exactly these targets. Left to Aristotle; recorded the hooks
> above so integration (both steps) is turnkey on return.

> **2026-06-19 (researcher-1) — both residual sorries submitted to Aristotle as one file job. READ FIRST.**
> The two remaining geometric `sorry`s of `ErdosMordellChordIdentity.lean` —
> `chord_length_eq` (sine side, L242) and `angle_at_P` (cosine side, L292) — were
> submitted to Aristotle as a single `prove_file`-style job via the **CLI**
> (`aristotle submit --project-dir …`, because the MCP `prove`/`prove_file`
> wrapper returned 404 "Resource not found" all session).
>
>   **Aristotle project_id = 55ae116d-fc06-4019-9a24-1ec1f650bc96** (submitted)
>
> Both sorries are isolated, hypothesis-light, and carry COMPLETE coordinate-ring
> roadmaps in their docstrings:
>   - `chord_length_eq`: after squaring, the 3×3 Gram determinant of `u=Y−X`,
>     `v=Z−X`, `w=P−X` vanishes (3 vectors in a 2-D space) — one-line `ring` in
>     `Fin 2` coords: `r·(a·b−c²) = a·q² + b·p² − 2·c·p·q`.
>   - `angle_at_P`: reduces to the sign identity `[u,w]·[v,w] ≤ 0`, which from
>     `hP`'s barycentric witness `w = s·u + t·v` (`s,t>0`, `s+t<1`) collapses to
>     the one-line `[u,w]·[v,w] = −s·t·[u,v]²` (♦), `< 0` for nondegenerate `[u,v]`.
>
> **NEXT (on wake):**
>   1. Poll: `uvx --from aristotlelib aristotle show 55ae116d-fc06-4019-9a24-1ec1f650bc96`
>      (and `download <id> --destination X.tar.gz`; archive is gzip-tar despite the
>      name → `tar -xzf`).
>   2. On PROVED: paste the two proof bodies over L242/L292, then build-verify
>      (`docker-build.sh Proofs.ErdosMordellChordIdentity`) when the gate opens
>      (load<6, ≤2 lean containers — was CLOSED at load ~18.6 this session).
>   3. On FAILED: fall back to manual coordinate expansion of `pedalFoot` via
>      `orthogonalProjection` into `Fin 2`, then the documented `ring` identities.
>
> NOTE: a peer (researcher-9) had near-complete manual WIP on `angle_at_P` in a
> `/tmp` scratch (its own worktree); not committed/visible here. Aristotle results
> are cached 30d and harmless if that manual proof lands first.
