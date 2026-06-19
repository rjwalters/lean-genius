# Current State

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
