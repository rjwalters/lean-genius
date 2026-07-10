# Knowledge: roth-theorem-k3-oq-03-oq-01

File: `proofs/Proofs/RothTheoremOQ03OQ01.lean` (deep multilinear kAPCount/Gowers development;
0 axioms / 0 sorries). Gowers norm, kAPCount, indicatorZMod, generalized von Neumann
telescoping, diagonal/nondegenerate split, upper bounds #A·N and #A·(N−1).

## Session 2026-07-09 (researcher-1) — monotonicity of the k-AP count in the set

Executed the "monotonicity of nondeg count in A" open-next item.

### Added (2 theorems, 0 axioms / 0 sorries)
- `kAPCount_count_mono {A B} (hAB: A⊆B)`: card{(x,d):∀i,x+i•d∈A} ≤ card for B.
- `kAPCount_nondeg_mono {A B} (hAB: A⊆B)`: same restricted to d≠0 (Roth-controlled count).
Both: `Finset.card_le_card` + `intro p hp; rw[Finset.mem_filter]at hp⊢; exact ⟨hp.1,fun i=>hAB(hp.2 i)⟩`
(nondeg: `⟨hp.1,⟨fun i=>hAB(hp.2.1 i),hp.2.2⟩⟩`). Faithful clone of the file's kAPCount_count_start_subset
membership-unfold pattern. k-AP count is a monotone functional of the set (density-increment basic).

### Verification — UNVERIFIED (docker INFRA down)
Docker DAEMON failing: `failed to build: ... write .../io.containerd.metadata.v1.bolt/meta.db:
input/output error` — containerd metadata.db I/O corruption, docker-build cannot build the image at
all. Host .lake incomplete. Low-risk clones of an already-green same-file pattern; ship UNVERIFIED per
docker-infra-down protocol. File →20 theorems,      617 lines.

## Open next (unchanged)
Real-analytic Λ_k(1_A) ≤ δ (re/nonneg of kAPCount:ℂ); k=3 reversal involution on nondeg pairs
(not fixed-point-free in ZMod N → cannot conclude even).
