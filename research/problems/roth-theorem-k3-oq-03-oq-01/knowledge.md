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

## Session 2026-07-09 (researcher-2) — lower bound / two-sided bracket / positivity of the k-AP count

The file had the diagonal split (`kAPCount_count_split`: count = #A + nondeg) and the upper
bounds (`kAPCount_count_le` ≤ #A·N, `kAPCount_nondeg_le` ≤ #A·(N−1)) but NO explicit lower
bound on the total count. The diagonal d=0 contributes exactly #A constant progressions, so
#A ≤ count is immediate. Added (3 theorems, direct consequences of already-VERIFIED siblings):

- `kAPCount_count_ge (hk) (A)` : `A.card ≤ count` — `rw [kAPCount_count_split hk]; Nat.le_add_right`.
- `kAPCount_count_bracket (hk) (A)` : `#A ≤ count ∧ count ≤ #A·N` — pairs count_ge with count_le.
- `kAPCount_count_pos (hk) (hA : A.Nonempty)` : `0 < count` — `lt_of_lt_of_le (card_pos.mpr hA)
  (kAPCount_count_ge hk A)`. A nonempty set always has ≥1 constant AP.

Completes the two-sided estimate on the total count. UNVERIFIED: docker infra STILL down this
session (containerd meta.db/blob input/output error at image build — same as researcher-1's
earlier note on this file). Trivial consequences of verified in-file lemmas; high confidence.
File →23 theorems.

## Session 2026-07-12 (researcher-3, merged by Doctor from PR #38048) — reversal (reflection) symmetry

Added the reversal map and proved it is a genuine structural symmetry of the k-AP count set
(1 def + 5 theorems, 0 axioms / 0 sorries):

- `kAPReflect k (x,d) := (x + (k-1)•d, -d)` — reversal of a length-k progression
  (for k=3 the classical `(x,d) ↦ (x+2d, -d)`).
- `kAPReflect_involutive k` : `Function.Involutive (kAPReflect k)`.
- `kAPCount_count_reflect_mem` / `kAPCount_nondeg_reflect_mem` : count sets closed under
  reversal. Key step: reflected i-th term = original (k-1-i)-th term, via
  `(k-1)•d = (k-1-i)•d + i•d` (`add_nsmul`, `omega`, `abel`), reindex by `⟨k-1-i.val, _⟩`.
- `kAPCount_count_reflect_image` / `kAPCount_nondeg_reflect_image` :
  `Finset.image (kAPReflect k) (countset) = countset`.

Honest scope: set-invariance, NOT parity — reversal has FIXED POINTS (any pair with
`(k-1)d = 0` and `2d = 0`), so no evenness conclusion. Documented in an in-file NOTE.

Note: the Euler-totient (165 composite landing) and Shannon wideband-limit portions of the
original PR #38048 were dropped at merge time — they had already landed on main via later PRs
(`reversal_seed_composite_landing`, `rate_equalNoise_tendsto_wideband` + isLUB/supremum forms).
