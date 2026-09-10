# Cost memo — proving the 48→49 drop (goal #47 / board #37)

Editor, 2026-09-10 06:10Z. Inputs: `DROP_CLOSURE_INVENTORY.md` (sol-1,
6ac434a030, reviews #1560/#1564 partly pending), `H1_PRODUCER_POSTDRAIN_PASS_SPEC.md`
(Fable, cebfa6e3b4), `H1_REPLAY_SHARDED_FLEET_SPEC.md` (sol-2, 4ae8c1fc71,
review #1558 PASS), the 2026-09-10 rescue record. Numbers are the owners'
models, labelled measured vs modelled vs unknown. Nothing here authorizes a
launch; the go is the operator's, on the day the seed round closes.

## What "the drop is proven" requires

`minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7`, i.e. the Lean socket
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighLratChecks` (or the
landed seven-base cube-grid alternative) with all four inputs supplied by
kernel-checked evidence: H1 exclusion, H3 and H5 checks, H7 exclusion; then a
cold build and axiom audit of the assembled module (mandate 1318).

## Sectors

| Sector | State (2026-09-10) | Remaining work | Cost basis | Dollars | Wall |
|---|---|---|---|---|---|
| H1 producer (SAT) | 12,063 of 13,351 capacity rows have a certificate object (SCREENED, not certified); 1,288 gaps = 1,031 never claimed + 33 trim-fail + 22 unknown-at-cap + 17 no-line + 7 lost + 178 outside the v3 queue; 13 quarantined rescued 05:41Z | v4 post-drain pass: solve the ~1,290 gaps with multipart upload; hard tail (33 trim-fail, 22 unknown, 7 lost big orbits) needs the 128 GB boxes and longer caps | MEASURED rates from v3 (Fable): ≈230 box-h c7g.16xlarge for the v3 remainder; add ≈15% for the 178 outside rows; tail ≈60 rows × ~6 box-h MODELLED | $250–300 spot / ≈$550 on-demand (base) + $150–400 tail | 1.3 d on 8 boxes + tail 1–2 d |
| H1 Lean replay | Frozen stack proven end to end (pilot-8, conflict v6); 1 of ~12,000 consumed; single-writer 984 s/cert MEASURED | Sharded fleet, one single-writer per shard, merge step; fix `put_immutable` single-PUT limit for large `olean.zst` (sol-2 gate); local multi-job dry run as launch gate | MODELLED byte-weighted (sol-2 #1558): 13,350 rows ≈ 5,364 box-h r7g.2xlarge | ≈$3,140 on-demand at N=32 (needs quota 128→256 vCPU); same $ at N=16 within quota; spot ≈40% less with reclaim-resume risk | 8.75 d at N=32; 17.5 d at N=16 |
| H3/H5 | 406 roots; 270 proofs replayed locally (all "easy", 1–2 LRAT actions); 136 roots (7 H3 + 129 H5) have NO proof — the host-untrimmable cubes; landed Lean cube-cover gives 392 positive cubes + 14 covers as the finer route | Match old artifacts to current CNFs (done for 270); split the 136 hard roots per the cube-cover file; solve + trim on 128 GB boxes; assemble the seven base UNSATs | UNKNOWN — historical attempts produced 52 GB untrimmable DRATs; no measured rate for the hard roots | Budget envelope $1,000–3,000; FIRST FUNDED TASK is a one-root pilot on a c7g.16xlarge to measure | Unknown; the long-pole risk |
| H7 | 43 evidence slots: 14 direct receipts (13 pass Lean, 1 at 60 s cap), 29 adaptive parents × 8 leaves = 232 leaves, none with accepted terminal markers; evidence generator needs the runtime's LRAT preparation (sol-3, in progress) | Solve 232 leaves; fix generator; assemble the 19/15/7/2 evidence vectors | MODELLED from the H7 canonical census (most cubes ≤ 16 s, some ≥ 600 s): ≈100–300 core-h | ≈$100–250 | 1–2 d, parallel with H1 |
| Final Lean closure | Aggregation interfaces exist; nothing assembled | Generate evidence modules, cold build on the integration tip, `#print axioms`, tag `erdos85-drop-v1` | Host CPU (Fable) | $0 | 2–3 d after the last certificate |
| S3 / storage | 6 TB certificates (Glacier rule after replay); replay adds ≈12,000 oleans (mean ≈350 MB) ≈ 4 TB | — | Standard→Glacier IR | ≈$90/mo new + existing ≈$51/mo | — |

## Totals

- Infrastructure with H3/H5 at the midpoint of its envelope: **≈$5,000–7,000**.
- Recommended authorization envelope: **$10,000**, released in two tranches:
  1. **Tranche 1 (≈$1,500, day 0):** producer post-drain pass, H7 leaves, and
     the H3/H5 one-root pilot. This measures the only unknown before the big spend.
  2. **Tranche 2 (≈$3,500 + H3/H5 remainder, day 2):** replay fleet, sized by
     what tranche 1 showed.
- Wall time from funding: **3–4 weeks** if the H3/H5 hard roots split tractably;
  the replay fleet (9–18 days) is the fixed floor.

## Zero-cost actions worth doing before the money lands

1. File the us-east-1 on-demand vCPU quota increase (128 → 256+) now; it takes
   days to approve and halves the replay wall time.
2. Land the `put_immutable` multipart fix and the multi-job local dry run so the
   replay launch is same-day.
3. Finish the inventory's pending review (#1564, H1 accounting) and the H7
   generator fix.
4. Let the surviving v3 box drain (already paid); nothing of value sits only on it.

## What this memo does not claim

The 12,063 objects are screened, not certified; certification is the replay
stack's verdict, and the replay count in the model (13,350) already assumes
every row is replayed. H3/H5 cost is not measured. Theorem A stays CONDITIONAL
until the socket's four inputs are kernel-checked on a cold build.
