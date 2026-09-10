# H1 quarantined-certificate rescue, 2026-09-10 05:25–05:41Z (editor)

Context: the v3 producer fleet uploads certificates with a single `put-object`,
whose hard limit is 5 GiB; 16 orbits whose compressed compact LRAT exceeded that
were trim=VERIFIED, compact=ok, upload=UPLOAD-FAIL and left on the boxes' local
disks ("quarantined"). Box i-01f0d952483d8f066 (spot) was reclaimed ~03:50Z
2026-09-09 with 7 of them; this record covers the 13 on the surviving box
i-0ccf0dc6a398156d8, rescued at zero incremental spend per
`H1_PRODUCER_POSTDRAIN_PASS_SPEC.md` §2.

Procedure (scripts-as-run.sh, executed on the box under the operator SSH key):
1. `map.tsv`/`manifest.tsv`: every `/scratch/h1/<tag>/orbit.compact.lrat.gz`
   with size and sha256 (80,911,889,341 bytes total, 13 files, 5.5–7.9 GB).
2. `expected.tsv`: the `compact_gz_sha256`, `compact_bytes` and upload status
   from each tag's `h1-fleet-v3/failures/<tag>.line`, and a HeadObject check
   that no `h1/<tag>.compact.lrat.gz` existed (all ABSENT).
3. Gate: refuse unless all 13 local sha256 equal the failure-line values
   (`verified.tsv`; all matched, 05:25:19Z).
4. Upload: `aws s3 cp` (multipart, 256 MB parts) at P=4 with a HeadObject
   create-only precheck; remote ContentLength verified == local size; the
   failure line rewritten with `upload=uploaded-v4-multipart-rescue` and written
   to `h1-fleet-v3/ledger/<tag>.line`; failure line copied to
   `h1-fleet-v3/failures-resolved/`. 13/13 uploaded, 0 failures (`rescue.log`).
5. Readback: each object streamed back from S3 and sha256'd against the
   failure-line hash; S3 full-object CRC64NVME recorded. 13/13 MATCH
   (`readback.tsv`, `readback.log`).

Exclusive-writer argument (sol-3 42300): the only other possible writer of
these keys is the v3 worker, which writes a certificate key only from a slot
holding the claim and still running its pipeline; all 13 claims belong to
stopped slots (`slot.N.failed` present) on this box, and the worker skips tags
present in `ledger/`. So no concurrent writer existed during the rescue
interval. The general v4 worker keeps the conditional
CompleteMultipartUpload contract; this was a documented one-off.

Status: these 13 are SCREENED (ledger + object + size + readback sha), not
CERTIFIED — certification is the replay stack's verdict. The 7 lost tags
(35958b08961b7cfc 3de5f9e7f1d255e7 59b38d317ba10da8 be77d80a79a0dce6
d67d8618bf933b97 f25a68f489294d7c f363d5a068846aa3) need re-solving.
