# Optional admission of the 28 H7 covers into Lean

Status: **prepared; no new cover computation launched**.

Claude assigned this follow-up for after the external campaign and its input
freeze. The frozen inventory currently reviewed here is the manifest with
SHA-256 `f2d2be89aeee6603201649a70a64a6cdf4f20acc6e9268d502f686f0d39dcb6c`.
It contains 28 covers over 377,776 leaves. This package checks covers only;
it neither schedules nor proposes admission of all leaf proofs into Lean.

`plan.py` prints the exact inventory, pipeline source hashes, and existing
F6/t5 pilot receipt available for reuse. The prior pilot passed in 577.113
seconds, with the standard axioms plus one native-checking axiom. Recheck
its retained proof/source/object hashes when assembling the final evidence;
the new producer refuses to regenerate that cover. The other 27 covers are
pending. Multiplying one pilot's time by 28 is not a verified cost estimate.

After the campaign/input freeze, each case is an explicitly submitted pair
of bounded jobs on the existing cloud builder:

1. Run `produce.py --cube NAME --inputs DIR --input-manifest-sha256 SHA
   --output FRESH_DIR` on the cloud host. It accepts only a reviewed cube
   and the exact frozen manifest. The pinned CaDiCaL gets 120 seconds;
   each solver/checker process has a 180-second wall cap, 64-MiB per-file
   limit, and 16-GiB address-space limit. The checker heap stays at 2,000 MB.
   The producer requires solver UNSAT and the exact checker verified-UNSAT
   line, preserves all artifacts, and never retries automatically.
2. Retrieve, preserve, and hash the produced CNF, raw/packed proof, source,
   receipt, and logs. The large artifacts belong outside Git.
3. Inside cloud Docker, run `lake env python3 check.py --production DIR
   --production-receipt-sha256 SHA --output FRESH_DIR`, from `proofs/` using
   the appropriate repository-relative script path. Set a bounded outer
   memory/time limit when submitting the job. It validates all inputs and
   the exact generated source before and after compiling. Unique module
   names allow the resulting cover theorems to be imported together later.
4. Independently audit each result's source/object/log/receipt hashes,
   compiler command, and both axiom reports before calling it verified.
   The expected set is the standard three axioms plus exactly that cover's
   `check._native.native_decide.ax_1_1`. Retain failures as failures.

The source generator uses the same formula and proof preparation as the
verified pilot, with the selected `(F,t)` substituted in the representative
mask, cover CNF, and checked-cover proposition. A metadata test compares
the F6/t5 template byte-for-byte with the verified pilot, apart from the new
namespace. Other tests check all 28 distinct targets/names, reject changed
inventories and unsafe paths, bind reuse evidence, and confirm that local
compute execution is refused. They run no Lean or solver calculation.

Production limits may be too small for some covers. Such failures require
review and an explicit later decision; this package does not expand limits,
retry with larger heaps, start a fleet, or loop through every cover. Keep
the already frozen producer/checker sources unchanged while a production
receipt is awaiting its Lean check, since their hashes are bound together.
