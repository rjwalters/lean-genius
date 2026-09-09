# Replay pilot bootstrap compatibility repair

2026-09-08; editor report Squad #40751(a), review #1474; subsequent
dispatcher-environment failure confirmed from the cloud terminal receipt.

The reviewed pilot bootstrap expected `docker image inspect .Id` to be the
image config digest. The editor observed the reviewed OCI digest instead on
the Docker 29/containerd pilot. `build_pilot_bootstrap_compat.py` reproducibly
repairs that gate using the byte-pinned original `pilot-bootstrap-reviewed-v3.sh`.
The original fixture is evidence of review #1357, not the script to launch.

From the repository root, using a new output path:

```sh
python3 research/problems/erdos-85-wip-01/sat49/build_pilot_bootstrap_compat.py --output /tmp/pilot-bootstrap-compat.sh
bash -n /tmp/pilot-bootstrap-compat.sh
shellcheck /tmp/pilot-bootstrap-compat.sh
python3 -m unittest discover -s research/problems/erdos-85-wip-01/sat49 -p test_build_pilot_bootstrap_compat.py
```

The generator accepts only original SHA
`f48a6c4222ca9cf517b6a2a969fbddfeb64cb96fa58901dfe02435fb49b025c3`.
The first identity/logging-only output was 11803 bytes, SHA
`5a1f41b92d7e19b197654b5cbff0f50db9b8e5893580995f42699eef2839c971`.
Generation is local and create-only; it prints a hash-linked build receipt.

The generated gate accepts exactly the reviewed config or raw OCI digest.
The archive evidence and `image_config_id` publication field continue to use
the pinned config. Identity schema v3 adds `loaded_image_id` and
`loaded_image_id_kind` for the actual daemon observation. All freight,
RootFS, manifest, and image evidence checks remain in place.

The EXIT trap closes the log pipe and waits for tee, then attempts create-only
upload of the complete log at `bootstrap-terminal/<instance>.log` before the
terminal JSON. It preserves the dispatcher's exit status and the existing
shutdown fallback even if upload fails. Early failures before instance
discovery/AWS installation retain the original inability to publish remotely.

The generated script downloads the original immutable data freight. Its own
bytes differ from the bootstrap row of freight receipt v3 (SHA `387849c5...`),
so that old receipt must not be presented as verification of this script.
The editor must use a new reviewed script object/key and record its hash in
the launch handoff. This change performs no upload, launch, or mutation of
the already-running pilot. A local/mocked test is not end-to-end certificate
consumption, and no finite-drop or A-REG theorem is promoted by this repair.

## Dispatcher environment follow-up

The later pilot `i-02d306e2bc450827a` passed the image gate but ended at
2026-09-08 21:19 UTC with `accepted=0`, `failed=1`. Its remote terminal
archive contains the worker error
`production LEAN_PATH must equal the frozen overlay root`.
Evidence is under S3 prefix
`sat49/campaign-20260825/h1-replay/bootstrap-terminal/` in that instance's
`.json`, `.log`, and `.state.tgz` objects. This is distinct from the older
local pilot's missing-Mathlib-data compile failure.

The generator now exports `LEAN_PATH="$ROOT/overlay"` immediately before
invoking the dispatcher. The pinned dispatcher inherits its environment
when spawning the worker; the pinned production worker requires precisely
`/opt/replay/overlay`. The generated bootstrap fixes ROOT to `/opt/replay`.
The regression test runs a real child-process handoff, reproduces failure
with the original block, checks both unset and incorrect inherited paths,
and checks that the dispatcher exit status is preserved. It also executes
the original bootstrap preamble, which already exports `HOME=/root`, and
checks both variables in the dispatcher and its child. HOME is part of the
deployment contract; the observed worker failure specifically checks
LEAN_PATH. The only added export is LEAN_PATH, and existing exports are
preserved. No duplicate HOME assignment is needed.

The current output is 11898 bytes, SHA-256
`3790ccaf4329c42a4d5e525262fc5be1669d9648ef09a0d2130d71491662cf81`.
The earlier 11803-byte output/hash above identifies the first repair only.
All ten compatibility tests, `bash -n`, and `shellcheck` pass. This remains
a local tested repair: no new upload, worker launch, or accepted replay is
claimed. The launch owner must record the new script identity in the
reviewed handoff rather than reuse the earlier output hash.

## Pilot 7: frozen AWS identity remains inconsistent

Pilot `i-0ec622c891fb46325` reached the dispatcher but accepted zero leaves.
Its failed-dispatch record reports, before compilation:

```text
expected: aws-cli/2.36.34 Python/3.13.11 Linux/aarch64
observed: aws-cli/2.36.34 Python/3.14.6 Linux/6.17.0-1019-aws exe/aarch64.ubuntu.24
```

The actual EC2 UserData was independently retrieved read-only on 2026-09-08:
12009 bytes, SHA-256
`736176305d14a27c4eea7cf36fe24c6f97bed60c4ff831fd644b85a4e97d71c1`.
It retains the pinned AWS ZIP hash
`2b9d9305db94af64baee48106f54b6652ede5732494c0ba61ae305720ac72505`
and installer. However, its pre-dispatch checks compare only AWS version,
Linux and architecture substrings, and a zstd version substring. They no
longer compare the observed identities with the frozen manifest fields.
The worker still requires exact equality with `manifest.aws_cli_identity`,
so the relaxed bootstrap check merely postpones this failure.

This launch copy is distinct from the generated 11898-byte script above,
which preserves both exact manifest identity checks. The latter would stop
at its earlier gate with the same inconsistent freight. A subsequent launch
needs a reviewed manifest consistent with the installed tools (or tools
matching the existing manifest); changing the manifest requires recording
its new hash throughout the handoff. No worker identity check is relaxed by
this repair. The separate parser and native-axiom findings concern later
gates, not the cause of this pilot's failure.

Terminal evidence remains under
`sat49/campaign-20260825/h1-replay/bootstrap-terminal/i-0ec622c891fb46325.*`;
the failed worker ran for 546539234 ns. This is preflight evidence, not an
accepted certificate or a completed finite exclusion.

## Preparing a new frozen handoff

The generator's `--full-tool-identities` mode requires exact
`docker_identity` and `python_identity` manifest fields, in addition to
the existing exact AWS/zstd checks. Default rendering still reproduces
the earlier 11898-byte script. This mode alone does not update freight.

For a new freight set, pass `--refreeze pins.json` together with
`--full-tool-identities`. The JSON object must contain exactly:

- `schema`: `erdos85-pilot-bootstrap-refreeze-v1`;
- `freight_prefix`: the full S3 key prefix inside the existing bucket;
- `repository_commit`: the full 40-character lowercase commit hash;
- `repo_archive` and `overlay_archive`: distinct `.tar.zst` basenames;
- `repo_archive_sha256`, `overlay_archive_sha256`, `manifest_sha256`,
  `overlay_manifest_sha256`, `overlay_receipt_sha256`, and
  `overlay_identity_sha256`: 64-character lowercase hashes.

The generator updates the shell hash assignments, archive references,
and embedded repository/overlay manifest assertions together. Queue,
image, image-evidence, AWS ZIP, and worker platform pins are preserved.
The new prefix must contain the complete referenced freight set,
including those preserved artifacts. No upload or copy is performed by
this command. The build receipt records the exact input file's SHA-256
as `refreeze_sha256`; output remains create-only and requires its own
review. These syntax and consistency checks do not authenticate the
referenced artifacts: their actual hashes must be verified in the freight
handoff, followed by the full-payload replay and receipt validation.

The input mechanism is tested locally. A generated candidate still needs
artifact-specific review and a full local replay before launch; no
launch-ready output is asserted here.

The first full local replay then exposed a missing runtime dependency:
`aws s3api put-object help` exited 255 with no stdout because neither
`groff` nor `mandoc` was available. Refreeze mode now explicitly installs
`groff-base`, which the frozen worker's help-based capability check needs.
The historical default and identity-only mode retain their earlier bytes.
With `groff-base` installed in the distinct local host image, the actual
help command subsequently exited zero and its 65699-byte stdout contained
both exact `--if-match` and `--if-none-match` strings required by the worker.
This dependency repair does not relax the capability check or establish
that the remaining replay gates pass; the local run must exercise them.
