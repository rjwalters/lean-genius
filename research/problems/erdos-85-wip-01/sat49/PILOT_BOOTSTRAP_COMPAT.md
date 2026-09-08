# Replay pilot bootstrap compatibility repair

2026-09-08; editor report Squad #40751(a), review #1474.

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
Its output is 11803 bytes, SHA
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
