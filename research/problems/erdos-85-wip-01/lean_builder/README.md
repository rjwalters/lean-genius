# erdos85 cloud Lean builder

A Graviton EC2 host for heavy Lean builds and long `native_decide` runs, so they stay off
the host Mac (swap off; OOM there crashes the machine). Agents (Claude, codex) drive it with
one command, `e85-remote`. No SSH setup is needed: access is SSH tunnelled through AWS SSM
Session Manager, and the security group has **no inbound rules**.

| | |
|---|---|
| Instance | `r7g.4xlarge` (16 vCPU Graviton3, 128 GiB), **on-demand**, us-east-1a, tag `Project=erdos85-lean-builder`, `Role=builder` |
| AMI | private `erdos85-lean-builder-<UTC date>` (AL2023 arm64), see "Rebuilding the AMI" |
| Root | 200 GB gp3 (4000 IOPS / 250 MB/s), persists across stop/start |
| Access | `aws ssm start-session` + key `~/.ssh/e85-lean-builder`, AWS profile `2am-admin` |
| Auto-stop | STOP (never terminate) after **60 min idle** or **10 h uptime per UTC day** |

## Install (Mac)

```bash
research/problems/erdos-85-wip-01/lean_builder/install.sh   # -> ~/.local/bin/e85-remote
```

This needs `aws` with the `2am-admin` profile, `session-manager-plugin` (brew cask) and the
private key `~/.ssh/e85-lean-builder`. Re-run `install.sh` after pulling changes. The wrapper
pushes its copy of `e85-host.sh`, `e85-watchdog.sh` and `docker-build.sh` to the host when
they differ, so the host tooling follows the installed copy.

## Usage

```bash
e85-remote start [--wall 14]    # start (and raise today's UTC wall to 14 h); ~1-2 min
e85-remote status               # EC2 state, watchdog counters, containers, recent jobs
e85-remote stop

# Build a module at the tip of a PUSHED branch (or a commit sha):
e85-remote build erdos85/h7t0-formal-20261007 \
    Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeCounting --mem 100 --timeout 3h

# Run any command in that branch's proofs/ dir INSIDE the pinned Lean image
# (same mounts and memory cap as a build), e.g. a long native_decide check:
e85-remote run erdos85/h7t0-formal-20261007 --mem 110 --timeout 8h -- \
    lake env lean Proofs/Erdos85Foo.lean
e85-remote run <branch> --host -- git log -3      # on the host, in the worktree root

e85-remote jobs                  # list jobs (RUNNING / exit=N)
e85-remote logs <job-id>         # reattach or replay; returns the job's exit status
e85-remote kill <job-id>

e85-remote sync-artifacts /Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/strata-lrat/h7_t1_rep0.packed.lz4p7
e85-remote worktrees | clean <name>      # per-branch worktrees and build volumes
e85-remote ssh                           # raw shell, for debugging
```

* `build` and `run` auto-start a stopped builder (`E85_NO_AUTOSTART=1` disables this), stream
  the log, and exit with the job's status. Jobs run detached on the host: if the Mac side is
  interrupted, the job keeps going, and `e85-remote logs <id>` picks it up again.
* Options: `--mem GB` (Docker hard cap, default 64; the host has ~123 GiB), `--timeout`
  (default `2h`), `--threads N` (passes `LEAN_NUM_THREADS`), `--cache` (runs `lake exe cache get`
  first, holding an exclusive lock on the shared Mathlib volume), `--full`, `--no-follow` (submit
  and return the job id; use `e85-remote logs <id>` later).
* For agents whose shell tool has a time limit, use `--no-follow` and then run `e85-remote logs <id>`
  in the background. If a follower is killed, the job itself is unaffected.
* The branch must be pushed. The host fetches `origin/<branch>` and force-checks it out
  (detached) in `/opt/e85/wt/<branch with / → __>`. Remote worktrees are disposable mirrors.
* Worktrees are **sparse** (`proofs/` + `scripts/`, plus top-level files) because the full tree is
  ~5 GB, mostly `research/`. A new branch worktree takes ~7 s. Pass `--full` once if a `run`
  command needs the whole tree.

### Concurrency and isolation

* One git worktree **per branch** (`commit-<sha12>` for raw commits), and one Docker volume
  `lean-build-<name>` per worktree for `proofs/.lake/build`. Each new volume is seeded by a
  reflink (copy-on-write, near-instant, no extra disk) copy of the warm base volume
  `lean-mathlib-cache`, so a first build of a new branch only rebuilds what differs.
* Mathlib (`lean-mathlib-packages`) is shared read-mostly: builds take a shared lock and
  `--cache` takes it exclusively.
* Jobs on the **same** branch are serialised (per-worktree lock; the second one waits and
  says so). Jobs on different branches run in parallel, each with its own `--mem` cap. Keep
  the sum of `--mem` below ~120 GB.

### include_str artifacts

Some modules (`…SevenHighT{1-7}Rep*Certificate`, order-64 fixed-k / ten-six / per-cell, Cayley
μ3 certificates) `include_str` files by absolute Mac path under
`/Volumes/Stripe/lean-genius/artifacts`. The host keeps the same tree at the same absolute
path, and the build bind-mounts it read-only at that path (`LEAN_EXTRA_MOUNTS`, an opt-in
`docker-build.sh` override). The AMI contains every non-sat49 referenced artifact plus the 13
H7 strata certificates (70 files, 2.8 GB). The other ~174 sat49 strata files (~68 GB) are not
pre-loaded. Push any you need with `e85-remote sync-artifacts <path>`, which stages them in
private `s3://2am-erdos85-certs/lean-builder/artifacts/` and pulls them onto the host. Future
AMI rebuilds pick them up from there too.

## Auto-stop (cost control)

`e85-watchdog` (systemd timer, every minute) **stops** the instance (`shutdown -h`, with
`InstanceInitiatedShutdownBehavior=stop`) when either:

* **idle 60 min**: no running Docker container, no live e85 job, and no ssh/SSM session
  (the wrapper's SSH control connection lingers 5 min after the last command), or
* **daily wall**: 10 h of uptime in the current UTC day. It warns 30 min ahead, and the
  wall stops running jobs too. To allow more for one day, run `e85-remote start --wall 14`
  (this sets instance tag `E85WallHours=14@<UTC date>`). Defaults live in
  `/etc/e85-builder.conf`.

`e85-remote status` shows the counters (`busy=[…] idle=…/60m uptime-today=…/600m`).

## Cost

* r7g.4xlarge on-demand is $0.8568/h, so the 10 h wall caps compute at **≈ $8.57/day**.
  Typical use is far less, because idle-stop kicks in 60 min after the last job.
* EBS: 200 GB gp3 + 4000 IOPS/250 MB/s ≈ $21/month (≈ $0.70/day) whether running or stopped.
  The AMI snapshot is ≈ $3–5/month.
* **Why on-demand, not spot:** the point of this host is multi-hour `native_decide` and
  certificate builds, where a spot reclaim throws away hours of work. At the 10 h/day cap,
  on-demand fits the $10/day budget with no interruption risk. Spot (≈ $0.30/h) with
  stop-on-interruption is an option if the budget tightens. Relaunch with
  `--instance-market-options` (persistent request, `InstanceInterruptionBehavior=stop`) and
  avoid us-east-1d.
* For more threads, `r7g.8xlarge` (32 vCPU / 256 GiB, $1.71/h) is a stop → `modify-instance-attribute
  --instance-type` → start away. Lower the wall to ~5 h if you do this.

## Measured (2026-10-07/08, r7g.4xlarge)

| job | result | wall |
|---|---|---|
| AMI warm: `lake exe cache get` + `…SevenHighT0CanonicalCnfSatisfaction` (OOMs at 12 GiB on the Mac) | ok, 8758 jobs | ~38 min |
| `…SevenHighT0CanonicalEmptyCubeCounting` (fresh branch volume, seeded) | ok, 8924 jobs | ~47 min (one ~30 min single-threaded module, `…CanonicalEmptyOrbitCover`) |
| `…SevenHighT0CanonicalEmptyCubeMixedCapstone` (all 13 H7 LRAT certificate modules) | ok, 8954 jobs, peak ≈ 20 GB | 2 h 35 min (`T1Rep0Certificate`, 1.6 GB LRAT: 8149 s alone) |
| new sparse branch worktree | | ~7 s |

## Rebuilding the AMI

```bash
cd research/problems/erdos-85-wip-01/lean_builder
./provision.sh setup-instance                 # fresh AL2023 arm64 -> prints <iid> (Role=ami-setup)
./provision.sh run-setup <iid>                # runs ami_setup.sh in tmux on the instance
E85_INSTANCE_ID=<iid> ./e85-remote ssh tail -f /var/log/e85-ami-setup.log   # wait for EXIT=0
./provision.sh create-ami <iid>               # stop + create private AMI erdos85-lean-builder-<date>
./provision.sh launch <ami-id>                # new long-lived builder (Role=builder)
aws ec2 terminate-instances --instance-ids <setup iid> <old builder iid>   # profile 2am-admin
```

`ami_setup.sh` does the following:

* installs docker, git, python3.12, zstd, tmux, bc and jq;
* loads the pinned image `sha256:a5ca6c4e…` from the checker kit (Requester Pays, read by the
  owner account) and tags it `lean4-arm64:v4.31.0`, the name `docker-build.sh` uses;
* clones `/opt/lean-genius`;
* installs `/opt/e85/bin/{e85-host,docker-build.sh}` and the watchdog;
* syncs the artifacts;
* warms Mathlib (`lake exe cache get`) and the base build volume by building
  `E85_WARM_MODULES` (default `Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfSatisfaction`,
  which OOMs at 12 GiB on the Mac).

Keep the AMI **private**. Never touch the public checker AMI `ami-05697724475f2e748` or the
`public/` S3 prefixes.

## Files

| file | where it runs | role |
|---|---|---|
| `e85-remote` | Mac | the wrapper agents use |
| `install.sh` | Mac | installs the wrapper into `~/.local/bin` |
| `provision.sh` | Mac (operator) | setup instance → AMI → builder |
| `ami_setup.sh` | builder (root) | provisions the image |
| `e85-host.sh` | builder | job runner: worktrees, volumes, locks, logs |
| `e85-watchdog.sh` | builder (root, timer) | idle / daily-wall stop |
| `../../../../proofs/scripts/docker-build.sh` | builder | the normal build script, plus opt-in `LEAN_REPO_ROOT`, `LEAN_CACHE_VOLUME`, `LEAN_CPU_LIMIT`, `LEAN_EXTRA_MOUNTS`, `LEAN_DOCKER_CMD` |
