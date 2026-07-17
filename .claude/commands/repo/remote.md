---
name: "remote"
description: "Launch a cloud dev session on GCP or AWS with this repo ready to go, then open an SSH session"
domain: repo
type: command
user-invocable: true
---

# /repo:remote — Remote Dev Session

Stand up (or reuse) a cloud VM with this repository cloned and synced, then
hand the user a live SSH session in a new terminal window.

## Usage

```
/repo:remote                   # Interactive: pick provider, instance, size
/repo:remote gcp               # Skip the provider question
/repo:remote aws
/repo:remote --status          # List instances created by this command
/repo:remote --down            # Stop instances created by this command
/repo:remote --down --delete   # Terminate/delete them
```

## Configuration (optional)

If the consumer repo has `.claude/remote.json`, read defaults from it. All
fields are optional:

```json
{
  "provider": "gcp",
  "gcp": { "project": "my-project", "zone": "us-west1-a", "machineType": "e2-standard-8" },
  "aws": { "region": "us-west-2", "instanceType": "m5.2xlarge", "keyName": "my-key" },
  "diskGb": 100,
  "image": "ubuntu-2404-lts",
  "idleShutdownMinutes": 120,
  "setup": "make setup"
}
```

Built-in defaults when the file is absent: GCP `e2-standard-4` / AWS
`m5.xlarge`, 50 GB disk, latest Ubuntu LTS, 120-minute idle shutdown.

## Steps

### 1. Detect providers

```bash
gcloud auth list --filter=status:ACTIVE --format='value(account)' 2>/dev/null
aws sts get-caller-identity --query Account --output text 2>/dev/null
```

- Both authenticated → ask the user which to use (mention the default machine
  type and rough hourly price for each)
- One authenticated → use it, say so
- Neither → help the user authenticate. Do **not** run `gcloud auth login` or
  `aws sso login` yourself — these need a browser; tell the user to run them
  in their own terminal (or with a `!` prefix in this session) and wait.

### 2. Look for an existing instance

Instances created by this command carry a label/tag `repo-remote=<repo-name>`
(repo name = basename of the git root). If one exists:
- RUNNING → offer to reuse it (skip to step 4)
- STOPPED → offer to start it (much faster and cheaper than creating)

```bash
gcloud compute instances list --filter="labels.repo-remote=<name>" \
  --format="table(name,zone,status,machineType)"
aws ec2 describe-instances \
  --filters "Name=tag:repo-remote,Values=<name>" "Name=instance-state-name,Values=running,stopped"
```

### 3. Create the instance (with confirmation)

**Before creating anything**, show the user the exact command, the machine
spec, and the estimated hourly cost, and get an explicit yes.

Requirements for the created instance:
- Label/tag it `repo-remote=<repo-name>` so `--status`/`--down` only ever
  touch instances this command created
- Ubuntu LTS image, disk size from config
- Install an idle-shutdown guard (cron that checks SSH sessions + CPU and
  runs `shutdown -h` after the configured idle window) so a forgotten VM
  doesn't burn money
- GCP: prefer OS Login / IAP; AWS: use the configured key pair and a security
  group that allows SSH from the user's IP only

If the zone/region is stocked out, offer the nearest alternative zone or the
next machine type down rather than failing.

### 4. Get the repo onto the instance

Pick based on what exists:

- **Repo has an `origin` remote** and the user's forge auth can be used
  non-interactively (e.g. `gh auth token` for GitHub over HTTPS): clone it on
  the VM, check out the current branch.
- **Then sync uncommitted work** (or when there is no usable remote, sync the
  whole tree): rsync the working tree over SSH, excluding gitignored content:

```bash
# Respect .gitignore; include untracked-but-not-ignored files
rsync -az --delete \
  --filter=':- .gitignore' --exclude '.git/' \
  ./ <host>:~/​<repo-name>/
```

Never copy `.env` files, keys, or anything credential-like unless the user
explicitly asks; call out anything skipped for this reason.

### 5. Bootstrap

- Install baseline tooling on first boot: git, build-essential, and whatever
  the repo obviously needs (detect from `pyproject.toml`, `package.json`,
  `Cargo.toml`, …)
- If config has a `setup` command, offer to run it
- Write/refresh a local SSH config entry so the connection is one word:

```
Host repo-remote-<name>
    HostName <ip-or-iap-alias>
    User <user>
    # GCP+IAP: use a ProxyCommand via `gcloud compute start-iap-tunnel`
```

### 6. Open the SSH view

Verify reachability first:

```bash
ssh -o ConnectTimeout=30 repo-remote-<name> 'echo "SSH OK: $(hostname)"'
```

Then open a new terminal window with the session. Claude Code cannot host an
interactive SSH session itself, so hand it to the OS:

- **macOS**: `osascript -e 'tell app "Terminal" to do script "ssh repo-remote-<name>"' -e 'tell app "Terminal" to activate'`
  (if the user runs iTerm2, use the equivalent iTerm AppleScript)
- **Linux**: try `x-terminal-emulator -e ssh repo-remote-<name>` or the
  desktop's terminal
- **Fallback / SSH-only session**: print the command and tell the user to run
  `ssh repo-remote-<name>` in a separate terminal

### 7. Report

End with a compact status block: instance name, zone, machine type, hourly
cost estimate, idle-shutdown window, the SSH alias, and the teardown command
(`/repo:remote --down`).

## `--status` and `--down`

- `--status`: list all instances labeled `repo-remote=<repo-name>` with state
  and uptime; estimate accumulated cost
- `--down`: stop them (confirm first, listing exactly what will stop);
  `--down --delete` terminates/deletes instead — confirm with the instance
  names spelled out, since disks go with them

## Safety Rules

1. **Never create, stop, or delete cloud resources without showing the exact
   plan and getting a yes** — including estimated cost for creation
2. **Only ever touch instances carrying this repo's `repo-remote` label** —
   never enumerate-and-guess
3. **Never copy credentials to the VM** unless explicitly asked
4. **Always install the idle-shutdown guard** — a VM that outlives the session
   should turn itself off
