#!/usr/bin/env bash
# e85-host: job runner on the erdos85 Lean builder (installed at /opt/e85/bin/e85-host).
# Driven by the Mac-side `e85-remote` wrapper; usable directly on the host too.
#
#   e85-host build <ref> <Module> [--mem GB] [--timeout 2h] [--threads N] [--cache] [--full] [--no-follow]
#   e85-host run   <ref> [--host] [--mem GB] [--timeout 2h] [--threads N] [--full] [--no-follow] -- <cmd...>
#   e85-host follow <job> | jobs | kill <job> | status | worktrees | clean <name>
#
# Layout:
#   /opt/lean-genius            bare-ish main clone (fetch target; worktrees hang off it)
#   /opt/e85/wt/<name>          one git worktree per branch (or per commit: commit-<sha12>)
#   docker volume lean-build-<name>
#                               per-worktree proofs/.lake/build, reflink-seeded from the warm
#                               base volume `lean-mathlib-cache`
#   docker volume lean-mathlib-packages
#                               shared Mathlib source+oleans (read by every build)
#   /opt/e85/jobs/<id>/         log, cmd, exit, pid
#   /Volumes/Stripe/lean-genius/artifacts
#                               include_str targets, mounted read-only at the same path
set -euo pipefail

REPO=/opt/lean-genius
E85=/opt/e85
WT_ROOT=$E85/wt
JOBS=$E85/jobs
LOCKS=$E85/locks
ARTIFACTS=/Volumes/Stripe/lean-genius/artifacts
BASE_VOLUME=lean-mathlib-cache
DOCKER_BUILD=$E85/bin/docker-build.sh
mkdir -p "$WT_ROOT" "$JOBS" "$LOCKS"

die() { echo "e85-host: $*" >&2; exit 2; }

wt_name() {  # branch -> worktree/volume name
    local ref=$1
    if [[ "$ref" =~ ^[0-9a-f]{7,40}$ ]]; then echo "commit-${ref:0:12}"; else echo "${ref//[^A-Za-z0-9._-]/__}"; fi
}

# ---------------------------------------------------------------- job-side helpers
# New worktrees are sparse (proofs/ + scripts/: all a Lean build needs; the full tree is
# ~5 GB, mostly research/). `--full` switches a worktree to a full checkout for good.
SPARSE_DIRS="proofs scripts"
prepare_worktree() {  # <ref> <name> <full:0|1>  -> checks out ref (detached) in $WT_ROOT/<name>, prints sha
    local ref=$1 name=$2 full=${3:-0} wt=$WT_ROOT/$2 sha
    exec 8>"$LOCKS/repo.lock"; flock 8
    if [[ "$ref" =~ ^[0-9a-f]{7,40}$ ]]; then
        git -C "$REPO" cat-file -e "${ref}^{commit}" 2>/dev/null || git -C "$REPO" fetch -q origin || true
        git -C "$REPO" cat-file -e "${ref}^{commit}" 2>/dev/null || git -C "$REPO" fetch -q origin "$ref"
        sha=$(git -C "$REPO" rev-parse "${ref}^{commit}")
    else
        git -C "$REPO" fetch -q origin "+refs/heads/${ref}:refs/remotes/origin/${ref}"
        sha=$(git -C "$REPO" rev-parse "refs/remotes/origin/${ref}^{commit}")
    fi
    if [[ ! -e "$wt/.git" ]]; then
        git -C "$REPO" worktree prune
        git -C "$REPO" worktree add -q --no-checkout --detach "$wt" "$sha" >&2
        [[ "$full" == 1 ]] || git -C "$wt" sparse-checkout set --cone $SPARSE_DIRS >&2
        git -C "$wt" checkout -q -f --detach "$sha" >&2
    else
        [[ "$full" == 1 ]] && git -C "$wt" sparse-checkout disable >&2
        # remote worktrees are disposable mirrors of the pushed ref: discard local edits
        git -C "$wt" checkout -q -f --detach "$sha" >&2
    fi
    flock -u 8; exec 8>&-
    echo "$sha"
}

ensure_volume() {  # <volume>: create + reflink-seed from the warm base volume
    local vol=$1
    docker volume inspect "$vol" >/dev/null 2>&1 && return 0
    exec 7>"$LOCKS/volumes.lock"; flock 7
    if ! docker volume inspect "$vol" >/dev/null 2>&1; then
        docker volume create --label e85=build "$vol" >/dev/null
        local src dst
        src=$(docker volume inspect -f '{{.Mountpoint}}' "$BASE_VOLUME" 2>/dev/null || true)
        dst=$(docker volume inspect -f '{{.Mountpoint}}' "$vol")
        if [[ -n "$src" && "$vol" != "$BASE_VOLUME" ]]; then
            echo "[e85] seeding $vol from $BASE_VOLUME (reflink copy)"
            sudo cp -a --reflink=auto "$src/." "$dst/"
        fi
    fi
    flock -u 7; exec 7>&-
}

job_main() {  # runs detached; args: <jobdir>
    local jd=$1; source "$jd/spec"
    local name; name=$(wt_name "$REF")
    exec 9>"$LOCKS/wt-$name.lock"
    if ! flock -n 9; then echo "[e85] waiting for another job on worktree $name ..."; flock 9; fi
    echo "[e85] job $(basename "$jd")  ref=$REF  worktree=$WT_ROOT/$name  started $(date -u +%FT%TZ)"
    local sha; sha=$(prepare_worktree "$REF" "$name" "${FULL:-0}")
    echo "[e85] commit $sha ($(git -C "$WT_ROOT/$name" log -1 --format=%s | cut -c1-90))"
    echo "$sha" > "$jd/sha"
    if [[ "$MODE" == host ]]; then
        cd "$WT_ROOT/$name"
        echo "[e85] host command: $CMD"
        timeout --foreground "$TIMEOUT" bash -c "$CMD"
        return
    fi
    local vol="${VOLUME:-lean-build-$name}"   # E85_VOLUME=lean-mathlib-cache warms the base (AMI setup)
    ensure_volume "$vol"
    export LEAN_REPO_ROOT="$WT_ROOT/$name" LEAN_CACHE_VOLUME="$vol" \
           LEAN_MEMORY_LIMIT=$((MEM_GB * 1024)) LEAN_BUILD_TIMEOUT="$TIMEOUT" \
           LEAN_CPU_LIMIT="${CPUS}" LEAN_SKIP_CACHE=true
    [[ -d "$ARTIFACTS" ]] && export LEAN_EXTRA_MOUNTS="$ARTIFACTS"
    [[ -n "$THREADS" ]] && export LEAN_NUM_THREADS="$THREADS"
    [[ "$MODE" == run ]] && export LEAN_DOCKER_CMD="$CMD"
    # Builds hold a shared lock on the Mathlib packages volume; --cache (lake exe cache get)
    # takes it exclusively so a refresh never races a running build.
    exec 6>"$LOCKS/packages.lock"
    if [[ "$CACHE" == 1 ]]; then
        flock 6
        LEAN_DOCKER_CMD="lake exe cache get" LEAN_SKIP_CACHE=false "$DOCKER_BUILD"
        flock -u 6
    fi
    flock -s 6
    if [[ "$MODE" == build ]]; then "$DOCKER_BUILD" "$TARGET"; else "$DOCKER_BUILD"; fi
}

# ---------------------------------------------------------------- client-side commands
follow() {
    local jd=$JOBS/$1
    [[ -d "$jd" ]] || die "no such job $1"
    while [[ ! -s "$jd/pid" && ! -e "$jd/exit" ]]; do sleep 0.2; done
    local pid; pid=$(cat "$jd/pid" 2>/dev/null || echo 0)
    tail -n +1 -F --pid="$pid" "$jd/log" 2>/dev/null || true
    while [[ ! -e "$jd/exit" ]]; do
        kill -0 "$pid" 2>/dev/null || { echo "[e85] job runner vanished (host stopped?)"; return 255; }
        sleep 1
    done
    local rc; rc=$(cat "$jd/exit")
    echo "[e85] job $1 finished: exit $rc  ($(date -u +%FT%TZ))"
    return "$rc"
}

submit() {  # mode ref target/cmd ...
    local mode=$1 ref=$2; shift 2
    local mem=64 timeout=2h threads="" cache=0 nofollow=0 full=0 target="" cmd=""
    [[ "$mode" == build ]] && { target=${1:?module}; shift; }
    [[ "$mode" == run ]] && mode=run
    while [[ $# -gt 0 ]]; do
        case $1 in
            --mem) mem=$2; shift 2;;
            --timeout) timeout=$2; shift 2;;
            --threads) threads=$2; shift 2;;
            --cache) cache=1; shift;;
            --host) mode=host; shift;;
            --full) full=1; shift;;
            --no-follow) nofollow=1; shift;;
            --) shift; cmd="$*"; break;;
            *) die "unknown option $1";;
        esac
    done
    [[ "$mem" =~ ^[0-9]+$ ]] || die "--mem must be an integer number of GB"
    [[ "$timeout" =~ ^[0-9]+[smh]?$ ]] || die "--timeout like 90m / 2h / 3600s"
    [[ -z "$threads" || "$threads" =~ ^[1-9][0-9]*$ ]] || die "--threads must be a positive integer"
    [[ "$mode" != build && -z "$cmd" ]] && die "run needs: -- <cmd>"
    local id; id="$(date -u +%Y%m%dT%H%M%S)-$(wt_name "$ref" | cut -c1-40)-$$"
    local jd=$JOBS/$id; mkdir -p "$jd"
    {
        printf 'MODE=%q\nREF=%q\nTARGET=%q\nCMD=%q\n' "$mode" "$ref" "$target" "$cmd"
        printf 'MEM_GB=%q\nTIMEOUT=%q\nTHREADS=%q\nCACHE=%q\nCPUS=%q\n' "$mem" "$timeout" "$threads" "$cache" "$(nproc)"
        printf 'VOLUME=%q\nFULL=%q\n' "${E85_VOLUME:-}" "$full"
    } > "$jd/spec"
    setsid nohup bash -c 'echo $$ > "$1/pid"; "$0" __job "$1"; echo $? > "$1/exit"' \
        "$(readlink -f "$0")" "$jd" > "$jd/log" 2>&1 < /dev/null &
    echo "[e85] submitted job $id   (reattach: e85-remote logs $id)"
    [[ "$nofollow" == 1 ]] && return 0
    follow "$id"
}

jobs_list() {
    local jd id st
    for jd in $(ls -dt "$JOBS"/*/ 2>/dev/null | head -${1:-15}); do
        id=$(basename "$jd")
        if [[ -e "$jd/exit" ]]; then st="exit=$(cat "$jd/exit")"
        elif kill -0 "$(cat "$jd/pid" 2>/dev/null || echo 0)" 2>/dev/null; then st=RUNNING
        else st=DEAD; fi
        ( source "$jd/spec"; printf '%-62s %-9s %s %s\n' "$id" "$st" "$MODE" "${TARGET:-$CMD}" | cut -c1-160 )
    done
}

kill_job() {
    local jd=$JOBS/$1 pid
    pid=$(cat "$jd/pid") || die "no such job"
    # docker-build.sh traps TERM and stops its container
    pkill -TERM -s "$pid" 2>/dev/null || kill -TERM "$pid"
    echo "[e85] sent TERM to job $1 (session $pid)"
}

status() {
    local day; day=$(date -u +%F)
    echo "host:      $(hostname)  $(nproc) vCPU  $(free -g | awk '/Mem:/{print $2" GiB RAM, "$7" GiB avail"}')"
    echo "uptime:    $(uptime -p)   today(UTC) $(( $(cat /var/lib/e85-watchdog/uptime-$day 2>/dev/null || echo 0) / 60 )) min"
    [[ -r /var/lib/e85-watchdog/state ]] && echo "watchdog:  $(cat /var/lib/e85-watchdog/state)"
    echo "disk:      $(df -h / | awk 'NR==2{print $3" used / "$2" ("$5")"}')"
    echo "containers:"; docker ps --format '  {{.Names}}  {{.Status}}  {{.Command}}' | cut -c1-140
    echo "recent jobs:"; jobs_list 8 | sed 's/^/  /'
}

case "${1:-}" in
    __job) job_main "$2" ;;
    build) shift; [[ $# -ge 2 ]] || die "usage: build <ref> <Module> [opts]"; submit build "$@" ;;
    run) shift; [[ $# -ge 1 ]] || die "usage: run <ref> [opts] -- <cmd>"; submit run "$@" ;;
    follow|logs) follow "${2:?job id}" ;;
    jobs) jobs_list "${2:-25}" ;;
    kill) kill_job "${2:?job id}" ;;
    status) status ;;
    worktrees) git -C "$REPO" worktree list; docker volume ls --filter label=e85=build ;;
    clean)
        n=${2:?worktree name}; exec 9>"$LOCKS/wt-$n.lock"; flock -n 9 || die "job running on $n"
        sudo rm -rf "${WT_ROOT:?}/$n"; git -C "$REPO" worktree prune
        docker volume rm "lean-build-$n" >/dev/null 2>&1 || true; echo "removed $n" ;;
    *) sed -n '2,10p' "$0"; exit 2 ;;
esac
