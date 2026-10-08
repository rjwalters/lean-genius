#!/usr/bin/env bash
# e85-watchdog: runs every minute (systemd timer e85-watchdog.timer) on the Lean builder.
# STOPS the instance (shutdown -h; the instance is launched with
# InstanceInitiatedShutdownBehavior=stop, so this never terminates it) when either
#   * idle:  no running docker container, no live e85 job, and no logged-in session
#            (ssh / SSM) for IDLE_MINUTES (default 60), or
#   * wall:  the instance has been up WALL_HOURS (default 10) in the current UTC day.
# Overrides: /etc/e85-builder.conf (IDLE_MINUTES=, WALL_HOURS=) or, for one UTC day only,
# the instance tag E85WallHours="<hours>@<YYYY-MM-DD>" (set by `e85-remote start --wall H`).
set -uo pipefail
IDLE_MINUTES=60
WALL_HOURS=10
[[ -r /etc/e85-builder.conf ]] && source /etc/e85-builder.conf
ST=/var/lib/e85-watchdog
mkdir -p "$ST"
now=$(date +%s)
day=$(date -u +%F)
boot=$(( now - $(cut -d. -f1 /proc/uptime) ))

# Per-day override from instance tag (IMDS tags must be enabled; harmless if not).
tok=$(curl -s -m 2 -X PUT http://169.254.169.254/latest/api/token -H 'X-aws-ec2-metadata-token-ttl-seconds: 60' || true)
tag=$(curl -s -m 2 -f -H "X-aws-ec2-metadata-token: $tok" http://169.254.169.254/latest/meta-data/tags/instance/E85WallHours 2>/dev/null || true)
if [[ "$tag" =~ ^([0-9]+)@([0-9-]+)$ && "${BASH_REMATCH[2]}" == "$day" ]]; then WALL_HOURS=${BASH_REMATCH[1]}; fi

# Accumulate today's uptime (delta since last tick, capped so a stopped period never counts).
last_tick=$(cat "$ST/last_tick" 2>/dev/null || echo "$boot")
(( last_tick < boot )) && last_tick=$boot
delta=$(( now - last_tick )); (( delta > 120 )) && delta=120; (( delta < 0 )) && delta=0
up=$(( $(cat "$ST/uptime-$day" 2>/dev/null || echo 0) + delta ))
echo "$up" > "$ST/uptime-$day"; echo "$now" > "$ST/last_tick"
find "$ST" -name 'uptime-*' -mtime +14 -delete 2>/dev/null

# Busy?
why=""
[[ -n "$(docker ps -q 2>/dev/null)" ]] && why+="containers "
for p in /opt/e85/jobs/*/pid; do
    [[ -e "$p" && ! -e "$(dirname "$p")/exit" ]] && kill -0 "$(cat "$p")" 2>/dev/null && { why+="jobs "; break; }
done
pgrep -f '^sshd(-session)?: [^ ]+@' >/dev/null && why+="ssh "
pgrep -x ssm-session-wor >/dev/null && why+="ssm "
[[ -n "$(who)" ]] && why+="tty "
last_busy=$(cat "$ST/last_busy" 2>/dev/null || echo "$boot")
(( last_busy < boot )) && last_busy=$boot
[[ -n "$why" ]] && { last_busy=$now; echo "$now" > "$ST/last_busy"; }
idle=$(( now - last_busy ))

printf 'busy=[%s] idle=%dm/%dm  uptime-today=%dm/%dm (UTC %s)\n' "${why% }" $((idle/60)) "$IDLE_MINUTES" \
    $((up/60)) $((WALL_HOURS*60)) "$day" > "$ST/state"

stop() { logger -t e85-watchdog "STOP: $1"; echo "$(date -u +%FT%TZ) STOP: $1" >> "$ST/log"
         wall "e85-watchdog: stopping instance: $1" 2>/dev/null; sync; shutdown -h now; exit 0; }
(( up >= WALL_HOURS * 3600 )) && stop "daily wall ${WALL_HOURS}h reached (UTC $day)"
(( up >= WALL_HOURS * 3600 - 1800 && up < WALL_HOURS * 3600 - 1740 )) && \
    wall "e85-watchdog: daily ${WALL_HOURS}h wall in 30 min; instance will STOP" 2>/dev/null
(( idle >= IDLE_MINUTES * 60 )) && stop "idle ${IDLE_MINUTES}m"
exit 0
