#!/bin/bash
# GENERATED collision-safe v3 retry worker; audited-v2-sha256=c762e8bccefc596e889c4be91ee2dba545d54c6748dd1841e1ff75c2249f34fb
# H1 spot-fleet orbit worker (goal #42). One process per slot; work-stealing via S3 conditional PUT claims.
# Layout (bucket 2am-erdos85-certs, prefix sat49/campaign-20260825):
#   h1/<tag>.compact.lrat.gz          certificate (same key layout as the host grind)
#   h1-fleet-v3/claims/<tag>          claim marker (PutObject If-None-Match:* => atomic)
#   h1-fleet-v3/ledger/<tag>.line     one ledger line per finished orbit (same format as host h1.ledger + node=)
#   h1-fleet-v3/nodes/<instance>/...  heartbeats / final summary
# Lean-exact discipline: v2cnf emit + v2cnf check MATCH before solving; kissat --no-factor --no-preprocessfactor;
# drat-trim s VERIFIED; compact_h1_v2_lrat.py; raw deleted; only compact gz uploaded.
set -u
F=/opt/h1/freight; W0=/scratch/h1
B=2am-erdos85-certs; PFX=sat49/campaign-20260825; META=h1-fleet-v3
CAP=${H1_CAP:-3600}; NODE=$(cat /opt/h1/node); SLOT=$1
DT=/usr/local/bin/drat-trim; KISSAT=/usr/local/bin/kissat
export AWS_DEFAULT_REGION=us-east-1
log() { echo "$(date -u +%FT%TZ) slot=$SLOT $*" >> /opt/h1/worker.log; }
mark_unexpected_exit() {
  RC=$?
  if [ ! -f /opt/h1/slot.$SLOT.done ] && [ ! -f /opt/h1/slot.$SLOT.failed ]; then
    echo "tag=${TAG:--} unexpected-exit rc=$RC" > /opt/h1/slot.$SLOT.failed
    log "UNEXPECTED-EXIT tag=${TAG:--} rc=$RC; claim (if any) quarantined"
  fi
}
trap mark_unexpected_exit EXIT
s3ls_ledger() { aws s3api list-objects-v2 --bucket $B --prefix $PFX/$META/ledger/ --query 'Contents[].Key' --output text 2>/dev/null | tr '\t' '\n' | sed 's#.*/##; s/\.line$//' | sort > /opt/h1/ledger.$SLOT; }
s3ls_claims() { aws s3api list-objects-v2 --bucket $B --prefix $PFX/$META/claims/ --query 'Contents[].Key' --output text 2>/dev/null | tr '\t' '\n' | sed 's#.*/##' | sort > /opt/h1/claims.$SLOT; }
# deterministic per-node/slot shuffle so nodes do not contend on the same head of the list
sort -R --random-source=<(yes "$NODE$SLOT" | head -c 100000) $F/jobs.tsv > /opt/h1/jobs.$SLOT
while true; do
  s3ls_ledger; s3ls_claims
  picked=""
  while IFS=$'\t' read -r tag prof fam idx; do
    # The retry queue is immutable, but a certificate can land after its
    # coverage snapshot.  Proceed only after an explicit NotFound response;
    # permission, network, throttle, and service errors quarantine the lane.
    if aws s3api head-object --bucket "$B" --key "$PFX/h1/$tag.compact.lrat.gz" > /dev/null 2> "/opt/h1/head-object.$SLOT.err"; then
      continue
    elif ! grep -Eq '^(aws: \[ERROR\]: )?An error occurred \((404|NotFound|NoSuchKey)\) when calling the HeadObject operation:' "/opt/h1/head-object.$SLOT.err"; then
      log "CERT-PRECHECK-FAIL tag=$tag; indeterminate object state, stopping slot"
      echo "tag=$tag certificate-precheck-fail" > /opt/h1/slot.$SLOT.failed
      exit 1
    fi
    grep -qx "$tag" /opt/h1/ledger.$SLOT && continue
    grep -qx "$tag" /opt/h1/claims.$SLOT && continue
    if aws s3api put-object --bucket $B --key $PFX/$META/claims/$tag --if-none-match '*' --body /opt/h1/node >/dev/null 2>&1; then picked="$tag"; PROF=$prof; FAM=$fam; IDX=$idx; break; fi
  done < /opt/h1/jobs.$SLOT
  [ -z "$picked" ] && { log "no work left"; echo done > /opt/h1/slot.$SLOT.done; exit 0; }
  TAG=$picked; W=$W0/$TAG; mkdir -p $W; TABLE=$F/tables/$TAG.table
  T0=$(date -u +%s)
  $F/v2cnf emit $PROF $TABLE > $W/orbit.cnf 2> $W/emit.err
  if [ ! -s $W/orbit.cnf ]; then L="$(date -u +%FT%TZ) $TAG p=$PROF i=$IDX EMIT-FAIL node=$NODE"; else
  CHK=$($F/v2cnf check $PROF $TABLE $W/orbit.cnf 2>&1 | tr '\n' ' ')
  case "$CHK" in *MATCH*) ;; *) L="$(date -u +%FT%TZ) $TAG p=$PROF i=$IDX EMIT-CHECK-FAIL $CHK node=$NODE";; esac; fi
  if [ -n "${L:-}" ]; then
    echo "$L" > $W/failure.line
    aws s3 cp --only-show-errors $W/failure.line s3://$B/$PFX/$META/failures/$TAG.line >/dev/null 2>&1 || true
    log "EMIT-PIPELINE-FAIL tag=$TAG; claim quarantined, stopping slot"
    echo "tag=$TAG emit-pipeline-fail" > /opt/h1/slot.$SLOT.failed
    exit 1
  fi
  if [ -z "${L:-}" ]; then
    CNF_SHA=$(sha256sum $W/orbit.cnf | cut -d' ' -f1); NCL=$(head -1 $W/orbit.cnf | awk '{print $4}')
    T1=$(date -u +%s)
    # The fleet binary is built with `configure --quiet` (DQUIET), so passing
    # the runtime `-q` flag is an error in Kissat 4.0.4 and exits immediately.
    $KISSAT -f --no-binary --no-factor --no-preprocessfactor --time=$CAP $W/orbit.cnf $W/orbit.drat > $W/kissat.out 2>&1; RC=$?
    T2=$(date -u +%s)
    case $RC in
      20) $DT $W/orbit.cnf $W/orbit.drat -L $W/orbit.lrat > $W/drat-trim.out 2>&1
          if grep -q 's VERIFIED' $W/drat-trim.out; then TRIM=VERIFIED; else TRIM=TRIM-FAIL; fi
          T3=$(date -u +%s); DRAT_BYTES=$(stat -c%s $W/orbit.drat); rm -f $W/orbit.drat
          RAW_SHA=$(sha256sum $W/orbit.lrat | cut -d' ' -f1); RAW_BYTES=$(stat -c%s $W/orbit.lrat)
          python3 $F/compact_h1_v2_lrat.py $W/orbit.lrat $NCL $W/orbit.compact.lrat > $W/compact.out 2>&1 && CP=ok || CP=COMPACT-FAIL
          if [ $CP = ok ] && [ $TRIM = VERIFIED ]; then
            CSHA=$(sha256sum $W/orbit.compact.lrat | cut -d' ' -f1); CBYTES=$(stat -c%s $W/orbit.compact.lrat)
            gzip -6 -f $W/orbit.compact.lrat; GZSHA=$(sha256sum $W/orbit.compact.lrat.gz | cut -d' ' -f1)
            UP=UPLOAD-FAIL; for try in 1 2 3; do aws s3api put-object --bucket "$B" --key "$PFX/h1/$TAG.compact.lrat.gz" --body "$W/orbit.compact.lrat.gz" --if-none-match '*' > $W/upload.out 2>&1 && { UP=uploaded; break; }; sleep 30; done
          else CSHA=-; CBYTES=0; GZSHA=-; UP=-; fi
          L="$(date -u +%FT%TZ) $TAG p=$PROF i=$IDX UNSAT rc=20 emit_s=$((T1-T0)) solve_s=$((T2-T1)) trim_s=$((T3-T2)) cap_s=$CAP cnf_sha256=$CNF_SHA cnf_clauses=$NCL drat_bytes=$DRAT_BYTES trim=$TRIM raw_lrat_sha256=$RAW_SHA raw_lrat_bytes=$RAW_BYTES compact=$CP compact_lrat_sha256=$CSHA compact_bytes=$CBYTES compact_gz_sha256=$GZSHA upload=$UP node=$NODE"
          if [ "$TRIM" != VERIFIED ] || [ "$CP" != ok ] || [ "$UP" != uploaded ]; then
            echo "$L" > $W/failure.line
            aws s3 cp --only-show-errors $W/failure.line s3://$B/$PFX/$META/failures/$TAG.line >/dev/null 2>&1 || true
            log "CERT-PIPELINE-FAIL tag=$TAG trim=$TRIM compact=$CP upload=$UP; raw LRAT retained, claim quarantined, stopping slot"
            echo "tag=$TAG cert-pipeline-fail" > /opt/h1/slot.$SLOT.failed
            exit 1
          fi
          rm -f $W/orbit.lrat ;;
      10) rm -f $W/orbit.drat
          MODEL_UP=UPLOAD-FAIL; for try in 1 2 3; do aws s3 cp --only-show-errors $W/kissat.out s3://$B/$PFX/$META/sat-models/$TAG.model >/dev/null 2>&1 && { MODEL_UP=uploaded; break; }; sleep 30; done
          if [ "$MODEL_UP" != uploaded ]; then
            log "SAT-MODEL-UPLOAD-FAIL tag=$TAG; claim quarantined, stopping slot"
            echo "tag=$TAG sat-model-upload-fail" > /opt/h1/slot.$SLOT.failed
            exit 1
          fi
          L="$(date -u +%FT%TZ) $TAG p=$PROF i=$IDX SAT rc=10 solve_s=$((T2-T1)) cnf_sha256=$CNF_SHA model-uploaded node=$NODE" ;;
      0)  rm -f $W/orbit.drat
          L="$(date -u +%FT%TZ) $TAG p=$PROF i=$IDX UNKNOWN rc=0 solve_s=$((T2-T1)) cap_s=$CAP cnf_sha256=$CNF_SHA node=$NODE" ;;
      *)  rm -f $W/orbit.drat
          log "INFRA-FAIL tag=$TAG rc=$RC solve_s=$((T2-T1)); claim quarantined, stopping slot"
          rm -rf $W
          echo "tag=$TAG rc=$RC" > /opt/h1/slot.$SLOT.failed
          exit 1 ;;
    esac
  fi
  echo "$L" > $W/ledger.line
  LANDED=no
  for try in 1 2 3; do aws s3 cp --only-show-errors $W/ledger.line s3://$B/$PFX/$META/ledger/$TAG.line >/dev/null 2>&1 && { LANDED=yes; break; }; sleep 30; done
  if [ "$LANDED" != yes ]; then
    log "LEDGER-UPLOAD-FAIL tag=$TAG; claim quarantined, stopping slot"
    rm -rf $W
    echo "tag=$TAG ledger-upload-fail" > /opt/h1/slot.$SLOT.failed
    exit 1
  fi
  echo "$L" >> /opt/h1/node.ledger; log "$L"
  rm -rf $W; unset L
done
