#!/bin/bash
set -u
export AWS_DEFAULT_REGION=us-east-1
R=$HOME/rescue; B=2am-erdos85-certs; PFX=sat49/campaign-20260825; META=h1-fleet-v3
log(){ echo "$(date -u +%FT%TZ) $*"; }
# 1. wait for sha manifest
while [ ! -f $R/sha.done ]; do sleep 15; done
[ "$(wc -l < $R/manifest.tsv)" = 13 ] || { log "manifest has $(wc -l < $R/manifest.tsv) lines, expected 13; ABORT"; exit 1; }
# 2. verify every local sha == failure-line sha; abort on any mismatch
: > $R/verified.tsv
while IFS=$'\t' read n tag gz sz sha; do
  t=$(echo "$gz" | sed 's#/scratch/h1/\([0-9a-f]*\)/.*#\1#')
  exp=$(awk -v t=$t '$1==t{print $2}' $R/expected.tsv)
  if [ "$sha" != "$exp" ]; then log "SHA MISMATCH $t local=$sha expected=$exp; ABORT"; exit 1; fi
  printf '%s\t%s\t%s\t%s\n' "$t" "$gz" "$sz" "$sha" >> $R/verified.tsv
done < $R/manifest.tsv
log "all 13 local sha256 match failure records"
aws configure set default.s3.multipart_chunksize 256MB
aws configure set default.s3.max_concurrent_requests 16
# 3. upload with P=4, create-only precheck, verify size, write ledger line
up(){ t=$1; gz=$2; sz=$3; sha=$4; K=$PFX/h1/$t.compact.lrat.gz
  if aws s3api head-object --bucket $B --key $K >/dev/null 2>&1; then log "$t EXISTS-SKIP"; return 0; fi
  if ! aws s3 cp --only-show-errors --expected-size $sz "$gz" s3://$B/$K; then log "$t CP-FAIL"; return 1; fi
  rs=$(aws s3api head-object --bucket $B --key $K --query ContentLength --output text 2>/dev/null)
  if [ "$rs" != "$sz" ]; then log "$t SIZE-MISMATCH remote=$rs local=$sz"; return 1; fi
  fl=/scratch/h1/$t/failure.line
  if [ -f $fl ]; then sed 's/upload=UPLOAD-FAIL/upload=uploaded-v4-multipart-rescue/' $fl > $R/$t.ledger.line
  else aws s3 cp --only-show-errors s3://$B/$PFX/$META/failures/$t.line - | sed 's/upload=UPLOAD-FAIL/upload=uploaded-v4-multipart-rescue/' > $R/$t.ledger.line; fi
  aws s3 cp --only-show-errors $R/$t.ledger.line s3://$B/$PFX/$META/ledger/$t.line || { log "$t LEDGER-PUT-FAIL"; return 1; }
  aws s3 cp --only-show-errors s3://$B/$PFX/$META/failures/$t.line s3://$B/$PFX/$META/failures-resolved/$t.line 2>/dev/null || true
  log "$t UPLOADED size=$sz sha=$sha ledger=written"; }
export -f up log; export R B PFX META
cat $R/verified.tsv | xargs -P 4 -L 1 bash -c 'up "$0" "$1" "$2" "$3"' 2>&1
log "RESCUE DONE: uploaded=$(grep -c ' UPLOADED ' $R/rescue.log) fails=$(grep -c -E 'FAIL|MISMATCH' $R/rescue.log)"
====
#!/bin/bash
set -u; export AWS_DEFAULT_REGION=us-east-1
R=$HOME/rescue; B=2am-erdos85-certs; PFX=sat49/campaign-20260825
while ! grep -q -E "RESCUE DONE|ABORT" $R/rescue.log; do sleep 30; done
grep -q ABORT $R/rescue.log && { echo "rescue aborted; no readback"; exit 1; }
: > $R/readback.tsv
while IFS=$'\t' read t gz sz sha; do
  K=$PFX/h1/$t.compact.lrat.gz
  rsha=$(aws s3 cp --only-show-errors s3://$B/$K - | sha256sum | cut -d' ' -f1)
  crc=$(aws s3api head-object --bucket $B --key $K --checksum-mode ENABLED --query ChecksumCRC64NVME --output text 2>/dev/null)
  v=$( [ "$rsha" = "$sha" ] && echo MATCH || echo MISMATCH )
  printf '%s\t%s\t%s\t%s\t%s\n' "$t" "$sz" "$sha" "$rsha" "$v" >> $R/readback.tsv
  echo "$(date -u +%FT%TZ) $t readback=$v crc64=$crc"
done < $R/verified.tsv
echo "READBACK DONE: match=$(grep -c MATCH$ $R/readback.tsv) mismatch=$(grep -c MISMATCH$ $R/readback.tsv)"
