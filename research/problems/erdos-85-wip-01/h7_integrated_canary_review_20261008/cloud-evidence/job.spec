MODE=host
REF=797579e113ab59e1bcbcb93eb0b84540b628ded0
TARGET=''
CMD=python3.12\ research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/test_campaign.py\ 2\>\&1\ \|\ tail\ -3\;\ bash\ research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/e2e_test.sh\ ~/h7camp/inputs\ ~/h7camp/e2e\ ~/h7pilot/bin/cadical\ ~/h7pilot/bin/cake_lpr\ 2\ \>\ ~/h7camp/e2e.log\ 2\>\&1\;\ rc=\$\?\;\ grep\ -cE\ \"\^PASS\"\ ~/h7camp/e2e.log\;\ grep\ -E\ \"\^\(FAIL\|E2E\)\"\ ~/h7camp/e2e.log\;\ exit\ \$rc
MEM_GB=64
TIMEOUT=40m
THREADS=''
CACHE=0
CPUS=16
VOLUME=''
FULL=1
