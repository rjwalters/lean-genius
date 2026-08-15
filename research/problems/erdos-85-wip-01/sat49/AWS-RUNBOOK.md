# Running a solver fleet on AWS: what this campaign learned

Operational notes from the Erdős-85 order-49 sweep, written 2026-08-15 as the
computational phase wound down in favour of the algebraic route.

These are measurements and traps from one real campaign, not general advice.
Account-specific identifiers (bucket names, principals, instance ids) are
deliberately absent; the lessons transfer, the inventory does not.

---

## 1. Move the computation to the data

Transfer out of AWS to the internet is billed per gigabyte. Transfer between
EC2 and S3 **in the same region is free**.

Measured on this campaign: **140 MB/s** pushing artifacts from an EC2 instance
to a same-region bucket, against **37 MB/s** pushing the same bytes from the
operator's workstation over the internet. In-region was both free and about
four times faster.

The consequence dominates every storage decision. Pulling a 16.5 TB certificate
corpus out of AWS costs roughly $1,479 at published rates. Reading the same
bytes from an instance sitting beside it costs nothing. Storing that corpus is
about $68/month, so a single read out costs what twenty-two months of storage
costs.

This also decides how outsiders verify the work. Rather than shipping the
corpus to a reviewer, publish a recipe for standing up a verifier next to it:
a full independent check of the corpus costs about **$5 and three hours** in
region, against $1,479 to move the corpus to the checker.

## 2. Write artifacts through to object storage as they are produced

The mistake this campaign made, and the one worth avoiding entirely.

Workers wrote verdicts and multi-gigabyte proofs to instance-local disk. A
collector on the operator's workstation pulled them over the internet on a
90-second poll. Spot reclamation destroyed anything not yet pulled.

It should have been: the worker writes each artifact to a same-region bucket
the moment it exists. No collector, no polling window, no workstation in the
path, and reclamation costs only the job actually in flight.

Everything needed for this is cheap and was eventually built anyway:

- a bucket in the same region as the fleet
- an **EC2 instance role** scoped to write and list that one bucket — no
  long-lived credentials on disk, revocable in a single call
- content-addressed keys, `<prefix>/<sha256[0:2]>/<sha256>.<ext>`, so a
  tampered artifact cannot be served under a good one's key

Never copy a long-lived access key onto a solver box. It outlives the machine
it was placed on. Use an instance role: the box reads short-lived credentials
from the metadata service and nothing lands on disk.

Note that IAM is eventually consistent. Associating an instance profile
immediately after creating it fails with `Invalid IAM Instance Profile name`
and succeeds on retry a few seconds later. That error means "not yet".

## 3. Spot interruption gives you two minutes, and nothing watches by default

Interruption behaviour on this campaign was **terminate**: the instance is
destroyed and its disk with it. AWS publishes a warning about two minutes ahead
at `http://169.254.169.254/latest/meta-data/spot/instance-action`.

**No instance was watching for it.** No poller, no systemd unit, no cron entry.
The two minutes elapsed unused on every reclamation.

Two minutes is ample for kilobyte artifacts and useless for gigabyte ones. With
write-through (section 2) there is nothing large left to rescue, which is the
real argument for it.

Measured loss: **11 of 1,027 dispatched orbits, 1.1%**, never returned a
verdict. That figure counts only the small artifact. Reclaimed instances also
took their large proofs, and a verdict without its proof cannot be replayed, so
1.1% understates the cost of the design.

## 4. Two EC2 Fleet traps that cost real money

**A `maintain` fleet replaces reclaimed instances automatically, so the
bootstrap must be able to fetch its own work.** This campaign's user-data
installed an SSH key, a SAT library, build tooling and a proof checker, then
stopped. Work was pushed to instances by hand. Every reclamation therefore
minted a replacement that built its tools and idled at load 0.00 until a human
noticed. Depending on reclamation rate and how long it went unseen, that is
between roughly $100 and $1,300 a month of nothing.

Either put the work fetch into user-data so a replacement self-provisions, or
use `request` type and accept that reclaimed capacity is simply gone. Do not
combine `maintain` with hand-dispatched work.

**Lowering target capacity does not stop replacement.** It lowers the level
replacement restores to; a `maintain` fleet at a reduced target still replaces a
reclaimed instance to reach that target. This was tried here, reported as
fixed, and two further idle instances appeared within half an hour to disprove
it.

`modify-fleet` cannot change a fleet's type, so `maintain` → `request` is not
available. To stop replacement while leaving running instances alone:

```sh
aws ec2 delete-fleets --fleet-ids <id> --no-terminate-instances
```

Then confirm nothing else can spawn:

```sh
aws ec2 describe-fleets --query 'Fleets[?FleetState==`active`]'
aws ec2 describe-spot-fleet-requests \
  --query 'SpotFleetRequestConfigs[?SpotFleetRequestState==`active`]'
```

**Target capacity may be denominated in vCPUs rather than instances.** A target
of 288 against nine 32-core machines is exactly full, not a failed request for
288 machines. Check the denomination before concluding the fleet is broken.

## 5. Costs, as measured

| | |
|---|---|
| `c7a.8xlarge` spot | ~$0.44/hr, about 36% of on-demand |
| nine solver instances plus support | ~$157/day |
| solve rate on the hard tail | ~16 orbits/hour across nine instances |
| certification rate | ~20/hour, back-end limited rather than solver limited |

**Cost Explorer lags roughly 24 hours.** A low figure for the current day means
nothing. When the number matters, compute it from running instances and their
rates. Trusting the lagging figure here produced a report that the fleet was
wound down and costing $55/day on a day it was in fact costing $157.

Tag instances at launch. Most of this fleet was untagged, so "which of these
are ours" had to be answered by launch time and elimination rather than by a
filter.

## 6. Before provisioning anything

1. Which principal is narrowest for this? If none fits, make one and record its
   scope and creation date somewhere durable.
2. Does it need to write from an instance? Instance role, never a copied key.
3. Same region as the data it touches?
4. Tagged, so a later inventory can find it?
5. If it dies, will something replace it automatically — and can that
   replacement do useful work without a human?

Campaign-specific detail for restarting the sweep itself is in
`COMPUTE-RUNBOOK.md` beside this file.
