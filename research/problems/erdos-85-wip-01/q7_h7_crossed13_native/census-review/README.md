# Independent crossed13 census coverage

The existing COMPLETE crossed13 source has 7,218 canonical assignments. A reverse-host subset coefficient DP independently counts 57,600 raw assignments in 5,443 states. The eight stabilizer actions are independently reconstructed from the matching seed and host counts. Every stored assignment is valid and orbit-minimal; their orbits are disjoint and cover exactly the raw count: 7,182 orbits of size eight and 36 of size four.

This proves coverage of the existing host assignment domain, not exclusion or completion of any graph. No capped profile was rerun. An initial setup assertion incorrectly expected four stabilizer actions and stopped before the count; it was corrected to the source's eight, confirmed by independent permutation enumeration. The single subsequent counting run completed in under a second.
