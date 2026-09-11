# Correction to the class-count presentation in2337

The canonical representative order in classes.json has labelled class counts48,24,24,48. PROOF.md listed48,24,48,24 without making the different order sufficiently clear. For any mapping from class index to count, use classes.json: indices0,1,2,3 have counts48,24,24,48 respectively.

The graph/support lists, canonical representatives and their counts are unchanged. Review2337 independently accepted the exact JSON domain with this explicit correction. No original source file or historical review receipt has been overwritten. The downstream2341 and2344 programs read classes.json and are unaffected.
