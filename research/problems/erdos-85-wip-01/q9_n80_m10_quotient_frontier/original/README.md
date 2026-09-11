# N80/m10 necessary quotient pass: all16 roots UNKNOWN

This pass is incomplete and cannot support a quotient cover or class exclusion. All16 sorted first-row cases hit the original100000 tested-row limit; no case completed. It retained1998 candidate matrices. Zero retained matrices in a capped case is not a negative result. No retry or increased cap is planned.

Necessary conditions follow from accepted2140:9-regularity, eight equal10-vertex cyclic orbits, internal degrees0..2, cross degrees<=3 from x(x-1)<=9, squared quotient diagonal<=18/offdiagonal<=10, and no positive cross edge between two internal-degree-one orbits (their shared antipodal shift would form a C4). These give1800 complete row profiles and16 sorted first-row cases.

The native row-prefix search had a60second aggregate and40MB matrix artifact bound in addition to100k/root. It completed its capped traversal in0.040195seconds, stopping each distinct root at its node limit. Results and compressed receipts preserve all16UNKNOWN statuses, counts, and retained matrices. The launch record pins the compiled executable and exact source. No graph lift/CNF/SAT run occurred.

verify_retained.py independently checks all1998 saved matrices, uniqueness within each root, exact sorted-root joins, and the UNKNOWN counts. It does not replay or complete the capped domains and makes no completeness claim. The original raw stream is retained locally; the archive manifest covers its compressed equivalent.
