/**
 * Precomputed search and sort keys for the gallery listing pages
 * (HomePage, ErdosPage, ResearchPage).
 *
 * Those pages filter and sort the full listings array (~4.8k entries) inside a
 * `useMemo` keyed on the search query. Two costs dominated that memo and are
 * hoisted here so they are paid once per data change instead of once per
 * keystroke:
 *
 * 1. **Lowercasing inside the filter predicate.** Each entry's title, full
 *    description and tags were lowercased on every pass, allocating ~2.5 MB of
 *    throwaway strings per keystroke. {@link buildHaystacks} folds the
 *    searchable fields of each entry into a single pre-lowercased string,
 *    memoized on `[listings, searchIndex]`, so the predicate is one
 *    `String.includes` per entry.
 * 2. **Comparator-side parsing.** Date sorts called `new Date(...)` twice per
 *    comparison (O(n log n) allocations) and alphabetical sorts called bare
 *    `localeCompare`, which constructs a fresh collator per call.
 *    {@link buildSortKeys} precomputes epoch-millisecond keys and
 *    {@link compareTitles} reuses one {@link Intl.Collator}.
 *
 * Pure and dependency-free so it runs in both the browser bundle and tsx test
 * scripts.
 */

/**
 * Shared collator for title sorts.
 *
 * `a.localeCompare(b)` has to construct a collator on every call, which shows
 * up on an n log n sort over thousands of entries. Constructed with default
 * options so ordering matches the `localeCompare()` calls this replaces.
 */
const titleCollator = new Intl.Collator()

/** Locale-aware title comparison, reusing a single cached collator. */
export function compareTitles(a: string, b: string): number {
  return titleCollator.compare(a, b)
}

/**
 * Normalize text for search: strip diacritics, lowercase, and collapse every
 * run of non-alphanumeric characters to a single space.
 *
 * Applied to BOTH the haystack fields and the query, so the two meet in the
 * middle. Without it, three natural searches all returned nothing:
 *
 * - `erdos 85` — the title is `Erdős Problem #85`, so `erdos 85` never appears
 *   as a contiguous run. Folding `ő`→`o` and turning `#` into a space makes it
 *   one.
 * - `erdos-85` — the slug, i.e. the identifier in the URL and the name people
 *   actually use, normalizes to the same `erdos 85`.
 * - `number theory` — previously only matched the literal spaced phrase, never
 *   the `number-theory` *tag* carried by 1,641 entries.
 *
 * Punctuation is collapsed rather than deleted so `4-cycle` becomes `4 cycle`
 * (two tokens) instead of `4cycle`. Matching stays a plain contiguous substring
 * test, so a multi-word query is still a *phrase* search — `number theory` does
 * not degenerate into "any entry containing both words somewhere".
 *
 * Uses the Unicode property escapes `\p{L}\p{N}` rather than `[a-z0-9]` so
 * non-Latin scripts (Greek letters in mathematical titles, CJK) survive instead
 * of being erased to an empty string.
 */
export function normalizeSearchText(value: string): string {
  return value
    .normalize('NFD')
    // Strip combining marks left by NFD: ő -> o, é -> e, ü -> u.
    .replace(/[\u0300-\u036f]/g, '')
    .toLowerCase()
    .replace(/[^\p{L}\p{N}]+/gu, ' ')
    .trim()
}

/**
 * Fold each entry's searchable fields into one normalized haystack string,
 * keyed by slug.
 *
 * Each field is normalized independently (see {@link normalizeSearchText}) and
 * the results are joined with a newline. Normalization can never *produce* a
 * newline, so a query can never match across a field boundary — the result set
 * stays equivalent to per-field matching.
 *
 * `undefined`, `null` and empty fields are dropped. Numeric fields (e.g. an
 * Erdős problem number) are stringified.
 *
 * Note that entries coming from the prebuilt search index are *already*
 * lowercased (`scripts/annotations/build.ts`); normalizing again here is
 * idempotent and costs nothing at steady state since this runs once per data
 * change.
 */
export function buildHaystacks<T extends { slug: string }>(
  items: readonly T[],
  toFields: (item: T) => ReadonlyArray<string | number | null | undefined>
): Map<string, string> {
  const haystacks = new Map<string, string>()
  for (const item of items) {
    const text = toFields(item)
      .filter((field): field is string | number => field !== null && field !== undefined && field !== '')
      .map((field) => normalizeSearchText(String(field)))
      .filter(Boolean)
      .join('\n')
    haystacks.set(item.slug, text)
  }
  return haystacks
}

/** Precomputed numeric sort keys for one listing. */
export interface SortKeys {
  /** `dateAdded` as epoch ms (0 when absent). */
  added: number
  /** `updatedAt` as epoch ms, falling back to {@link SortKeys.added}. */
  updated: number
}

/**
 * Parse the gallery's `MM/DD/YY` `dateAdded` format to epoch milliseconds.
 * Returns 0 for a missing or unparseable value so those entries sort last
 * under a descending sort, matching the previous `new Date(0)` fallback.
 */
export function parseDateAddedMs(dateStr?: string): number {
  if (!dateStr) return 0
  const [month, day, year] = dateStr.split('/').map(Number)
  if (Number.isNaN(month) || Number.isNaN(day) || Number.isNaN(year)) return 0
  return new Date(2000 + year, month - 1, day).getTime()
}

/**
 * Precompute date sort keys per slug so comparators do plain numeric
 * subtraction instead of parsing dates on every comparison.
 */
export function buildSortKeys<
  T extends { slug: string; dateAdded?: string; updatedAt?: string }
>(items: readonly T[]): Map<string, SortKeys> {
  const keys = new Map<string, SortKeys>()
  for (const item of items) {
    const added = parseDateAddedMs(item.dateAdded)
    // Git-derived `updatedAt` (ISO) when present, else `dateAdded`, so the
    // list stays stable on pre-rebuild data.
    const updated = item.updatedAt ? new Date(item.updatedAt).getTime() : added
    keys.set(item.slug, { added, updated: Number.isNaN(updated) ? added : updated })
  }
  return keys
}

/** Empty keys used when a slug is missing from the precomputed map. */
const NO_KEYS: SortKeys = { added: 0, updated: 0 }

/** Look up sort keys for a slug, falling back to zeroes. */
export function sortKeysFor(keys: Map<string, SortKeys>, slug: string): SortKeys {
  return keys.get(slug) ?? NO_KEYS
}
