/**
 * OQ slug / lineage utilities (issue #39825, epic #39821).
 *
 * Gallery entries derived from recursive "open question" (OQ) exploration have
 * historically encoded their entire ancestry in the slug/directory/URL:
 *
 *   abel-ruffini-oq-04-oq-02-oq-02-oq-08-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01
 *
 * That grows without bound (the deepest live entry is 11 OQ hops) and is
 * unreadable. This module decouples an entry's *identity* from its full
 * ancestry path by providing:
 *
 *   1. Lineage computation — recover `parentSlug` / `rootSlug` from any slug,
 *      whether it uses the legacy ancestry encoding or a new bounded slug.
 *   2. Bounded slug generation — mint a short, stable, human-readable slug for
 *      a new OQ-derived entry that does NOT grow with depth
 *      (`<root>-oqNNN` sequential, or `<root>-oqXXXXXX` short hash).
 *
 * The functions are pure and dependency-free (no `node:*` / DOM imports) so the
 * same module runs in build scripts (tsx/Node) and in the browser bundle.
 *
 * A "lineage segment" is a trailing `-<type>-<NN>` group appended by the
 * problem extractor (`.lean/scripts/extract-problems.ts`) when a result spawns
 * a child. The recognized types mirror `generateProblemId` there.
 */

/**
 * Child-entry types that the extractor appends as `-<type>-<NN>` segments.
 * Kept in sync with `.lean/scripts/extract-problems.ts::generateProblemId`.
 */
export const LINEAGE_SEGMENT_TYPES = [
  'oq',
  'incomplete',
  'wip',
  'conditional',
  'millennium',
] as const

export type LineageSegmentType = (typeof LINEAGE_SEGMENT_TYPES)[number]

const TYPE_ALTERNATION = LINEAGE_SEGMENT_TYPES.join('|')

/**
 * Matches a single trailing legacy ancestry segment, e.g. `-oq-04` or
 * `-incomplete-01`. The number is 1+ digits (extractor zero-pads to 2, but we
 * accept any width for forward-compatibility).
 */
const LEGACY_SEGMENT_RE = new RegExp(`-(?:${TYPE_ALTERNATION})-\\d+$`)

/**
 * Matches a trailing *bounded* slug suffix, e.g. `-oq007` (no dash before the
 * number). Bounded slugs are flat children of a root, so their parent and root
 * are identical (the base before the suffix).
 */
const BOUNDED_SEGMENT_RE = new RegExp(`-(?:${TYPE_ALTERNATION})\\d+$`)

/**
 * Global matcher used to *count* legacy OQ segments (depth). Mirrors the shell
 * helper `oq_depth` in `scripts/lib/oq-policy.sh` (`-oq-<digits>`), which only
 * counts `oq` hops.
 */
const OQ_SEGMENT_GLOBAL_RE = /-oq-\d+/g

/**
 * Global matcher for *any* recognized legacy lineage segment (used by
 * {@link lineageDepth}).
 */
const ANY_SEGMENT_GLOBAL_RE = new RegExp(`-(?:${TYPE_ALTERNATION})-\\d+`, 'g')

/**
 * Number of `-oq-<NN>` hops in a slug (0 for a root or a bounded slug).
 *
 * Matches `scripts/lib/oq-policy.sh::oq_depth` so the TS and shell views of
 * "OQ depth" agree.
 */
export function oqDepth(slug: string): number {
  if (!slug) return 0
  return (slug.match(OQ_SEGMENT_GLOBAL_RE) || []).length
}

/**
 * Number of recognized lineage segments of ANY type (`oq`, `incomplete`, …).
 * A mixed chain like `erdos-1018-oq-04-incomplete-01-oq-01` has depth 3.
 */
export function lineageDepth(slug: string): number {
  if (!slug) return 0
  return (slug.match(ANY_SEGMENT_GLOBAL_RE) || []).length
}

/**
 * Whether a slug uses the legacy ancestry encoding (has at least one trailing
 * `-<type>-<NN>` segment).
 */
export function hasLineageSegment(slug: string): boolean {
  return LEGACY_SEGMENT_RE.test(slug)
}

/**
 * The immediate parent slug, or `null` if the slug is already a root.
 *
 * - Legacy ancestry slug: drops the LAST `-<type>-<NN>` segment
 *   (`a-oq-04-oq-02` → `a-oq-04`).
 * - Bounded slug: drops the flat suffix, yielding its root
 *   (`abel-ruffini-oq007` → `abel-ruffini`).
 * - Root slug: `null`.
 */
export function parentSlug(slug: string): string | null {
  if (!slug) return null
  if (LEGACY_SEGMENT_RE.test(slug)) return slug.replace(LEGACY_SEGMENT_RE, '')
  if (BOUNDED_SEGMENT_RE.test(slug)) return slug.replace(BOUNDED_SEGMENT_RE, '')
  return null
}

/**
 * The root ancestor slug (all lineage segments stripped). A root slug maps to
 * itself. Handles mixed legacy chains and bounded slugs.
 *
 *   abel-ruffini-oq-04-oq-02        → abel-ruffini
 *   erdos-1018-oq-04-incomplete-01  → erdos-1018
 *   abel-ruffini-oq007              → abel-ruffini
 *   pythagorean-theorem             → pythagorean-theorem
 */
export function rootSlug(slug: string): string {
  if (!slug) return slug
  let current = slug
  // Strip a trailing bounded suffix first (at most one — bounded slugs are flat).
  if (BOUNDED_SEGMENT_RE.test(current)) {
    current = current.replace(BOUNDED_SEGMENT_RE, '')
  }
  // Then peel every legacy ancestry segment.
  while (LEGACY_SEGMENT_RE.test(current)) {
    current = current.replace(LEGACY_SEGMENT_RE, '')
  }
  return current
}

/**
 * Structured lineage for a slug: its immediate parent (or null) and its root.
 * This is exactly the pair persisted onto `meta.meta.{parentSlug,rootSlug}`.
 */
export interface Lineage {
  parentSlug: string | null
  rootSlug: string
}

/** Compute {@link Lineage} for a slug. */
export function computeLineage(slug: string): Lineage {
  return { parentSlug: parentSlug(slug), rootSlug: rootSlug(slug) }
}

/**
 * The full ancestry chain from root → … → immediate parent (exclusive of the
 * slug itself). Empty for a root slug.
 *
 *   ancestrySlugs('a-oq-04-oq-02') → ['a', 'a-oq-04']
 */
export function ancestrySlugs(slug: string): string[] {
  const chain: string[] = []
  let p = parentSlug(slug)
  while (p !== null) {
    chain.unshift(p)
    p = parentSlug(p)
  }
  return chain
}

// ---------------------------------------------------------------------------
// Bounded slug generation
// ---------------------------------------------------------------------------

/** Zero-pad a positive integer to at least `width` digits. */
function pad(n: number, width: number): string {
  const s = String(n)
  return s.length >= width ? s : '0'.repeat(width - s.length) + s
}

/**
 * Mint a bounded, human-readable slug for a NEW OQ-derived entry using a
 * per-root sequential counter. The result does NOT grow with ancestry depth.
 *
 *   boundedSlugSequential('abel-ruffini', 7) → 'abel-ruffini-oq007'
 *
 * `seq` is a 1-based ordinal that is unique among the root's descendants (the
 * migration script assigns it deterministically; a live minter would use
 * `nextSequentialSlug`). `root` is normalized with {@link rootSlug} so passing
 * a deep ancestry slug still yields a flat result.
 *
 * The `-oq<NNN>` form (no dash before the digits) is deliberately distinct from
 * the legacy `-oq-<NN>` ancestry encoding, so bounded slugs read as depth 0 and
 * are never re-parsed as another hop.
 */
export function boundedSlugSequential(
  root: string,
  seq: number,
  width = 3
): string {
  if (!Number.isInteger(seq) || seq < 1) {
    throw new Error(`boundedSlugSequential: seq must be a positive integer, got ${seq}`)
  }
  return `${rootSlug(root)}-oq${pad(seq, width)}`
}

/**
 * Deterministic 32-bit FNV-1a hash → lowercase base36. Dependency-free so this
 * module stays isomorphic (no `node:crypto`). Not cryptographic — used only to
 * derive a short, stable, collision-resistant slug suffix from a stable input.
 */
export function shortHash(input: string, length = 6): string {
  let h = 0x811c9dc5 // FNV offset basis
  for (let i = 0; i < input.length; i++) {
    h ^= input.charCodeAt(i)
    // FNV prime multiply, kept in 32-bit range via Math.imul.
    h = Math.imul(h, 0x01000193)
  }
  // >>> 0 to interpret as unsigned before base36.
  const base36 = (h >>> 0).toString(36)
  return base36.padStart(length, '0').slice(-length)
}

/**
 * Mint a bounded slug from the entry's FULL legacy ancestry slug using a short
 * stable hash. Unlike the sequential form this needs no sibling enumeration —
 * the same ancestry always maps to the same slug — at the cost of readability.
 *
 *   boundedSlugHash('abel-ruffini-oq-04-oq-02-oq-08') → 'abel-ruffini-oq1a2b3c'
 *
 * The hash is taken over the ancestry *below* the root so two distinct
 * descendants of the same root cannot collide unless their entire path matches.
 */
export function boundedSlugHash(fullSlug: string, length = 6): string {
  const root = rootSlug(fullSlug)
  const suffix = fullSlug.slice(root.length) // e.g. '-oq-04-oq-02-oq-08'
  return `${root}-oq${shortHash(suffix, length)}`
}

/**
 * Given a root and the set of slugs already in use, return the next available
 * sequential bounded slug for a new child. Scans `-oq<NNN>` suffixes already
 * present under the root and picks `max + 1`. Pure over its inputs (a live
 * minter passes the current directory listing / manifest keys).
 */
export function nextSequentialSlug(
  root: string,
  existingSlugs: Iterable<string>,
  width = 3
): string {
  const normRoot = rootSlug(root)
  const prefix = `${normRoot}-oq`
  let max = 0
  for (const s of existingSlugs) {
    if (!s.startsWith(prefix)) continue
    const tail = s.slice(prefix.length)
    // Only accept the bounded form: digits only (not '-01' legacy).
    if (/^\d+$/.test(tail)) {
      const n = parseInt(tail, 10)
      if (n > max) max = n
    }
  }
  return boundedSlugSequential(normRoot, max + 1, width)
}
