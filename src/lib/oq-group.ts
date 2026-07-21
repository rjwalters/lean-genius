/**
 * Gallery grouping for OQ-derived entries (issue #39826, epic #39821).
 *
 * A problem's recursive "open question" (OQ) descendants historically render as
 * N separate flat gallery cards whose slugs differ only by trailing `-oq-…`
 * segments (e.g. erdos-396 sprawls into 15 near-indistinguishable cards). This
 * module groups a set of {@link ProofListing}s under their *root problem* so the
 * gallery can present a single rollup card with the descendants nested beneath.
 *
 * Grouping is derived purely from each entry's slug via `src/lib/oq-slug.ts`
 * ({@link rootSlug} / {@link lineageDepth}) — it needs no `parentSlug`/`rootSlug`
 * meta backfill (that is the separate held issue #39828). It is pure and
 * dependency-free at runtime (the `ProofListing` import is type-only, erased by
 * the compiler) so it runs in both the browser bundle and tsx test scripts.
 */

import type { ProofListing } from '../types/proof'
import { rootSlug, lineageDepth } from './oq-slug'

/** Coarse status buckets used for the rollup summary on a root card. */
export type StatusBucket = 'verified' | 'axiomatized' | 'wip' | 'other'

/** Aggregated descendant status counts that roll up to the parent card. */
export interface RollupSummary {
  /** Number of descendants summarized (the "N sub-results" count). */
  total: number
  verified: number
  axiomatized: number
  wip: number
  other: number
}

/**
 * A root problem and its nested OQ descendants. Groups with no descendants are
 * ordinary standalone gallery entries and render as a single card unchanged.
 */
export interface ProofGroup {
  /** The shared root slug all members reduce to via {@link rootSlug}. */
  rootSlug: string
  /**
   * The listing shown as the main card: the true root entry when it is present
   * in the input, otherwise the shallowest descendant (so a group whose root
   * was filtered out still has a visible header).
   */
  header: ProofListing
  /**
   * Nested descendants (every member except {@link header}), ordered root→leaf
   * by lineage depth then slug so the tree reads top-down.
   */
  descendants: ProofListing[]
  /** Aggregated status counts over {@link descendants}. */
  summary: RollupSummary
}

/**
 * Classify a listing into a coarse status bucket for the rollup summary.
 *
 * `wip` is a *badge* (not a status), so it is checked first; the remaining
 * buckets map from the entry's status. Anything unrecognized falls to `other`.
 */
export function classifyListing(
  listing: Pick<ProofListing, 'status' | 'badge'>
): StatusBucket {
  if (listing.badge === 'wip') return 'wip'
  switch (listing.status) {
    case 'verified':
    case 'complete':
      return 'verified'
    case 'axiomatized':
      return 'axiomatized'
    case 'open-question':
    case 'pending':
      return 'wip'
    default:
      return 'other'
  }
}

/** Aggregate status counts over a set of descendants. */
export function summarize(descendants: ProofListing[]): RollupSummary {
  const summary: RollupSummary = {
    total: descendants.length,
    verified: 0,
    axiomatized: 0,
    wip: 0,
    other: 0,
  }
  for (const d of descendants) summary[classifyListing(d)]++
  return summary
}

/**
 * Group listings under their root problem.
 *
 * Group ordering follows the input order of each group's first-seen member, so
 * an already-sorted `listings` array (newest-first, A–Z, …) keeps its ordering
 * at the group level. Descendants within a group are ordered root→leaf.
 *
 * Pure over its input; does not mutate `listings`.
 */
export function groupListings(listings: ProofListing[]): ProofGroup[] {
  const buckets = new Map<string, ProofListing[]>()
  const order: string[] = []

  for (const listing of listings) {
    const root = rootSlug(listing.slug)
    let bucket = buckets.get(root)
    if (!bucket) {
      bucket = []
      buckets.set(root, bucket)
      order.push(root)
    }
    bucket.push(listing)
  }

  const groups: ProofGroup[] = []
  for (const root of order) {
    const members = buckets.get(root)!

    // Header = the true root entry if present, else the shallowest member.
    let header = members.find((m) => m.slug === root)
    if (!header) {
      header = members.reduce((best, m) =>
        lineageDepth(m.slug) < lineageDepth(best.slug) ? m : best
      )
    }

    const descendants = members
      .filter((m) => m !== header)
      .sort((a, b) => {
        const da = lineageDepth(a.slug)
        const db = lineageDepth(b.slug)
        return da !== db ? da - db : a.slug.localeCompare(b.slug)
      })

    groups.push({
      rootSlug: root,
      header,
      descendants,
      summary: summarize(descendants),
    })
  }

  return groups
}

/**
 * Human-readable one-line rollup, e.g. "15 sub-results (14 verified, 1 WIP)".
 * Returns `null` when there are no descendants to summarize.
 */
export function formatRollupSummary(summary: RollupSummary): string | null {
  if (summary.total === 0) return null
  const parts: string[] = []
  if (summary.verified) parts.push(`${summary.verified} verified`)
  if (summary.axiomatized) parts.push(`${summary.axiomatized} axiomatized`)
  if (summary.wip) parts.push(`${summary.wip} WIP`)
  if (summary.other) parts.push(`${summary.other} other`)
  const noun = summary.total === 1 ? 'sub-result' : 'sub-results'
  const breakdown = parts.length ? ` (${parts.join(', ')})` : ''
  return `${summary.total} ${noun}${breakdown}`
}
