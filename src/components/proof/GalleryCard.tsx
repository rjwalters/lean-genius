import { memo, useState } from 'react'
import { Link } from 'react-router-dom'
import {
  BookOpen,
  ArrowRight,
  ChevronRight,
  CheckCircle,
  Clock,
  AlertCircle,
} from 'lucide-react'
import {
  ProofBadge,
  WiedijkBadge,
  ErdosBadge,
  MathlibIndicator,
} from '@/components/ui/proof-badge'
import type { ProofListing } from '@/types/proof'
import {
  classifyListing,
  formatRollupSummary,
  type ProofGroup,
  type StatusBucket,
} from '@/lib/oq-group'
import { lineageDepth } from '@/lib/oq-slug'

/**
 * Status pill shown on the top-right of a gallery card. Exported so both the
 * root card here and other consumers share one source of truth.
 */
export function StatusBadge({ status }: { status: string }) {
  const config: Record<
    string,
    { icon: typeof CheckCircle; className: string; label: string }
  > = {
    verified: {
      icon: CheckCircle,
      className: 'bg-green-500/20 text-green-400',
      label: 'Verified',
    },
    pending: {
      icon: Clock,
      className: 'bg-yellow-500/20 text-yellow-400',
      label: 'Pending',
    },
    disputed: {
      icon: AlertCircle,
      className: 'bg-red-500/20 text-red-400',
      label: 'Disputed',
    },
    axiomatized: {
      icon: AlertCircle,
      className: 'bg-purple-500/20 text-purple-400',
      label: 'Axiomatized',
    },
    revised: {
      icon: Clock,
      className: 'bg-blue-500/20 text-blue-400',
      label: 'Revised',
    },
  }

  const { icon: Icon, className, label } = config[status] || config.pending

  return (
    <span
      className={`flex items-center gap-1 px-2 py-0.5 rounded text-xs font-medium ${className}`}
    >
      <Icon className="h-3 w-3" />
      {label}
    </span>
  )
}

/** Small colored dot indicating a descendant's status bucket. */
const BUCKET_DOT: Record<StatusBucket, string> = {
  verified: 'bg-green-400',
  axiomatized: 'bg-purple-400',
  wip: 'bg-yellow-400',
  other: 'bg-muted-foreground',
}

/** A single nested descendant row inside an expanded rollup. */
function DescendantRow({
  listing,
  baseDepth,
}: {
  listing: ProofListing
  baseDepth: number
}) {
  // Indent one step per lineage hop below the header (clamped so deep chains
  // don't run off the card).
  const indent = Math.min(Math.max(lineageDepth(listing.slug) - baseDepth, 0), 6)
  const bucket = classifyListing(listing)
  return (
    <Link
      to={`/proof/${listing.slug}`}
      className="flex items-center gap-2 py-1.5 pr-2 text-sm text-muted-foreground hover:text-annotation transition-colors"
      style={{ paddingLeft: `${indent * 14}px` }}
    >
      <span
        className={`h-1.5 w-1.5 rounded-full flex-shrink-0 ${BUCKET_DOT[bucket]}`}
        aria-hidden
      />
      <span className="truncate">{listing.title}</span>
    </Link>
  )
}

/**
 * A gallery card for one {@link ProofGroup}.
 *
 * - Groups with no descendants render exactly as a standalone proof card.
 * - Groups with descendants add a collapsible rollup footer: a summary line
 *   ("N sub-results (…)") and, when expanded, the nested descendant tree. Every
 *   descendant remains individually linkable via `/proof/:slug`.
 *
 * Memoized: the gallery page re-renders on unrelated state (filter panel
 * toggle, "Copied!" flash) and would otherwise rebuild every card's element
 * tree each time. `group` keeps its identity across those renders because
 * `groupListings` only re-runs when the filtered list actually changes.
 */
export const GalleryCard = memo(function GalleryCard({ group }: { group: ProofGroup }) {
  const { header, descendants, summary } = group
  const [expanded, setExpanded] = useState(false)
  const hasDescendants = descendants.length > 0
  const baseDepth = lineageDepth(header.slug)
  const summaryText = formatRollupSummary(summary)
  const listId = `oq-group-${group.rootSlug}`

  return (
    <div className="group flex flex-col bg-card border border-border rounded-xl hover:border-annotation/50 hover:bg-card/80 transition-all">
      <Link to={`/proof/${header.slug}`} className="block p-6">
        {/* Badge row - prominently displayed at top */}
        <div className="flex items-start justify-between mb-4">
          <ProofBadge badge={header.badge} />
          <StatusBadge status={header.status} />
        </div>

        <div className="flex items-start gap-3 mb-3">
          {header.wiedijkNumber ? (
            <WiedijkBadge number={header.wiedijkNumber} size="md" />
          ) : header.erdosNumber ? (
            <ErdosBadge number={header.erdosNumber} size="md" />
          ) : (
            <div className="h-10 w-10 rounded-lg bg-annotation/20 flex items-center justify-center flex-shrink-0">
              <BookOpen className="h-5 w-5 text-annotation" />
            </div>
          )}
          <h3 className="text-lg font-semibold group-hover:text-annotation transition-colors pt-1">
            {header.title}
          </h3>
        </div>

        {/* Date - letter style */}
        {header.dateAdded && (
          <p className="text-xs text-muted-foreground mb-2">{header.dateAdded}</p>
        )}

        <p className="text-sm text-muted-foreground mb-4 line-clamp-5">
          {header.description}
        </p>

        {/* Mathlib dependency indicator */}
        <MathlibIndicator
          dependencyCount={header.mathlibCount}
          sorries={header.sorries}
          className="mb-4"
        />

        <div className="flex items-center justify-between text-sm">
          <div className="flex flex-wrap gap-2">
            {header.tags.slice(0, 2).map((tag) => (
              <span
                key={tag}
                className="px-2 py-0.5 bg-muted rounded text-xs text-muted-foreground"
              >
                {tag}
              </span>
            ))}
          </div>
          <span className="text-xs text-muted-foreground">
            {header.annotationCount} annotations
          </span>
        </div>

        <div className="mt-4 flex items-center text-sm text-annotation opacity-0 group-hover:opacity-100 transition-opacity">
          <span>Explore proof</span>
          <ArrowRight className="h-4 w-4 ml-1" />
        </div>
      </Link>

      {/* Rollup footer: nested OQ descendants under their root problem. */}
      {hasDescendants && summaryText && (
        <div className="border-t border-border">
          <button
            type="button"
            onClick={() => setExpanded((v) => !v)}
            aria-expanded={expanded}
            aria-controls={listId}
            className="flex w-full items-center gap-2 px-6 py-3 text-left text-sm text-muted-foreground hover:text-foreground transition-colors"
          >
            <ChevronRight
              className={`h-4 w-4 flex-shrink-0 transition-transform ${expanded ? 'rotate-90' : ''}`}
            />
            <span className="font-medium">{summaryText}</span>
          </button>
          {expanded && (
            <ul id={listId} className="px-4 pb-3">
              {descendants.map((d) => (
                <li key={d.slug}>
                  <DescendantRow listing={d} baseDepth={baseDepth} />
                </li>
              ))}
            </ul>
          )}
        </div>
      )}
    </div>
  )
})
