import { memo } from 'react'
import { Link } from 'react-router-dom'
import { ArrowRight } from 'lucide-react'
import { ProofBadge, ErdosBadge, MathlibIndicator } from '@/components/ui/proof-badge'
import { StatusBadge } from './GalleryCard'
import type { ProofListing } from '@/types/proof'

/**
 * A single card in the Erdős gallery grid.
 *
 * Extracted verbatim from the inline `erdosProofs.map(…)` in ErdosPage so it
 * can be memoized: the page re-renders on unrelated state (filter panel toggle,
 * "Copied!" flash, milestones collapse) and previously rebuilt every card's
 * element tree each time.
 *
 * Not to be confused with `ErdosProblemCard`, which is the metadata panel on a
 * proof's detail page.
 */
export const ErdosGalleryCard = memo(function ErdosGalleryCard({
  listing,
}: {
  listing: ProofListing
}) {
  return (
    <Link
      to={`/proof/${listing.slug}`}
      className="group block bg-card border border-border rounded-xl p-6 hover:border-annotation/50 hover:bg-card/80 transition-all"
    >
      {/* Badge row */}
      <div className="flex items-start justify-between mb-4">
        <ProofBadge badge={listing.badge} />
        <StatusBadge status={listing.status} />
      </div>

      <div className="flex items-start gap-3 mb-3">
        <ErdosBadge number={listing.erdosNumber} size="md" />
        <h3 className="text-lg font-semibold group-hover:text-annotation transition-colors pt-1">
          {listing.title}
        </h3>
      </div>

      {/* Date */}
      {listing.dateAdded && (
        <p className="text-xs text-muted-foreground mb-2">
          {listing.dateAdded}
        </p>
      )}

      <p className="text-sm text-muted-foreground mb-4 line-clamp-5">
        {listing.description}
      </p>

      {/* Mathlib dependency indicator */}
      <MathlibIndicator
        dependencyCount={listing.mathlibCount}
        sorries={listing.sorries}
        className="mb-4"
      />

      <div className="flex items-center justify-between text-sm">
        <div className="flex flex-wrap gap-2">
          {listing.tags.slice(0, 2).map((tag) => (
            <span
              key={tag}
              className="px-2 py-0.5 bg-muted rounded text-xs text-muted-foreground"
            >
              {tag}
            </span>
          ))}
        </div>
        <span className="text-xs text-muted-foreground">
          {listing.annotationCount} annotations
        </span>
      </div>

      <div className="mt-4 flex items-center text-sm text-annotation opacity-0 group-hover:opacity-100 transition-opacity">
        <span>Explore proof</span>
        <ArrowRight className="h-4 w-4 ml-1" />
      </div>
    </Link>
  )
})
