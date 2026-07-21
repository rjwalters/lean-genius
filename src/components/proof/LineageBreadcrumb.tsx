import { useEffect, useMemo, useState } from 'react'
import { Link } from 'react-router-dom'
import { ChevronRight } from 'lucide-react'
import { ancestrySlugs } from '@/lib/oq-slug'
import { getListings } from '@/data/proofs'

/**
 * Breadcrumb showing an OQ-derived entry's lineage (root → … → this entry),
 * built from {@link ancestrySlugs}. Renders nothing for a root entry (no
 * ancestry). Ancestor labels are resolved to human titles from the gallery
 * listings when available, falling back to the slug while they load.
 *
 * The listings payload is fetched lazily and only when there is ancestry to
 * label, so root proof pages never pay for it. `getListings` caches the fetch
 * module-level, so this shares the gallery's single request.
 */
export function LineageBreadcrumb({
  slug,
  currentTitle,
}: {
  slug: string
  currentTitle: string
}) {
  const ancestors = useMemo(() => ancestrySlugs(slug), [slug])
  const [titles, setTitles] = useState<Record<string, string>>({})

  useEffect(() => {
    if (ancestors.length === 0) return
    let cancelled = false
    getListings()
      .then((listings) => {
        if (cancelled) return
        const map: Record<string, string> = {}
        for (const l of listings) map[l.slug] = l.title
        setTitles(map)
      })
      .catch(() => {
        /* fall back to slug labels */
      })
    return () => {
      cancelled = true
    }
  }, [ancestors])

  if (ancestors.length === 0) return null

  return (
    <nav
      aria-label="Lineage"
      className="flex flex-wrap items-center gap-1 px-6 py-3 text-sm text-muted-foreground border-b border-border"
    >
      {ancestors.map((ancestor) => (
        <span key={ancestor} className="flex items-center gap-1 min-w-0">
          <Link
            to={`/proof/${ancestor}`}
            className="hover:text-annotation transition-colors truncate max-w-[16rem]"
          >
            {titles[ancestor] ?? ancestor}
          </Link>
          <ChevronRight className="h-3.5 w-3.5 flex-shrink-0 opacity-60" aria-hidden />
        </span>
      ))}
      <span className="text-foreground font-medium truncate max-w-[16rem]" aria-current="page">
        {currentTitle}
      </span>
    </nav>
  )
}
