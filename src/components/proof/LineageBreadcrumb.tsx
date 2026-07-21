import { useEffect, useMemo, useState } from 'react'
import { Link } from 'react-router-dom'
import { ChevronRight } from 'lucide-react'
import { ancestrySlugs, ancestrySlugsFromMeta } from '@/lib/oq-slug'
import { getListings } from '@/data/proofs'

/**
 * Breadcrumb showing an OQ-derived entry's lineage (root → … → this entry).
 *
 * The lineage PREFERS the persisted `parentSlug` pointers backfilled by issue
 * #39828 (walked via {@link ancestrySlugsFromMeta}), falling back to slug-parsing
 * ({@link ancestrySlugs}) for legacy entries that lack the metadata. This is
 * required because the migration re-slugs deep entries to the bounded form
 * (`<root>-oqNNN`), whose slug no longer encodes ancestry — slug-parsing alone
 * would collapse the chain to just its root.
 *
 * Renders nothing for a root entry (no ancestry). Ancestor labels are resolved
 * to human titles from the gallery listings when available, falling back to the
 * slug while they load.
 *
 * The listings payload is fetched lazily and only when there is (slug-derived)
 * ancestry to label, so root proof pages never pay for it. `getListings` caches
 * the fetch module-level, so this shares the gallery's single request.
 */
export function LineageBreadcrumb({
  slug,
  currentTitle,
}: {
  slug: string
  currentTitle: string
}) {
  // Slug-parsed ancestry: correct for legacy slugs, and a cheap "is there any
  // ancestry at all?" gate that avoids fetching listings on root pages. For a
  // bounded slug it yields just the root, which the meta walk below expands.
  const slugAncestors = useMemo(() => ancestrySlugs(slug), [slug])
  const [ancestors, setAncestors] = useState<string[]>(slugAncestors)
  const [titles, setTitles] = useState<Record<string, string>>({})

  useEffect(() => {
    setAncestors(slugAncestors)
    if (slugAncestors.length === 0) return
    let cancelled = false
    getListings()
      .then((listings) => {
        if (cancelled) return
        const titleMap: Record<string, string> = {}
        const bySlug = new Map<string, { slug: string; parentSlug?: string | null }>()
        for (const l of listings) {
          titleMap[l.slug] = l.title
          bySlug.set(l.slug, { slug: l.slug, parentSlug: l.parentSlug })
        }
        setTitles(titleMap)
        // Prefer the persisted parentSlug chain (#39828); fall back to the
        // slug-parsed chain when this entry has no lineage metadata.
        setAncestors(ancestrySlugsFromMeta(slug, (s) => bySlug.get(s)))
      })
      .catch(() => {
        /* keep the slug-parsed ancestry + slug labels */
      })
    return () => {
      cancelled = true
    }
  }, [slug, slugAncestors])

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
