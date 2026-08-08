import { useState, useMemo, useCallback } from 'react'
import { Link, useNavigate } from 'react-router-dom'
import { getListings, getSearchIndex } from '@/data/proofs'
import { useAuth } from '@/contexts/AuthContext'
import { UserMenu } from '@/components/auth/UserMenu'
import { Footer } from '@/components/Footer'
import { LoadingScreen } from '@/components/LoadingScreen'
import { BadgeFilter } from '@/components/ui/proof-badge'
import { GalleryCard } from '@/components/proof'
import { LoadMore } from '@/components/ui/load-more'
import { groupListings } from '@/lib/oq-group'
import { WIEDIJK_BADGE_INFO, HILBERT_BADGE_INFO, MILLENNIUM_BADGE_INFO, ERDOS_BADGE_INFO } from '@/types/proof'
import { Plus, Filter, ArrowUpDown, Search, Github, Share2, Dices } from 'lucide-react'
import { useDebouncedUrlState, useUrlState, serializers, useFetchedData, useLazyFetchedData, useIncrementalList } from '@/hooks'
import { buildHaystacks, buildSortKeys, compareTitles, normalizeSearchText, sortKeysFor } from '@/lib/gallery-search'
import type { ProofBadge as ProofBadgeType, ProofListing } from '@/types/proof'

type SortOption = 'newest' | 'oldest' | 'alphabetical' | 'updated'

export function HomePage() {
  const { isAuthenticated } = useAuth()
  const navigate = useNavigate()

  // Listings are fetched at runtime rather than bundled (issue #35117).
  const { data: listings, error: listingsError } = useFetchedData(getListings)

  const goToRandomProof = useCallback(() => {
    if (!listings) return
    const proof = listings[Math.floor(Math.random() * listings.length)]
    if (proof) navigate(`/proof/${proof.slug}`)
  }, [navigate, listings])

  // URL-synced state. `searchInput` tracks every keystroke and drives the text
  // box; `searchQuery` is the debounced value and is what the (expensive)
  // filter/sort/group pipeline and the search-index fetch key off, so typing
  // does not re-filter the whole gallery on every character.
  const [searchInput, setSearchInput, searchQuery] = useDebouncedUrlState('q', '', serializers.string)

  // Full-text search index (issue #35117): fetched lazily only once the user
  // searches, so first paint never pays for it. Restores description search
  // recall past the 140-char listings excerpt. Falls back to the truncated
  // listing description while it loads or if the fetch fails.
  const { data: searchIndex } = useLazyFetchedData(getSearchIndex, searchQuery.trim().length > 0)
  const [selectedBadges, setSelectedBadges] = useUrlState<ProofBadgeType[]>(
    'badges',
    [],
    serializers.stringArray as { parse: (v: string | null) => ProofBadgeType[]; stringify: (v: ProofBadgeType[]) => string | null }
  )
  const [sortBy, setSortBy] = useUrlState<SortOption>(
    'sort',
    'newest',
    serializers.enum('newest', ['newest', 'oldest', 'alphabetical', 'updated'])
  )
  const [showWiedijkOnly, setShowWiedijkOnly] = useUrlState('wiedijk', false, serializers.boolean)
  const [showHilbertOnly, setShowHilbertOnly] = useUrlState('hilbert', false, serializers.boolean)
  const [showMillenniumOnly, setShowMillenniumOnly] = useUrlState('millennium', false, serializers.boolean)
  const [showErdosOnly, setShowErdosOnly] = useUrlState('erdos', false, serializers.boolean)

  // Local-only UI state (no URL persistence needed)
  const [showFilters, setShowFilters] = useState(false)
  const filterPanelId = 'proof-gallery-filters'

  // Pre-lowercased searchable text per slug, rebuilt only when the listings or
  // the search index change — not on every keystroke. Description matching
  // consults the full-text search index (issue #35117) when available so
  // matches past the 140-char listing excerpt still surface; the truncated
  // listing.description is the fallback while the index loads or for entries
  // absent from it.
  const haystacks = useMemo(
    () => buildHaystacks(listings ?? [], (listing) => [
      listing.title,
      searchIndex?.[listing.slug] ?? listing.description,
      ...listing.tags,
      // The slug is the identifier users see in the URL ("erdos-85"), so it
      // must be searchable; normalization turns it into "erdos 85".
      listing.slug,
    ]),
    [listings, searchIndex]
  )

  // Numeric date keys so the comparators below never parse dates.
  const sortKeys = useMemo(() => buildSortKeys(listings ?? []), [listings])

  // Filter and sort proofs
  const proofs = useMemo(() => {
    let filtered: ProofListing[] = listings ?? []

    const query = normalizeSearchText(searchQuery)
    if (query) {
      filtered = filtered.filter((listing) => haystacks.get(listing.slug)?.includes(query))
    }

    // Filter by badge type
    if (selectedBadges.length > 0) {
      filtered = filtered.filter((listing) =>
        listing.badge && selectedBadges.includes(listing.badge)
      )
    }

    // Filter by Wiedijk's 100
    if (showWiedijkOnly) {
      filtered = filtered.filter((listing) =>
        listing.wiedijkNumber !== undefined
      )
    }

    // Filter by Hilbert's Problems
    if (showHilbertOnly) {
      filtered = filtered.filter((listing) =>
        listing.hilbertNumber !== undefined
      )
    }

    // Filter by Millennium Prize Problems
    if (showMillenniumOnly) {
      filtered = filtered.filter((listing) =>
        listing.millenniumProblem !== undefined
      )
    }

    // Filter by Erdős Problems
    if (showErdosOnly) {
      filtered = filtered.filter((listing) =>
        listing.erdosNumber !== undefined
      )
    }

    // Sort proofs (keys precomputed in `sortKeys`; `updated` already falls back
    // to dateAdded so the list stays stable on pre-rebuild data).
    return [...filtered].sort((a, b) => {
      switch (sortBy) {
        case 'newest':
          return sortKeysFor(sortKeys, b.slug).added - sortKeysFor(sortKeys, a.slug).added
        case 'oldest':
          return sortKeysFor(sortKeys, a.slug).added - sortKeysFor(sortKeys, b.slug).added
        case 'alphabetical':
          return compareTitles(a.title, b.title)
        case 'updated':
          return sortKeysFor(sortKeys, b.slug).updated - sortKeysFor(sortKeys, a.slug).updated
        default:
          return 0
      }
    })
  }, [listings, haystacks, sortKeys, searchQuery, selectedBadges, sortBy, showWiedijkOnly, showHilbertOnly, showMillenniumOnly, showErdosOnly])

  // Group each problem's recursive OQ descendants under their root problem so a
  // family like erdos-396 renders as one rollup card instead of 15 flat cards
  // (issue #39826). Grouping is derived purely from slugs and preserves the
  // sorted order of the group headers.
  const groups = useMemo(() => groupListings(proofs), [proofs])

  // Mount the grid in batches rather than all ~1,600 cards at once.
  const { visible: visibleGroups, hasMore, remaining, sentinelRef, showAll } = useIncrementalList(groups)

  const handleBadgeToggle = (badge: ProofBadgeType) => {
    setSelectedBadges((prev) => {
      if (prev.includes(badge)) {
        return prev.filter((b) => b !== badge)
      }
      return [...prev, badge]
    })
  }

  const clearFilters = () => {
    setSelectedBadges([])
    setShowWiedijkOnly(false)
    setShowHilbertOnly(false)
    setShowMillenniumOnly(false)
    setShowErdosOnly(false)
    setSearchInput('')
  }

  const hasActiveFilters = searchQuery.trim() || selectedBadges.length > 0 || showWiedijkOnly || showHilbertOnly || showMillenniumOnly || showErdosOnly || sortBy !== 'newest'

  const [copySuccess, setCopySuccess] = useState(false)
  const handleShareView = async () => {
    try {
      await navigator.clipboard.writeText(window.location.href)
      setCopySuccess(true)
      setTimeout(() => setCopySuccess(false), 2000)
    } catch {
      // Fallback for older browsers
      const textArea = document.createElement('textarea')
      textArea.value = window.location.href
      document.body.appendChild(textArea)
      textArea.select()
      document.execCommand('copy')
      document.body.removeChild(textArea)
      setCopySuccess(true)
      setTimeout(() => setCopySuccess(false), 2000)
    }
  }

  // Loading / error states while the listings fetch is in flight (#35117).
  if (listingsError) {
    return (
      <div className="min-h-screen bg-background flex flex-col items-center justify-center gap-4">
        <p className="text-muted-foreground">Failed to load the proof gallery.</p>
        <button
          onClick={() => window.location.reload()}
          className="text-sm text-annotation hover:underline"
        >
          Reload
        </button>
      </div>
    )
  }
  if (!listings) {
    return <LoadingScreen message="Loading proofs..." />
  }

  return (
    <div className="min-h-screen bg-background">
      {/* Header */}
      <header className="border-b border-border">
        <div className="max-w-6xl mx-auto px-6 py-4 flex items-center justify-between">
          <span className="text-2xl font-bold tracking-tight">
            Lean<span className="text-annotation">Genius</span>
          </span>
          <div className="flex items-center gap-4">
            <Link
              to="/research"
              className="text-sm text-muted-foreground hover:text-foreground transition-colors"
            >
              Research
            </Link>
            {isAuthenticated && (
              <Link
                to="/submit"
                className="flex items-center gap-1.5 text-sm text-muted-foreground hover:text-foreground transition-colors"
              >
                <Plus className="h-4 w-4" />
                <span className="hidden sm:inline">Submit a Proof</span>
              </Link>
            )}
            <a
              href="https://github.com/rjwalters/lean-genius"
              target="_blank"
              rel="noopener noreferrer"
              className="text-muted-foreground hover:text-foreground transition-colors"
              aria-label="View on GitHub"
            >
              <Github className="h-5 w-5" />
            </a>
            <UserMenu />
          </div>
        </div>
      </header>

      {/* Hero */}
      <section className="max-w-6xl mx-auto px-6 py-16">
        <h1 className="text-4xl md:text-5xl font-bold mb-4">
          Formalized Mathematics,{' '}
          <span className="text-annotation">Explained</span>
        </h1>
        <p className="text-xl text-muted-foreground max-w-2xl">
          Explore machine-verified mathematical proofs with rich annotations,
          historical context, and step-by-step explanations.
        </p>
      </section>

      {/* Proof Cards */}
      <section className="max-w-6xl mx-auto px-6 pb-16">
        <div className="flex flex-col gap-4 sm:flex-row sm:items-center sm:justify-between mb-6">
          <h2 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground">
            {hasActiveFilters ? `Showing ${proofs.length} of ${listings.length} proofs` : `${listings.length} Proofs`}
          </h2>
          <div className="flex flex-wrap items-center gap-3 sm:gap-4">
            {/* Search Box */}
            <div className="relative flex-1 min-w-0 sm:flex-none">
              <Search className="absolute left-2.5 top-1/2 -translate-y-1/2 h-4 w-4 text-muted-foreground" />
              <input
                type="text"
                placeholder="Search proofs..."
                value={searchInput}
                onChange={(e) => setSearchInput(e.target.value)}
                className="pl-8 pr-3 py-1.5 text-sm bg-muted/50 border border-border rounded-lg w-full sm:w-48 placeholder:text-muted-foreground focus:outline-none focus:ring-1 focus:ring-annotation focus:border-annotation"
              />
            </div>
            {/* Random Proof */}
            <button
              onClick={goToRandomProof}
              title="Random proof"
              className="p-1.5 text-muted-foreground hover:text-foreground transition-colors"
            >
              <Dices className="h-4 w-4" />
            </button>
            {/* Sort Dropdown */}
            <div className="flex items-center gap-1.5">
              <ArrowUpDown className="h-4 w-4 text-muted-foreground" />
              <select
                value={sortBy}
                onChange={(e) => setSortBy(e.target.value as SortOption)}
                className="text-sm bg-transparent border-none text-muted-foreground hover:text-foreground cursor-pointer focus:outline-none focus:ring-0"
              >
                <option value="newest">Newest</option>
                <option value="oldest">Oldest</option>
                <option value="updated">Recently updated</option>
                <option value="alphabetical">A-Z</option>
              </select>
            </div>
            {/* Filter Button */}
            <button
              onClick={() => setShowFilters(!showFilters)}
              aria-expanded={showFilters}
              aria-controls={filterPanelId}
              className={`flex items-center gap-1.5 text-sm transition-colors ${
                showFilters || selectedBadges.length > 0 || showWiedijkOnly || showHilbertOnly || showMillenniumOnly || showErdosOnly
                  ? 'text-annotation'
                  : 'text-muted-foreground hover:text-foreground'
              }`}
            >
              <Filter className="h-4 w-4" />
              <span>Filter</span>
              {(selectedBadges.length > 0 || showWiedijkOnly || showHilbertOnly || showMillenniumOnly || showErdosOnly) && (
                <span className="bg-annotation/20 text-annotation px-1.5 py-0.5 rounded text-xs">
                  {selectedBadges.length + (showWiedijkOnly ? 1 : 0) + (showHilbertOnly ? 1 : 0) + (showMillenniumOnly ? 1 : 0) + (showErdosOnly ? 1 : 0)}
                </span>
              )}
            </button>
            {/* Share View Button - only show when there are active filters */}
            {hasActiveFilters && (
              <button
                onClick={handleShareView}
                className="flex items-center gap-1.5 text-sm text-muted-foreground hover:text-foreground transition-colors"
                title="Copy link to this view"
              >
                <Share2 className="h-4 w-4" />
                <span className="hidden sm:inline">{copySuccess ? 'Copied!' : 'Share'}</span>
              </button>
            )}
          </div>
        </div>

        {/* Filter Panel */}
        {showFilters && (
          <div id={filterPanelId} className="mb-6 p-4 bg-card border border-border rounded-lg">
            <div className="flex items-center justify-between mb-3">
              <span className="text-sm font-medium">Filter by Category</span>
              {(selectedBadges.length > 0 || showWiedijkOnly || showHilbertOnly || showMillenniumOnly || showErdosOnly) && (
                <button
                  onClick={clearFilters}
                  className="text-xs text-muted-foreground hover:text-foreground"
                >
                  Clear all
                </button>
              )}
            </div>
            <div className="flex flex-wrap items-center gap-2">
              <BadgeFilter
                selectedBadges={selectedBadges}
                onToggle={handleBadgeToggle}
              />
              {/* Wiedijk Filter Toggle */}
              <button
                onClick={() => setShowWiedijkOnly(!showWiedijkOnly)}
                aria-pressed={showWiedijkOnly}
                className={`inline-flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-sm font-medium transition-all
                  ${showWiedijkOnly
                    ? 'ring-2 ring-offset-2 ring-offset-background'
                    : 'opacity-50 hover:opacity-75'
                  }`}
                style={{
                  backgroundColor: `${WIEDIJK_BADGE_INFO.color}20`,
                  color: WIEDIJK_BADGE_INFO.textColor,
                  ...(showWiedijkOnly && { ringColor: WIEDIJK_BADGE_INFO.color })
                }}
              >
                <span className="inline-flex items-center justify-center h-4 w-4 rounded-full text-[9px] font-bold"
                  style={{
                    backgroundColor: `${WIEDIJK_BADGE_INFO.color}40`,
                    color: WIEDIJK_BADGE_INFO.textColor
                  }}
                >
                  100
                </span>
                <span className="hidden sm:inline">Wiedijk's 100</span>
              </button>
              {/* Hilbert Filter Toggle */}
              <button
                onClick={() => setShowHilbertOnly(!showHilbertOnly)}
                aria-pressed={showHilbertOnly}
                className={`inline-flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-sm font-medium transition-all
                  ${showHilbertOnly
                    ? 'ring-2 ring-offset-2 ring-offset-background'
                    : 'opacity-50 hover:opacity-75'
                  }`}
                style={{
                  backgroundColor: `${HILBERT_BADGE_INFO.color}20`,
                  color: HILBERT_BADGE_INFO.textColor,
                  ...(showHilbertOnly && { ringColor: HILBERT_BADGE_INFO.color })
                }}
              >
                <span className="inline-flex items-center justify-center h-4 w-4 rounded-full text-[9px] font-bold"
                  style={{
                    backgroundColor: `${HILBERT_BADGE_INFO.color}40`,
                    color: HILBERT_BADGE_INFO.textColor
                  }}
                >
                  23
                </span>
                <span className="hidden sm:inline">Hilbert's 23</span>
              </button>
              {/* Millennium Filter Toggle */}
              <button
                onClick={() => setShowMillenniumOnly(!showMillenniumOnly)}
                aria-pressed={showMillenniumOnly}
                className={`inline-flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-sm font-medium transition-all
                  ${showMillenniumOnly
                    ? 'ring-2 ring-offset-2 ring-offset-background'
                    : 'opacity-50 hover:opacity-75'
                  }`}
                style={{
                  backgroundColor: `${MILLENNIUM_BADGE_INFO.color}20`,
                  color: MILLENNIUM_BADGE_INFO.textColor,
                  ...(showMillenniumOnly && { ringColor: MILLENNIUM_BADGE_INFO.color })
                }}
              >
                <span className="inline-flex items-center justify-center h-4 w-4 rounded-full text-[9px] font-bold"
                  style={{
                    backgroundColor: `${MILLENNIUM_BADGE_INFO.color}40`,
                    color: MILLENNIUM_BADGE_INFO.textColor
                  }}
                >
                  7
                </span>
                <span className="hidden sm:inline">Millennium</span>
              </button>
              {/* Erdős Filter Toggle */}
              <button
                onClick={() => setShowErdosOnly(!showErdosOnly)}
                aria-pressed={showErdosOnly}
                className={`inline-flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-sm font-medium transition-all
                  ${showErdosOnly
                    ? 'ring-2 ring-offset-2 ring-offset-background'
                    : 'opacity-50 hover:opacity-75'
                  }`}
                style={{
                  backgroundColor: `${ERDOS_BADGE_INFO.color}20`,
                  color: ERDOS_BADGE_INFO.textColor,
                  ...(showErdosOnly && { ringColor: ERDOS_BADGE_INFO.color })
                }}
              >
                <span className="inline-flex items-center justify-center h-4 w-4 rounded-full text-[9px] font-bold"
                  style={{
                    backgroundColor: `${ERDOS_BADGE_INFO.color}40`,
                    color: ERDOS_BADGE_INFO.textColor
                  }}
                >
                  E
                </span>
                <span className="hidden sm:inline">Erdős</span>
              </button>
            </div>
          </div>
        )}

        <div className="grid gap-6 md:grid-cols-2 lg:grid-cols-3">
          {visibleGroups.map((group) => (
            <GalleryCard key={group.rootSlug} group={group} />
          ))}
        </div>
        {hasMore && (
          <LoadMore
            sentinelRef={sentinelRef}
            remaining={remaining}
            onShowAll={showAll}
            noun="proofs"
          />
        )}

        {/* Empty state when filters result in no proofs */}
        {proofs.length === 0 && (searchQuery.trim() || selectedBadges.length > 0 || showWiedijkOnly || showHilbertOnly || showMillenniumOnly || showErdosOnly) && (
          <div className="text-center py-12">
            <p className="text-muted-foreground mb-4">
              No proofs match your search{selectedBadges.length > 0 || showWiedijkOnly || showHilbertOnly || showMillenniumOnly || showErdosOnly ? ' and filters' : ''}.
            </p>
            <button
              onClick={clearFilters}
              className="text-sm text-annotation hover:underline"
            >
              Clear filters
            </button>
          </div>
        )}
      </section>

      <Footer />
    </div>
  )
}
