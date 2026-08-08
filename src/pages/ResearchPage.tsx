import { useState, useMemo } from 'react'
import { Link } from 'react-router-dom'
import { getResearchListings, getResearchSearchIndex } from '@/data/research'
// Auth context available if needed for future features
// import { useAuth } from '@/contexts/AuthContext'
import { UserMenu } from '@/components/auth/UserMenu'
import { Footer } from '@/components/Footer'
import { LoadingScreen } from '@/components/LoadingScreen'
import { ResearchCard, ContributeSection, RelatedToolsSection } from '@/components/research'
import { PHASE_INFO, TIER_INFO } from '@/types/research'
import { useDebouncedUrlState, useUrlState, serializers, useFetchedData, useLazyFetchedData, useIncrementalList } from '@/hooks'
import { LoadMore } from '@/components/ui/load-more'
import { buildHaystacks, compareTitles, normalizeSearchText } from '@/lib/gallery-search'
import type { ResearchPhase, ValueTier, ResearchStatus, ResearchListing } from '@/types/research'
import {
  FlaskConical,
  Filter,
  ArrowUpDown,
  Search,
  Sparkles,
  Activity,
  Target,
  Github,
  Share2
} from 'lucide-react'

type SortOption = 'newest' | 'activity' | 'significance' | 'alphabetical'

export function ResearchPage() {
  // Listings are fetched at runtime rather than bundled (issue #35117).
  const { data: researchListings, error: listingsError } = useFetchedData(getResearchListings)

  // URL-synced state. `searchInput` tracks every keystroke and drives the text
  // box; `searchQuery` is the debounced value and is what the (expensive)
  // filter/sort pipeline and the search-index fetch key off, so typing does not
  // re-filter the whole list on every character.
  const [searchInput, setSearchInput, searchQuery] = useDebouncedUrlState('q', '', serializers.string)

  // Full-text search index (issue #35117): fetched lazily only once the user
  // searches, so first paint never pays for it. Restores description search
  // recall past the 140-char listings excerpt. Falls back to the truncated
  // listing description while it loads or if the fetch fails.
  const { data: searchIndex } = useLazyFetchedData(getResearchSearchIndex, searchQuery.trim().length > 0)
  const [selectedPhases, setSelectedPhases] = useUrlState<ResearchPhase[]>(
    'phases',
    [],
    serializers.stringArray as { parse: (v: string | null) => ResearchPhase[]; stringify: (v: ResearchPhase[]) => string | null }
  )
  const [selectedTiers, setSelectedTiers] = useUrlState<ValueTier[]>(
    'tiers',
    [],
    serializers.stringArray as { parse: (v: string | null) => ValueTier[]; stringify: (v: ValueTier[]) => string | null }
  )
  const [selectedStatus, setSelectedStatus] = useUrlState<ResearchStatus[]>(
    'status',
    [],
    serializers.stringArray as { parse: (v: string | null) => ResearchStatus[]; stringify: (v: ResearchStatus[]) => string | null }
  )
  const [sortBy, setSortBy] = useUrlState<SortOption>(
    'sort',
    'newest',
    serializers.enum('newest', ['newest', 'activity', 'significance', 'alphabetical'])
  )

  // Local-only UI state (no URL persistence needed)
  const [showFilters, setShowFilters] = useState(false)
  const filterPanelId = 'research-gallery-filters'

  // Pre-lowercased searchable text per slug, rebuilt only when the listings or
  // the search index change — not on every keystroke. Description matching
  // consults the full-text search index (issue #35117) when available so
  // matches past the 140-char listing excerpt still surface; the truncated
  // problem.description is the fallback while the index loads or for entries
  // absent from it.
  const haystacks = useMemo(
    () => buildHaystacks(researchListings ?? [], (problem) => [
      problem.title,
      searchIndex?.[problem.slug] ?? problem.description,
      ...(problem.tags ?? []),
      // Searchable slug, consistent with the proof galleries.
      problem.slug,
    ]),
    [researchListings, searchIndex]
  )

  // Numeric date keys so the comparators below never parse dates.
  const sortKeys = useMemo(() => {
    const keys = new Map<string, { started: number; activity: number }>()
    for (const problem of researchListings ?? []) {
      const started = new Date(problem.started).getTime() || 0
      // `activity` falls back to `started` when the entry has no lastUpdate.
      const activity = problem.lastUpdate ? new Date(problem.lastUpdate).getTime() || started : started
      keys.set(problem.slug, { started, activity })
    }
    return keys
  }, [researchListings])

  // Filter and sort problems
  const problems = useMemo(() => {
    let filtered: ResearchListing[] = [...(researchListings ?? [])]

    const query = normalizeSearchText(searchQuery)
    if (query) {
      filtered = filtered.filter((problem) => haystacks.get(problem.slug)?.includes(query))
    }

    // Filter by phase
    if (selectedPhases.length > 0) {
      filtered = filtered.filter((problem) =>
        selectedPhases.includes(problem.phase)
      )
    }

    // Filter by tier
    if (selectedTiers.length > 0) {
      filtered = filtered.filter((problem) =>
        selectedTiers.includes(problem.tier)
      )
    }

    // Filter by status
    if (selectedStatus.length > 0) {
      filtered = filtered.filter((problem) =>
        selectedStatus.includes(problem.status)
      )
    }

    // Sort problems (date keys precomputed in `sortKeys`).
    const keyFor = (slug: string) => sortKeys.get(slug) ?? { started: 0, activity: 0 }
    return filtered.sort((a, b) => {
      switch (sortBy) {
        case 'newest':
          return keyFor(b.slug).started - keyFor(a.slug).started
        case 'activity':
          return keyFor(b.slug).activity - keyFor(a.slug).activity
        case 'significance':
          return (b.significance || 0) - (a.significance || 0)
        case 'alphabetical':
          return compareTitles(a.title, b.title)
        default:
          return 0
      }
    })
  }, [researchListings, haystacks, sortKeys, searchQuery, selectedPhases, selectedTiers, selectedStatus, sortBy])

  // Mount the grid in batches rather than every card at once.
  const { visible: visibleProblems, hasMore, remaining, sentinelRef, showAll } = useIncrementalList(problems)

  const handlePhaseToggle = (phase: ResearchPhase) => {
    setSelectedPhases((prev) =>
      prev.includes(phase) ? prev.filter((p) => p !== phase) : [...prev, phase]
    )
  }

  const handleTierToggle = (tier: ValueTier) => {
    setSelectedTiers((prev) =>
      prev.includes(tier) ? prev.filter((t) => t !== tier) : [...prev, tier]
    )
  }

  const handleStatusToggle = (status: ResearchStatus) => {
    setSelectedStatus((prev) =>
      prev.includes(status) ? prev.filter((s) => s !== status) : [...prev, status]
    )
  }

  const clearFilters = () => {
    setSelectedPhases([])
    setSelectedTiers([])
    setSelectedStatus([])
    setSearchInput('')
  }

  const hasFilters = selectedPhases.length > 0 || selectedTiers.length > 0 || selectedStatus.length > 0 || searchQuery.trim()
  const hasActiveFilters = hasFilters || sortBy !== 'newest'

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
        <p className="text-muted-foreground">Failed to load the research gallery.</p>
        <button
          onClick={() => window.location.reload()}
          className="text-sm text-annotation hover:underline"
        >
          Reload
        </button>
      </div>
    )
  }
  if (!researchListings) {
    return <LoadingScreen message="Loading research problems..." />
  }

  // Stats
  const activeCount = researchListings.filter(p => p.status === 'active').length
  const successCount = researchListings.filter(p => p.phase === 'COMPLETED').length
  const totalAttempts = researchListings.reduce((sum, p) => sum + p.attemptCount, 0)

  return (
    <div className="min-h-screen bg-background">
      {/* Header */}
      <header className="border-b border-border">
        <div className="max-w-6xl mx-auto px-6 py-4 flex items-center justify-between">
          <Link to="/" className="text-2xl font-bold tracking-tight">
            Lean<span className="text-annotation">Genius</span>
          </Link>
          <div className="flex items-center gap-4">
            <Link
              to="/"
              className="text-sm text-muted-foreground hover:text-foreground transition-colors"
            >
              Proofs
            </Link>
            <span className="text-sm text-annotation font-medium">
              Research
            </span>
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
      <section className="max-w-6xl mx-auto px-6 py-12">
        <div className="flex items-start gap-4 mb-4">
          <div className="h-12 w-12 rounded-xl bg-annotation/20 flex items-center justify-center">
            <FlaskConical className="h-6 w-6 text-annotation" />
          </div>
          <div>
            <h1 className="text-4xl md:text-5xl font-bold">
              Research in{' '}
              <span className="text-annotation">Progress</span>
            </h1>
            <p className="text-xl text-muted-foreground mt-2 max-w-2xl">
              Explore our AI-driven mathematical research process. Watch problems evolve
              from hypothesis to breakthrough—including the failed attempts along the way.
            </p>
          </div>
        </div>

        {/* Stats */}
        <div className="grid grid-cols-3 gap-4 mt-8 max-w-lg">
          <div className="bg-card border border-border rounded-lg p-4 text-center">
            <div className="flex items-center justify-center gap-2 text-green-400 mb-1">
              <Activity className="h-4 w-4" />
              <span className="text-2xl font-bold">{activeCount}</span>
            </div>
            <p className="text-xs text-muted-foreground">Active</p>
          </div>
          <div className="bg-card border border-border rounded-lg p-4 text-center">
            <div className="flex items-center justify-center gap-2 text-yellow-400 mb-1">
              <Sparkles className="h-4 w-4" />
              <span className="text-2xl font-bold">{successCount}</span>
            </div>
            <p className="text-xs text-muted-foreground">Successes</p>
          </div>
          <div className="bg-card border border-border rounded-lg p-4 text-center">
            <div className="flex items-center justify-center gap-2 text-blue-400 mb-1">
              <Target className="h-4 w-4" />
              <span className="text-2xl font-bold">{totalAttempts}</span>
            </div>
            <p className="text-xs text-muted-foreground">Attempts</p>
          </div>
        </div>

        {/* Contribute Section */}
        <div className="mt-8">
          <ContributeSection />
        </div>

        {/* Related Tools Section */}
        <div className="mt-4">
          <RelatedToolsSection />
        </div>
      </section>

      {/* Research Cards */}
      <section className="max-w-6xl mx-auto px-6 pb-16">
        <div className="flex flex-col gap-4 sm:flex-row sm:items-center sm:justify-between mb-6">
          <h2 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground">
            Research Problems ({problems.length})
          </h2>
          <div className="flex flex-wrap items-center gap-3 sm:gap-4">
            {/* Search Box */}
            <div className="relative flex-1 min-w-0 sm:flex-none">
              <Search className="absolute left-2.5 top-1/2 -translate-y-1/2 h-4 w-4 text-muted-foreground" />
              <input
                type="text"
                placeholder="Search problems..."
                value={searchInput}
                onChange={(e) => setSearchInput(e.target.value)}
                className="pl-8 pr-3 py-1.5 text-sm bg-muted/50 border border-border rounded-lg w-full sm:w-48 placeholder:text-muted-foreground focus:outline-none focus:ring-1 focus:ring-annotation focus:border-annotation"
              />
            </div>
            {/* Sort Dropdown */}
            <div className="flex items-center gap-1.5">
              <ArrowUpDown className="h-4 w-4 text-muted-foreground" />
              <select
                value={sortBy}
                onChange={(e) => setSortBy(e.target.value as SortOption)}
                className="text-sm bg-transparent border-none text-muted-foreground hover:text-foreground cursor-pointer focus:outline-none focus:ring-0"
              >
                <option value="newest">Newest</option>
                <option value="activity">Most Active</option>
                <option value="significance">Significance</option>
                <option value="alphabetical">A-Z</option>
              </select>
            </div>
            {/* Filter Button */}
            <button
              onClick={() => setShowFilters(!showFilters)}
              aria-expanded={showFilters}
              aria-controls={filterPanelId}
              className={`flex items-center gap-1.5 text-sm transition-colors ${
                showFilters || hasFilters
                  ? 'text-annotation'
                  : 'text-muted-foreground hover:text-foreground'
              }`}
            >
              <Filter className="h-4 w-4" />
              <span>Filter</span>
              {hasFilters && (
                <span className="bg-annotation/20 text-annotation px-1.5 py-0.5 rounded text-xs">
                  {selectedPhases.length + selectedTiers.length + selectedStatus.length + (searchQuery.trim() ? 1 : 0)}
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
          <div id={filterPanelId} className="mb-6 p-4 bg-card border border-border rounded-lg space-y-4">
            <div className="flex items-center justify-between">
              <span className="text-sm font-medium">Filters</span>
              {hasFilters && (
                <button
                  onClick={clearFilters}
                  className="text-xs text-muted-foreground hover:text-foreground"
                >
                  Clear all
                </button>
              )}
            </div>

            {/* Phase Filter */}
            <div>
              <span className="text-xs text-muted-foreground mb-2 block">Phase</span>
              <div className="flex flex-wrap gap-2">
                {(['OBSERVE', 'ORIENT', 'DECIDE', 'ACT', 'VERIFY', 'LEARN', 'COMPLETED'] as ResearchPhase[]).map((phase) => {
                  const info = PHASE_INFO[phase]
                  const isSelected = selectedPhases.includes(phase)
                  return (
                    <button
                      key={phase}
                      onClick={() => handlePhaseToggle(phase)}
                      aria-pressed={isSelected}
                      className={`inline-flex items-center gap-1 px-2 py-1 rounded-full text-xs font-medium transition-all ${
                        isSelected ? 'ring-2 ring-offset-1 ring-offset-background' : 'opacity-50 hover:opacity-75'
                      }`}
                      style={{
                        backgroundColor: `${info.color}20`,
                        color: info.color
                      }}
                    >
                      {info.label}
                    </button>
                  )
                })}
              </div>
            </div>

            {/* Tier Filter */}
            <div>
              <span className="text-xs text-muted-foreground mb-2 block">Tier</span>
              <div className="flex flex-wrap gap-2">
                {(['S', 'A', 'B', 'C'] as ValueTier[]).map((tier) => {
                  const info = TIER_INFO[tier]
                  const isSelected = selectedTiers.includes(tier)
                  return (
                    <button
                      key={tier}
                      onClick={() => handleTierToggle(tier)}
                      aria-pressed={isSelected}
                      className={`inline-flex items-center gap-1.5 px-2 py-1 rounded text-xs font-medium transition-all ${
                        isSelected ? 'ring-2 ring-offset-1 ring-offset-background' : 'opacity-50 hover:opacity-75'
                      }`}
                      style={{
                        backgroundColor: `${info.color}20`,
                        color: info.color
                      }}
                    >
                      <span className="font-bold">{tier}</span>
                      <span>{info.label}</span>
                    </button>
                  )
                })}
              </div>
            </div>

            {/* Status Filter */}
            <div>
              <span className="text-xs text-muted-foreground mb-2 block">Status</span>
              <div className="flex flex-wrap gap-2">
                {(['active', 'graduated'] as ResearchStatus[]).map((status) => {
                  const isSelected = selectedStatus.includes(status)
                  const color = status === 'active' ? '#22C55E' : '#3B82F6'
                  return (
                    <button
                      key={status}
                      onClick={() => handleStatusToggle(status)}
                      aria-pressed={isSelected}
                      className={`inline-flex items-center gap-1 px-2 py-1 rounded text-xs font-medium transition-all capitalize ${
                        isSelected ? 'ring-2 ring-offset-1 ring-offset-background' : 'opacity-50 hover:opacity-75'
                      }`}
                      style={{
                        backgroundColor: `${color}20`,
                        color: color
                      }}
                    >
                      {status}
                    </button>
                  )
                })}
              </div>
            </div>
          </div>
        )}

        {/* Problem Grid */}
        <div className="grid gap-6 md:grid-cols-2 lg:grid-cols-3">
          {visibleProblems.map((problem) => (
            <ResearchCard key={problem.slug} problem={problem} />
          ))}
        </div>
        {hasMore && (
          <LoadMore
            sentinelRef={sentinelRef}
            remaining={remaining}
            onShowAll={showAll}
            noun="problems"
          />
        )}

        {/* Empty state */}
        {problems.length === 0 && hasFilters && (
          <div className="text-center py-12">
            <p className="text-muted-foreground mb-4">
              No research problems match your filters.
            </p>
            <button
              onClick={clearFilters}
              className="text-sm text-annotation hover:underline"
            >
              Clear filters
            </button>
          </div>
        )}

        {problems.length === 0 && !hasFilters && (
          <div className="text-center py-12">
            <FlaskConical className="h-12 w-12 text-muted-foreground mx-auto mb-4" />
            <p className="text-muted-foreground">
              No research problems yet. Run the build script to generate data.
            </p>
          </div>
        )}
      </section>

      <Footer />
    </div>
  )
}
