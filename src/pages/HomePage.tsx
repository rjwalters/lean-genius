import { useState, useMemo } from 'react'
import { Link } from 'react-router-dom'
import { listings } from '@/data/proofs'
import { useAuth } from '@/contexts/AuthContext'
import { UserMenu } from '@/components/auth/UserMenu'
import { Footer } from '@/components/Footer'
import { ProofBadge, WiedijkBadge, BadgeFilter, MathlibIndicator } from '@/components/ui/proof-badge'
import { WIEDIJK_BADGE_INFO, HILBERT_BADGE_INFO, MILLENNIUM_BADGE_INFO } from '@/types/proof'
import { BookOpen, ArrowRight, Clock, CheckCircle, AlertCircle, Plus, Filter, ArrowUpDown, Search } from 'lucide-react'
import type { ProofBadge as ProofBadgeType, ProofListing } from '@/types/proof'

type SortOption = 'newest' | 'oldest' | 'alphabetical'

// Parse MM/DD/YY to Date object
function parseDateAdded(dateStr?: string): Date {
  if (!dateStr) return new Date(0)
  const [month, day, year] = dateStr.split('/').map(Number)
  return new Date(2000 + year, month - 1, day)
}

export function HomePage() {
  const { isAuthenticated } = useAuth()
  const [selectedBadges, setSelectedBadges] = useState<ProofBadgeType[]>([])
  const [showFilters, setShowFilters] = useState(false)
  const [sortBy, setSortBy] = useState<SortOption>('newest')
  const [showWiedijkOnly, setShowWiedijkOnly] = useState(false)
  const [showHilbertOnly, setShowHilbertOnly] = useState(false)
  const [showMillenniumOnly, setShowMillenniumOnly] = useState(false)
  const [searchQuery, setSearchQuery] = useState('')

  // Filter and sort proofs
  const proofs = useMemo(() => {
    let filtered: ProofListing[] = listings

    // Filter by search query
    if (searchQuery.trim()) {
      const query = searchQuery.toLowerCase()
      filtered = filtered.filter((listing) =>
        listing.title.toLowerCase().includes(query) ||
        listing.description.toLowerCase().includes(query) ||
        listing.tags.some(tag => tag.toLowerCase().includes(query))
      )
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

    // Sort proofs
    return [...filtered].sort((a, b) => {
      switch (sortBy) {
        case 'newest':
          return parseDateAdded(b.dateAdded).getTime() - parseDateAdded(a.dateAdded).getTime()
        case 'oldest':
          return parseDateAdded(a.dateAdded).getTime() - parseDateAdded(b.dateAdded).getTime()
        case 'alphabetical':
          return a.title.localeCompare(b.title)
        default:
          return 0
      }
    })
  }, [searchQuery, selectedBadges, sortBy, showWiedijkOnly, showHilbertOnly, showMillenniumOnly])

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
    setSearchQuery('')
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
            Available Proofs ({proofs.length})
          </h2>
          <div className="flex flex-wrap items-center gap-3 sm:gap-4">
            {/* Search Box */}
            <div className="relative flex-1 min-w-0 sm:flex-none">
              <Search className="absolute left-2.5 top-1/2 -translate-y-1/2 h-4 w-4 text-muted-foreground" />
              <input
                type="text"
                placeholder="Search proofs..."
                value={searchQuery}
                onChange={(e) => setSearchQuery(e.target.value)}
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
                <option value="oldest">Oldest</option>
                <option value="alphabetical">A-Z</option>
              </select>
            </div>
            {/* Filter Button */}
            <button
              onClick={() => setShowFilters(!showFilters)}
              className={`flex items-center gap-1.5 text-sm transition-colors ${
                showFilters || selectedBadges.length > 0 || showWiedijkOnly || showHilbertOnly || showMillenniumOnly
                  ? 'text-annotation'
                  : 'text-muted-foreground hover:text-foreground'
              }`}
            >
              <Filter className="h-4 w-4" />
              <span>Filter</span>
              {(selectedBadges.length > 0 || showWiedijkOnly || showHilbertOnly || showMillenniumOnly) && (
                <span className="bg-annotation/20 text-annotation px-1.5 py-0.5 rounded text-xs">
                  {selectedBadges.length + (showWiedijkOnly ? 1 : 0) + (showHilbertOnly ? 1 : 0) + (showMillenniumOnly ? 1 : 0)}
                </span>
              )}
            </button>
          </div>
        </div>

        {/* Filter Panel */}
        {showFilters && (
          <div className="mb-6 p-4 bg-card border border-border rounded-lg">
            <div className="flex items-center justify-between mb-3">
              <span className="text-sm font-medium">Filter by Category</span>
              {(selectedBadges.length > 0 || showWiedijkOnly || showHilbertOnly || showMillenniumOnly) && (
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
            </div>
          </div>
        )}

        <div className="grid gap-6 md:grid-cols-2 lg:grid-cols-3">
          {proofs.map((listing) => (
            <Link
              key={listing.slug}
              to={`/proof/${listing.slug}`}
              className="group block bg-card border border-border rounded-xl p-6 hover:border-annotation/50 hover:bg-card/80 transition-all"
            >
              {/* Badge row - prominently displayed at top */}
              <div className="flex items-start justify-between mb-4">
                <ProofBadge badge={listing.badge} />
                <StatusBadge status={listing.status} />
              </div>

              <div className="flex items-start gap-3 mb-3">
                {listing.wiedijkNumber ? (
                  <WiedijkBadge number={listing.wiedijkNumber} size="md" />
                ) : (
                  <div className="h-10 w-10 rounded-lg bg-annotation/20 flex items-center justify-center flex-shrink-0">
                    <BookOpen className="h-5 w-5 text-annotation" />
                  </div>
                )}
                <h3 className="text-lg font-semibold group-hover:text-annotation transition-colors pt-1">
                  {listing.title}
                </h3>
              </div>

              {/* Date - letter style */}
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
          ))}
        </div>

        {/* Empty state when filters result in no proofs */}
        {proofs.length === 0 && (searchQuery.trim() || selectedBadges.length > 0 || showWiedijkOnly || showHilbertOnly || showMillenniumOnly) && (
          <div className="text-center py-12">
            <p className="text-muted-foreground mb-4">
              No proofs match your search{selectedBadges.length > 0 || showWiedijkOnly || showHilbertOnly || showMillenniumOnly ? ' and filters' : ''}.
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

function StatusBadge({ status }: { status: string }) {
  const config: Record<string, { icon: typeof CheckCircle; className: string; label: string }> = {
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
    <span className={`flex items-center gap-1 px-2 py-0.5 rounded text-xs font-medium ${className}`}>
      <Icon className="h-3 w-3" />
      {label}
    </span>
  )
}
