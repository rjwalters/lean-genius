import { useState, useMemo } from 'react'
import { Link } from 'react-router-dom'
import { listings } from '@/data/proofs'
import { useAuth } from '@/contexts/AuthContext'
import { UserMenu } from '@/components/auth/UserMenu'
import { Footer } from '@/components/Footer'
import { ProofBadge, ErdosBadge, MathlibIndicator, BadgeFilter } from '@/components/ui/proof-badge'
import { BADGE_INFO, ERDOS_BADGE_INFO } from '@/types/proof'
import { ArrowRight, Clock, CheckCircle, AlertCircle, Plus, Filter, ArrowUpDown, Search, Github, Share2, ExternalLink, Calendar, Trophy } from 'lucide-react'
import { useDebouncedUrlState, useUrlState, serializers } from '@/hooks'
import type { ProofBadge as ProofBadgeType, ProofListing } from '@/types/proof'

type SortOption = 'problem-number' | 'newest' | 'alphabetical'

// Parse MM/DD/YY to Date object
function parseDateAdded(dateStr?: string): Date {
  if (!dateStr) return new Date(0)
  const [month, day, year] = dateStr.split('/').map(Number)
  return new Date(2000 + year, month - 1, day)
}

// AI Milestones - hardcoded historic events
const AI_MILESTONES = [
  {
    date: 'November 2025',
    title: 'Erdős #124: Prime Gaps Conjecture',
    description: 'First Erdős problem solved by Aristotle proof search system',
    proofSlug: 'erdos-124',
    solver: 'Aristotle',
  },
  {
    date: 'January 2026',
    title: 'Erdős #728: Descending GPF Sequences',
    description: 'Solved by GPT-5.2 with Aristotle formalization (1,416 lines of proof)',
    proofSlug: 'erdos-728',
    solver: 'GPT-5.2 + Aristotle',
  },
]

export function ErdosPage() {
  const { isAuthenticated } = useAuth()

  // URL-synced state
  const [searchQuery, setSearchQuery] = useDebouncedUrlState('q', '', serializers.string)
  const [selectedBadges, setSelectedBadges] = useUrlState<ProofBadgeType[]>(
    'badges',
    [],
    serializers.stringArray as { parse: (v: string | null) => ProofBadgeType[]; stringify: (v: ProofBadgeType[]) => string | null }
  )
  const [sortBy, setSortBy] = useUrlState<SortOption>(
    'sort',
    'problem-number',
    serializers.enum('problem-number', ['problem-number', 'newest', 'alphabetical'])
  )
  const [showAiSolvedOnly, setShowAiSolvedOnly] = useUrlState('ai', false, serializers.boolean)

  // Local-only UI state
  const [showFilters, setShowFilters] = useState(false)
  const [showMilestones, setShowMilestones] = useState(true)

  // Filter to Erdős problems only, then apply additional filters
  const erdosProofs = useMemo(() => {
    // Start with only Erdős problems
    let filtered: ProofListing[] = listings.filter(l => l.erdosNumber !== undefined)

    // Filter by search query
    if (searchQuery.trim()) {
      const query = searchQuery.toLowerCase()
      filtered = filtered.filter((listing) =>
        listing.title.toLowerCase().includes(query) ||
        listing.description.toLowerCase().includes(query) ||
        listing.tags.some(tag => tag.toLowerCase().includes(query)) ||
        (listing.erdosNumber && listing.erdosNumber.toString().includes(query))
      )
    }

    // Filter by badge type
    if (selectedBadges.length > 0) {
      filtered = filtered.filter((listing) =>
        listing.badge && selectedBadges.includes(listing.badge)
      )
    }

    // Filter by AI-solved
    if (showAiSolvedOnly) {
      filtered = filtered.filter((listing) => listing.badge === 'ai-solved')
    }

    // Sort proofs
    return [...filtered].sort((a, b) => {
      switch (sortBy) {
        case 'problem-number':
          return (a.erdosNumber || 0) - (b.erdosNumber || 0)
        case 'newest':
          return parseDateAdded(b.dateAdded).getTime() - parseDateAdded(a.dateAdded).getTime()
        case 'alphabetical':
          return a.title.localeCompare(b.title)
        default:
          return 0
      }
    })
  }, [searchQuery, selectedBadges, sortBy, showAiSolvedOnly])

  // Compute statistics
  const stats = useMemo(() => {
    const all = listings.filter(l => l.erdosNumber !== undefined)
    const aiSolved = all.filter(l => l.badge === 'ai-solved')
    const complete = all.filter(l => l.sorries === 0)
    return {
      total: all.length,
      aiSolved: aiSolved.length,
      complete: complete.length,
    }
  }, [])

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
    setShowAiSolvedOnly(false)
    setSearchQuery('')
  }

  const hasActiveFilters = searchQuery.trim() || selectedBadges.length > 0 || showAiSolvedOnly || sortBy !== 'problem-number'

  const [copySuccess, setCopySuccess] = useState(false)
  const handleShareView = async () => {
    try {
      await navigator.clipboard.writeText(window.location.href)
      setCopySuccess(true)
      setTimeout(() => setCopySuccess(false), 2000)
    } catch {
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

  return (
    <div className="min-h-screen bg-background">
      {/* Header */}
      <header className="border-b border-border">
        <div className="max-w-6xl mx-auto px-6 py-4 flex items-center justify-between">
          <Link to="/" className="text-2xl font-bold tracking-tight hover:opacity-80 transition-opacity">
            Lean<span className="text-annotation">Genius</span>
          </Link>
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

      {/* Hero Section */}
      <section className="max-w-6xl mx-auto px-6 py-12 border-b border-border">
        <div className="flex flex-col md:flex-row md:items-start md:justify-between gap-6">
          <div className="flex-1">
            <h1 className="text-4xl md:text-5xl font-bold mb-4">
              Erdős <span className="text-annotation">Problems</span>
            </h1>
            <p className="text-lg text-muted-foreground max-w-2xl mb-4">
              Paul Erdős (1913–1996) was one of the most prolific mathematicians in history,
              publishing over 1,500 papers and posing hundreds of problems across combinatorics,
              number theory, and probability. Many remain open today.
            </p>
            <a
              href="https://www.erdosproblems.com/"
              target="_blank"
              rel="noopener noreferrer"
              className="inline-flex items-center gap-1.5 text-annotation hover:underline"
            >
              <ExternalLink className="h-4 w-4" />
              <span>erdosproblems.com</span>
            </a>
          </div>
          {/* Statistics */}
          <div className="flex gap-6 md:gap-8">
            <div className="text-center">
              <div className="text-3xl font-bold" style={{ color: ERDOS_BADGE_INFO.color }}>{stats.total}</div>
              <div className="text-sm text-muted-foreground">Problems</div>
            </div>
            <div className="text-center">
              <div className="text-3xl font-bold text-cyan-400">{stats.aiSolved}</div>
              <div className="text-sm text-muted-foreground">AI-Solved</div>
            </div>
            <div className="text-center">
              <div className="text-3xl font-bold text-green-400">{stats.complete}</div>
              <div className="text-sm text-muted-foreground">Complete</div>
            </div>
          </div>
        </div>
      </section>

      {/* AI Milestones Timeline */}
      {AI_MILESTONES.length > 0 && (
        <section className="max-w-6xl mx-auto px-6 py-8 border-b border-border">
          <button
            onClick={() => setShowMilestones(!showMilestones)}
            className="flex items-center gap-2 text-sm font-semibold uppercase tracking-wide text-muted-foreground hover:text-foreground transition-colors mb-4"
          >
            <Trophy className="h-4 w-4 text-cyan-400" />
            <span>AI Milestones</span>
            <span className="text-xs font-normal">({showMilestones ? 'hide' : 'show'})</span>
          </button>
          {showMilestones && (
            <div className="grid gap-4 md:grid-cols-2">
              {AI_MILESTONES.map((milestone, idx) => (
                <Link
                  key={idx}
                  to={`/proof/${milestone.proofSlug}`}
                  className="group block bg-card border border-border rounded-xl p-5 hover:border-cyan-400/50 hover:bg-card/80 transition-all"
                >
                  <div className="flex items-start gap-3">
                    <div className="h-10 w-10 rounded-lg bg-cyan-400/20 flex items-center justify-center flex-shrink-0">
                      <Calendar className="h-5 w-5 text-cyan-400" />
                    </div>
                    <div className="flex-1 min-w-0">
                      <div className="text-xs text-cyan-400 font-medium mb-1">{milestone.date}</div>
                      <h3 className="font-semibold group-hover:text-cyan-400 transition-colors truncate">
                        {milestone.title}
                      </h3>
                      <p className="text-sm text-muted-foreground mt-1">
                        {milestone.description}
                      </p>
                      <div className="mt-2 text-xs text-muted-foreground">
                        Solved by: <span className="text-cyan-400">{milestone.solver}</span>
                      </div>
                    </div>
                  </div>
                </Link>
              ))}
            </div>
          )}
        </section>
      )}

      {/* Problem Grid */}
      <section className="max-w-6xl mx-auto px-6 py-8">
        <div className="flex flex-col gap-4 sm:flex-row sm:items-center sm:justify-between mb-6">
          <h2 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground">
            Formalized Problems ({erdosProofs.length})
          </h2>
          <div className="flex flex-wrap items-center gap-3 sm:gap-4">
            {/* Search Box */}
            <div className="relative flex-1 min-w-0 sm:flex-none">
              <Search className="absolute left-2.5 top-1/2 -translate-y-1/2 h-4 w-4 text-muted-foreground" />
              <input
                type="text"
                placeholder="Search problems..."
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
                <option value="problem-number">By Number</option>
                <option value="newest">Newest</option>
                <option value="alphabetical">A-Z</option>
              </select>
            </div>
            {/* Filter Button */}
            <button
              onClick={() => setShowFilters(!showFilters)}
              className={`flex items-center gap-1.5 text-sm transition-colors ${
                showFilters || selectedBadges.length > 0 || showAiSolvedOnly
                  ? 'text-annotation'
                  : 'text-muted-foreground hover:text-foreground'
              }`}
            >
              <Filter className="h-4 w-4" />
              <span>Filter</span>
              {(selectedBadges.length > 0 || showAiSolvedOnly) && (
                <span className="bg-annotation/20 text-annotation px-1.5 py-0.5 rounded text-xs">
                  {selectedBadges.length + (showAiSolvedOnly ? 1 : 0)}
                </span>
              )}
            </button>
            {/* Share View Button */}
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
          <div className="mb-6 p-4 bg-card border border-border rounded-lg">
            <div className="flex items-center justify-between mb-3">
              <span className="text-sm font-medium">Filter by Category</span>
              {(selectedBadges.length > 0 || showAiSolvedOnly) && (
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
              {/* AI-Solved Filter Toggle */}
              <button
                onClick={() => setShowAiSolvedOnly(!showAiSolvedOnly)}
                className={`inline-flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-sm font-medium transition-all
                  ${showAiSolvedOnly
                    ? 'ring-2 ring-offset-2 ring-offset-background'
                    : 'opacity-50 hover:opacity-75'
                  }`}
                style={{
                  backgroundColor: `${BADGE_INFO['ai-solved'].color}20`,
                  color: BADGE_INFO['ai-solved'].color,
                  ...(showAiSolvedOnly && { ringColor: BADGE_INFO['ai-solved'].color })
                }}
              >
                <span>{BADGE_INFO['ai-solved'].emoji}</span>
                <span className="hidden sm:inline">AI-Solved</span>
              </button>
            </div>
          </div>
        )}

        <div className="grid gap-6 md:grid-cols-2 lg:grid-cols-3">
          {erdosProofs.map((listing) => (
            <Link
              key={listing.slug}
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
          ))}
        </div>

        {/* Empty state */}
        {erdosProofs.length === 0 && (searchQuery.trim() || selectedBadges.length > 0 || showAiSolvedOnly) && (
          <div className="text-center py-12">
            <p className="text-muted-foreground mb-4">
              No problems match your search{selectedBadges.length > 0 || showAiSolvedOnly ? ' and filters' : ''}.
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

      {/* External Links Section */}
      <section className="max-w-6xl mx-auto px-6 py-8 border-t border-border">
        <h2 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-4">
          External Resources
        </h2>
        <div className="grid gap-4 sm:grid-cols-2 lg:grid-cols-4">
          <ExternalLinkCard
            href="https://www.erdosproblems.com/"
            title="Erdős Problems"
            description="The canonical database of Erdős problems"
          />
          <ExternalLinkCard
            href="https://www.erdosproblems.com/forum"
            title="Discussion Forum"
            description="Community discussions on open problems"
          />
          <ExternalLinkCard
            href="https://github.com/google-deepmind/formal-conjectures"
            title="Formal Conjectures"
            description="DeepMind's formalized conjectures repository"
          />
          <ExternalLinkCard
            href="https://terrytao.wordpress.com/"
            title="Terence Tao's Blog"
            description="Commentary on mathematics and Erdős problems"
          />
        </div>
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

function ExternalLinkCard({ href, title, description }: { href: string; title: string; description: string }) {
  return (
    <a
      href={href}
      target="_blank"
      rel="noopener noreferrer"
      className="block p-4 bg-card border border-border rounded-lg hover:border-annotation/50 hover:bg-card/80 transition-all group"
    >
      <div className="flex items-center gap-2 mb-1">
        <h3 className="font-medium group-hover:text-annotation transition-colors">{title}</h3>
        <ExternalLink className="h-3.5 w-3.5 text-muted-foreground" />
      </div>
      <p className="text-sm text-muted-foreground">{description}</p>
    </a>
  )
}
