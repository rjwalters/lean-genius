import { useState, useMemo } from 'react'
import { Link } from 'react-router-dom'
import { getAllProofs } from '@/data/proofs'
import { useAuth } from '@/contexts/AuthContext'
import { UserMenu } from '@/components/auth/UserMenu'
import { ProofBadge, BadgeFilter, MathlibIndicator } from '@/components/ui/proof-badge'
import { BookOpen, ArrowRight, Clock, CheckCircle, AlertCircle, Plus, Filter, Github, ArrowUpDown, Calendar } from 'lucide-react'
import type { ProofBadge as ProofBadgeType } from '@/types/proof'

type SortOption = 'newest' | 'oldest' | 'alphabetical'

// Parse MM/DD/YY to Date object
function parseDateAdded(dateStr?: string): Date {
  if (!dateStr) return new Date(0)
  const [month, day, year] = dateStr.split('/').map(Number)
  return new Date(2000 + year, month - 1, day)
}

export function HomePage() {
  const allProofs = getAllProofs()
  const { isAuthenticated } = useAuth()
  const [selectedBadges, setSelectedBadges] = useState<ProofBadgeType[]>([])
  const [showFilters, setShowFilters] = useState(false)
  const [sortBy, setSortBy] = useState<SortOption>('newest')

  // Filter and sort proofs
  const proofs = useMemo(() => {
    let filtered = allProofs
    if (selectedBadges.length > 0) {
      filtered = allProofs.filter(({ proof }) =>
        proof.meta.badge && selectedBadges.includes(proof.meta.badge)
      )
    }

    // Sort proofs
    return [...filtered].sort((a, b) => {
      switch (sortBy) {
        case 'newest':
          return parseDateAdded(b.proof.meta.dateAdded).getTime() - parseDateAdded(a.proof.meta.dateAdded).getTime()
        case 'oldest':
          return parseDateAdded(a.proof.meta.dateAdded).getTime() - parseDateAdded(b.proof.meta.dateAdded).getTime()
        case 'alphabetical':
          return a.proof.title.localeCompare(b.proof.title)
        default:
          return 0
      }
    })
  }, [allProofs, selectedBadges, sortBy])

  const handleBadgeToggle = (badge: ProofBadgeType) => {
    setSelectedBadges((prev) => {
      if (prev.includes(badge)) {
        return prev.filter((b) => b !== badge)
      }
      return [...prev, badge]
    })
  }

  const clearFilters = () => setSelectedBadges([])

  return (
    <div className="min-h-screen bg-background">
      {/* Header */}
      <header className="border-b border-border">
        <div className="max-w-6xl mx-auto px-6 py-4 flex items-center justify-between">
          <span className="text-2xl font-bold tracking-tight">
            Lean<span className="text-annotation">Genius</span>
          </span>
          <div className="flex items-center gap-4">
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
        <div className="flex items-center justify-between mb-6">
          <h2 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground">
            Available Proofs ({proofs.length})
          </h2>
          <div className="flex items-center gap-4">
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
                showFilters || selectedBadges.length > 0
                  ? 'text-annotation'
                  : 'text-muted-foreground hover:text-foreground'
              }`}
            >
              <Filter className="h-4 w-4" />
              <span>Filter</span>
              {selectedBadges.length > 0 && (
                <span className="bg-annotation/20 text-annotation px-1.5 py-0.5 rounded text-xs">
                  {selectedBadges.length}
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
              {selectedBadges.length > 0 && (
                <button
                  onClick={clearFilters}
                  className="text-xs text-muted-foreground hover:text-foreground"
                >
                  Clear all
                </button>
              )}
            </div>
            <BadgeFilter
              selectedBadges={selectedBadges}
              onToggle={handleBadgeToggle}
            />
          </div>
        )}

        <div className="grid gap-6 md:grid-cols-2 lg:grid-cols-3">
          {proofs.map(({ proof, annotations }) => (
            <Link
              key={proof.slug}
              to={`/proof/${proof.slug}`}
              className="group block bg-card border border-border rounded-xl p-6 hover:border-annotation/50 hover:bg-card/80 transition-all"
            >
              {/* Badge row - prominently displayed at top */}
              <div className="flex items-start justify-between mb-4">
                <ProofBadge badge={proof.meta.badge} />
                <StatusBadge status={proof.meta.status} />
              </div>

              <div className="flex items-start gap-3 mb-3">
                <div className="h-10 w-10 rounded-lg bg-annotation/20 flex items-center justify-center flex-shrink-0">
                  <BookOpen className="h-5 w-5 text-annotation" />
                </div>
                <h3 className="text-lg font-semibold group-hover:text-annotation transition-colors pt-1">
                  {proof.title}
                </h3>
              </div>

              <p className="text-sm text-muted-foreground mb-4 line-clamp-2">
                {proof.description}
              </p>

              {/* Mathlib dependency indicator */}
              <MathlibIndicator
                dependencyCount={proof.meta.mathlibDependencies?.length}
                sorries={proof.meta.sorries}
                className="mb-4"
              />

              <div className="flex items-center justify-between text-sm">
                <div className="flex flex-wrap gap-2">
                  {proof.meta.tags.slice(0, 2).map((tag) => (
                    <span
                      key={tag}
                      className="px-2 py-0.5 bg-muted rounded text-xs text-muted-foreground"
                    >
                      {tag}
                    </span>
                  ))}
                </div>
                <div className="flex items-center gap-3 text-muted-foreground">
                  {proof.meta.dateAdded && (
                    <span className="flex items-center gap-1 text-xs">
                      <Calendar className="h-3 w-3" />
                      {proof.meta.dateAdded}
                    </span>
                  )}
                  <span className="text-xs">
                    {annotations.length} annotations
                  </span>
                </div>
              </div>

              <div className="mt-4 flex items-center text-sm text-annotation opacity-0 group-hover:opacity-100 transition-opacity">
                <span>Explore proof</span>
                <ArrowRight className="h-4 w-4 ml-1" />
              </div>
            </Link>
          ))}
        </div>

        {/* Empty state when filters result in no proofs */}
        {proofs.length === 0 && selectedBadges.length > 0 && (
          <div className="text-center py-12">
            <p className="text-muted-foreground mb-4">
              No proofs match the selected filters.
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

      {/* Footer */}
      <footer className="border-t border-border">
        <div className="max-w-6xl mx-auto px-6 py-8 text-center text-sm text-muted-foreground">
          <p>
            Proofs are formalized in{' '}
            <a
              href="https://lean-lang.org/"
              target="_blank"
              rel="noopener noreferrer"
              className="text-annotation hover:underline"
            >
              Lean 4
            </a>{' '}
            with{' '}
            <a
              href="https://github.com/leanprover-community/mathlib4"
              target="_blank"
              rel="noopener noreferrer"
              className="text-annotation hover:underline"
            >
              Mathlib
            </a>
            {' · '}
            <Link to="/about" className="text-annotation hover:underline">
              About
            </Link>
            {' · '}
            <a
              href="https://github.com/rwalters/lean-genius"
              target="_blank"
              rel="noopener noreferrer"
              className="inline-flex items-center gap-1 text-annotation hover:underline"
            >
              <Github className="h-3.5 w-3.5" />
              <span>GitHub</span>
            </a>
          </p>
        </div>
      </footer>
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
