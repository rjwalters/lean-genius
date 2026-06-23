import { useState, useEffect } from 'react'
import { useParams, Link } from 'react-router-dom'
import { getResearchProblemAsync } from '@/data/research'
import { PhaseIndicator, TierBadge, PhaseProgressVertical } from '@/components/research'
import { MarkdownMath } from '@/components/ui/markdown-math'
// PHASE_INFO available if needed for phase styling
// import { PHASE_INFO } from '@/types/research'
import type { ResearchProblem } from '@/types/research'
import {
  ArrowLeft,
  FlaskConical,
  CheckCircle2,
  AlertCircle,
  ExternalLink,
  ChevronDown,
  ChevronRight,
  Target,
  Lightbulb,
  BookOpen,
  FileText,
  Archive,
  Code2,
  Github
} from 'lucide-react'

function isValidFormalStatement(formal: string | undefined): boolean {
  if (!formal || !formal.trim()) return false
  // Navigation junk from scraper
  if (formal.includes('Forum') || formal.includes('Favourites') || formal.includes('Random Solved')) return false
  // Placeholder text
  if (formal === '(LaTeX not available)') return false
  // Another placeholder variant
  if (formal.includes('\\text{(formal')) return false
  return true
}

function getSafeGithubUrl(url: string | undefined): string | undefined {
  if (!url) return undefined

  try {
    const parsed = new URL(url.trim())
    return parsed.protocol === 'https:' && parsed.hostname === 'github.com'
      ? parsed.href
      : undefined
  } catch {
    return undefined
  }
}

/** Default number of items to show before requiring expand */
const COLLAPSED_ITEM_LIMIT = 20

export function ResearchProblemPage() {
  const { slug } = useParams<{ slug: string }>()
  const [problem, setProblem] = useState<ResearchProblem | null>(null)
  const [loading, setLoading] = useState(true)
  const [activeTab, setActiveTab] = useState<'overview' | 'formalization' | 'knowledge'>('overview')
  const [expandedSessions, setExpandedSessions] = useState<string[]>([])
  const [showArchived, setShowArchived] = useState(false)
  const [showAllBuiltItems, setShowAllBuiltItems] = useState(false)
  const [showAllInsights, setShowAllInsights] = useState(false)
  const [showSessionNotes, setShowSessionNotes] = useState(false)

  useEffect(() => {
    if (!slug) return

    setLoading(true)
    getResearchProblemAsync(slug)
      .then((data) => {
        setProblem(data || null)
        setLoading(false)
      })
      .catch(() => {
        setProblem(null)
        setLoading(false)
      })
  }, [slug])

  const toggleSession = (filename: string) => {
    setExpandedSessions((prev) =>
      prev.includes(filename) ? prev.filter((s) => s !== filename) : [...prev, filename]
    )
  }

  if (loading) {
    return (
      <div className="min-h-screen bg-background flex items-center justify-center">
        <div className="text-center">
          <FlaskConical className="h-12 w-12 text-muted-foreground animate-pulse mx-auto mb-4" />
          <p className="text-muted-foreground">Loading research problem...</p>
        </div>
      </div>
    )
  }

  if (!problem) {
    return (
      <div className="min-h-screen bg-background flex items-center justify-center">
        <div className="text-center">
          <AlertCircle className="h-12 w-12 text-red-400 mx-auto mb-4" />
          <h1 className="text-2xl font-bold mb-2">Problem Not Found</h1>
          <p className="text-muted-foreground mb-4">
            The research problem "{slug}" could not be found.
          </p>
          <Link to="/research" className="text-annotation hover:underline">
            Back to Research
          </Link>
        </div>
      </div>
    )
  }

  const isGraduated = problem.status === 'graduated'
  const builtItemsCount = problem.knowledge.builtItems?.length || 0
  const insightsCount = problem.knowledge.insights?.length || 0
  const knowledgeItemCount = builtItemsCount + insightsCount
  const hasLeanFiles = problem.leanFiles && problem.leanFiles.length > 0
  const leanFilesCount = problem.leanFiles?.length || 0
  const leanTotalLines = problem.leanFiles?.reduce((s, f) => s + f.lineCount, 0) || 0
  const leanTotalTheorems = problem.leanFiles?.reduce((s, f) => s + f.theoremCount, 0) || 0
  const leanTotalAxioms = problem.leanFiles?.reduce((s, f) => s + f.axiomCount, 0) || 0
  const leanTotalSorries = problem.leanFiles?.reduce((s, f) => s + f.sorryCount, 0) || 0

  return (
    <div className="min-h-screen bg-background flex flex-col">
      {/* Header */}
      <header className="border-b border-border bg-card/50 backdrop-blur sticky top-0 z-10">
        <div className="max-w-7xl mx-auto px-6 py-3 flex items-center justify-between">
          <div className="flex items-center gap-4">
            <Link
              to="/research"
              className="flex items-center gap-1 text-sm text-muted-foreground hover:text-foreground transition-colors"
            >
              <ArrowLeft className="h-4 w-4" />
              <span className="hidden sm:inline">Research</span>
            </Link>
            <div className="h-4 w-px bg-border" />
            <h1 className="font-semibold truncate max-w-md">{problem.title}</h1>
          </div>
          <div className="flex items-center gap-3">
            <PhaseIndicator phase={problem.phase} size="sm" />
            <TierBadge tier={problem.tier} size="sm" />
            {isGraduated && (
              <span className="inline-flex items-center gap-1 px-2 py-0.5 rounded text-xs font-medium bg-green-500/20 text-green-400">
                <CheckCircle2 className="h-3 w-3" />
                Graduated
              </span>
            )}
          </div>
        </div>
      </header>

      {/* Main Content */}
      <div className="flex-1 flex">
        {/* Left Sidebar - Phase Progress */}
        <aside className="hidden lg:block w-64 border-r border-border p-6">
          <div className="sticky top-24">
            <h2 className="text-sm font-semibold text-muted-foreground mb-4 uppercase tracking-wide">
              Research Phase
            </h2>
            <PhaseProgressVertical currentPhase={problem.phase} className="mb-8" />

            {/* Quick Stats */}
            <div className="space-y-3">
              <div className="flex justify-between text-sm">
                <span className="text-muted-foreground">Built Items</span>
                <span>{builtItemsCount}</span>
              </div>
              <div className="flex justify-between text-sm">
                <span className="text-muted-foreground">Insights</span>
                <span>{insightsCount}</span>
              </div>
              <div className="flex justify-between text-sm">
                <span className="text-muted-foreground">Started</span>
                <span>{new Date(problem.started).toLocaleDateString()}</span>
              </div>
              {problem.completed && (
                <div className="flex justify-between text-sm">
                  <span className="text-muted-foreground">Completed</span>
                  <span>{new Date(problem.completed).toLocaleDateString()}</span>
                </div>
              )}
              {hasLeanFiles && (
                <>
                  <div className="flex justify-between text-sm">
                    <span className="text-muted-foreground">Lean Files</span>
                    <span>{leanFilesCount}</span>
                  </div>
                  <div className="flex justify-between text-sm">
                    <span className="text-muted-foreground">Lean Lines</span>
                    <span>{leanTotalLines.toLocaleString()}</span>
                  </div>
                </>
              )}
            </div>

            {/* Linked Proof */}
            {problem.linkedProof && (
              <div className="mt-6 p-3 bg-green-500/10 border border-green-500/30 rounded-lg">
                <p className="text-xs text-green-400 font-medium mb-2">Graduated to Proof</p>
                <Link
                  to={`/proof/${problem.linkedProof}`}
                  className="text-sm text-green-400 hover:underline flex items-center gap-1"
                >
                  View Proof <ExternalLink className="h-3 w-3" />
                </Link>
              </div>
            )}
          </div>
        </aside>

        {/* Main Content Area */}
        <main className="flex-1 overflow-auto">
          {/* Tab Navigation */}
          <div className="border-b border-border bg-card/30">
            <div className="max-w-4xl mx-auto px-6">
              <nav className="flex gap-6">
                {[
                  { id: 'overview', label: 'Overview', icon: Target },
                  ...(hasLeanFiles ? [{ id: 'formalization', label: 'Formalization', icon: Code2 }] : []),
                  { id: 'knowledge', label: 'Knowledge', icon: Lightbulb }
                ].map((tab) => {
                  const Icon = tab.icon
                  const isActive = activeTab === tab.id
                  return (
                    <button
                      key={tab.id}
                      onClick={() => setActiveTab(tab.id as typeof activeTab)}
                      className={`flex items-center gap-2 py-3 border-b-2 transition-colors ${
                        isActive
                          ? 'border-annotation text-annotation'
                          : 'border-transparent text-muted-foreground hover:text-foreground'
                      }`}
                    >
                      <Icon className="h-4 w-4" />
                      <span className="text-sm font-medium">{tab.label}</span>
                      {tab.id === 'formalization' && leanFilesCount > 0 && (
                        <span className="text-xs bg-muted px-1.5 py-0.5 rounded">
                          {leanFilesCount}
                        </span>
                      )}
                      {tab.id === 'knowledge' && knowledgeItemCount > 0 && (
                        <span className="text-xs bg-muted px-1.5 py-0.5 rounded">
                          {knowledgeItemCount}
                        </span>
                      )}
                    </button>
                  )
                })}
              </nav>
            </div>
          </div>

          {/* Tab Content */}
          <div className="max-w-4xl mx-auto px-6 py-8">
            {activeTab === 'overview' && (
              <div className="space-y-8">
                {/* Problem Statement */}
                <section>
                  <h2 className="text-lg font-semibold mb-4 flex items-center gap-2">
                    <FileText className="h-5 w-5 text-annotation" />
                    Problem Statement
                  </h2>
                  {isValidFormalStatement(problem.problemStatement.formal) && (
                    <div className="bg-card border border-border rounded-lg p-4 mb-4">
                      <p className="text-xs text-muted-foreground mb-2 uppercase tracking-wide">Formal</p>
                      <div className="text-lg">
                        <MarkdownMath>{`$$${problem.problemStatement.formal}$$`}</MarkdownMath>
                      </div>
                    </div>
                  )}
                  <div className="text-muted-foreground">
                    <MarkdownMath>{problem.problemStatement.plain}</MarkdownMath>
                  </div>
                  {problem.problemStatement.whyMatters?.length > 0 && (
                    <div className="mt-4">
                      <p className="text-sm font-medium mb-2">Why This Matters:</p>
                      <ul className="list-disc list-inside space-y-1 text-sm text-muted-foreground">
                        {problem.problemStatement.whyMatters.map((item, i) => (
                          <li key={i}>{item}</li>
                        ))}
                      </ul>
                    </div>
                  )}
                </section>

                {/* Current State */}
                <section>
                  <h2 className="text-lg font-semibold mb-4 flex items-center gap-2">
                    <Target className="h-5 w-5 text-annotation" />
                    Current State
                  </h2>
                  <div className="bg-card border border-border rounded-lg p-4 space-y-4">
                    <div className="flex items-center gap-4">
                      <PhaseIndicator phase={problem.currentState.phase} size="md" />
                      <span className="text-sm text-muted-foreground">
                        since {new Date(problem.currentState.since).toLocaleDateString()}
                      </span>
                    </div>
                    {problem.currentState.focus && (
                      <div>
                        <p className="text-sm font-medium mb-1">Current Focus</p>
                        <p className="text-sm text-muted-foreground">{problem.currentState.focus}</p>
                      </div>
                    )}
                    {problem.currentState.blockers.length > 0 && (
                      <div className="p-3 bg-red-500/10 border border-red-500/30 rounded">
                        <p className="text-sm font-medium text-red-400 mb-1">Blockers</p>
                        <ul className="list-disc list-inside text-sm text-red-400/80">
                          {problem.currentState.blockers.map((blocker, i) => (
                            <li key={i}>{blocker}</li>
                          ))}
                        </ul>
                      </div>
                    )}
                    {problem.currentState.nextAction && (
                      <div>
                        <p className="text-sm font-medium mb-1">Next Action</p>
                        <p className="text-sm text-muted-foreground">{problem.currentState.nextAction}</p>
                      </div>
                    )}
                  </div>
                </section>

                {/* Research Progress */}
                {(problem.knowledge.progressSummary || builtItemsCount > 0) && (
                  <section>
                    <h2 className="text-lg font-semibold mb-4 flex items-center gap-2">
                      <CheckCircle2 className="h-5 w-5 text-annotation" />
                      Research Progress
                    </h2>

                    {/* Progress Summary */}
                    {problem.knowledge.progressSummary && (
                      <div className="bg-annotation/10 border border-annotation/30 rounded-lg p-4 mb-4">
                        <p className="text-sm text-foreground">{problem.knowledge.progressSummary}</p>
                      </div>
                    )}

                    {/* Built Items */}
                    {builtItemsCount > 0 && (
                      <div className="space-y-2">
                        <p className="text-sm font-medium text-muted-foreground mb-2">
                          What We've Built ({builtItemsCount} items)
                        </p>
                        <div className="space-y-1.5">
                          {(problem.knowledge.builtItems || [])
                            .slice(0, showAllBuiltItems ? undefined : COLLAPSED_ITEM_LIMIT)
                            .map((item, i) => (
                              <div key={i} className="flex items-start gap-2 py-1">
                                <CheckCircle2 className="h-3.5 w-3.5 text-green-400 mt-0.5 flex-shrink-0" />
                                <div className="min-w-0">
                                  <code className="text-xs font-mono text-annotation">{item.name}</code>
                                  {item.description && (
                                    <span className="text-xs text-muted-foreground ml-2">
                                      -- {item.description}
                                    </span>
                                  )}
                                </div>
                              </div>
                            ))}
                        </div>
                        {builtItemsCount > COLLAPSED_ITEM_LIMIT && (
                          <button
                            onClick={() => setShowAllBuiltItems(!showAllBuiltItems)}
                            className="flex items-center gap-1 text-xs text-annotation hover:underline mt-2"
                          >
                            {showAllBuiltItems ? (
                              <>
                                <ChevronDown className="h-3 w-3" />
                                Show fewer
                              </>
                            ) : (
                              <>
                                <ChevronRight className="h-3 w-3" />
                                Show all {builtItemsCount} items
                              </>
                            )}
                          </button>
                        )}
                      </div>
                    )}
                  </section>
                )}

                {/* Related Proofs */}
                {problem.relatedProofs.length > 0 && (
                  <section>
                    <h2 className="text-lg font-semibold mb-4 flex items-center gap-2">
                      <BookOpen className="h-5 w-5 text-annotation" />
                      Related Proofs
                    </h2>
                    <div className="flex flex-wrap gap-3">
                      {problem.relatedProofs.map((proofSlug) => (
                        <Link
                          key={proofSlug}
                          to={`/proof/${proofSlug}`}
                          className="inline-flex items-center gap-2 px-4 py-2 bg-card border border-border rounded-lg text-sm hover:border-annotation/50 transition-colors group"
                        >
                          <BookOpen className="h-4 w-4 text-annotation" />
                          <span className="font-medium">{proofSlug}</span>
                          <span className="text-xs text-muted-foreground group-hover:text-annotation transition-colors">
                            View proof
                          </span>
                        </Link>
                      ))}
                    </div>
                  </section>
                )}

                {/* Tags */}
                {(problem.tags ?? []).length > 0 && (
                  <section>
                    <h2 className="text-sm font-semibold text-muted-foreground mb-3 uppercase tracking-wide">
                      Tags
                    </h2>
                    <div className="flex flex-wrap gap-2">
                      {(problem.tags ?? []).map((tag) => (
                        <span
                          key={tag}
                          className="px-2 py-1 bg-muted rounded text-sm text-muted-foreground"
                        >
                          {tag}
                        </span>
                      ))}
                    </div>
                  </section>
                )}
              </div>
            )}

            {activeTab === 'formalization' && hasLeanFiles && (
              <div className="space-y-6">
                <h2 className="text-lg font-semibold mb-4 flex items-center gap-2">
                  <Code2 className="h-5 w-5 text-annotation" />
                  Lean Formalization
                </h2>

                {/* Summary Banner */}
                <div className="bg-card border border-border rounded-lg p-5">
                  <h3 className="text-sm font-semibold text-muted-foreground mb-4 uppercase tracking-wide">
                    Formalization Summary
                  </h3>
                  <div className="grid grid-cols-2 sm:grid-cols-5 gap-4">
                    <div className="text-center">
                      <p className="text-2xl font-bold">{leanFilesCount}</p>
                      <p className="text-xs text-muted-foreground mt-1">Files</p>
                    </div>
                    <div className="text-center">
                      <p className="text-2xl font-bold">{leanTotalLines.toLocaleString()}</p>
                      <p className="text-xs text-muted-foreground mt-1">Lines of Lean</p>
                    </div>
                    <div className="text-center">
                      <p className="text-2xl font-bold text-green-400">{leanTotalTheorems}</p>
                      <p className="text-xs text-muted-foreground mt-1">Theorems</p>
                    </div>
                    <div className="text-center">
                      <p className="text-2xl font-bold text-blue-400">{leanTotalAxioms}</p>
                      <p className="text-xs text-muted-foreground mt-1">Axioms</p>
                    </div>
                    <div className="text-center">
                      <p className={`text-2xl font-bold ${leanTotalSorries === 0 ? 'text-green-400' : 'text-red-400'}`}>
                        {leanTotalSorries}
                      </p>
                      <p className="text-xs text-muted-foreground mt-1">Sorries</p>
                    </div>
                  </div>
                </div>

                {/* File List */}
                <div className="space-y-3">
                  {problem.leanFiles!.map((file) => {
                    const matchingProof = problem.relatedProofs.find((slug) =>
                      file.path.toLowerCase().includes(slug.toLowerCase().replace(/-/g, ''))
                    )
                    const githubUrl = getSafeGithubUrl(file.githubUrl)

                    return (
                      <div
                        key={file.path}
                        className="bg-card border border-border rounded-lg p-4"
                      >
                        <div className="flex items-start justify-between gap-4">
                          <div className="min-w-0 flex-1">
                            <div className="flex items-center gap-2 mb-2">
                              <code className="text-sm font-mono font-semibold text-foreground">
                                {file.filename}
                              </code>
                              {file.isAristotle && (
                                <span className="inline-flex items-center px-2 py-0.5 rounded text-xs font-medium bg-amber-500/20 text-amber-400">
                                  Proof Search Target
                                </span>
                              )}
                            </div>
                            <p className="text-xs text-muted-foreground font-mono mb-3">
                              {file.path}
                            </p>
                            <div className="flex flex-wrap gap-2">
                              <span className="inline-flex items-center gap-1 px-2 py-0.5 rounded text-xs bg-muted text-muted-foreground">
                                {file.lineCount.toLocaleString()} lines
                              </span>
                              <span className="inline-flex items-center gap-1 px-2 py-0.5 rounded text-xs bg-green-500/15 text-green-400">
                                {file.theoremCount} theorems
                              </span>
                              <span className="inline-flex items-center gap-1 px-2 py-0.5 rounded text-xs bg-blue-500/15 text-blue-400">
                                {file.axiomCount} axioms
                              </span>
                              <span className={`inline-flex items-center gap-1 px-2 py-0.5 rounded text-xs ${
                                file.sorryCount === 0
                                  ? 'bg-green-500/15 text-green-400'
                                  : 'bg-red-500/15 text-red-400'
                              }`}>
                                {file.sorryCount} {file.sorryCount === 1 ? 'sorry' : 'sorries'}
                              </span>
                              {file.defCount > 0 && (
                                <span className="inline-flex items-center gap-1 px-2 py-0.5 rounded text-xs bg-purple-500/15 text-purple-400">
                                  {file.defCount} defs
                                </span>
                              )}
                            </div>
                          </div>
                          <div className="flex flex-col gap-2 flex-shrink-0">
                            {githubUrl && (
                              <a
                                href={githubUrl}
                                target="_blank"
                                rel="noopener noreferrer"
                                className="inline-flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium bg-muted hover:bg-muted/80 rounded transition-colors"
                              >
                                <Github className="h-3.5 w-3.5" />
                                View on GitHub
                              </a>
                            )}
                            {matchingProof && (
                              <Link
                                to={`/proof/${matchingProof}`}
                                className="inline-flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium text-annotation bg-annotation/10 hover:bg-annotation/20 rounded transition-colors"
                              >
                                <BookOpen className="h-3.5 w-3.5" />
                                View in Gallery
                              </Link>
                            )}
                          </div>
                        </div>
                      </div>
                    )
                  })}
                </div>
              </div>
            )}

            {activeTab === 'knowledge' && (
              <div className="space-y-8">
                <h2 className="text-lg font-semibold mb-4 flex items-center gap-2">
                  <Lightbulb className="h-5 w-5 text-annotation" />
                  Research Knowledge Base
                </h2>

                {/* Always show structured data first */}

                {/* Progress Summary */}
                {problem.knowledge.progressSummary && (
                  <section>
                    <h3 className="text-sm font-semibold text-muted-foreground mb-2 uppercase tracking-wide">
                      Progress Summary
                    </h3>
                    <div className="bg-annotation/10 border border-annotation/30 rounded-lg p-4">
                      <p className="text-sm text-foreground">{problem.knowledge.progressSummary}</p>
                    </div>
                  </section>
                )}

                {/* Built Items */}
                {builtItemsCount > 0 && (
                  <section>
                    <h3 className="text-sm font-semibold text-muted-foreground mb-2 uppercase tracking-wide">
                      What We've Built ({builtItemsCount})
                    </h3>
                    <div className="space-y-2">
                      {(problem.knowledge.builtItems || [])
                        .slice(0, showAllBuiltItems ? undefined : COLLAPSED_ITEM_LIMIT)
                        .map((item, i) => (
                          <div key={i} className="flex items-start gap-3 p-2 bg-card border border-border rounded">
                            <CheckCircle2 className="h-4 w-4 text-green-400 mt-0.5 flex-shrink-0" />
                            <div>
                              <code className="text-sm font-mono text-annotation">{item.name}</code>
                              {item.description && (
                                <span className="text-sm text-muted-foreground ml-2">-- {item.description}</span>
                              )}
                            </div>
                          </div>
                        ))}
                    </div>
                    {builtItemsCount > COLLAPSED_ITEM_LIMIT && (
                      <button
                        onClick={() => setShowAllBuiltItems(!showAllBuiltItems)}
                        className="flex items-center gap-1 text-sm text-annotation hover:underline mt-3"
                      >
                        {showAllBuiltItems ? (
                          <>
                            <ChevronDown className="h-4 w-4" />
                            Show fewer
                          </>
                        ) : (
                          <>
                            <ChevronRight className="h-4 w-4" />
                            Show all {builtItemsCount} items
                          </>
                        )}
                      </button>
                    )}
                  </section>
                )}

                {/* Technical Insights */}
                {insightsCount > 0 && (
                  <section>
                    <h3 className="text-sm font-semibold text-muted-foreground mb-2 uppercase tracking-wide">
                      Technical Insights ({insightsCount})
                    </h3>
                    <ul className="space-y-2">
                      {(problem.knowledge.insights || [])
                        .slice(0, showAllInsights ? undefined : COLLAPSED_ITEM_LIMIT)
                        .map((insight, i) => (
                          <li key={i} className="flex items-start gap-2">
                            <Lightbulb className="h-4 w-4 text-yellow-400 mt-0.5 flex-shrink-0" />
                            <span className="text-muted-foreground">{insight}</span>
                          </li>
                        ))}
                    </ul>
                    {insightsCount > COLLAPSED_ITEM_LIMIT && (
                      <button
                        onClick={() => setShowAllInsights(!showAllInsights)}
                        className="flex items-center gap-1 text-sm text-annotation hover:underline mt-3"
                      >
                        {showAllInsights ? (
                          <>
                            <ChevronDown className="h-4 w-4" />
                            Show fewer
                          </>
                        ) : (
                          <>
                            <ChevronRight className="h-4 w-4" />
                            Show all {insightsCount} insights
                          </>
                        )}
                      </button>
                    )}
                  </section>
                )}

                {/* Mathlib Gaps */}
                {problem.knowledge.mathlibGaps.length > 0 && (
                  <section>
                    <h3 className="text-sm font-semibold text-muted-foreground mb-2 uppercase tracking-wide">
                      Mathlib Gaps
                    </h3>
                    <div className="p-4 bg-orange-500/5 border border-orange-500/20 rounded-lg">
                      <p className="text-xs text-orange-400 mb-2">What Mathlib is missing:</p>
                      <ul className="list-disc list-inside space-y-1 text-sm text-muted-foreground">
                        {problem.knowledge.mathlibGaps.map((gap, i) => (
                          <li key={i}>{gap}</li>
                        ))}
                      </ul>
                    </div>
                  </section>
                )}

                {/* Next Steps */}
                {problem.knowledge.nextSteps.length > 0 && (
                  <section>
                    <h3 className="text-sm font-semibold text-muted-foreground mb-2 uppercase tracking-wide">
                      Next Steps
                    </h3>
                    <ol className="list-decimal list-inside space-y-2 text-muted-foreground">
                      {problem.knowledge.nextSteps.map((step, i) => (
                        <li key={i}>{step}</li>
                      ))}
                    </ol>
                  </section>
                )}

                {/* Empty state when no structured data at all */}
                {!problem.knowledge.progressSummary &&
                 builtItemsCount === 0 &&
                 insightsCount === 0 &&
                 problem.knowledge.mathlibGaps.length === 0 &&
                 problem.knowledge.nextSteps.length === 0 &&
                 !problem.knowledge.markdown &&
                 (!problem.knowledge.archivedSessions || problem.knowledge.archivedSessions.length === 0) && (
                  <p className="text-muted-foreground text-center py-8">
                    No knowledge documented yet.
                  </p>
                )}

                {/* Session Notes (markdown) - collapsible */}
                {problem.knowledge.markdown && (
                  <section className="border-t border-border pt-6">
                    <button
                      onClick={() => setShowSessionNotes(!showSessionNotes)}
                      className="w-full flex items-center justify-between p-3 bg-card border border-border rounded-lg hover:bg-muted/50 transition-colors"
                    >
                      <div className="flex items-center gap-3">
                        <FileText className="h-5 w-5 text-muted-foreground" />
                        <span className="font-medium">Session Notes</span>
                        <span className="text-xs text-muted-foreground">Full research log</span>
                      </div>
                      {showSessionNotes ? (
                        <ChevronDown className="h-4 w-4 text-muted-foreground" />
                      ) : (
                        <ChevronRight className="h-4 w-4 text-muted-foreground" />
                      )}
                    </button>
                    {showSessionNotes && (
                      <div className="mt-3 prose prose-invert prose-sm max-w-none">
                        <MarkdownMath>{problem.knowledge.markdown}</MarkdownMath>
                      </div>
                    )}
                  </section>
                )}

                {/* Archived Sessions */}
                {problem.knowledge.archivedSessions && problem.knowledge.archivedSessions.length > 0 && (
                  <section className="border-t border-border pt-6">
                    <button
                      onClick={() => setShowArchived(!showArchived)}
                      className="w-full flex items-center justify-between p-3 bg-card border border-border rounded-lg hover:bg-muted/50 transition-colors"
                    >
                      <div className="flex items-center gap-3">
                        <Archive className="h-5 w-5 text-muted-foreground" />
                        <span className="font-medium">Archived Sessions</span>
                        <span className="text-xs text-muted-foreground bg-muted px-2 py-0.5 rounded">
                          {problem.knowledge.archivedSessions.length} older session{problem.knowledge.archivedSessions.length !== 1 ? 's' : ''}
                        </span>
                      </div>
                      {showArchived ? (
                        <ChevronDown className="h-4 w-4 text-muted-foreground" />
                      ) : (
                        <ChevronRight className="h-4 w-4 text-muted-foreground" />
                      )}
                    </button>

                    {showArchived && (
                      <div className="mt-3 space-y-2">
                        {problem.knowledge.archivedSessions.map((session) => {
                          const isExpanded = expandedSessions.includes(session.filename)
                          return (
                            <div
                              key={session.filename}
                              className="bg-card/50 border border-border rounded-lg overflow-hidden"
                            >
                              <button
                                onClick={() => toggleSession(session.filename)}
                                className="w-full px-4 py-2 flex items-center justify-between hover:bg-muted/30 transition-colors"
                              >
                                <div className="flex items-center gap-3">
                                  <span className="text-sm font-mono text-muted-foreground">
                                    #{session.sessionNumber}
                                  </span>
                                  <span className="text-sm">{session.date}</span>
                                  <span className="text-xs text-muted-foreground">
                                    {session.filename}
                                  </span>
                                </div>
                                {isExpanded ? (
                                  <ChevronDown className="h-4 w-4 text-muted-foreground" />
                                ) : (
                                  <ChevronRight className="h-4 w-4 text-muted-foreground" />
                                )}
                              </button>
                              {isExpanded && (
                                <div className="px-4 pb-4 border-t border-border/50 pt-3">
                                  <div className="prose prose-invert prose-sm max-w-none">
                                    <MarkdownMath>{session.markdown}</MarkdownMath>
                                  </div>
                                </div>
                              )}
                            </div>
                          )
                        })}
                      </div>
                    )}
                  </section>
                )}
              </div>
            )}
          </div>
        </main>
      </div>
    </div>
  )
}
