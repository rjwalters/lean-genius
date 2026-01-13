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
  Beaker,
  FileText,
  Archive
} from 'lucide-react'

export function ResearchProblemPage() {
  const { slug } = useParams<{ slug: string }>()
  const [problem, setProblem] = useState<ResearchProblem | null>(null)
  const [loading, setLoading] = useState(true)
  const [activeTab, setActiveTab] = useState<'overview' | 'approaches' | 'knowledge'>('overview')
  const [expandedApproaches, setExpandedApproaches] = useState<string[]>([])
  const [expandedSessions, setExpandedSessions] = useState<string[]>([])
  const [showArchived, setShowArchived] = useState(false)

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

  const toggleApproach = (id: string) => {
    setExpandedApproaches((prev) =>
      prev.includes(id) ? prev.filter((a) => a !== id) : [...prev, id]
    )
  }

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
                <span className="text-muted-foreground">Approaches</span>
                <span>{problem.approaches.length}</span>
              </div>
              <div className="flex justify-between text-sm">
                <span className="text-muted-foreground">Attempts</span>
                <span>{problem.currentState.attemptCounts.total}</span>
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
                  { id: 'approaches', label: 'Approaches', icon: Beaker },
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
                      {tab.id === 'approaches' && (
                        <span className="text-xs bg-muted px-1.5 py-0.5 rounded">
                          {problem.approaches.length}
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
                  {problem.problemStatement.formal && (
                    <div className="bg-card border border-border rounded-lg p-4 mb-4">
                      <p className="text-xs text-muted-foreground mb-2 uppercase tracking-wide">Formal</p>
                      <div className="text-lg">
                        <MarkdownMath>{`$$${problem.problemStatement.formal}$$`}</MarkdownMath>
                      </div>
                    </div>
                  )}
                  <p className="text-muted-foreground">
                    {problem.problemStatement.plain}
                  </p>
                  {problem.problemStatement.whyMatters.length > 0 && (
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

                {/* Related Proofs */}
                {problem.relatedProofs.length > 0 && (
                  <section>
                    <h2 className="text-lg font-semibold mb-4 flex items-center gap-2">
                      <BookOpen className="h-5 w-5 text-annotation" />
                      Related Proofs
                    </h2>
                    <div className="flex flex-wrap gap-2">
                      {problem.relatedProofs.map((proofSlug) => (
                        <Link
                          key={proofSlug}
                          to={`/proof/${proofSlug}`}
                          className="inline-flex items-center gap-1 px-3 py-1.5 bg-card border border-border rounded-lg text-sm hover:border-annotation/50 transition-colors"
                        >
                          <BookOpen className="h-3 w-3 text-muted-foreground" />
                          {proofSlug}
                        </Link>
                      ))}
                    </div>
                  </section>
                )}

                {/* Tags */}
                {problem.tags.length > 0 && (
                  <section>
                    <h2 className="text-sm font-semibold text-muted-foreground mb-3 uppercase tracking-wide">
                      Tags
                    </h2>
                    <div className="flex flex-wrap gap-2">
                      {problem.tags.map((tag) => (
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

            {activeTab === 'approaches' && (
              <div className="space-y-4">
                <h2 className="text-lg font-semibold mb-4 flex items-center gap-2">
                  <Beaker className="h-5 w-5 text-annotation" />
                  Approaches Tried
                </h2>
                {problem.approaches.length === 0 ? (
                  <p className="text-muted-foreground text-center py-8">
                    No approaches documented yet.
                  </p>
                ) : (
                  <div className="space-y-3">
                    {problem.approaches.map((approach, index) => {
                      const isExpanded = expandedApproaches.includes(approach.id)
                      const statusColor = approach.status === 'completed' ? '#22C55E' :
                        approach.status === 'abandoned' ? '#EF4444' : '#F59E0B'

                      return (
                        <div
                          key={approach.id}
                          className="bg-card border border-border rounded-lg overflow-hidden"
                        >
                          <button
                            onClick={() => toggleApproach(approach.id)}
                            className="w-full px-4 py-3 flex items-center justify-between hover:bg-muted/50 transition-colors"
                          >
                            <div className="flex items-center gap-3">
                              <span className="text-sm text-muted-foreground">
                                #{index + 1}
                              </span>
                              <span className="font-medium">{approach.name}</span>
                              <span
                                className="px-2 py-0.5 rounded text-xs font-medium capitalize"
                                style={{
                                  backgroundColor: `${statusColor}20`,
                                  color: statusColor
                                }}
                              >
                                {approach.status}
                              </span>
                              <span className="text-xs text-muted-foreground">
                                {approach.attempts.length} attempt{approach.attempts.length !== 1 ? 's' : ''}
                              </span>
                            </div>
                            {isExpanded ? (
                              <ChevronDown className="h-4 w-4 text-muted-foreground" />
                            ) : (
                              <ChevronRight className="h-4 w-4 text-muted-foreground" />
                            )}
                          </button>
                          {isExpanded && (
                            <div className="px-4 pb-4 border-t border-border pt-4 space-y-4">
                              {approach.strategy && (
                                <div>
                                  <p className="text-sm font-medium mb-1">Strategy</p>
                                  <p className="text-sm text-muted-foreground whitespace-pre-wrap">
                                    {approach.strategy}
                                  </p>
                                </div>
                              )}
                              {approach.attempts.length > 0 && (
                                <div>
                                  <p className="text-sm font-medium mb-2">Attempts</p>
                                  <div className="space-y-1">
                                    {approach.attempts.map((attempt, i) => (
                                      <div
                                        key={i}
                                        className="flex items-center gap-2 text-sm"
                                      >
                                        {attempt.succeeded ? (
                                          <CheckCircle2 className="h-3 w-3 text-green-400" />
                                        ) : (
                                          <AlertCircle className="h-3 w-3 text-red-400" />
                                        )}
                                        <span className="font-mono text-xs text-muted-foreground">
                                          {attempt.file}
                                        </span>
                                      </div>
                                    ))}
                                  </div>
                                </div>
                              )}
                              {approach.postMortem && (
                                <div className="p-3 bg-red-500/5 border border-red-500/20 rounded">
                                  <p className="text-sm font-medium text-red-400 mb-2">Post-Mortem</p>
                                  {approach.postMortem.whatFailed.length > 0 && (
                                    <div className="mb-2">
                                      <p className="text-xs text-red-400/70 mb-1">What Failed:</p>
                                      <ul className="list-disc list-inside text-sm text-muted-foreground">
                                        {approach.postMortem.whatFailed.map((item, i) => (
                                          <li key={i}>{item}</li>
                                        ))}
                                      </ul>
                                    </div>
                                  )}
                                  {approach.postMortem.lessonsLearned.length > 0 && (
                                    <div>
                                      <p className="text-xs text-yellow-400/70 mb-1">Lessons Learned:</p>
                                      <ul className="list-disc list-inside text-sm text-muted-foreground">
                                        {approach.postMortem.lessonsLearned.map((item, i) => (
                                          <li key={i}>{item}</li>
                                        ))}
                                      </ul>
                                    </div>
                                  )}
                                </div>
                              )}
                            </div>
                          )}
                        </div>
                      )
                    })}
                  </div>
                )}
              </div>
            )}

            {activeTab === 'knowledge' && (
              <div className="space-y-8">
                <h2 className="text-lg font-semibold mb-4 flex items-center gap-2">
                  <Lightbulb className="h-5 w-5 text-annotation" />
                  Research Knowledge Base
                </h2>

                {/* Full markdown content if available */}
                {problem.knowledge.markdown ? (
                  <section className="prose prose-invert prose-sm max-w-none">
                    <MarkdownMath>{problem.knowledge.markdown}</MarkdownMath>
                  </section>
                ) : null}

                {/* Archived Sessions */}
                {problem.knowledge.archivedSessions && problem.knowledge.archivedSessions.length > 0 && (
                  <section className="mt-8 border-t border-border pt-6">
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

                {!problem.knowledge.markdown && (
                  <>
                    {/* Fallback to structured data */}
                    {problem.knowledge.progressSummary && (
                      <section>
                        <h3 className="text-sm font-semibold text-muted-foreground mb-2 uppercase tracking-wide">
                          Progress Summary
                        </h3>
                        <p className="text-muted-foreground">{problem.knowledge.progressSummary}</p>
                      </section>
                    )}

                    {problem.knowledge.builtItems && problem.knowledge.builtItems.length > 0 && (
                      <section>
                        <h3 className="text-sm font-semibold text-muted-foreground mb-2 uppercase tracking-wide">
                          What We've Built
                        </h3>
                        <div className="space-y-2">
                          {problem.knowledge.builtItems.map((item, i) => (
                            <div key={i} className="flex items-start gap-3 p-2 bg-card border border-border rounded">
                              <CheckCircle2 className="h-4 w-4 text-green-400 mt-0.5 flex-shrink-0" />
                              <div>
                                <code className="text-sm font-mono text-annotation">{item.name}</code>
                                {item.description && (
                                  <span className="text-sm text-muted-foreground ml-2">— {item.description}</span>
                                )}
                              </div>
                            </div>
                          ))}
                        </div>
                      </section>
                    )}

                    {problem.knowledge.insights.length > 0 && !problem.knowledge.builtItems?.length && (
                      <section>
                        <h3 className="text-sm font-semibold text-muted-foreground mb-2 uppercase tracking-wide">
                          Technical Insights
                        </h3>
                        <ul className="space-y-2">
                          {problem.knowledge.insights.map((insight, i) => (
                            <li key={i} className="flex items-start gap-2">
                              <Lightbulb className="h-4 w-4 text-yellow-400 mt-0.5 flex-shrink-0" />
                              <span className="text-muted-foreground">{insight}</span>
                            </li>
                          ))}
                        </ul>
                      </section>
                    )}

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

                    {problem.knowledge.insights.length === 0 &&
                     (!problem.knowledge.builtItems || problem.knowledge.builtItems.length === 0) &&
                     problem.knowledge.mathlibGaps.length === 0 &&
                     problem.knowledge.nextSteps.length === 0 &&
                     !problem.knowledge.progressSummary && (
                      <p className="text-muted-foreground text-center py-8">
                        No knowledge documented yet.
                      </p>
                    )}
                  </>
                )}
              </div>
            )}
          </div>
        </main>
      </div>
    </div>
  )
}
