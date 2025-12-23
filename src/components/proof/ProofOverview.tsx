import { useState } from 'react'
import { ChevronDown, ChevronUp, ExternalLink, Lightbulb, Package, Award, History, CheckCircle, Clock, AlertCircle, AlertTriangle, Eye } from 'lucide-react'
import { Button } from '@/components/ui/button'
import { MarkdownMath, MarkdownMathInline } from '@/components/ui/markdown-math'
import { ProofBadge } from '@/components/ui/proof-badge'
import { BADGE_INFO } from '@/types/proof'
import type { Proof, ProofVersionInfo, VersionHistoryEntry } from '@/types/proof'
import {
  Dialog,
  DialogContent,
  DialogHeader,
  DialogTitle,
  DialogDescription,
} from '@/components/ui/dialog'
import { ScrollArea } from '@/components/ui/scroll-area'

interface ProofOverviewProps {
  proof: Proof
  versionInfo?: ProofVersionInfo
}

// Helper to get status icon and color
function getVersionStatusConfig(status: VersionHistoryEntry['status']) {
  const config: Record<VersionHistoryEntry['status'], { icon: typeof CheckCircle; className: string; label: string }> = {
    verified: { icon: CheckCircle, className: 'text-green-400', label: 'Verified' },
    pending: { icon: Clock, className: 'text-yellow-400', label: 'Pending' },
    disputed: { icon: AlertCircle, className: 'text-red-400', label: 'Disputed' },
    conditional: { icon: AlertTriangle, className: 'text-orange-400', label: 'Conditional' },
    axiomatized: { icon: AlertCircle, className: 'text-purple-400', label: 'Axiomatized' },
    revised: { icon: Clock, className: 'text-blue-400', label: 'Revised' },
  }
  return config[status] || config.pending
}

export function ProofOverview({ proof, versionInfo }: ProofOverviewProps) {
  const [isExpanded, setIsExpanded] = useState(true)
  const [isVersionHistoryExpanded, setIsVersionHistoryExpanded] = useState(false)
  const [selectedVersion, setSelectedVersion] = useState<VersionHistoryEntry | null>(null)
  const { overview, meta } = proof

  if (!overview) return null

  return (
    <div className="border-b border-border bg-card/50">
      {/* Header */}
      <button
        onClick={() => setIsExpanded(!isExpanded)}
        className="w-full px-6 py-4 flex items-center justify-between hover:bg-muted/50 transition-colors"
      >
        <div className="flex items-center gap-3">
          <div className="h-8 w-8 rounded-lg bg-annotation/20 flex items-center justify-center">
            <Lightbulb className="h-4 w-4 text-annotation" />
          </div>
          <div className="text-left">
            <h2 className="text-lg font-semibold">Introduction & Overview</h2>
            <p className="text-sm text-muted-foreground">
              Historical context and proof strategy
            </p>
          </div>
        </div>
        <Button variant="ghost" size="icon" className="shrink-0">
          {isExpanded ? (
            <ChevronUp className="h-5 w-5" />
          ) : (
            <ChevronDown className="h-5 w-5" />
          )}
        </Button>
      </button>

      {/* Content */}
      {isExpanded && (
        <div className="px-6 pb-6 space-y-6">
          {/* Author credit */}
          {meta.author && (
            <div className="flex items-center gap-2 text-sm text-muted-foreground bg-muted/30 rounded-lg px-4 py-3">
              <span>Proof by</span>
              <span className="font-medium text-foreground">{meta.author}</span>
              {meta.authorHandle && (
                <span className="text-annotation">{meta.authorHandle}</span>
              )}
              {meta.date && (
                <>
                  <span className="mx-1">·</span>
                  <span>{new Date(meta.date).toLocaleDateString('en-US', {
                    year: 'numeric',
                    month: 'long',
                    day: 'numeric'
                  })}</span>
                </>
              )}
              {meta.sourceUrl && (
                <a
                  href={meta.sourceUrl}
                  target="_blank"
                  rel="noopener noreferrer"
                  className="ml-auto flex items-center gap-1 text-annotation hover:underline"
                >
                  <span>Source</span>
                  <ExternalLink className="h-3 w-3" />
                </a>
              )}
            </div>
          )}

          {/* Version History */}
          {versionInfo && versionInfo.versionHistory.length > 1 && (
            <div className="bg-muted/20 rounded-lg border border-border/50 overflow-hidden">
              <button
                onClick={() => setIsVersionHistoryExpanded(!isVersionHistoryExpanded)}
                className="w-full px-4 py-3 flex items-center justify-between hover:bg-muted/30 transition-colors"
              >
                <div className="flex items-center gap-2">
                  <History className="h-4 w-4 text-muted-foreground" />
                  <span className="text-sm font-medium">Version History</span>
                  <span className="text-xs text-muted-foreground">
                    (Currently viewing {versionInfo.currentVersion})
                  </span>
                </div>
                <ChevronDown className={`h-4 w-4 text-muted-foreground transition-transform ${isVersionHistoryExpanded ? 'rotate-180' : ''}`} />
              </button>

              {isVersionHistoryExpanded && (
                <div className="px-4 pb-4 space-y-3">
                  {versionInfo.versionHistory.map((version) => {
                    const isCurrent = version.version === versionInfo.currentVersion
                    const statusConfig = getVersionStatusConfig(version.status)
                    const StatusIcon = statusConfig.icon

                    return (
                      <div
                        key={version.version}
                        className="pb-2"
                      >
                        <div
                          className={`rounded-lg p-3 ${isCurrent ? 'bg-annotation/10 border border-annotation/30' : 'bg-muted/10 hover:bg-muted/20 cursor-pointer transition-colors'}`}
                          onClick={() => !isCurrent && version.content && setSelectedVersion(version)}
                          role={!isCurrent && version.content ? 'button' : undefined}
                          tabIndex={!isCurrent && version.content ? 0 : undefined}
                          onKeyDown={(e) => {
                            if (!isCurrent && version.content && (e.key === 'Enter' || e.key === ' ')) {
                              e.preventDefault()
                              setSelectedVersion(version)
                            }
                          }}
                        >
                          <div className="flex items-center gap-2 flex-wrap">
                            <span className={`font-mono text-sm font-semibold ${isCurrent ? 'text-annotation' : 'text-foreground'}`}>
                              {version.version}
                            </span>
                            <span className="text-sm text-foreground/90">{version.name}</span>
                            {isCurrent && (
                              <span className="text-xs bg-annotation/20 text-annotation px-1.5 py-0.5 rounded">
                                Current
                              </span>
                            )}
                            {!isCurrent && version.content && (
                              <span className="ml-auto flex items-center gap-1 text-xs text-muted-foreground hover:text-foreground">
                                <Eye className="h-3 w-3" />
                                View
                              </span>
                            )}
                          </div>

                          <div className="flex items-center gap-3 mt-1.5 text-xs text-muted-foreground">
                            <span>{new Date(version.date).toLocaleDateString('en-US', {
                              year: 'numeric',
                              month: 'short',
                              day: 'numeric'
                            })}</span>
                            <span className={`flex items-center gap-1 ${statusConfig.className}`}>
                              <StatusIcon className="h-3 w-3" />
                              {statusConfig.label}
                            </span>
                          </div>

                          {version.summary && (
                            <p className="text-xs text-muted-foreground mt-2 leading-relaxed">
                              {version.summary}
                            </p>
                          )}
                        </div>
                      </div>
                    )
                  })}
                </div>
              )}
            </div>
          )}

          {/* Badge & Mathlib Transparency */}
          {(meta.badge || meta.mathlibDependencies || meta.originalContributions) && (
            <div className="grid gap-4 sm:grid-cols-2">
              {/* Badge info */}
              {meta.badge && (
                <div className="bg-muted/20 rounded-lg p-4 border border-border/50">
                  <div className="flex items-center gap-2 mb-2">
                    <Award className="h-4 w-4 text-muted-foreground" />
                    <h4 className="text-sm font-medium">Proof Category</h4>
                  </div>
                  <div className="flex items-center gap-3">
                    <ProofBadge badge={meta.badge} size="md" />
                  </div>
                  <p className="text-xs text-muted-foreground mt-2">
                    {BADGE_INFO[meta.badge].description}
                  </p>
                </div>
              )}

              {/* Mathlib dependencies */}
              {meta.mathlibDependencies && meta.mathlibDependencies.length > 0 && (
                <div className="bg-muted/20 rounded-lg p-4 border border-border/50">
                  <div className="flex items-center gap-2 mb-2">
                    <Package className="h-4 w-4 text-muted-foreground" />
                    <h4 className="text-sm font-medium">Mathlib Dependencies</h4>
                  </div>
                  <ul className="space-y-2">
                    {meta.mathlibDependencies.slice(0, 3).map((dep, i) => (
                      <li key={i} className="text-xs">
                        <code className="bg-background/50 px-1.5 py-0.5 rounded text-annotation font-mono">
                          {dep.theorem}
                        </code>
                        <p className="text-muted-foreground mt-0.5">{dep.description}</p>
                      </li>
                    ))}
                    {meta.mathlibDependencies.length > 3 && (
                      <li className="text-xs text-muted-foreground">
                        +{meta.mathlibDependencies.length - 3} more dependencies
                      </li>
                    )}
                  </ul>
                </div>
              )}

              {/* Original contributions */}
              {meta.originalContributions && meta.originalContributions.length > 0 && (
                <div className="bg-annotation/5 rounded-lg p-4 border border-annotation/20 sm:col-span-2">
                  <div className="flex items-center gap-2 mb-2">
                    <span className="text-lg">🏆</span>
                    <h4 className="text-sm font-medium text-annotation">What's Original</h4>
                  </div>
                  <ul className="space-y-1">
                    {meta.originalContributions.map((contribution, i) => (
                      <li key={i} className="text-sm text-foreground/90 flex gap-2">
                        <span className="text-annotation">•</span>
                        <span>{contribution}</span>
                      </li>
                    ))}
                  </ul>
                </div>
              )}
            </div>
          )}

          {/* Historical Context */}
          <section>
            <h3 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-3">
              Historical Context
            </h3>
            <MarkdownMath className="prose prose-invert prose-sm max-w-none text-foreground/90 leading-relaxed">
              {overview.historicalContext}
            </MarkdownMath>
          </section>

          {/* Problem Statement */}
          <section>
            <h3 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-3">
              The Problem
            </h3>
            <div className="bg-muted/20 rounded-lg p-4 border border-border/50">
              <MarkdownMath className="text-foreground/90 leading-relaxed">
                {overview.problemStatement}
              </MarkdownMath>
            </div>
          </section>

          {/* Proof Strategy */}
          <section>
            <h3 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-3">
              Proof Strategy
            </h3>
            <MarkdownMath className="prose prose-invert prose-sm max-w-none text-foreground/90 leading-relaxed">
              {overview.proofStrategy}
            </MarkdownMath>
          </section>

          {/* Key Insights */}
          {overview.keyInsights && overview.keyInsights.length > 0 && (
            <section>
              <h3 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-3">
                Key Insights
              </h3>
              <ul className="space-y-2">
                {overview.keyInsights.map((insight, i) => (
                  <li
                    key={i}
                    className="flex gap-3 text-sm text-foreground/90 bg-annotation/5 rounded-lg p-3 border border-annotation/20"
                  >
                    <span className="shrink-0 h-5 w-5 rounded-full bg-annotation/20 text-annotation text-xs flex items-center justify-center font-medium">
                      {i + 1}
                    </span>
                    <MarkdownMathInline className="leading-relaxed">
                      {insight}
                    </MarkdownMathInline>
                  </li>
                ))}
              </ul>
            </section>
          )}
        </div>
      )}

      {/* Version Content Dialog */}
      <Dialog open={!!selectedVersion} onOpenChange={(open) => !open && setSelectedVersion(null)}>
        <DialogContent className="max-w-3xl max-h-[85vh] flex flex-col">
          {selectedVersion && selectedVersion.content && (
            <>
              <DialogHeader>
                <DialogTitle className="flex items-center gap-3">
                  <span className="font-mono text-annotation">{selectedVersion.version}</span>
                  <span>{selectedVersion.name}</span>
                </DialogTitle>
                <DialogDescription className="flex items-center gap-3">
                  <span>{new Date(selectedVersion.date).toLocaleDateString('en-US', {
                    year: 'numeric',
                    month: 'long',
                    day: 'numeric'
                  })}</span>
                  <span className={`flex items-center gap-1 ${getVersionStatusConfig(selectedVersion.status).className}`}>
                    {(() => {
                      const StatusIcon = getVersionStatusConfig(selectedVersion.status).icon
                      return <StatusIcon className="h-3 w-3" />
                    })()}
                    {getVersionStatusConfig(selectedVersion.status).label}
                  </span>
                </DialogDescription>
              </DialogHeader>

              <ScrollArea className="flex-1 -mx-6 px-6">
                <div className="space-y-6 pb-4">
                  {/* Verdict/Status */}
                  {selectedVersion.content.objection && (
                    <div className="bg-red-500/10 border border-red-500/30 rounded-lg p-4">
                      <h4 className="text-sm font-semibold text-red-400 mb-2">
                        {selectedVersion.content.objection.verdict}
                      </h4>
                      <p className="text-sm text-foreground/90">
                        {selectedVersion.content.objection.summary}
                      </p>
                    </div>
                  )}

                  {/* Description */}
                  <div>
                    <h4 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-2">
                      Description
                    </h4>
                    <p className="text-sm text-foreground/90 leading-relaxed">
                      {selectedVersion.content.description}
                    </p>
                  </div>

                  {/* Proof Strategy */}
                  {selectedVersion.content.overview?.proofStrategy && (
                    <div>
                      <h4 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-2">
                        Proof Strategy
                      </h4>
                      <MarkdownMath className="prose prose-invert prose-sm max-w-none text-foreground/90">
                        {selectedVersion.content.overview.proofStrategy}
                      </MarkdownMath>
                    </div>
                  )}

                  {/* Key Insights */}
                  {selectedVersion.content.overview?.keyInsights && selectedVersion.content.overview.keyInsights.length > 0 && (
                    <div>
                      <h4 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-2">
                        Key Insights
                      </h4>
                      <ul className="space-y-2">
                        {selectedVersion.content.overview.keyInsights.map((insight, i) => (
                          <li
                            key={i}
                            className="flex gap-3 text-sm text-foreground/90 bg-muted/20 rounded-lg p-3"
                          >
                            <span className="shrink-0 h-5 w-5 rounded-full bg-muted text-muted-foreground text-xs flex items-center justify-center font-medium">
                              {i + 1}
                            </span>
                            <span className="leading-relaxed">{insight}</span>
                          </li>
                        ))}
                      </ul>
                    </div>
                  )}

                  {/* Conclusion */}
                  {selectedVersion.content.conclusion && (
                    <div>
                      <h4 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-2">
                        Conclusion
                      </h4>
                      <MarkdownMath className="prose prose-invert prose-sm max-w-none text-foreground/90">
                        {selectedVersion.content.conclusion.summary}
                      </MarkdownMath>
                    </div>
                  )}
                </div>
              </ScrollArea>
            </>
          )}
        </DialogContent>
      </Dialog>
    </div>
  )
}
