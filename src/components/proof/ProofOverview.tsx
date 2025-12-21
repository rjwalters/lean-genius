import { useState } from 'react'
import { ChevronDown, ChevronUp, ExternalLink, Lightbulb } from 'lucide-react'
import { Button } from '@/components/ui/button'
import { MathText } from '@/components/ui/math'
import type { Proof } from '@/types/proof'

interface ProofOverviewProps {
  proof: Proof
}

export function ProofOverview({ proof }: ProofOverviewProps) {
  const [isExpanded, setIsExpanded] = useState(true)
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

          {/* Historical Context */}
          <section>
            <h3 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-3">
              Historical Context
            </h3>
            <div className="prose prose-invert prose-sm max-w-none">
              {overview.historicalContext.split('\n\n').map((para, i) => (
                <p key={i} className="text-foreground/90 leading-relaxed mb-3">
                  <MathText>{para}</MathText>
                </p>
              ))}
            </div>
          </section>

          {/* Problem Statement */}
          <section>
            <h3 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-3">
              The Problem
            </h3>
            <div className="bg-muted/20 rounded-lg p-4 border border-border/50">
              {overview.problemStatement.split('\n\n').map((para, i) => (
                <div key={i} className="text-foreground/90 leading-relaxed mb-3 last:mb-0">
                  <MathText>{para}</MathText>
                </div>
              ))}
            </div>
          </section>

          {/* Proof Strategy */}
          <section>
            <h3 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-3">
              Proof Strategy
            </h3>
            <div className="prose prose-invert prose-sm max-w-none">
              {overview.proofStrategy.split('\n\n').map((para, i) => (
                <div key={i} className="text-foreground/90 leading-relaxed mb-3">
                  <MathText>{para}</MathText>
                </div>
              ))}
            </div>
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
                    <span className="leading-relaxed">
                      <MathText>{insight}</MathText>
                    </span>
                  </li>
                ))}
              </ul>
            </section>
          )}
        </div>
      )}
    </div>
  )
}
