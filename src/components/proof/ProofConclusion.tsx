import { useState } from 'react'
import { ChevronDown, ChevronUp, MessageSquare, AlertCircle, Lightbulb } from 'lucide-react'
import { Button } from '@/components/ui/button'
import { MarkdownMath, MarkdownMathInline } from '@/components/ui/markdown-math'
import type { Proof } from '@/types/proof'

interface ProofConclusionProps {
  proof: Proof
}

export function ProofConclusion({ proof }: ProofConclusionProps) {
  const [isExpanded, setIsExpanded] = useState(true)
  const [isAltInterpExpanded, setIsAltInterpExpanded] = useState(false)
  const { conclusion } = proof

  if (!conclusion) return null

  return (
    <div className="border-t border-border bg-card/50">
      {/* Header */}
      <button
        onClick={() => setIsExpanded(!isExpanded)}
        className="w-full px-6 py-4 flex items-center justify-between hover:bg-muted/50 transition-colors"
      >
        <div className="flex items-center gap-3">
          <div className="h-8 w-8 rounded-lg bg-green-500/20 flex items-center justify-center">
            <MessageSquare className="h-4 w-4 text-green-400" />
          </div>
          <div className="text-left">
            <h2 className="text-lg font-semibold">Final Thoughts</h2>
            <p className="text-sm text-muted-foreground">
              Analysis summary and implications
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
          {/* Summary */}
          <section>
            <h3 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-3">
              Summary
            </h3>
            <MarkdownMath className="prose prose-invert prose-sm max-w-none text-foreground/90 leading-relaxed">
              {conclusion.summary}
            </MarkdownMath>
          </section>

          {/* Implications */}
          <section>
            <h3 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-3">
              Implications
            </h3>
            <div className="bg-green-500/5 rounded-lg p-4 border border-green-500/20">
              <MarkdownMath className="text-foreground/90 leading-relaxed">
                {conclusion.implications}
              </MarkdownMath>
            </div>
          </section>

          {/* Open Questions */}
          {conclusion.openQuestions && conclusion.openQuestions.length > 0 && (
            <section>
              <h3 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-3 flex items-center gap-2">
                <AlertCircle className="h-4 w-4 text-yellow-400" />
                Open Questions
              </h3>
              <ul className="space-y-2">
                {conclusion.openQuestions.map((question, i) => (
                  <li
                    key={i}
                    className="flex gap-3 text-sm text-foreground/90 bg-yellow-500/5 rounded-lg p-3 border border-yellow-500/20"
                  >
                    <span className="shrink-0 h-5 w-5 rounded-full bg-yellow-500/20 text-yellow-400 text-xs flex items-center justify-center font-medium">
                      ?
                    </span>
                    <MarkdownMathInline className="leading-relaxed">
                      {question}
                    </MarkdownMathInline>
                  </li>
                ))}
              </ul>
            </section>
          )}

          {/* Alternative Interpretation (collapsible) */}
          {conclusion.alternativeInterpretation && (
            <section className="border border-purple-500/30 rounded-lg overflow-hidden">
              <button
                onClick={() => setIsAltInterpExpanded(!isAltInterpExpanded)}
                className="w-full px-4 py-3 flex items-center justify-between bg-purple-500/10 hover:bg-purple-500/15 transition-colors"
              >
                <div className="flex items-center gap-3">
                  <Lightbulb className="h-4 w-4 text-purple-400" />
                  <div className="text-left">
                    <h3 className="text-sm font-semibold text-purple-300">
                      {conclusion.alternativeInterpretation.title}
                    </h3>
                    <p className="text-xs text-muted-foreground">
                      A different philosophical perspective on this proof
                    </p>
                  </div>
                </div>
                {isAltInterpExpanded ? (
                  <ChevronUp className="h-4 w-4 text-purple-400" />
                ) : (
                  <ChevronDown className="h-4 w-4 text-purple-400" />
                )}
              </button>

              {isAltInterpExpanded && (
                <div className="px-4 py-4 space-y-4 bg-purple-500/5">
                  {/* Summary */}
                  <div className="text-sm text-foreground/80 italic border-l-2 border-purple-500/50 pl-3">
                    {conclusion.alternativeInterpretation.summary}
                  </div>

                  {/* Main Perspective */}
                  <div>
                    <h4 className="text-xs font-semibold uppercase tracking-wide text-purple-400 mb-2">
                      The Perspective
                    </h4>
                    <MarkdownMath className="prose prose-invert prose-sm max-w-none text-foreground/90 leading-relaxed">
                      {conclusion.alternativeInterpretation.perspective}
                    </MarkdownMath>
                  </div>

                  {/* Computational View */}
                  {conclusion.alternativeInterpretation.computationalView && (
                    <div>
                      <h4 className="text-xs font-semibold uppercase tracking-wide text-purple-400 mb-2">
                        Computational View
                      </h4>
                      <MarkdownMath className="prose prose-invert prose-sm max-w-none text-foreground/90 leading-relaxed">
                        {conclusion.alternativeInterpretation.computationalView}
                      </MarkdownMath>
                    </div>
                  )}

                  {/* Historical Context */}
                  {conclusion.alternativeInterpretation.historicalContext && (
                    <div>
                      <h4 className="text-xs font-semibold uppercase tracking-wide text-purple-400 mb-2">
                        Historical Context
                      </h4>
                      <MarkdownMath className="prose prose-invert prose-sm max-w-none text-foreground/90 leading-relaxed">
                        {conclusion.alternativeInterpretation.historicalContext}
                      </MarkdownMath>
                    </div>
                  )}

                  {/* Lean Foundations */}
                  {conclusion.alternativeInterpretation.leanFoundations && (
                    <div>
                      <h4 className="text-xs font-semibold uppercase tracking-wide text-purple-400 mb-2">
                        What Lean Actually Proves
                      </h4>
                      <MarkdownMath className="prose prose-invert prose-sm max-w-none text-foreground/90 leading-relaxed">
                        {conclusion.alternativeInterpretation.leanFoundations}
                      </MarkdownMath>
                    </div>
                  )}
                </div>
              )}
            </section>
          )}

          {/* Status reminder */}
          <div className="flex items-center gap-2 text-sm text-muted-foreground bg-muted/30 rounded-lg px-4 py-3 mt-4">
            <span
              className={`px-2 py-0.5 rounded text-xs font-medium ${
                proof.meta.status === 'verified'
                  ? 'bg-green-500/20 text-green-400'
                  : proof.meta.status === 'pending'
                    ? 'bg-yellow-500/20 text-yellow-400'
                    : 'bg-red-500/20 text-red-400'
              }`}
            >
              {proof.meta.status}
            </span>
            <span>
              {proof.meta.status === 'pending'
                ? 'This proof contains sorry statements or has not yet been verified in Lean.'
                : proof.meta.status === 'verified'
                  ? 'This proof compiles in Lean with no sorry statements.'
                  : 'This proof is disputed and requires further analysis.'}
            </span>
          </div>
        </div>
      )}
    </div>
  )
}
