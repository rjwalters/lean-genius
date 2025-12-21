import { useState } from 'react'
import type { Annotation } from '@/types/proof'
import { cn } from '@/lib/utils'
import { X, BookOpen, MessageSquare } from 'lucide-react'
import { Button } from '@/components/ui/button'
import { MathText } from '@/components/ui/math'
import { CommentSection } from '@/components/comments'

interface AnnotationPanelProps {
  annotation: Annotation | null
  proofId: string
  lineNumber: number | null
  onClose: () => void
}

export function AnnotationPanel({ annotation, proofId, lineNumber, onClose }: AnnotationPanelProps) {
  const [activeTab, setActiveTab] = useState<'annotation' | 'comments'>('annotation')

  if (!lineNumber) {
    return (
      <div className="h-full flex items-center justify-center text-muted-foreground p-6">
        <div className="text-center">
          <div className="text-4xl mb-4">
            <span className="opacity-30">{"{ }"}</span>
          </div>
          <p className="text-sm">Click on a line to see its annotation or discussion</p>
          <p className="text-xs mt-2 opacity-60">
            Lines with colored dots have annotations
          </p>
        </div>
      </div>
    )
  }

  const significanceStyles = {
    critical: 'border-l-red-500 bg-red-500/5',
    key: 'border-l-annotation bg-annotation/5',
    supporting: 'border-l-indigo-500 bg-indigo-500/5',
  }

  const significanceLabels = {
    critical: 'Critical',
    key: 'Key Step',
    supporting: 'Supporting',
  }

  const typeLabels: Record<string, string> = {
    theorem: 'Theorem',
    lemma: 'Lemma',
    definition: 'Definition',
    tactic: 'Tactic',
    concept: 'Concept',
    insight: 'Insight',
    warning: 'Warning',
  }

  return (
    <div className="h-full flex flex-col overflow-hidden">
      {/* Tab header */}
      <div className="shrink-0 flex border-b border-border">
        <button
          onClick={() => setActiveTab('annotation')}
          className={cn(
            'flex-1 flex items-center justify-center gap-2 py-3 text-sm font-medium transition-colors',
            activeTab === 'annotation'
              ? 'border-b-2 border-annotation text-foreground'
              : 'text-muted-foreground hover:text-foreground'
          )}
        >
          <BookOpen className="h-4 w-4" />
          Annotation
        </button>
        <button
          onClick={() => setActiveTab('comments')}
          className={cn(
            'flex-1 flex items-center justify-center gap-2 py-3 text-sm font-medium transition-colors',
            activeTab === 'comments'
              ? 'border-b-2 border-annotation text-foreground'
              : 'text-muted-foreground hover:text-foreground'
          )}
        >
          <MessageSquare className="h-4 w-4" />
          Discussion
        </button>
        <Button variant="ghost" size="icon" onClick={onClose} className="h-10 w-10 shrink-0">
          <X className="h-4 w-4" />
        </Button>
      </div>

      {/* Tab content */}
      <div className="flex-1 overflow-auto">
        {activeTab === 'annotation' ? (
          annotation ? (
            <div
              className={cn(
                'p-4 border-l-4',
                significanceStyles[annotation.significance]
              )}
            >
              <div className="flex items-center gap-2 mb-3">
                <span
                  className={cn(
                    'text-xs px-2 py-0.5 rounded-full font-medium',
                    annotation.significance === 'critical' && 'bg-red-500/20 text-red-400',
                    annotation.significance === 'key' && 'bg-annotation/20 text-annotation',
                    annotation.significance === 'supporting' && 'bg-indigo-500/20 text-indigo-400'
                  )}
                >
                  {significanceLabels[annotation.significance]}
                </span>
                <span className="text-xs text-muted-foreground">
                  {typeLabels[annotation.type] || annotation.type}
                </span>
              </div>

              <h3 className="text-lg font-semibold mb-3">{annotation.title}</h3>
              <div className="text-sm text-muted-foreground leading-relaxed mb-4">
                <MathText>{annotation.content}</MathText>
              </div>

              {annotation.mathContext && (
                <div className="mt-4 p-3 bg-muted/30 rounded-md">
                  <h4 className="text-xs font-medium text-muted-foreground uppercase tracking-wider mb-2">
                    Mathematical Context
                  </h4>
                  <div className="text-sm leading-relaxed">
                    <MathText>{annotation.mathContext}</MathText>
                  </div>
                </div>
              )}

              {annotation.relatedConcepts && annotation.relatedConcepts.length > 0 && (
                <div className="mt-4">
                  <h4 className="text-xs font-medium text-muted-foreground uppercase tracking-wider mb-2">
                    Related Concepts
                  </h4>
                  <div className="flex flex-wrap gap-2">
                    {annotation.relatedConcepts.map((concept) => (
                      <span
                        key={concept}
                        className="text-xs px-2 py-1 bg-muted rounded-md"
                      >
                        {concept}
                      </span>
                    ))}
                  </div>
                </div>
              )}

              <div className="mt-4 pt-4 border-t border-border/50">
                <p className="text-xs text-muted-foreground">
                  Lines {annotation.range.startLine}
                  {annotation.range.endLine !== annotation.range.startLine &&
                    `–${annotation.range.endLine}`}
                </p>
              </div>
            </div>
          ) : (
            <div className="h-full flex items-center justify-center text-muted-foreground p-6">
              <div className="text-center">
                <BookOpen className="h-8 w-8 mx-auto mb-2 opacity-30" />
                <p className="text-sm">No annotation for line {lineNumber}</p>
                <p className="text-xs mt-1 opacity-60">
                  Switch to Discussion to view or add comments
                </p>
              </div>
            </div>
          )
        ) : (
          <CommentSection proofId={proofId} lineNumber={lineNumber} />
        )}
      </div>
    </div>
  )
}
