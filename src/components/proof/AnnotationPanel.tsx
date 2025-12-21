import type { Annotation } from '@/types/proof'
import { cn } from '@/lib/utils'
import { X } from 'lucide-react'
import { Button } from '@/components/ui/button'

interface AnnotationPanelProps {
  annotation: Annotation | null
  onClose: () => void
}

export function AnnotationPanel({ annotation, onClose }: AnnotationPanelProps) {
  if (!annotation) {
    return (
      <div className="h-full flex items-center justify-center text-muted-foreground p-6">
        <div className="text-center">
          <div className="text-4xl mb-4">
            <span className="opacity-30">{"{ }"}</span>
          </div>
          <p className="text-sm">Click on an annotated line to see its explanation</p>
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
    <div className="h-full overflow-auto">
      <div className="p-4 border-b border-border flex items-center justify-between">
        <div className="flex items-center gap-2">
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
        <Button variant="ghost" size="icon" onClick={onClose} className="h-6 w-6">
          <X className="h-4 w-4" />
        </Button>
      </div>

      <div
        className={cn(
          'p-4 border-l-4',
          significanceStyles[annotation.significance]
        )}
      >
        <h3 className="text-lg font-semibold mb-3">{annotation.title}</h3>
        <p className="text-sm text-muted-foreground leading-relaxed mb-4">
          {annotation.content}
        </p>

        {annotation.mathContext && (
          <div className="mt-4 p-3 bg-muted/30 rounded-md">
            <h4 className="text-xs font-medium text-muted-foreground uppercase tracking-wider mb-2">
              Mathematical Context
            </h4>
            <p className="text-sm font-mono leading-relaxed">
              {annotation.mathContext}
            </p>
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
    </div>
  )
}
