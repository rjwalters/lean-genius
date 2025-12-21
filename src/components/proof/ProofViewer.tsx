import { useMemo, useCallback } from 'react'
import { ScrollArea } from '@/components/ui/scroll-area'
import { ProofLine } from './ProofLine'
import type { Proof, Annotation } from '@/types/proof'

interface ProofViewerProps {
  proof: Proof
  annotations: Annotation[]
  selectedLine: number | null
  onLineSelect: (lineNumber: number) => void
}

export function ProofViewer({
  proof,
  annotations,
  selectedLine,
  onLineSelect,
}: ProofViewerProps) {
  const lines = useMemo(() => proof.source.split('\n'), [proof.source])

  // Create a map of line numbers to annotations
  const annotationsByLine = useMemo(() => {
    const map = new Map<number, Annotation[]>()
    for (const ann of annotations) {
      for (let line = ann.range.startLine; line <= ann.range.endLine; line++) {
        const existing = map.get(line) || []
        existing.push(ann)
        map.set(line, existing)
      }
    }
    return map
  }, [annotations])

  const handleLineClick = useCallback(
    (lineNumber: number) => {
      onLineSelect(lineNumber)
    },
    [onLineSelect]
  )

  return (
    <ScrollArea className="h-full">
      <div className="py-4 font-mono">
        {lines.map((content, index) => {
          const lineNumber = index + 1
          const lineAnnotations = annotationsByLine.get(lineNumber) || []
          return (
            <ProofLine
              key={lineNumber}
              lineNumber={lineNumber}
              content={content}
              annotations={lineAnnotations}
              isSelected={selectedLine === lineNumber}
              onClick={() => handleLineClick(lineNumber)}
            />
          )
        })}
      </div>
    </ScrollArea>
  )
}
