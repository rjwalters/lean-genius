import { tokenizeLine, tokenTypeToClass, type Token } from '@/lib/lean-tokenizer'
import type { Annotation } from '@/types/proof'
import { cn } from '@/lib/utils'

interface ProofLineProps {
  lineNumber: number
  content: string
  annotations: Annotation[]
  isSelected: boolean
  onClick: () => void
  inBlockComment?: boolean
}

export function ProofLine({
  lineNumber,
  content,
  annotations,
  isSelected,
  onClick,
  inBlockComment = false,
}: ProofLineProps) {
  const { tokens } = tokenizeLine(content, inBlockComment)
  const hasAnnotation = annotations.length > 0
  const significance = annotations[0]?.significance

  return (
    <div
      className={cn(
        'group flex cursor-pointer transition-colors duration-150',
        hasAnnotation && 'hover:bg-annotation/10',
        isSelected && 'bg-annotation/20',
        !hasAnnotation && 'hover:bg-muted/30'
      )}
      onClick={onClick}
    >
      {/* Line number */}
      <div
        className={cn(
          'w-14 shrink-0 select-none pr-4 text-right text-sm tabular-nums',
          'text-muted-foreground/50',
          hasAnnotation && 'text-annotation/70',
          isSelected && 'text-annotation'
        )}
      >
        {lineNumber}
      </div>

      {/* Annotation indicator */}
      <div className="w-4 shrink-0 flex items-center justify-center">
        {hasAnnotation && (
          <div
            className={cn(
              'w-2 h-2 rounded-full transition-transform',
              'group-hover:scale-125',
              significance === 'critical' && 'bg-red-500',
              significance === 'key' && 'bg-annotation',
              significance === 'supporting' && 'bg-indigo-500',
              !significance && 'bg-annotation'
            )}
          />
        )}
      </div>

      {/* Code content */}
      <code className="flex-1 whitespace-pre text-sm leading-6">
        {content.length === 0 ? (
          <span>&nbsp;</span>
        ) : (
          <TokenizedContent content={content} tokens={tokens} />
        )}
      </code>
    </div>
  )
}

// Render content with proper whitespace preservation
function TokenizedContent({
  content,
  tokens,
}: {
  content: string
  tokens: Token[]
}) {
  const result: React.ReactNode[] = []
  let lastEnd = 0

  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i]
    // Add whitespace before this token
    if (token.start > lastEnd) {
      result.push(
        <span key={`ws-${i}`}>
          {content.slice(lastEnd, token.start)}
        </span>
      )
    }
    result.push(
      <span key={`tok-${i}`} className={tokenTypeToClass(token.type)}>
        {token.value}
      </span>
    )
    lastEnd = token.end
  }

  // Trailing content
  if (lastEnd < content.length) {
    result.push(
      <span key="ws-end">
        {content.slice(lastEnd)}
      </span>
    )
  }

  return <>{result}</>
}
