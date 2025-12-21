import type { ProofSection } from '@/types/proof'
import { cn } from '@/lib/utils'
import { ScrollArea } from '@/components/ui/scroll-area'

interface TableOfContentsProps {
  title: string
  sections: ProofSection[]
  currentLine: number | null
  onSectionClick: (section: ProofSection) => void
}

export function TableOfContents({
  title,
  sections,
  currentLine,
  onSectionClick,
}: TableOfContentsProps) {
  // Find which section contains the current line
  const currentSection = currentLine
    ? sections.find(
        (s) => currentLine >= s.startLine && currentLine <= s.endLine
      )
    : null

  return (
    <div className="h-full flex flex-col">
      <div className="p-4 border-b border-border">
        <h2 className="font-semibold text-sm text-muted-foreground uppercase tracking-wider">
          Contents
        </h2>
        <h1 className="text-lg font-bold mt-1 leading-tight">{title}</h1>
      </div>

      <ScrollArea className="flex-1">
        <nav className="p-2">
          {sections.map((section, index) => (
            <button
              key={section.id}
              onClick={() => onSectionClick(section)}
              className={cn(
                'w-full text-left p-3 rounded-md transition-colors',
                'hover:bg-muted/50',
                currentSection?.id === section.id && 'bg-muted'
              )}
            >
              <div className="flex items-start gap-3">
                <span
                  className={cn(
                    'text-xs font-mono mt-0.5 shrink-0',
                    currentSection?.id === section.id
                      ? 'text-annotation'
                      : 'text-muted-foreground'
                  )}
                >
                  {String(index + 1).padStart(2, '0')}
                </span>
                <div className="min-w-0">
                  <h3
                    className={cn(
                      'text-sm font-medium leading-tight',
                      currentSection?.id === section.id && 'text-annotation'
                    )}
                  >
                    {section.title}
                  </h3>
                  <p className="text-xs text-muted-foreground mt-1 line-clamp-2">
                    {section.summary}
                  </p>
                </div>
              </div>
            </button>
          ))}
        </nav>
      </ScrollArea>

      <div className="p-4 border-t border-border">
        <div className="text-xs text-muted-foreground">
          <div className="flex items-center gap-2 mb-1">
            <span className="w-2 h-2 rounded-full bg-red-500" />
            <span>Critical to proof</span>
          </div>
          <div className="flex items-center gap-2 mb-1">
            <span className="w-2 h-2 rounded-full bg-annotation" />
            <span>Key step</span>
          </div>
          <div className="flex items-center gap-2">
            <span className="w-2 h-2 rounded-full bg-indigo-500" />
            <span>Supporting</span>
          </div>
        </div>
      </div>
    </div>
  )
}
