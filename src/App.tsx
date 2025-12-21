import { useState, useMemo, useCallback, useRef } from 'react'
import { ProofViewer, AnnotationPanel, TableOfContents, ProofOverview, ProofConclusion } from '@/components/proof'
import { getProof } from '@/data/proofs'
import type { Annotation, ProofSection } from '@/types/proof'
import { Menu } from 'lucide-react'
import { Button } from '@/components/ui/button'
import {
  Sheet,
  SheetContent,
  SheetTrigger,
} from '@/components/ui/sheet'

function App() {
  const proofData = getProof('navier-stokes')
  const [selectedLine, setSelectedLine] = useState<number | null>(null)
  const [sidebarOpen, setSidebarOpen] = useState(false)
  const viewerRef = useRef<HTMLDivElement>(null)

  // Find annotation for selected line
  const selectedAnnotation = useMemo<Annotation | null>(() => {
    if (!selectedLine || !proofData) return null
    return (
      proofData.annotations.find(
        (ann) =>
          selectedLine >= ann.range.startLine &&
          selectedLine <= ann.range.endLine
      ) || null
    )
  }, [selectedLine, proofData])

  const handleLineSelect = useCallback((lineNumber: number) => {
    setSelectedLine((prev) => (prev === lineNumber ? null : lineNumber))
  }, [])

  const handleSectionClick = useCallback((section: ProofSection) => {
    setSelectedLine(section.startLine)
    setSidebarOpen(false)
    // Scroll to section (approximate - would need virtualization for precision)
    if (viewerRef.current) {
      const lineHeight = 24 // Approximate line height in pixels
      viewerRef.current.scrollTop = (section.startLine - 1) * lineHeight
    }
  }, [])

  const handleAnnotationClose = useCallback(() => {
    setSelectedLine(null)
  }, [])

  if (!proofData) {
    return (
      <div className="h-screen flex items-center justify-center">
        <p className="text-muted-foreground">Proof not found</p>
      </div>
    )
  }

  const { proof, annotations } = proofData

  return (
    <div className="h-screen flex flex-col overflow-hidden">
      {/* Header */}
      <header className="h-14 shrink-0 border-b border-border flex items-center px-4 gap-4">
        {/* Mobile menu */}
        <Sheet open={sidebarOpen} onOpenChange={setSidebarOpen}>
          <SheetTrigger asChild>
            <Button variant="ghost" size="icon" className="lg:hidden">
              <Menu className="h-5 w-5" />
            </Button>
          </SheetTrigger>
          <SheetContent side="left" className="w-80 p-0">
            <TableOfContents
              title={proof.title}
              sections={proof.sections}
              currentLine={selectedLine}
              onSectionClick={handleSectionClick}
            />
          </SheetContent>
        </Sheet>

        <div className="flex items-center gap-2">
          <span className="text-xl font-bold tracking-tight">
            Lean<span className="text-annotation">Genius</span>
          </span>
        </div>

        <div className="flex-1" />

        <div className="hidden sm:flex items-center gap-2 text-sm text-muted-foreground">
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
          <span>{annotations.length} annotations</span>
        </div>
      </header>

      {/* Main content */}
      <div className="flex-1 flex overflow-hidden">
        {/* Left sidebar - Table of Contents (desktop) */}
        <aside className="hidden lg:block w-72 shrink-0 border-r border-border">
          <TableOfContents
            title={proof.title}
            sections={proof.sections}
            currentLine={selectedLine}
            onSectionClick={handleSectionClick}
          />
        </aside>

        {/* Main proof viewer */}
        <main ref={viewerRef} className="flex-1 overflow-auto">
          <ProofOverview proof={proof} />
          <ProofViewer
            proof={proof}
            annotations={annotations}
            selectedLine={selectedLine}
            onLineSelect={handleLineSelect}
          />
          <ProofConclusion proof={proof} />
        </main>

        {/* Right sidebar - Annotation panel */}
        <aside className="hidden md:block w-96 shrink-0 border-l border-border bg-card">
          <AnnotationPanel
            annotation={selectedAnnotation}
            onClose={handleAnnotationClose}
          />
        </aside>
      </div>

      {/* Mobile annotation panel */}
      {selectedAnnotation && (
        <Sheet
          open={!!selectedAnnotation}
          onOpenChange={(open) => !open && handleAnnotationClose()}
          modal={false}
        >
          <SheetContent side="bottom" className="h-[70vh] p-0 md:hidden" showOverlay={false}>
            <AnnotationPanel
              annotation={selectedAnnotation}
              onClose={handleAnnotationClose}
            />
          </SheetContent>
        </Sheet>
      )}
    </div>
  )
}

export default App
