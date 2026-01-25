import { useState, useMemo, useCallback, useRef, useEffect } from 'react'
import { useParams, Link } from 'react-router-dom'
import { ProofViewer, AnnotationPanel, TableOfContents, ProofOverview, ProofConclusion } from '@/components/proof'
import { getProofAsync } from '@/data/proofs'
import type { Annotation, ProofSection, ProofData } from '@/types/proof'
import { Menu, Github } from 'lucide-react'
import { Button } from '@/components/ui/button'
import {
  Sheet,
  SheetContent,
  SheetTrigger,
} from '@/components/ui/sheet'
import { UserMenu } from '@/components/auth'
import { ProofBadge } from '@/components/ui/proof-badge'

export function ProofPage() {
  const { slug } = useParams<{ slug: string }>()
  const [proofData, setProofData] = useState<ProofData | null>(null)
  const [loading, setLoading] = useState(true)
  const [error, setError] = useState<string | null>(null)
  const [selectedLine, setSelectedLine] = useState<number | null>(null)
  const [sidebarOpen, setSidebarOpen] = useState(false)
  const viewerRef = useRef<HTMLDivElement>(null)

  // Load proof data asynchronously
  useEffect(() => {
    setLoading(true)
    setProofData(null)
    setError(null)
    getProofAsync(slug || '')
      .then((data) => {
        setProofData(data || null)
        setLoading(false)
      })
      .catch((err) => {
        console.error(`Failed to load proof '${slug}':`, err)
        setError(err instanceof Error ? err.message : 'Unknown error loading proof')
        setLoading(false)
      })
  }, [slug])

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

  if (loading) {
    return (
      <div className="h-screen flex flex-col items-center justify-center gap-4">
        <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-annotation" />
        <p className="text-muted-foreground">Loading proof...</p>
      </div>
    )
  }

  if (error) {
    return (
      <div className="h-screen flex flex-col items-center justify-center gap-4 p-8">
        <div className="text-center max-w-md">
          <h1 className="text-2xl font-bold mb-2 text-red-400">Error Loading Proof</h1>
          <p className="text-muted-foreground mb-4">
            Failed to load proof &quot;{slug}&quot;
          </p>
          <pre className="text-left text-xs bg-muted p-4 rounded-lg overflow-auto max-h-48 mb-4">
            {error}
          </pre>
          <Link to="/" className="text-annotation hover:underline">
            ← Back to home
          </Link>
        </div>
      </div>
    )
  }

  if (!proofData) {
    return (
      <div className="h-screen flex flex-col items-center justify-center gap-4">
        <p className="text-muted-foreground">Proof not found</p>
        <Link to="/" className="text-annotation hover:underline">
          Back to home
        </Link>
      </div>
    )
  }

  const { proof, annotations, versionInfo } = proofData

  // Show "Coming Soon" state for proofs without annotations
  if (annotations.length === 0) {
    return (
      <div className="h-screen flex flex-col overflow-hidden">
        <header className="h-14 shrink-0 border-b border-border flex items-center px-4 gap-4">
          <Link to="/" className="flex items-center gap-2 hover:opacity-80 transition-opacity">
            <span className="text-xl font-bold tracking-tight">
              Lean<span className="text-annotation">Genius</span>
            </span>
          </Link>
          <div className="flex-1" />
          <a
            href="https://github.com/rjwalters/lean-genius"
            target="_blank"
            rel="noopener noreferrer"
            className="text-muted-foreground hover:text-foreground transition-colors"
            aria-label="View on GitHub"
          >
            <Github className="h-5 w-5" />
          </a>
          <UserMenu />
        </header>
        <div className="flex-1 flex flex-col items-center justify-center gap-6 p-8">
          <div className="text-center max-w-md">
            <h1 className="text-2xl font-bold mb-2">{proof.title}</h1>
            <p className="text-muted-foreground mb-6">{proof.description}</p>
            <div className="inline-flex items-center gap-2 px-4 py-2 rounded-lg bg-yellow-500/10 text-yellow-400 border border-yellow-500/20">
              <span className="text-lg">🚧</span>
              <span className="font-medium">Coming Soon</span>
            </div>
            <p className="text-sm text-muted-foreground mt-4">
              Annotations for this proof are currently being developed.
            </p>
          </div>
          <Link to="/" className="text-annotation hover:underline text-sm">
            ← Back to gallery
          </Link>
        </div>
      </div>
    )
  }

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

        <Link to="/" className="flex items-center gap-2 hover:opacity-80 transition-opacity">
          <span className="text-xl font-bold tracking-tight">
            Lean<span className="text-annotation">Genius</span>
          </span>
        </Link>

        <div className="flex-1" />

        <div className="hidden sm:flex items-center gap-3 text-sm text-muted-foreground">
          <ProofBadge badge={proof.meta.badge} />
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

        <a
          href="https://github.com/rjwalters/lean-genius"
          target="_blank"
          rel="noopener noreferrer"
          className="text-muted-foreground hover:text-foreground transition-colors"
          aria-label="View on GitHub"
        >
          <Github className="h-5 w-5" />
        </a>
        <UserMenu />
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
          <ProofOverview proof={proof} versionInfo={versionInfo} />
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
            proofId={proof.id}
            lineNumber={selectedLine}
            onClose={handleAnnotationClose}
          />
        </aside>
      </div>

      {/* Mobile annotation panel */}
      {selectedLine && (
        <Sheet
          open={!!selectedLine}
          onOpenChange={(open) => !open && handleAnnotationClose()}
          modal={false}
        >
          <SheetContent
            side="bottom"
            className="h-[70vh] p-0 md:hidden"
            showOverlay={false}
            showCloseButton={false}
            onInteractOutside={(e) => e.preventDefault()}
            onPointerDownOutside={(e) => e.preventDefault()}
          >
            <AnnotationPanel
              annotation={selectedAnnotation}
              proofId={proof.id}
              lineNumber={selectedLine}
              onClose={handleAnnotationClose}
            />
          </SheetContent>
        </Sheet>
      )}
    </div>
  )
}
