import { useState } from 'react'
import { ChevronDown, ChevronUp, GitFork, Terminal, GitPullRequest, ExternalLink } from 'lucide-react'

export function ContributeSection() {
  const [isExpanded, setIsExpanded] = useState(true)

  return (
    <div className="bg-gradient-to-r from-annotation/5 to-annotation/10 border border-annotation/20 rounded-xl overflow-hidden">
      {/* Header - Always visible */}
      <button
        onClick={() => setIsExpanded(!isExpanded)}
        className="w-full px-6 py-4 flex items-center justify-between hover:bg-annotation/5 transition-colors"
      >
        <div className="flex items-center gap-3">
          <div className="h-8 w-8 rounded-lg bg-annotation/20 flex items-center justify-center">
            <GitPullRequest className="h-4 w-4 text-annotation" />
          </div>
          <div className="text-left">
            <h3 className="font-semibold text-foreground">Contribute Research</h3>
            <p className="text-sm text-muted-foreground">
              Help advance these proofs using Claude Code
            </p>
          </div>
        </div>
        <div className="flex items-center gap-2 text-annotation">
          <span className="text-sm font-medium">
            {isExpanded ? 'Hide' : 'Show'} Instructions
          </span>
          {isExpanded ? (
            <ChevronUp className="h-4 w-4" />
          ) : (
            <ChevronDown className="h-4 w-4" />
          )}
        </div>
      </button>

      {/* Expanded Content */}
      {isExpanded && (
        <div className="px-6 pb-6 border-t border-annotation/10">
          <div className="mt-4 space-y-6">
            {/* Prerequisites */}
            <div>
              <h4 className="text-sm font-semibold text-muted-foreground uppercase tracking-wide mb-2">
                Prerequisites
              </h4>
              <ul className="text-sm text-muted-foreground space-y-1">
                <li className="flex items-center gap-2">
                  <span className="text-annotation">•</span>
                  <a
                    href="https://docs.anthropic.com/en/docs/claude-code"
                    target="_blank"
                    rel="noopener noreferrer"
                    className="text-annotation hover:underline inline-flex items-center gap-1"
                  >
                    Claude Code CLI <ExternalLink className="h-3 w-3" />
                  </a>
                </li>
                <li className="flex items-center gap-2">
                  <span className="text-annotation">•</span>
                  <a
                    href="https://cli.github.com/"
                    target="_blank"
                    rel="noopener noreferrer"
                    className="text-annotation hover:underline inline-flex items-center gap-1"
                  >
                    GitHub CLI (gh) <ExternalLink className="h-3 w-3" />
                  </a>
                </li>
                <li className="flex items-center gap-2">
                  <span className="text-annotation">•</span>
                  <span>Basic familiarity with Lean 4 (helpful but not required)</span>
                </li>
              </ul>
            </div>

            {/* Steps */}
            <div className="grid gap-4 md:grid-cols-3">
              {/* Step 1: Fork & Clone */}
              <div className="bg-card/50 border border-border rounded-lg p-4">
                <div className="flex items-center gap-2 mb-3">
                  <div className="h-6 w-6 rounded-full bg-annotation/20 flex items-center justify-center text-annotation text-xs font-bold">
                    1
                  </div>
                  <GitFork className="h-4 w-4 text-muted-foreground" />
                  <span className="font-medium text-sm">Fork & Clone</span>
                </div>
                <div className="space-y-2">
                  <p className="text-xs text-muted-foreground">
                    Fork the repository on GitHub, then clone your fork:
                  </p>
                  <pre className="text-xs bg-background/50 rounded p-2 overflow-x-auto">
                    <code className="text-annotation">git clone https://github.com/YOUR_USERNAME/lean-genius.git{'\n'}cd lean-genius</code>
                  </pre>
                </div>
              </div>

              {/* Step 2: Research */}
              <div className="bg-card/50 border border-border rounded-lg p-4">
                <div className="flex items-center gap-2 mb-3">
                  <div className="h-6 w-6 rounded-full bg-annotation/20 flex items-center justify-center text-annotation text-xs font-bold">
                    2
                  </div>
                  <Terminal className="h-4 w-4 text-muted-foreground" />
                  <span className="font-medium text-sm">Run Research</span>
                </div>
                <div className="space-y-2">
                  <p className="text-xs text-muted-foreground">
                    Start Claude Code and run the research skill (repeat as needed):
                  </p>
                  <pre className="text-xs bg-background/50 rounded p-2 overflow-x-auto">
                    <code className="text-annotation">claude{'\n'}/research</code>
                  </pre>
                  <p className="text-xs text-muted-foreground italic">
                    Run multiple iterations to make meaningful progress.
                  </p>
                </div>
              </div>

              {/* Step 3: Publish */}
              <div className="bg-card/50 border border-border rounded-lg p-4">
                <div className="flex items-center gap-2 mb-3">
                  <div className="h-6 w-6 rounded-full bg-annotation/20 flex items-center justify-center text-annotation text-xs font-bold">
                    3
                  </div>
                  <GitPullRequest className="h-4 w-4 text-muted-foreground" />
                  <span className="font-medium text-sm">Open PR</span>
                </div>
                <div className="space-y-2">
                  <p className="text-xs text-muted-foreground">
                    When ready to submit your work:
                  </p>
                  <pre className="text-xs bg-background/50 rounded p-2 overflow-x-auto">
                    <code className="text-annotation">/publish</code>
                  </pre>
                  <p className="text-xs text-muted-foreground italic">
                    Creates a PR with your research contributions.
                  </p>
                </div>
              </div>
            </div>

            {/* What happens */}
            <div className="bg-card/30 border border-border/50 rounded-lg p-4">
              <h4 className="text-sm font-semibold mb-2">What the AI researches:</h4>
              <ul className="text-xs text-muted-foreground space-y-1">
                <li>• <strong>Claims a problem</strong> from the candidate pool based on knowledge gaps</li>
                <li>• <strong>Searches Mathlib</strong> for existing infrastructure and approaches</li>
                <li>• <strong>Builds lemmas</strong> and proof infrastructure in Lean 4</li>
                <li>• <strong>Documents findings</strong> including blockers, insights, and next steps</li>
                <li>• <strong>Updates knowledge base</strong> so future sessions can build on your work</li>
              </ul>
            </div>

            {/* CTA */}
            <div className="flex items-center gap-4 pt-2">
              <a
                href="https://github.com/rjwalters/lean-genius/fork"
                target="_blank"
                rel="noopener noreferrer"
                className="inline-flex items-center gap-2 px-4 py-2 bg-[#f59e0b]/30 text-white/70 rounded-lg font-medium text-sm hover:bg-[#f59e0b] hover:text-white transition-colors"
              >
                <GitFork className="h-4 w-4" />
                Fork on GitHub
              </a>
              <a
                href="https://github.com/rjwalters/lean-genius/pulls"
                target="_blank"
                rel="noopener noreferrer"
                className="inline-flex items-center gap-2 text-sm text-muted-foreground hover:text-foreground transition-colors"
              >
                View open PRs
                <ExternalLink className="h-3 w-3" />
              </a>
            </div>
          </div>
        </div>
      )}
    </div>
  )
}
