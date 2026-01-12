import { useState } from 'react'
import { ChevronDown, ChevronUp, Cpu, ExternalLink, Zap, Brain, Shield } from 'lucide-react'

interface Tool {
  name: string
  url: string
  description: string
  approach: string
  strengths: string[]
  icon: 'cpu' | 'brain' | 'zap'
}

const RELATED_TOOLS: Tool[] = [
  {
    name: 'Aristotle',
    url: 'https://aristotle.harmonic.fun/',
    description: 'Mathematical superintelligence by Harmonic. IMO Gold Medal level, solved Erdős #124 variant.',
    approach: 'Monte Carlo Graph Search + 200B+ param transformer + RL expert iteration',
    strengths: [
      'Fully autonomous proof search',
      'Native Lean 4 + Mathlib integration',
      'Can fill multiple sorries in one pass',
      'Provides counterexamples for invalid statements'
    ],
    icon: 'brain'
  },
  {
    name: 'AlphaProof',
    url: 'https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/',
    description: 'DeepMind\'s formal reasoning system. IMO 2024 Silver Medal equivalent.',
    approach: 'AlphaZero-style RL + Gemini for formalization + proof search',
    strengths: [
      'Strong on competition math',
      'Novel proof discovery',
      'Automated problem formalization'
    ],
    icon: 'zap'
  },
  {
    name: 'LeanGenius OODA',
    url: '#',
    description: 'Our approach: Human-guided iterative refinement with Claude Opus.',
    approach: 'Observe-Orient-Decide-Act loop with human oversight at each stage',
    strengths: [
      'Transparent reasoning process',
      'Human-in-the-loop control',
      'General-purpose (not math-only)',
      'Explainable decisions'
    ],
    icon: 'cpu'
  }
]

const IconComponent = ({ icon }: { icon: Tool['icon'] }) => {
  switch (icon) {
    case 'brain':
      return <Brain className="h-5 w-5" />
    case 'zap':
      return <Zap className="h-5 w-5" />
    case 'cpu':
    default:
      return <Cpu className="h-5 w-5" />
  }
}

export function RelatedToolsSection() {
  const [isExpanded, setIsExpanded] = useState(false)

  return (
    <div className="bg-gradient-to-r from-blue-500/5 to-purple-500/10 border border-blue-500/20 rounded-xl overflow-hidden">
      {/* Header - Always visible */}
      <button
        onClick={() => setIsExpanded(!isExpanded)}
        className="w-full px-6 py-4 flex items-center justify-between hover:bg-blue-500/5 transition-colors"
      >
        <div className="flex items-center gap-3">
          <div className="h-8 w-8 rounded-lg bg-blue-500/20 flex items-center justify-center">
            <Shield className="h-4 w-4 text-blue-400" />
          </div>
          <div className="text-left">
            <h3 className="font-semibold text-foreground">AI Proof Systems Landscape</h3>
            <p className="text-sm text-muted-foreground">
              Compare approaches to AI-assisted theorem proving
            </p>
          </div>
        </div>
        <div className="flex items-center gap-2 text-blue-400">
          <span className="text-sm font-medium">
            {isExpanded ? 'Hide' : 'Show'} Comparison
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
        <div className="px-6 pb-6 border-t border-blue-500/10">
          <div className="mt-4 space-y-4">
            {/* Tool Cards */}
            <div className="grid gap-4 md:grid-cols-3">
              {RELATED_TOOLS.map((tool) => (
                <div
                  key={tool.name}
                  className="bg-card/50 border border-border rounded-lg p-4 flex flex-col"
                >
                  <div className="flex items-center gap-2 mb-2">
                    <div className="h-8 w-8 rounded-lg bg-muted flex items-center justify-center text-muted-foreground">
                      <IconComponent icon={tool.icon} />
                    </div>
                    <div className="flex-1">
                      <h4 className="font-semibold text-sm">{tool.name}</h4>
                    </div>
                    {tool.url !== '#' && (
                      <a
                        href={tool.url}
                        target="_blank"
                        rel="noopener noreferrer"
                        className="text-muted-foreground hover:text-foreground transition-colors"
                      >
                        <ExternalLink className="h-4 w-4" />
                      </a>
                    )}
                  </div>
                  <p className="text-xs text-muted-foreground mb-3">
                    {tool.description}
                  </p>
                  <div className="mb-3">
                    <span className="text-[10px] uppercase tracking-wide text-muted-foreground">
                      Approach
                    </span>
                    <p className="text-xs text-foreground/80 mt-0.5">
                      {tool.approach}
                    </p>
                  </div>
                  <div className="mt-auto">
                    <span className="text-[10px] uppercase tracking-wide text-muted-foreground">
                      Strengths
                    </span>
                    <ul className="mt-1 space-y-0.5">
                      {tool.strengths.map((strength, i) => (
                        <li key={i} className="text-xs text-muted-foreground flex items-start gap-1">
                          <span className="text-blue-400 mt-1">•</span>
                          <span>{strength}</span>
                        </li>
                      ))}
                    </ul>
                  </div>
                </div>
              ))}
            </div>

            {/* Differentiation Note */}
            <div className="bg-card/30 border border-border/50 rounded-lg p-4">
              <h4 className="text-sm font-semibold mb-2">Our Philosophy</h4>
              <p className="text-xs text-muted-foreground">
                While autonomous systems like Aristotle and AlphaProof excel at specific domains,
                we believe <strong>human oversight</strong> remains crucial for research-level mathematics.
                Our OODA loop approach keeps humans in control of strategic decisions while leveraging
                AI for tactical proof search. This transparency enables learning from both successes
                and failures.
              </p>
            </div>
          </div>
        </div>
      )}
    </div>
  )
}
