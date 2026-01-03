import { Link } from 'react-router-dom'
import { ArrowLeft, Github, BookOpen, Target, Users, Sparkles } from 'lucide-react'
import { Footer } from '@/components/Footer'

export function AboutPage() {
  return (
    <div className="min-h-screen bg-background">
      <Header />

      {/* Hero */}
      <section className="max-w-4xl mx-auto px-6 py-16">
        <h1 className="text-4xl md:text-5xl font-bold mb-4">
          About <span className="text-annotation">LeanGenius</span>
        </h1>
        <p className="text-xl text-muted-foreground">
          Making formalized mathematics accessible to everyone.
        </p>
      </section>

      {/* Mission */}
      <section className="max-w-4xl mx-auto px-6 pb-12">
        <div className="bg-card border border-border rounded-xl p-8">
          <div className="flex items-center gap-3 mb-4">
            <div className="h-10 w-10 rounded-lg bg-annotation/20 flex items-center justify-center">
              <Target className="h-5 w-5 text-annotation" />
            </div>
            <h2 className="text-2xl font-semibold">Our Mission</h2>
          </div>
          <p className="text-muted-foreground leading-relaxed">
            LeanGenius bridges the gap between formal mathematics and human understanding.
            We take machine-verified proofs written in Lean 4 and enrich them with
            annotations, historical context, and step-by-step explanations that make
            the underlying mathematics accessible to students, educators, and curious minds.
          </p>
        </div>
      </section>

      {/* Goals */}
      <section className="max-w-4xl mx-auto px-6 pb-12">
        <h2 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-6">
          Project Goals
        </h2>
        <div className="grid gap-6 md:grid-cols-2">
          <GoalCard
            icon={BookOpen}
            title="Educational Accessibility"
            description="Transform dense formal proofs into learning experiences with rich annotations explaining each step, tactic, and mathematical concept."
          />
          <GoalCard
            icon={Sparkles}
            title="Proof Exploration"
            description="Provide an interactive environment where users can explore proof structure, understand dependencies, and see how theorems connect."
          />
          <GoalCard
            icon={Users}
            title="Community Contributions"
            description="Enable mathematicians and Lean enthusiasts to submit their own formalized proofs and contribute annotations to existing ones."
          />
          <GoalCard
            icon={Target}
            title="Verification Transparency"
            description="Showcase the power of formal verification by making it clear how each proof has been machine-checked for correctness."
          />
        </div>
      </section>

      {/* GitHub Repositories */}
      <section className="max-w-4xl mx-auto px-6 pb-16">
        <h2 className="text-sm font-semibold uppercase tracking-wide text-muted-foreground mb-6">
          Open Source
        </h2>
        <RepoCard
            name="lean-genius"
            description="The complete monorepo containing the web application, Lean 4 proofs with Mathlib, and all verified theorems. Built with React, TypeScript, and Cloudflare Workers."
            url="https://github.com/rjwalters/lean-genius"
          />
      </section>

      <Footer />
    </div>
  )
}

function Header() {
  return (
    <header className="border-b border-border">
      <div className="max-w-6xl mx-auto px-6 py-4 flex items-center gap-4">
        <Link
          to="/"
          className="flex items-center gap-2 text-muted-foreground hover:text-foreground transition-colors"
        >
          <ArrowLeft className="h-4 w-4" />
          <span className="text-2xl font-bold tracking-tight">
            Lean<span className="text-annotation">Genius</span>
          </span>
        </Link>
      </div>
    </header>
  )
}

function GoalCard({
  icon: Icon,
  title,
  description,
}: {
  icon: React.ComponentType<{ className?: string }>
  title: string
  description: string
}) {
  return (
    <div className="bg-card border border-border rounded-xl p-6">
      <div className="flex items-center gap-3 mb-3">
        <div className="h-8 w-8 rounded-lg bg-annotation/20 flex items-center justify-center">
          <Icon className="h-4 w-4 text-annotation" />
        </div>
        <h3 className="font-semibold">{title}</h3>
      </div>
      <p className="text-sm text-muted-foreground leading-relaxed">{description}</p>
    </div>
  )
}

function RepoCard({
  name,
  description,
  url,
}: {
  name: string
  description: string
  url: string
}) {
  return (
    <a
      href={url}
      target="_blank"
      rel="noopener noreferrer"
      className="group block bg-card border border-border rounded-xl p-6 hover:border-annotation/50 hover:bg-card/80 transition-all"
    >
      <div className="flex items-center gap-3 mb-3">
        <div className="h-10 w-10 rounded-lg bg-muted flex items-center justify-center">
          <Github className="h-5 w-5 text-foreground" />
        </div>
        <div>
          <h3 className="font-semibold group-hover:text-annotation transition-colors">
            {name}
          </h3>
          <span className="text-xs text-muted-foreground">github.com/rjwalters</span>
        </div>
      </div>
      <p className="text-sm text-muted-foreground leading-relaxed">{description}</p>
    </a>
  )
}
