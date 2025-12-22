import { useState } from 'react'
import { Link, useNavigate } from 'react-router-dom'
import { useAuth, getSessionToken } from '@/contexts/AuthContext'
import { Button } from '@/components/ui/button'
import { cn } from '@/lib/utils'
import { ArrowLeft, Send, CheckCircle, AlertCircle } from 'lucide-react'

export function SubmitPage() {
  const { isAuthenticated, isLoading } = useAuth()
  const navigate = useNavigate()

  const [title, setTitle] = useState('')
  const [description, setDescription] = useState('')
  const [leanSource, setLeanSource] = useState('')
  const [mathlibVersion, setMathlibVersion] = useState('')
  const [githubUrl, setGithubUrl] = useState('')
  const [additionalNotes, setAdditionalNotes] = useState('')

  const [isSubmitting, setIsSubmitting] = useState(false)
  const [error, setError] = useState<string | null>(null)
  const [success, setSuccess] = useState(false)

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault()
    setError(null)
    setIsSubmitting(true)

    try {
      const sessionToken = getSessionToken()
      const response = await fetch('/api/submissions/create', {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          Authorization: `Bearer ${sessionToken}`,
        },
        body: JSON.stringify({
          title,
          description,
          leanSource,
          mathlibVersion: mathlibVersion || undefined,
          githubUrl: githubUrl || undefined,
          additionalNotes: additionalNotes || undefined,
        }),
      })

      const data = await response.json()

      if (!response.ok) {
        setError(data.details || data.error || 'Submission failed')
        return
      }

      setSuccess(true)
    } catch (err) {
      console.error('Submission error:', err)
      setError('An unexpected error occurred')
    } finally {
      setIsSubmitting(false)
    }
  }

  // Loading state
  if (isLoading) {
    return (
      <div className="min-h-screen bg-background flex items-center justify-center">
        <div className="text-muted-foreground">Loading...</div>
      </div>
    )
  }

  // Not authenticated
  if (!isAuthenticated) {
    return (
      <div className="min-h-screen bg-background">
        <Header />
        <div className="max-w-2xl mx-auto px-6 py-16 text-center">
          <AlertCircle className="h-12 w-12 text-muted-foreground mx-auto mb-4" />
          <h1 className="text-2xl font-bold mb-2">Sign in required</h1>
          <p className="text-muted-foreground mb-6">
            You need to be signed in to submit a proof.
          </p>
          <Button onClick={() => navigate('/')}>
            Go to homepage
          </Button>
        </div>
      </div>
    )
  }

  // Success state
  if (success) {
    return (
      <div className="min-h-screen bg-background">
        <Header />
        <div className="max-w-2xl mx-auto px-6 py-16 text-center">
          <CheckCircle className="h-12 w-12 text-green-400 mx-auto mb-4" />
          <h1 className="text-2xl font-bold mb-2">Proof submitted!</h1>
          <p className="text-muted-foreground mb-6">
            Thank you for your submission. We'll review it and get back to you via email.
          </p>
          <div className="flex gap-4 justify-center">
            <Button variant="outline" onClick={() => {
              setSuccess(false)
              setTitle('')
              setDescription('')
              setLeanSource('')
              setMathlibVersion('')
              setGithubUrl('')
              setAdditionalNotes('')
            }}>
              Submit another
            </Button>
            <Button onClick={() => navigate('/')}>
              Back to proofs
            </Button>
          </div>
        </div>
      </div>
    )
  }

  return (
    <div className="min-h-screen bg-background">
      <Header />

      <div className="max-w-2xl mx-auto px-6 py-8">
        <h1 className="text-3xl font-bold mb-2">Submit a Proof</h1>
        <p className="text-muted-foreground mb-8">
          Share a Lean 4 proof with the community. We'll review your submission,
          run it through our analysis pipeline, and add annotations before publishing.
        </p>

        <form onSubmit={handleSubmit} className="space-y-6">
          {/* Title */}
          <div>
            <label htmlFor="title" className="block text-sm font-medium mb-1">
              Proof Title <span className="text-red-400">*</span>
            </label>
            <input
              id="title"
              type="text"
              value={title}
              onChange={(e) => setTitle(e.target.value)}
              className={cn(
                'w-full px-3 py-2 rounded-md border border-border',
                'bg-background text-foreground',
                'focus:outline-none focus:ring-2 focus:ring-annotation'
              )}
              placeholder="e.g., Irrationality of the square root of 3"
              required
              maxLength={200}
            />
          </div>

          {/* Description */}
          <div>
            <label htmlFor="description" className="block text-sm font-medium mb-1">
              Description <span className="text-red-400">*</span>
            </label>
            <textarea
              id="description"
              value={description}
              onChange={(e) => setDescription(e.target.value)}
              rows={4}
              className={cn(
                'w-full px-3 py-2 rounded-md border border-border',
                'bg-background text-foreground resize-y',
                'focus:outline-none focus:ring-2 focus:ring-annotation'
              )}
              placeholder="Describe what this proof demonstrates and why it's interesting..."
              required
              minLength={10}
              maxLength={5000}
            />
            <p className="text-xs text-muted-foreground mt-1">
              Include mathematical context, significance, and any interesting aspects of the formalization.
            </p>
          </div>

          {/* Lean Source */}
          <div>
            <label htmlFor="leanSource" className="block text-sm font-medium mb-1">
              Lean 4 Source Code <span className="text-red-400">*</span>
            </label>
            <textarea
              id="leanSource"
              value={leanSource}
              onChange={(e) => setLeanSource(e.target.value)}
              rows={12}
              className={cn(
                'w-full px-3 py-2 rounded-md border border-border font-mono text-sm',
                'bg-background text-foreground resize-y',
                'focus:outline-none focus:ring-2 focus:ring-annotation'
              )}
              placeholder={`import Mathlib.Data.Real.Irrational

theorem sqrt3_irrational : Irrational (Real.sqrt 3) := by
  ...`}
              required
              minLength={10}
              maxLength={100000}
            />
            <p className="text-xs text-muted-foreground mt-1">
              Paste your complete Lean 4 source code including imports.
            </p>
          </div>

          {/* Mathlib Version */}
          <div>
            <label htmlFor="mathlibVersion" className="block text-sm font-medium mb-1">
              Mathlib Version
            </label>
            <input
              id="mathlibVersion"
              type="text"
              value={mathlibVersion}
              onChange={(e) => setMathlibVersion(e.target.value)}
              className={cn(
                'w-full px-3 py-2 rounded-md border border-border',
                'bg-background text-foreground',
                'focus:outline-none focus:ring-2 focus:ring-annotation'
              )}
              placeholder="e.g., v4.14.0 or leanprover-community/mathlib4@abc1234"
              maxLength={50}
            />
            <p className="text-xs text-muted-foreground mt-1">
              The version of Mathlib your proof compiles against.
            </p>
          </div>

          {/* GitHub URL */}
          <div>
            <label htmlFor="githubUrl" className="block text-sm font-medium mb-1">
              GitHub Repository
            </label>
            <input
              id="githubUrl"
              type="url"
              value={githubUrl}
              onChange={(e) => setGithubUrl(e.target.value)}
              className={cn(
                'w-full px-3 py-2 rounded-md border border-border',
                'bg-background text-foreground',
                'focus:outline-none focus:ring-2 focus:ring-annotation'
              )}
              placeholder="https://github.com/username/repo"
            />
            <p className="text-xs text-muted-foreground mt-1">
              Link to your repository if the proof is already hosted.
            </p>
          </div>

          {/* Additional Notes */}
          <div>
            <label htmlFor="additionalNotes" className="block text-sm font-medium mb-1">
              Additional Notes
            </label>
            <textarea
              id="additionalNotes"
              value={additionalNotes}
              onChange={(e) => setAdditionalNotes(e.target.value)}
              rows={3}
              className={cn(
                'w-full px-3 py-2 rounded-md border border-border',
                'bg-background text-foreground resize-y',
                'focus:outline-none focus:ring-2 focus:ring-annotation'
              )}
              placeholder="Any other context, references, or notes..."
              maxLength={5000}
            />
          </div>

          {/* Error */}
          {error && (
            <div className="text-sm text-red-400 bg-red-500/10 px-4 py-3 rounded-md flex items-start gap-2">
              <AlertCircle className="h-4 w-4 mt-0.5 shrink-0" />
              {error}
            </div>
          )}

          {/* Submit Button */}
          <div className="flex gap-4 pt-4">
            <Button
              type="button"
              variant="outline"
              onClick={() => navigate('/')}
            >
              Cancel
            </Button>
            <Button
              type="submit"
              disabled={isSubmitting}
              className="flex-1"
            >
              {isSubmitting ? (
                'Submitting...'
              ) : (
                <>
                  <Send className="h-4 w-4" />
                  Submit Proof
                </>
              )}
            </Button>
          </div>
        </form>
      </div>
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
