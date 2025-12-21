import { useState } from 'react'
import { useAuth } from '@/contexts/AuthContext'
import { Button } from '@/components/ui/button'
import {
  Dialog,
  DialogContent,
  DialogHeader,
  DialogTitle,
} from '@/components/ui/dialog'
import { cn } from '@/lib/utils'

interface AuthModalProps {
  open: boolean
  onOpenChange: (open: boolean) => void
}

export function AuthModal({ open, onOpenChange }: AuthModalProps) {
  const { login, register } = useAuth()
  const [mode, setMode] = useState<'login' | 'register'>('login')
  const [email, setEmail] = useState('')
  const [password, setPassword] = useState('')
  const [username, setUsername] = useState('')
  const [error, setError] = useState<string | null>(null)
  const [isSubmitting, setIsSubmitting] = useState(false)

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault()
    setError(null)
    setIsSubmitting(true)

    try {
      const result = mode === 'login'
        ? await login(email, password)
        : await register(email, password, username)

      if (result.success) {
        onOpenChange(false)
        setEmail('')
        setPassword('')
        setUsername('')
      } else {
        setError(result.error || 'An error occurred')
      }
    } finally {
      setIsSubmitting(false)
    }
  }

  const switchMode = () => {
    setMode((m) => (m === 'login' ? 'register' : 'login'))
    setError(null)
  }

  return (
    <Dialog open={open} onOpenChange={onOpenChange}>
      <DialogContent className="sm:max-w-md">
        <DialogHeader>
          <DialogTitle>
            {mode === 'login' ? 'Sign in to LeanGenius' : 'Create an account'}
          </DialogTitle>
        </DialogHeader>

        <form onSubmit={handleSubmit} className="space-y-4 mt-4">
          {mode === 'register' && (
            <div>
              <label htmlFor="username" className="text-sm font-medium">
                Username
              </label>
              <input
                id="username"
                type="text"
                value={username}
                onChange={(e) => setUsername(e.target.value)}
                className={cn(
                  'mt-1 w-full px-3 py-2 rounded-md border border-border',
                  'bg-background text-foreground',
                  'focus:outline-none focus:ring-2 focus:ring-annotation'
                )}
                placeholder="your_username"
                required
                minLength={3}
                maxLength={20}
                pattern="^[a-zA-Z][a-zA-Z0-9_]{2,19}$"
              />
              <p className="text-xs text-muted-foreground mt-1">
                3-20 characters, starts with letter, letters/numbers/underscores only
              </p>
            </div>
          )}

          <div>
            <label htmlFor="email" className="text-sm font-medium">
              Email
            </label>
            <input
              id="email"
              type="email"
              value={email}
              onChange={(e) => setEmail(e.target.value)}
              className={cn(
                'mt-1 w-full px-3 py-2 rounded-md border border-border',
                'bg-background text-foreground',
                'focus:outline-none focus:ring-2 focus:ring-annotation'
              )}
              placeholder="you@example.com"
              required
            />
          </div>

          <div>
            <label htmlFor="password" className="text-sm font-medium">
              Password
            </label>
            <input
              id="password"
              type="password"
              value={password}
              onChange={(e) => setPassword(e.target.value)}
              className={cn(
                'mt-1 w-full px-3 py-2 rounded-md border border-border',
                'bg-background text-foreground',
                'focus:outline-none focus:ring-2 focus:ring-annotation'
              )}
              placeholder={mode === 'register' ? 'At least 8 characters' : 'Your password'}
              required
              minLength={mode === 'register' ? 8 : 1}
            />
          </div>

          {error && (
            <div className="text-sm text-red-400 bg-red-500/10 px-3 py-2 rounded-md">
              {error}
            </div>
          )}

          <Button
            type="submit"
            className="w-full"
            disabled={isSubmitting}
          >
            {isSubmitting
              ? 'Please wait...'
              : mode === 'login'
                ? 'Sign in'
                : 'Create account'}
          </Button>

          <p className="text-sm text-center text-muted-foreground">
            {mode === 'login' ? (
              <>
                Don't have an account?{' '}
                <button
                  type="button"
                  onClick={switchMode}
                  className="text-annotation hover:underline"
                >
                  Sign up
                </button>
              </>
            ) : (
              <>
                Already have an account?{' '}
                <button
                  type="button"
                  onClick={switchMode}
                  className="text-annotation hover:underline"
                >
                  Sign in
                </button>
              </>
            )}
          </p>
        </form>
      </DialogContent>
    </Dialog>
  )
}
