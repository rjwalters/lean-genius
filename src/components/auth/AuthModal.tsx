import { useState } from 'react'
import { useAuth } from '@/contexts/AuthContext'
import { Button } from '@/components/ui/button'
import {
  Dialog,
  DialogContent,
  DialogHeader,
  DialogTitle,
  DialogDescription,
} from '@/components/ui/dialog'
import { cn } from '@/lib/utils'

interface AuthModalProps {
  open: boolean
  onOpenChange: (open: boolean) => void
}

export function AuthModal({ open, onOpenChange }: AuthModalProps) {
  const { login, loginWithGoogle, register } = useAuth()
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
          <DialogDescription>
            {mode === 'login'
              ? 'Sign in to save your progress and join the discussion.'
              : 'Create an account to save your progress and join the discussion.'}
          </DialogDescription>
        </DialogHeader>

        <div className="mt-4">
          <Button
            type="button"
            variant="outline"
            className="w-full flex items-center justify-center gap-2"
            onClick={loginWithGoogle}
          >
            <svg className="h-5 w-5" viewBox="0 0 24 24">
              <path
                fill="currentColor"
                d="M22.56 12.25c0-.78-.07-1.53-.2-2.25H12v4.26h5.92c-.26 1.37-1.04 2.53-2.21 3.31v2.77h3.57c2.08-1.92 3.28-4.74 3.28-8.09z"
              />
              <path
                fill="currentColor"
                d="M12 23c2.97 0 5.46-.98 7.28-2.66l-3.57-2.77c-.98.66-2.23 1.06-3.71 1.06-2.86 0-5.29-1.93-6.16-4.53H2.18v2.84C3.99 20.53 7.7 23 12 23z"
              />
              <path
                fill="currentColor"
                d="M5.84 14.09c-.22-.66-.35-1.36-.35-2.09s.13-1.43.35-2.09V7.07H2.18C1.43 8.55 1 10.22 1 12s.43 3.45 1.18 4.93l2.85-2.22.81-.62z"
              />
              <path
                fill="currentColor"
                d="M12 5.38c1.62 0 3.06.56 4.21 1.64l3.15-3.15C17.45 2.09 14.97 1 12 1 7.7 1 3.99 3.47 2.18 7.07l3.66 2.84c.87-2.6 3.3-4.53 6.16-4.53z"
              />
            </svg>
            Continue with Google
          </Button>

          <div className="relative my-4">
            <div className="absolute inset-0 flex items-center">
              <div className="w-full border-t border-border" />
            </div>
            <div className="relative flex justify-center text-xs uppercase">
              <span className="bg-background px-2 text-muted-foreground">
                Or continue with email
              </span>
            </div>
          </div>
        </div>

        <form onSubmit={handleSubmit} className="space-y-4">
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
