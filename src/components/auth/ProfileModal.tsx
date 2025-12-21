import { useState, useEffect } from 'react'
import { useAuth, getSessionToken } from '@/contexts/AuthContext'
import { Button } from '@/components/ui/button'
import {
  Dialog,
  DialogContent,
  DialogHeader,
  DialogTitle,
} from '@/components/ui/dialog'
import { cn } from '@/lib/utils'
import { User, Check, AlertCircle } from 'lucide-react'

interface ProfileModalProps {
  open: boolean
  onOpenChange: (open: boolean) => void
}

interface UsernameStatus {
  username: string
  displayName: string
  canChange: boolean
  nextChangeAt: number | null
}

export function ProfileModal({ open, onOpenChange }: ProfileModalProps) {
  const { user, refreshUser } = useAuth()
  const [usernameStatus, setUsernameStatus] = useState<UsernameStatus | null>(null)
  const [newUsername, setNewUsername] = useState('')
  const [isLoading, setIsLoading] = useState(false)
  const [isSaving, setIsSaving] = useState(false)
  const [error, setError] = useState<string | null>(null)
  const [success, setSuccess] = useState<string | null>(null)

  // Fetch username status when modal opens
  useEffect(() => {
    if (open && user) {
      fetchUsernameStatus()
    }
  }, [open, user])

  const fetchUsernameStatus = async () => {
    setIsLoading(true)
    setError(null)
    try {
      const token = getSessionToken()
      const response = await fetch('/api/users/me/username', {
        headers: { Authorization: `Bearer ${token}` },
      })
      if (response.ok) {
        const data = await response.json()
        setUsernameStatus(data)
        setNewUsername(data.username || '')
      }
    } catch (err) {
      setError('Failed to load profile')
    } finally {
      setIsLoading(false)
    }
  }

  const handleSave = async () => {
    if (!newUsername.trim() || newUsername === usernameStatus?.username) return

    setIsSaving(true)
    setError(null)
    setSuccess(null)

    try {
      const token = getSessionToken()
      const response = await fetch('/api/users/me/username', {
        method: 'PUT',
        headers: {
          'Content-Type': 'application/json',
          Authorization: `Bearer ${token}`,
        },
        body: JSON.stringify({ username: newUsername.trim() }),
      })

      const data = await response.json()

      if (!response.ok) {
        setError(data.error || 'Failed to update username')
        return
      }

      setSuccess('Username updated successfully!')
      setUsernameStatus((prev) => prev ? {
        ...prev,
        username: data.username,
        displayName: data.username,
        canChange: false,
        nextChangeAt: data.nextChangeAt,
      } : null)

      // Refresh user in auth context
      await refreshUser()
    } catch (err) {
      setError('An unexpected error occurred')
    } finally {
      setIsSaving(false)
    }
  }

  const formatDate = (timestamp: number) => {
    return new Date(timestamp).toLocaleDateString('en-US', {
      year: 'numeric',
      month: 'long',
      day: 'numeric',
    })
  }

  const isValidUsername = (username: string) => {
    return /^[a-zA-Z][a-zA-Z0-9_]{2,19}$/.test(username)
  }

  const hasChanges = newUsername !== usernameStatus?.username
  const canSave = hasChanges && isValidUsername(newUsername) && usernameStatus?.canChange

  return (
    <Dialog open={open} onOpenChange={onOpenChange}>
      <DialogContent className="sm:max-w-md">
        <DialogHeader>
          <DialogTitle className="flex items-center gap-2">
            <User className="h-5 w-5" />
            Profile Settings
          </DialogTitle>
        </DialogHeader>

        {isLoading ? (
          <div className="py-8 text-center text-muted-foreground">
            Loading...
          </div>
        ) : (
          <div className="space-y-6 mt-4">
            {/* Email (read-only) */}
            <div>
              <label className="text-sm font-medium text-muted-foreground">
                Email
              </label>
              <p className="mt-1 text-sm">{user?.email}</p>
            </div>

            {/* Username */}
            <div>
              <label htmlFor="username" className="text-sm font-medium">
                Username
              </label>
              <input
                id="username"
                type="text"
                value={newUsername}
                onChange={(e) => {
                  setNewUsername(e.target.value)
                  setError(null)
                  setSuccess(null)
                }}
                disabled={!usernameStatus?.canChange}
                className={cn(
                  'mt-1 w-full px-3 py-2 rounded-md border border-border',
                  'bg-background text-foreground',
                  'focus:outline-none focus:ring-2 focus:ring-annotation',
                  'disabled:opacity-50 disabled:cursor-not-allowed'
                )}
                placeholder="your_username"
                minLength={3}
                maxLength={20}
              />
              <p className="text-xs text-muted-foreground mt-1">
                3-20 characters, starts with letter, letters/numbers/underscores only
              </p>

              {/* Cooldown message */}
              {usernameStatus && !usernameStatus.canChange && usernameStatus.nextChangeAt && (
                <p className="text-xs text-amber-500 mt-2">
                  You can change your username again on {formatDate(usernameStatus.nextChangeAt)}
                </p>
              )}
            </div>

            {/* Error message */}
            {error && (
              <div className="flex items-center gap-2 text-sm text-red-400 bg-red-500/10 px-3 py-2 rounded-md">
                <AlertCircle className="h-4 w-4 shrink-0" />
                {error}
              </div>
            )}

            {/* Success message */}
            {success && (
              <div className="flex items-center gap-2 text-sm text-green-400 bg-green-500/10 px-3 py-2 rounded-md">
                <Check className="h-4 w-4 shrink-0" />
                {success}
              </div>
            )}

            {/* Save button */}
            <div className="flex justify-end gap-2">
              <Button
                variant="ghost"
                onClick={() => onOpenChange(false)}
              >
                Close
              </Button>
              <Button
                onClick={handleSave}
                disabled={!canSave || isSaving}
              >
                {isSaving ? 'Saving...' : 'Save Changes'}
              </Button>
            </div>
          </div>
        )}
      </DialogContent>
    </Dialog>
  )
}
