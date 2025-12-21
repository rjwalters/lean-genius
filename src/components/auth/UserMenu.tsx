import { useState } from 'react'
import { useAuth } from '@/contexts/AuthContext'
import { Button } from '@/components/ui/button'
import { AuthModal } from './AuthModal'
import { ProfileModal } from './ProfileModal'
import { User, LogOut, Settings } from 'lucide-react'

export function UserMenu() {
  const { user, isAuthenticated, isLoading, logout } = useAuth()
  const [authModalOpen, setAuthModalOpen] = useState(false)
  const [profileModalOpen, setProfileModalOpen] = useState(false)

  if (isLoading) {
    return (
      <div className="w-8 h-8 rounded-full bg-muted animate-pulse" />
    )
  }

  if (!isAuthenticated) {
    return (
      <>
        <Button
          variant="ghost"
          size="sm"
          onClick={() => setAuthModalOpen(true)}
          className="gap-2"
        >
          <User className="h-4 w-4" />
          <span className="hidden sm:inline">Sign in</span>
        </Button>
        <AuthModal open={authModalOpen} onOpenChange={setAuthModalOpen} />
      </>
    )
  }

  return (
    <>
      <div className="flex items-center gap-2">
        <span className="text-sm text-muted-foreground hidden sm:inline">
          {user?.username}
        </span>
        <Button
          variant="ghost"
          size="icon"
          onClick={() => setProfileModalOpen(true)}
          title="Profile settings"
        >
          <Settings className="h-4 w-4" />
        </Button>
        <Button
          variant="ghost"
          size="icon"
          onClick={() => logout()}
          title="Sign out"
        >
          <LogOut className="h-4 w-4" />
        </Button>
      </div>
      <ProfileModal open={profileModalOpen} onOpenChange={setProfileModalOpen} />
    </>
  )
}
