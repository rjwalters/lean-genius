import { createContext, useContext, useState, useEffect, useCallback, type ReactNode } from 'react'
import type { AuthState } from '@/types/auth'

const SESSION_KEY = 'leangenius_session_token'

function readSessionToken(): string | null {
  try {
    return localStorage.getItem(SESSION_KEY)
  } catch {
    return null
  }
}

function writeSessionToken(token: string) {
  try {
    localStorage.setItem(SESSION_KEY, token)
  } catch (error) {
    console.warn('Unable to persist session token:', error)
  }
}

function clearSessionToken() {
  try {
    localStorage.removeItem(SESSION_KEY)
  } catch (error) {
    console.warn('Unable to clear session token:', error)
  }
}

interface AuthContextType extends AuthState {
  login: (email: string, password: string) => Promise<{ success: boolean; error?: string }>
  loginWithGoogle: () => void
  register: (email: string, password: string, username: string) => Promise<{ success: boolean; error?: string }>
  logout: () => Promise<void>
  refreshUser: () => Promise<void>
}

const AuthContext = createContext<AuthContextType | undefined>(undefined)

export function AuthProvider({ children }: { children: ReactNode }) {
  const [state, setState] = useState<AuthState>({
    user: null,
    isAuthenticated: false,
    isLoading: true,
  })

  // Check session on mount and handle OAuth callback
  useEffect(() => {
    const checkSession = async () => {
      // Check for OAuth callback token in URL
      const urlParams = new URLSearchParams(window.location.search)
      const oauthToken = urlParams.get('oauth_token')
      const authError = urlParams.get('auth_error')

      // Clear URL params without triggering navigation
      if (oauthToken || authError) {
        const newUrl = window.location.pathname
        window.history.replaceState({}, '', newUrl)
      }

      // Handle OAuth error
      if (authError) {
        console.error('OAuth error:', authError)
        setState({ user: null, isAuthenticated: false, isLoading: false })
        return
      }

      // Use OAuth token if present, otherwise check localStorage
      const sessionToken = oauthToken || readSessionToken()

      if (!sessionToken) {
        setState({ user: null, isAuthenticated: false, isLoading: false })
        return
      }

      // Store the OAuth token if we got one
      if (oauthToken) {
        writeSessionToken(oauthToken)
      }

      try {
        const response = await fetch('/api/auth/me', {
          headers: { Authorization: `Bearer ${sessionToken}` },
        })

        if (response.ok) {
          const data = await response.json()
          setState({
            user: data.user,
            isAuthenticated: true,
            isLoading: false,
          })
        } else {
          // Invalid/expired session
          clearSessionToken()
          setState({ user: null, isAuthenticated: false, isLoading: false })
        }
      } catch (error) {
        console.error('Session check failed:', error)
        clearSessionToken()
        setState({ user: null, isAuthenticated: false, isLoading: false })
      }
    }

    checkSession()
  }, [])

  const loginWithGoogle = useCallback(() => {
    // Redirect to Google OAuth endpoint
    window.location.href = '/api/auth/google/login'
  }, [])

  const login = useCallback(async (email: string, password: string) => {
    try {
      const response = await fetch('/api/auth/login', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ email, password }),
      })

      const data = await response.json()

      if (!response.ok) {
        return {
          success: false,
          error: data.details || data.error || 'Login failed',
        }
      }

      writeSessionToken(data.session_token)
      setState({
        user: data.user,
        isAuthenticated: true,
        isLoading: false,
      })

      return { success: true }
    } catch (error) {
      console.error('Login failed:', error)
      return {
        success: false,
        error: 'An unexpected error occurred',
      }
    }
  }, [])

  const register = useCallback(async (email: string, password: string, username: string) => {
    try {
      const response = await fetch('/api/auth/register', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ email, password, username }),
      })

      const data = await response.json()

      if (!response.ok) {
        return {
          success: false,
          error: data.details || data.error || 'Registration failed',
        }
      }

      writeSessionToken(data.session_token)
      setState({
        user: data.user,
        isAuthenticated: true,
        isLoading: false,
      })

      return { success: true }
    } catch (error) {
      console.error('Registration failed:', error)
      return {
        success: false,
        error: 'An unexpected error occurred',
      }
    }
  }, [])

  const logout = useCallback(async () => {
    const sessionToken = readSessionToken()

    if (sessionToken) {
      try {
        await fetch('/api/auth/logout', {
          method: 'POST',
          headers: { Authorization: `Bearer ${sessionToken}` },
        })
      } catch (error) {
        console.error('Logout API call failed:', error)
      }
    }

    clearSessionToken()
    setState({ user: null, isAuthenticated: false, isLoading: false })
  }, [])

  const refreshUser = useCallback(async () => {
    const sessionToken = readSessionToken()

    if (!sessionToken) return

    try {
      const response = await fetch('/api/auth/me', {
        headers: { Authorization: `Bearer ${sessionToken}` },
      })

      if (response.ok) {
        const data = await response.json()
        setState((prev) => ({ ...prev, user: data.user }))
      }
    } catch (error) {
      console.error('Failed to refresh user:', error)
    }
  }, [])

  return (
    <AuthContext.Provider
      value={{
        ...state,
        login,
        loginWithGoogle,
        register,
        logout,
        refreshUser,
      }}
    >
      {children}
    </AuthContext.Provider>
  )
}

export function useAuth() {
  const context = useContext(AuthContext)
  if (context === undefined) {
    throw new Error('useAuth must be used within an AuthProvider')
  }
  return context
}

// Helper to get session token for API calls
export function getSessionToken(): string | null {
  return readSessionToken()
}
