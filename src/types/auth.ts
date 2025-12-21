export interface User {
  id: string
  email: string
  username: string
  createdAt: number
  lastLogin?: number
}

export interface AuthState {
  user: User | null
  isAuthenticated: boolean
  isLoading: boolean
}
