import { Component, type ReactNode } from 'react'
import { Link } from 'react-router-dom'

interface Props {
  children: ReactNode
  fallback?: ReactNode
}

interface State {
  hasError: boolean
  error: Error | null
}

/**
 * Error boundary component that catches JavaScript errors in child components.
 * Displays a fallback UI instead of crashing the whole app.
 */
export class ErrorBoundary extends Component<Props, State> {
  constructor(props: Props) {
    super(props)
    this.state = { hasError: false, error: null }
  }

  static getDerivedStateFromError(error: Error): State {
    return { hasError: true, error }
  }

  componentDidCatch(error: Error, errorInfo: React.ErrorInfo) {
    console.error('ErrorBoundary caught an error:', error, errorInfo)
  }

  render() {
    if (this.state.hasError) {
      if (this.props.fallback) {
        return this.props.fallback
      }

      return (
        <div className="h-screen flex flex-col items-center justify-center gap-4 p-8">
          <div className="text-center max-w-md">
            <h1 className="text-2xl font-bold mb-2 text-red-400">Something went wrong</h1>
            <p className="text-muted-foreground mb-4">
              An error occurred while rendering this page.
            </p>
            {this.state.error && (
              <pre className="text-left text-xs bg-muted p-4 rounded-lg overflow-auto max-h-48 mb-4">
                {this.state.error.message}
              </pre>
            )}
            <Link to="/" className="text-annotation hover:underline">
              ← Back to home
            </Link>
          </div>
        </div>
      )
    }

    return this.props.children
  }
}
