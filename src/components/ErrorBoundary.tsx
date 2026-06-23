import { Component, type ReactNode } from 'react'

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

  private isChunkLoadError(): boolean {
    const msg = this.state.error?.message || ''
    return (
      msg.includes('dynamically imported module') ||
      msg.includes('Failed to fetch') ||
      msg.includes('Loading chunk') ||
      msg.includes('Loading CSS chunk')
    )
  }

  render() {
    if (this.state.hasError) {
      if (this.props.fallback) {
        return this.props.fallback
      }

      const isChunkError = this.isChunkLoadError()

      return (
        <div className="h-screen flex flex-col items-center justify-center gap-4 p-8">
          <div className="text-center max-w-md" role="alert" aria-live="assertive">
            <h1 className="text-2xl font-bold mb-2 text-red-400">
              {isChunkError ? 'Page update available' : 'Something went wrong'}
            </h1>
            <p className="text-muted-foreground mb-4">
              {isChunkError
                ? 'The site was recently updated. Reload to get the latest version.'
                : 'An error occurred while rendering this page.'}
            </p>
            {isChunkError ? (
              <button
                type="button"
                onClick={() => window.location.reload()}
                className="inline-flex items-center gap-2 px-4 py-2 bg-annotation text-white rounded-lg hover:opacity-90 transition-opacity mb-4"
              >
                Reload page
              </button>
            ) : (
              this.state.error && (
                <pre className="text-left text-xs bg-muted p-4 rounded-lg overflow-auto max-h-48 mb-4">
                  {this.state.error.message}
                </pre>
              )
            )}
            <div>
              <a href="/" className="text-annotation hover:underline">
                ← Back to home
              </a>
            </div>
          </div>
        </div>
      )
    }

    return this.props.children
  }
}
