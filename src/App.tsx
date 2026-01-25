import { lazy, Suspense } from 'react'
import { BrowserRouter, Routes, Route } from 'react-router-dom'
import { AuthProvider } from '@/contexts/AuthContext'
import { ErrorBoundary } from '@/components/ErrorBoundary'

// Lazy load pages for code splitting
const HomePage = lazy(() => import('@/pages/HomePage').then(m => ({ default: m.HomePage })))
const ProofPage = lazy(() => import('@/pages/ProofPage').then(m => ({ default: m.ProofPage })))
const ResearchPage = lazy(() => import('@/pages/ResearchPage').then(m => ({ default: m.ResearchPage })))
const ResearchProblemPage = lazy(() => import('@/pages/ResearchProblemPage').then(m => ({ default: m.ResearchProblemPage })))
const SubmitPage = lazy(() => import('@/pages/SubmitPage').then(m => ({ default: m.SubmitPage })))
const AboutPage = lazy(() => import('@/pages/AboutPage').then(m => ({ default: m.AboutPage })))
const ErdosPage = lazy(() => import('@/pages/ErdosPage').then(m => ({ default: m.ErdosPage })))

function LoadingSpinner() {
  return (
    <div className="min-h-screen flex items-center justify-center">
      <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-annotation" />
    </div>
  )
}

function App() {
  return (
    <ErrorBoundary>
      <AuthProvider>
        <BrowserRouter>
          <Suspense fallback={<LoadingSpinner />}>
            <Routes>
              <Route path="/" element={<HomePage />} />
              <Route path="/proof/:slug" element={<ProofPage />} />
              <Route path="/research" element={<ResearchPage />} />
              <Route path="/research/:slug" element={<ResearchProblemPage />} />
              <Route path="/submit" element={<SubmitPage />} />
              <Route path="/about" element={<AboutPage />} />
              <Route path="/erdos" element={<ErdosPage />} />
            </Routes>
          </Suspense>
        </BrowserRouter>
      </AuthProvider>
    </ErrorBoundary>
  )
}

export default App
