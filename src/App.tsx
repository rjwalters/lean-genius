import { Suspense } from 'react'
import { BrowserRouter, Routes, Route } from 'react-router-dom'
import { AuthProvider } from '@/contexts/AuthContext'
import { ErrorBoundary } from '@/components/ErrorBoundary'
import { lazyWithRetry } from '@/utils/lazyWithRetry'
import { LoadingScreen } from '@/components/LoadingScreen'

// Lazy load pages with auto-reload on stale chunk errors
const HomePage = lazyWithRetry(() => import('@/pages/HomePage').then(m => ({ default: m.HomePage })))
const ProofPage = lazyWithRetry(() => import('@/pages/ProofPage').then(m => ({ default: m.ProofPage })))
const ResearchPage = lazyWithRetry(() => import('@/pages/ResearchPage').then(m => ({ default: m.ResearchPage })))
const ResearchProblemPage = lazyWithRetry(() => import('@/pages/ResearchProblemPage').then(m => ({ default: m.ResearchProblemPage })))
const SubmitPage = lazyWithRetry(() => import('@/pages/SubmitPage').then(m => ({ default: m.SubmitPage })))
const AboutPage = lazyWithRetry(() => import('@/pages/AboutPage').then(m => ({ default: m.AboutPage })))
const ErdosPage = lazyWithRetry(() => import('@/pages/ErdosPage').then(m => ({ default: m.ErdosPage })))

function App() {
  return (
    <ErrorBoundary>
      <AuthProvider>
        <BrowserRouter>
          <Suspense fallback={<LoadingScreen />}>
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
