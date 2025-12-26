import { BrowserRouter, Routes, Route } from 'react-router-dom'
import { AuthProvider } from '@/contexts/AuthContext'
import { HomePage } from '@/pages/HomePage'
import { ProofPage } from '@/pages/ProofPage'
import { SubmitPage } from '@/pages/SubmitPage'
import { AboutPage } from '@/pages/AboutPage'

function App() {
  return (
    <AuthProvider>
      <BrowserRouter>
        <Routes>
          <Route path="/" element={<HomePage />} />
          <Route path="/proof/:slug" element={<ProofPage />} />
          <Route path="/submit" element={<SubmitPage />} />
          <Route path="/about" element={<AboutPage />} />
        </Routes>
      </BrowserRouter>
    </AuthProvider>
  )
}

export default App
