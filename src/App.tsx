import { BrowserRouter, Routes, Route } from 'react-router-dom'
import { AuthProvider } from '@/contexts/AuthContext'
import { HomePage } from '@/pages/HomePage'
import { ProofPage } from '@/pages/ProofPage'

function App() {
  return (
    <AuthProvider>
      <BrowserRouter>
        <Routes>
          <Route path="/" element={<HomePage />} />
          <Route path="/proof/:slug" element={<ProofPage />} />
        </Routes>
      </BrowserRouter>
    </AuthProvider>
  )
}

export default App
