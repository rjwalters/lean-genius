import path from 'path'
import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import tailwindcss from '@tailwindcss/vite'

// https://vite.dev/config/
export default defineConfig({
  plugins: [react(), tailwindcss()],
  resolve: {
    alias: {
      '@': path.resolve(__dirname, './src'),
    },
  },
  // Suppress CSS warnings for "loom:*" properties
  // These come from Tailwind scanning markdown docs (CLAUDE.md, .loom/roles/*.md)
  // which contain GitHub label names like "loom:issue" that look like
  // Tailwind's arbitrary value syntax [property:value]
  esbuild: {
    logOverride: {
      'unsupported-css-property': 'silent',
    },
  },
  build: {
    rollupOptions: {
      output: {
        manualChunks(id) {
          // Vendor chunks
          if (id.includes('node_modules/react-dom')) return 'vendor-react'
          if (id.includes('node_modules/react-router')) return 'vendor-react'
          if (id.includes('node_modules/react/')) return 'vendor-react'
          if (id.includes('node_modules/katex')) return 'vendor-katex'
          if (id.includes('node_modules/react-katex')) return 'vendor-katex'
          if (id.includes('node_modules/rehype-katex')) return 'vendor-katex'
          if (id.includes('node_modules/remark-math')) return 'vendor-katex'
          if (id.includes('node_modules/react-markdown')) return 'vendor-markdown'
          if (id.includes('node_modules/@radix-ui')) return 'vendor-ui'
          if (id.includes('node_modules/lucide-react')) return 'vendor-icons'
          // Per-proof chunks (dynamic imports handle this automatically)
          // listings.json stays in main bundle (small, needed for HomePage)
        },
      },
    },
  },
})
