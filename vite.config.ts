import path from 'path'
import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import tailwindcss from '@tailwindcss/vite'
import { execSync } from 'child_process'

// Get git commit hash and build time at build time
const getGitCommitHash = () => {
  try {
    return execSync('git rev-parse --short HEAD').toString().trim()
  } catch {
    return 'unknown'
  }
}

const getBuildTime = () => {
  return new Date().toISOString()
}

// https://vite.dev/config/
export default defineConfig({
  plugins: [react(), tailwindcss()],
  define: {
    __COMMIT_HASH__: JSON.stringify(getGitCommitHash()),
    __BUILD_TIME__: JSON.stringify(getBuildTime()),
  },
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
          // KaTeX math rendering - large but safe to chunk
          if (id.includes('node_modules/katex')) return 'vendor-katex'
          if (id.includes('node_modules/react-katex')) return 'vendor-katex'
          if (id.includes('node_modules/rehype-katex')) return 'vendor-katex'
          if (id.includes('node_modules/remark-math')) return 'vendor-katex'
          // Note: React/react-router/radix-ui/lucide-react are left to Vite
          // to avoid module initialization order issues
          // Per-proof chunks are handled by dynamic imports in proofs/index.ts
        },
      },
    },
  },
})
