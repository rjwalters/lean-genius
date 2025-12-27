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
})
