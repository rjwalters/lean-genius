/// <reference types="vite/client" />

declare module '*.lean?raw' {
  const content: string
  export default content
}

// Build-time constants injected by vite.config.ts
declare const __COMMIT_HASH__: string
declare const __BUILD_TIME__: string
