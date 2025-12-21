/// <reference types="vite/client" />

declare module '*.lean?raw' {
  const content: string
  export default content
}
