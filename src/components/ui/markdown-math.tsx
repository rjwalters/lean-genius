import 'katex/dist/katex.min.css'
import type { ReactNode } from 'react'
import ReactMarkdown from 'react-markdown'
import remarkMath from 'remark-math'
import rehypeKatex from 'rehype-katex'

interface MarkdownMathProps {
  children: string
  className?: string
}

/**
 * Rehype plugin: unwrap <p> inside <li> (caused by "loose" markdown lists
 * with blank lines between items). Prevents list markers from detaching
 * from paragraph content when using list-inside positioning.
 */
function rehypeUnwrapListParagraphs() {
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  return (tree: any) => {
    function walk(node: any) {
      if (!node.children) return
      for (const child of node.children) walk(child)
      if (node.tagName === 'li') {
        const flat: any[] = []
        for (const child of node.children) {
          if (child.type === 'element' && child.tagName === 'p') {
            flat.push(...child.children)
          } else {
            flat.push(child)
          }
        }
        node.children = flat
      }
    }
    walk(tree)
  }
}

/**
 * Renders markdown text with LaTeX math support.
 *
 * Supports:
 * - Inline math: $...$
 * - Block math: $$...$$
 * - Bold: **text**
 * - Italic: *text* or _text_
 * - Lists: 1. item or - item
 * - And other standard markdown
 */
export function MarkdownMath({ children, className }: MarkdownMathProps) {
  return (
    <div className={className}>
      <ReactMarkdown
        remarkPlugins={[remarkMath]}
        rehypePlugins={[rehypeUnwrapListParagraphs, rehypeKatex]}
        components={{
          // Style paragraphs to match existing design
          p: ({ children }: { children?: ReactNode }) => (
            <p className="mb-3 last:mb-0">{children}</p>
          ),
          // Style lists
          ol: ({ children }: { children?: ReactNode }) => (
            <ol className="list-decimal list-inside space-y-2 mb-3">{children}</ol>
          ),
          ul: ({ children }: { children?: ReactNode }) => (
            <ul className="list-disc list-inside space-y-2 mb-3">{children}</ul>
          ),
          li: ({ children }: { children?: ReactNode }) => (
            <li className="leading-relaxed">{children}</li>
          ),
          // Style strong/bold
          strong: ({ children }: { children?: ReactNode }) => (
            <strong className="font-semibold text-foreground">{children}</strong>
          ),
          // Style emphasis/italic
          em: ({ children }: { children?: ReactNode }) => (
            <em className="italic">{children}</em>
          ),
          // Style code
          code: ({ children }: { children?: ReactNode }) => (
            <code className="bg-muted/50 px-1.5 py-0.5 rounded text-sm font-mono">{children}</code>
          ),
        }}
      >
        {children}
      </ReactMarkdown>
    </div>
  )
}

/**
 * Inline variant for use within text flows (no wrapper div, renders as span).
 */
export function MarkdownMathInline({ children, className }: MarkdownMathProps) {
  return (
    <span className={className}>
      <ReactMarkdown
        remarkPlugins={[remarkMath]}
        rehypePlugins={[rehypeUnwrapListParagraphs, rehypeKatex]}
        components={{
          // Remove paragraph wrapper for inline use
          p: ({ children }: { children?: ReactNode }) => <>{children}</>,
          strong: ({ children }: { children?: ReactNode }) => (
            <strong className="font-semibold text-foreground">{children}</strong>
          ),
          em: ({ children }: { children?: ReactNode }) => (
            <em className="italic">{children}</em>
          ),
          code: ({ children }: { children?: ReactNode }) => (
            <code className="bg-muted/50 px-1.5 py-0.5 rounded text-sm font-mono">{children}</code>
          ),
        }}
      >
        {children}
      </ReactMarkdown>
    </span>
  )
}
