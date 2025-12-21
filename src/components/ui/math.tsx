import 'katex/dist/katex.min.css'
import { InlineMath, BlockMath } from 'react-katex'
import { Fragment } from 'react'

interface MathTextProps {
  children: string
  className?: string
}

/**
 * Renders text with inline ($...$) and block ($$...$$) LaTeX math.
 *
 * Example:
 *   "The spectral gap $\lambda_1 = 4\pi^2$ controls dissipation."
 *   "$$E = mc^2$$"
 */
export function MathText({ children, className }: MathTextProps) {
  const parts = parseMath(children)

  return (
    <span className={className}>
      {parts.map((part, i) => (
        <Fragment key={i}>
          {part.type === 'text' && part.content}
          {part.type === 'inline' && (
            <InlineMath math={part.content} />
          )}
          {part.type === 'block' && (
            <div className="my-3">
              <BlockMath math={part.content} />
            </div>
          )}
        </Fragment>
      ))}
    </span>
  )
}

interface MathPart {
  type: 'text' | 'inline' | 'block'
  content: string
}

function parseMath(text: string): MathPart[] {
  const parts: MathPart[] = []

  // Regex to match $$...$$ (block) or $...$ (inline)
  // Block math first (greedy for $$)
  const mathRegex = /\$\$([^$]+)\$\$|\$([^$]+)\$/g

  let lastIndex = 0
  let match

  while ((match = mathRegex.exec(text)) !== null) {
    // Add text before this match
    if (match.index > lastIndex) {
      parts.push({
        type: 'text',
        content: text.slice(lastIndex, match.index),
      })
    }

    // Add the math part
    if (match[1] !== undefined) {
      // Block math ($$...$$)
      parts.push({
        type: 'block',
        content: match[1].trim(),
      })
    } else if (match[2] !== undefined) {
      // Inline math ($...$)
      parts.push({
        type: 'inline',
        content: match[2].trim(),
      })
    }

    lastIndex = match.index + match[0].length
  }

  // Add remaining text
  if (lastIndex < text.length) {
    parts.push({
      type: 'text',
      content: text.slice(lastIndex),
    })
  }

  return parts
}

/**
 * Render just inline math without parsing
 */
export function Math({ children }: { children: string }) {
  return <InlineMath math={children} />
}

/**
 * Render just block math without parsing
 */
export function MathBlock({ children }: { children: string }) {
  return <BlockMath math={children} />
}
