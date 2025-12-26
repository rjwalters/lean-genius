export type TokenType =
  | 'keyword'
  | 'type'
  | 'function'
  | 'string'
  | 'number'
  | 'comment'
  | 'operator'
  | 'punctuation'
  | 'identifier'
  | 'tactic'
  | 'attribute'

export interface Token {
  type: TokenType
  value: string
  start: number
  end: number
}

const KEYWORDS = new Set([
  'theorem', 'lemma', 'def', 'definition', 'structure', 'class', 'instance',
  'inductive', 'coinductive', 'axiom', 'constant', 'variable', 'universe',
  'namespace', 'section', 'end', 'open', 'import', 'export', 'private', 'protected',
  'noncomputable', 'partial', 'unsafe', 'where', 'extends', 'with', 'deriving',
  'if', 'then', 'else', 'match', 'do', 'return', 'let', 'have', 'show', 'suffices',
  'fun', 'assume', 'forall', 'exists', 'by', 'from', 'at', 'in',
  'set_option', 'attribute', 'local', 'scoped',
])

const TACTICS = new Set([
  'intro', 'intros', 'apply', 'exact', 'refine', 'use', 'obtain', 'rcases',
  'cases', 'induction', 'simp', 'simp_all', 'ring', 'linarith', 'nlinarith',
  'norm_num', 'positivity', 'field_simp', 'push_neg', 'contrapose', 'by_contra',
  'by_cases', 'split', 'constructor', 'ext', 'funext', 'congr', 'rfl', 'refl',
  'symm', 'trans', 'calc', 'rw', 'rewrite', 'conv', 'unfold', 'dsimp', 'change',
  'specialize', 'generalize', 'clear', 'rename', 'subst', 'injection', 'exfalso',
  'trivial', 'decide', 'native_decide', 'norm_cast', 'assumption', 'contradiction',
])

const TYPES = new Set([
  'Type', 'Prop', 'Sort', 'Set', 'Nat', 'Int', 'Real', 'Bool', 'String', 'Unit',
  'List', 'Array', 'Option', 'Fin', 'Vector', 'Subtype', 'Quotient',
  'ℕ', 'ℤ', 'ℝ', 'ℚ', 'ℂ',
])

const OPERATORS = new Set([
  '→', '←', '↔', '∧', '∨', '¬', '∀', '∃', '∈', '∉', '⊆', '⊂', '⊇', '⊃',
  '∪', '∩', '×', '⊕', '⊗', '≤', '≥', '≠', '≈', '≡', '∘', '⁻¹',
  '+', '-', '*', '/', '^', '=', '<', '>', '|', '&', '!', '?', ':=', '=>',
  '·', '•', '∑', '∏', '∫', '∂', '∇', '√', 'λ',
])

export interface TokenizeResult {
  tokens: Token[]
  endsInBlockComment: boolean
}

export function tokenizeLine(line: string, inBlockComment: boolean = false): TokenizeResult {
  const tokens: Token[] = []
  let i = 0

  // If we're continuing a block comment from a previous line
  if (inBlockComment) {
    const endIdx = line.indexOf('-/')
    if (endIdx !== -1) {
      // Block comment ends on this line
      tokens.push({
        type: 'comment',
        value: line.slice(0, endIdx + 2),
        start: 0,
        end: endIdx + 2,
      })
      i = endIdx + 2
      inBlockComment = false
    } else {
      // Entire line is still inside the block comment
      tokens.push({
        type: 'comment',
        value: line,
        start: 0,
        end: line.length,
      })
      return { tokens, endsInBlockComment: true }
    }
  }

  while (i < line.length) {
    // Skip whitespace
    if (/\s/.test(line[i])) {
      i++
      continue
    }

    // Comments
    if (line.slice(i, i + 2) === '--') {
      tokens.push({
        type: 'comment',
        value: line.slice(i),
        start: i,
        end: line.length,
      })
      break
    }

    // Block comment start (will handle full block in multi-line context)
    if (line.slice(i, i + 2) === '/-') {
      const endIdx = line.indexOf('-/', i + 2)
      if (endIdx !== -1) {
        tokens.push({
          type: 'comment',
          value: line.slice(i, endIdx + 2),
          start: i,
          end: endIdx + 2,
        })
        i = endIdx + 2
      } else {
        tokens.push({
          type: 'comment',
          value: line.slice(i),
          start: i,
          end: line.length,
        })
        return { tokens, endsInBlockComment: true }
      }
      continue
    }

    // Strings
    if (line[i] === '"') {
      let j = i + 1
      while (j < line.length && line[j] !== '"') {
        if (line[j] === '\\') j++
        j++
      }
      tokens.push({
        type: 'string',
        value: line.slice(i, j + 1),
        start: i,
        end: j + 1,
      })
      i = j + 1
      continue
    }

    // Numbers
    if (/[0-9]/.test(line[i])) {
      let j = i
      while (j < line.length && /[0-9.]/.test(line[j])) j++
      tokens.push({
        type: 'number',
        value: line.slice(i, j),
        start: i,
        end: j,
      })
      i = j
      continue
    }

    // Operators (check multi-char first)
    let foundOp = false
    for (const op of [':=', '=>', '→', '←', '↔', '∧', '∨', '¬', '∀', '∃', '∈', '∉', '⊆', '≤', '≥', '≠']) {
      if (line.slice(i, i + op.length) === op) {
        tokens.push({
          type: 'operator',
          value: op,
          start: i,
          end: i + op.length,
        })
        i += op.length
        foundOp = true
        break
      }
    }
    if (foundOp) continue

    // Single char operators
    if (OPERATORS.has(line[i])) {
      tokens.push({
        type: 'operator',
        value: line[i],
        start: i,
        end: i + 1,
      })
      i++
      continue
    }

    // Punctuation
    if (/[()[\]{},;.]/.test(line[i])) {
      tokens.push({
        type: 'punctuation',
        value: line[i],
        start: i,
        end: i + 1,
      })
      i++
      continue
    }

    // Attributes
    if (line[i] === '@') {
      let j = i + 1
      while (j < line.length && /[a-zA-Z0-9_]/.test(line[j])) j++
      tokens.push({
        type: 'attribute',
        value: line.slice(i, j),
        start: i,
        end: j,
      })
      i = j
      continue
    }

    // Identifiers / keywords / tactics / types
    if (/[a-zA-Z_α-ωΑ-Ω₀-₉]/.test(line[i])) {
      let j = i
      while (j < line.length && /[a-zA-Z0-9_'α-ωΑ-Ω₀-₉]/.test(line[j])) j++
      const word = line.slice(i, j)

      let type: TokenType = 'identifier'
      if (KEYWORDS.has(word)) {
        type = 'keyword'
      } else if (TACTICS.has(word)) {
        type = 'tactic'
      } else if (TYPES.has(word)) {
        type = 'type'
      } else if (word[0] === word[0].toUpperCase() && /[A-Z]/.test(word[0])) {
        // Capitalized identifiers are usually types/constructors
        type = 'type'
      }

      tokens.push({
        type,
        value: word,
        start: i,
        end: j,
      })
      i = j
      continue
    }

    // Unicode math symbols as operators
    if (/[λπ∞∂∇∑∏∫√]/.test(line[i])) {
      tokens.push({
        type: 'operator',
        value: line[i],
        start: i,
        end: i + 1,
      })
      i++
      continue
    }

    // Fallback: treat as identifier
    tokens.push({
      type: 'identifier',
      value: line[i],
      start: i,
      end: i + 1,
    })
    i++
  }

  return { tokens, endsInBlockComment: false }
}

export function tokenTypeToClass(type: TokenType): string {
  const classMap: Record<TokenType, string> = {
    keyword: 'text-lean-keyword',
    type: 'text-lean-type',
    function: 'text-lean-function',
    string: 'text-lean-string',
    number: 'text-lean-number',
    comment: 'text-lean-comment italic',
    operator: 'text-lean-operator',
    punctuation: 'text-muted-foreground',
    identifier: 'text-foreground',
    tactic: 'text-lean-function',
    attribute: 'text-lean-keyword opacity-80',
  }
  return classMap[type]
}
