/**
 * Lean file parser for annotation anchoring
 *
 * Parses Lean 4 files to extract all anchorable constructs:
 * - Declarations (theorem, lemma, def, structure, etc.)
 * - Section doc comments (/-! ... -/)
 * - Doc comments (/-- ... -/)
 * - Block comments (/- ... -/)
 * - Namespaces
 * - Imports
 */

import type {
  LeanConstruct,
  ParsedLeanFile,
  AnchorType,
  DeclarationKind,
} from './types.js';

const DECLARATION_KEYWORDS: DeclarationKind[] = [
  'theorem',
  'lemma',
  'def',
  'abbrev',
  'structure',
  'axiom',
  'instance',
  'class',
  'inductive',
  'example',
];

/**
 * Parse a Lean file and extract all anchorable constructs
 */
export function parseLeanFile(content: string, path: string): ParsedLeanFile {
  const lines = content.split('\n');
  const constructs: LeanConstruct[] = [];

  let i = 0;
  while (i < lines.length) {
    const line = lines[i];
    const trimmed = line.trim();

    // Check for block comment start (file header, etc.)
    if (trimmed.startsWith('/-') && !trimmed.startsWith('/--') && !trimmed.startsWith('/-!')) {
      const result = parseBlockComment(lines, i);
      constructs.push(result.construct);
      i = result.endIndex + 1;
      continue;
    }

    // Check for section doc comment (/-! ... -/)
    if (trimmed.startsWith('/-!')) {
      const result = parseSectionDoc(lines, i);
      constructs.push(result.construct);
      i = result.endIndex + 1;
      continue;
    }

    // Check for doc comment (/-- ... -/)
    if (trimmed.startsWith('/--')) {
      const result = parseDocComment(lines, i);
      constructs.push(result.construct);
      i = result.endIndex + 1;
      continue;
    }

    // Check for imports
    if (trimmed.startsWith('import ')) {
      const result = parseImports(lines, i);
      constructs.push(result.construct);
      i = result.endIndex + 1;
      continue;
    }

    // Check for namespace
    if (trimmed.startsWith('namespace ')) {
      const name = trimmed.replace('namespace ', '').trim();
      constructs.push({
        type: 'namespace',
        name,
        startLine: i + 1,
        endLine: i + 1,
        content: line,
      });
      i++;
      continue;
    }

    // Check for declarations
    const declResult = tryParseDeclaration(lines, i);
    if (declResult) {
      constructs.push(declResult.construct);
      i = declResult.endIndex + 1;
      continue;
    }

    i++;
  }

  // Link doc comments to their following declarations
  linkDocComments(constructs);

  return { path, constructs, lines };
}

/**
 * Parse a block comment (/- ... -/)
 */
function parseBlockComment(
  lines: string[],
  startIndex: number
): { construct: LeanConstruct; endIndex: number } {
  const startLine = startIndex + 1;
  let endIndex = startIndex;
  let content = '';
  let depth = 0;

  for (let i = startIndex; i < lines.length; i++) {
    const line = lines[i];
    content += (i > startIndex ? '\n' : '') + line;

    // Count nested comment depth
    for (let j = 0; j < line.length - 1; j++) {
      if (line[j] === '/' && line[j + 1] === '-') {
        depth++;
        j++;
      } else if (line[j] === '-' && line[j + 1] === '/') {
        depth--;
        j++;
        if (depth === 0) {
          endIndex = i;
          break;
        }
      }
    }

    if (depth === 0) {
      endIndex = i;
      break;
    }
  }

  return {
    construct: {
      type: 'block-comment',
      startLine,
      endLine: endIndex + 1,
      content,
    },
    endIndex,
  };
}

/**
 * Parse a section doc comment (/-! ... -/)
 */
function parseSectionDoc(
  lines: string[],
  startIndex: number
): { construct: LeanConstruct; endIndex: number } {
  const startLine = startIndex + 1;
  let endIndex = startIndex;
  let content = '';
  let depth = 1; // Already inside /-!

  for (let i = startIndex; i < lines.length; i++) {
    const line = lines[i];
    content += (i > startIndex ? '\n' : '') + line;

    // Find closing -/
    for (let j = (i === startIndex ? 3 : 0); j < line.length - 1; j++) {
      if (line[j] === '/' && line[j + 1] === '-' && !(line[j + 2] === '!' || line[j + 2] === '-')) {
        depth++;
        j++;
      } else if (line[j] === '-' && line[j + 1] === '/') {
        depth--;
        j++;
        if (depth === 0) {
          endIndex = i;
          break;
        }
      }
    }

    if (depth === 0) {
      endIndex = i;
      break;
    }
  }

  return {
    construct: {
      type: 'section-doc',
      startLine,
      endLine: endIndex + 1,
      content,
    },
    endIndex,
  };
}

/**
 * Parse a doc comment (/-- ... -/)
 */
function parseDocComment(
  lines: string[],
  startIndex: number
): { construct: LeanConstruct; endIndex: number } {
  const startLine = startIndex + 1;
  let endIndex = startIndex;
  let content = '';

  for (let i = startIndex; i < lines.length; i++) {
    const line = lines[i];
    content += (i > startIndex ? '\n' : '') + line;

    // Find closing -/
    if (line.includes('-/')) {
      endIndex = i;
      break;
    }
  }

  return {
    construct: {
      type: 'doc-comment',
      startLine,
      endLine: endIndex + 1,
      content,
    },
    endIndex,
  };
}

/**
 * Parse import block
 */
function parseImports(
  lines: string[],
  startIndex: number
): { construct: LeanConstruct; endIndex: number } {
  const startLine = startIndex + 1;
  let endIndex = startIndex;
  let content = '';

  for (let i = startIndex; i < lines.length; i++) {
    const trimmed = lines[i].trim();
    if (trimmed.startsWith('import ')) {
      content += (i > startIndex ? '\n' : '') + lines[i];
      endIndex = i;
    } else if (trimmed === '' && i === startIndex + 1) {
      // Allow one blank line
      continue;
    } else {
      break;
    }
  }

  return {
    construct: {
      type: 'imports',
      startLine,
      endLine: endIndex + 1,
      content,
    },
    endIndex,
  };
}

/**
 * Try to parse a declaration at the given line
 */
function tryParseDeclaration(
  lines: string[],
  startIndex: number
): { construct: LeanConstruct; endIndex: number } | null {
  const line = lines[startIndex];
  const trimmed = line.trim();

  // Check for declaration keywords
  let foundKind: DeclarationKind | null = null;
  let afterKeyword = '';

  for (const keyword of DECLARATION_KEYWORDS) {
    // Match: "theorem name", "@[attr] theorem name", "private theorem name", etc.
    const patterns = [
      new RegExp(`^${keyword}\\s+`),
      new RegExp(`^@\\[.*?\\]\\s*${keyword}\\s+`),
      new RegExp(`^private\\s+${keyword}\\s+`),
      new RegExp(`^protected\\s+${keyword}\\s+`),
      new RegExp(`^noncomputable\\s+${keyword}\\s+`),
    ];

    for (const pattern of patterns) {
      const match = trimmed.match(pattern);
      if (match) {
        foundKind = keyword;
        afterKeyword = trimmed.slice(match[0].length);
        break;
      }
    }
    if (foundKind) break;
  }

  if (!foundKind) return null;

  // Extract name (first identifier after keyword)
  // Note: 'example' declarations don't have names, they go directly to ':'
  const nameMatch = afterKeyword.match(/^([a-zA-Z_][a-zA-Z0-9_']*)/);
  let name: string | undefined;
  if (foundKind === 'example') {
    // Examples are anonymous - use a placeholder name based on line number
    name = `example_${startIndex + 1}`;
  } else if (nameMatch) {
    name = nameMatch[1];
  } else {
    return null;
  }

  // Find the end of the declaration
  const endIndex = findDeclarationEnd(lines, startIndex);

  return {
    construct: {
      type: 'declaration',
      kind: foundKind,
      name,
      startLine: startIndex + 1,
      endLine: endIndex + 1,
      content: lines.slice(startIndex, endIndex + 1).join('\n'),
    },
    endIndex,
  };
}

/**
 * Find where a declaration ends (handles multi-line definitions)
 */
function findDeclarationEnd(lines: string[], startIndex: number): number {
  let braceDepth = 0;
  let parenDepth = 0;
  let inProofBlock = false;

  for (let i = startIndex; i < lines.length; i++) {
    const line = lines[i];

    // Strip line comments before counting delimiters
    // This prevents parens/braces in comments from affecting depth tracking
    const lineWithoutComment = line.replace(/--.*$/, '');

    // Track brace and paren depth (only in non-comment code)
    for (const char of lineWithoutComment) {
      if (char === '{') braceDepth++;
      if (char === '}') braceDepth--;
      if (char === '(') parenDepth++;
      if (char === ')') parenDepth--;
    }

    // Check for "by" starting a tactic proof
    if (line.includes(':= by') || line.trim() === 'by' || line.trim().startsWith('by ')) {
      inProofBlock = true;
    }

    // Check for next declaration or blank line as terminator
    if (i > startIndex) {
      const nextTrimmed = lines[i].trim();

      // Empty line with balanced braces often ends a declaration
      if (nextTrimmed === '' && braceDepth <= 0 && parenDepth <= 0) {
        return i - 1;
      }

      // New top-level declaration starts
      if (braceDepth <= 0 && parenDepth <= 0) {
        for (const keyword of DECLARATION_KEYWORDS) {
          if (
            nextTrimmed.startsWith(keyword + ' ') ||
            nextTrimmed.match(new RegExp(`^@\\[.*?\\]\\s*${keyword}\\s+`)) ||
            nextTrimmed.startsWith('private ' + keyword) ||
            nextTrimmed.startsWith('protected ' + keyword)
          ) {
            return i - 1;
          }
        }
        // Other top-level constructs
        if (
          nextTrimmed.startsWith('namespace ') ||
          nextTrimmed.startsWith('end ') ||
          nextTrimmed.startsWith('section ') ||
          nextTrimmed.startsWith('/-!') ||
          nextTrimmed.startsWith('#')
        ) {
          return i - 1;
        }
      }
    }
  }

  return lines.length - 1;
}

/**
 * Link doc comments to their following declarations
 */
function linkDocComments(constructs: LeanConstruct[]): void {
  for (let i = 0; i < constructs.length - 1; i++) {
    const current = constructs[i];
    const next = constructs[i + 1];

    if (current.type === 'doc-comment' && next.type === 'declaration') {
      // Check if doc comment is immediately before declaration (allowing blank lines)
      if (next.startLine - current.endLine <= 2) {
        next.docCommentStart = current.startLine;
      }
    }
  }
}

/**
 * Find a construct by anchor specification
 */
export function findByAnchor(
  parsed: ParsedLeanFile,
  anchor: {
    type: AnchorType;
    name?: string;
    kind?: DeclarationKind;
    pattern?: string;
    contains?: string;
  }
): LeanConstruct | null {
  for (const construct of parsed.constructs) {
    // Type must match
    if (construct.type !== anchor.type) continue;

    // For declarations, check name and optionally kind
    if (anchor.type === 'declaration') {
      if (anchor.name && construct.name !== anchor.name) continue;
      if (anchor.kind && construct.kind !== anchor.kind) continue;
      return construct;
    }

    // For comments, check contains
    if (anchor.contains) {
      if (!construct.content.includes(anchor.contains)) continue;
      return construct;
    }

    // For patterns, use regex
    if (anchor.pattern) {
      const regex = new RegExp(anchor.pattern);
      if (!regex.test(construct.content)) continue;
      return construct;
    }

    // Namespace match by name
    if (anchor.type === 'namespace') {
      if (anchor.name && construct.name !== anchor.name) continue;
      return construct;
    }

    // Imports just match the first import block
    if (anchor.type === 'imports') {
      return construct;
    }
  }

  return null;
}

/**
 * Find what construct a given line belongs to
 * (Useful for converting line numbers to anchors)
 */
export function findConstructAtLine(
  parsed: ParsedLeanFile,
  lineNumber: number
): LeanConstruct | null {
  // Find the most specific construct containing this line
  let bestMatch: LeanConstruct | null = null;

  for (const construct of parsed.constructs) {
    const effectiveStart = construct.docCommentStart ?? construct.startLine;

    if (lineNumber >= effectiveStart && lineNumber <= construct.endLine) {
      // Prefer more specific matches (smaller range)
      if (
        !bestMatch ||
        (construct.endLine - effectiveStart) < (bestMatch.endLine - (bestMatch.docCommentStart ?? bestMatch.startLine))
      ) {
        bestMatch = construct;
      }
    }
  }

  return bestMatch;
}

/**
 * Generate an anchor for a construct
 */
export function generateAnchor(construct: LeanConstruct): {
  type: AnchorType;
  name?: string;
  kind?: DeclarationKind;
  contains?: string;
} {
  if (construct.type === 'declaration') {
    return {
      type: 'declaration',
      name: construct.name,
      kind: construct.kind,
    };
  }

  if (construct.type === 'namespace') {
    return {
      type: 'namespace',
      name: construct.name,
    };
  }

  if (construct.type === 'imports') {
    return { type: 'imports' };
  }

  // For comments, extract a distinctive phrase
  if (construct.type === 'section-doc' || construct.type === 'block-comment' || construct.type === 'doc-comment') {
    // Try to find a ## header
    const headerMatch = construct.content.match(/##\s+(.+)/);
    if (headerMatch) {
      return {
        type: construct.type,
        contains: headerMatch[1].trim(),
      };
    }

    // Use first substantial line (for identifying the comment)
    const lines = construct.content.split('\n');
    for (const line of lines) {
      // Remove comment markers and whitespace
      const cleaned = line.replace(/^[\s\-\/\*!]+/, '').replace(/\-\/\s*$/, '').trim();
      if (cleaned.length > 10) {
        // Escape special regex chars for pattern safety
        const safeContent = cleaned.slice(0, 50);
        return {
          type: construct.type,
          contains: safeContent,
        };
      }
    }

    // Last resort: use the first 30 chars of the whole content
    const fallback = construct.content.replace(/[\/\-\*!\s]+/g, ' ').trim().slice(0, 30);
    if (fallback.length > 5) {
      return {
        type: construct.type,
        contains: fallback,
      };
    }
  }

  return { type: construct.type };
}
