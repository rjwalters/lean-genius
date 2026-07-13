#!/usr/bin/env npx tsx
/**
 * Validate that Seeker-created research stubs have been filled in.
 *
 * The Seeker intentionally initializes problem.md from a template, then is
 * expected to replace all bracketed placeholders before handing work to a
 * Researcher or opening a PR. This guard fails fast when those placeholders
 * remain in markdown or generated site JSON.
 *
 * Run:
 *   npx tsx scripts/research/validate-seeker-stubs.ts <slug>
 *   npx tsx scripts/research/validate-seeker-stubs.ts --staged
 *   npx tsx scripts/research/validate-seeker-stubs.ts --changed
 *   npx tsx scripts/research/validate-seeker-stubs.ts --all
 */

import { execFileSync } from 'child_process'
import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __filename = fileURLToPath(import.meta.url)
const __dirname = path.dirname(__filename)
const ROOT = path.join(__dirname, '../..')
const RESEARCH_PROBLEMS_DIR = path.join(ROOT, 'research/problems')
const JSON_PROBLEMS_DIR = path.join(ROOT, 'src/data/research/problems')
const TEMPLATE_PATH = path.join(ROOT, 'research/templates/problem.md')

const LATEX_PLACEHOLDER = '[LaTeX formulation of the theorem/conjecture]'
const PLAIN_PLACEHOLDER = '[Explain what we\'re trying to prove in accessible terms]'
const TITLE_PLACEHOLDER = '[Problem Title]'
const EXACT_PLACEHOLDERS = buildExactPlaceholderLines()

interface Finding {
  filePath: string
  line?: number
  message: string
}

function relative(filePath: string): string {
  return path.relative(ROOT, filePath)
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value)
}

function getStringField(record: Record<string, unknown>, key: string): string {
  const value = record[key]
  return typeof value === 'string' ? value : ''
}

function buildExactPlaceholderLines(): Set<string> {
  const placeholders = new Set<string>([
    `# Problem: ${TITLE_PLACEHOLDER}`,
    PLAIN_PLACEHOLDER,
    LATEX_PLACEHOLDER,
    `\\text{${LATEX_PLACEHOLDER}}`,
  ])

  if (!fs.existsSync(TEMPLATE_PATH)) return placeholders

  const template = fs.readFileSync(TEMPLATE_PATH, 'utf-8')
    .replaceAll('{{TITLE}}', TITLE_PLACEHOLDER)
    .replaceAll('{{SLUG}}', 'placeholder-slug')
    .replaceAll('{{DATE}}', 'placeholder-date')
    .replaceAll('{{SOURCE}}', 'placeholder-source')

  for (const line of template.split('\n')) {
    const trimmed = line.trim()
    if (trimmed && trimmed.includes('[') && trimmed.includes(']')) {
      placeholders.add(trimmed)
    }
  }

  return placeholders
}

function slugFromPath(filePath: string): string | null {
  const normalized = filePath.replaceAll('\\', '/')

  const researchMatch = normalized.match(/^research\/problems\/([^/]+)\//)
  if (researchMatch) return researchMatch[1]

  const jsonMatch = normalized.match(/^src\/data\/research\/problems\/([^/]+)\.json$/)
  if (jsonMatch) return jsonMatch[1]

  return null
}

function gitNames(args: string[]): string[] {
  try {
    const output = execFileSync('git', args, {
      cwd: ROOT,
      encoding: 'utf-8',
      stdio: ['ignore', 'pipe', 'ignore'],
    })
    return output.split('\n').map(line => line.trim()).filter(Boolean)
  } catch {
    return []
  }
}

function changedSlugs(stagedOnly: boolean): Set<string> {
  const files = stagedOnly
    ? gitNames(['diff', '--name-only', '--cached', '--', 'research/problems', 'src/data/research/problems'])
    : [
        ...gitNames(['diff', '--name-only', 'HEAD', '--', 'research/problems', 'src/data/research/problems']),
        ...gitNames(['ls-files', '--others', '--exclude-standard', '--', 'research/problems', 'src/data/research/problems']),
      ]

  return new Set(files.map(slugFromPath).filter((slug): slug is string => slug !== null))
}

function allSlugs(): Set<string> {
  const slugs = new Set<string>()

  if (fs.existsSync(RESEARCH_PROBLEMS_DIR)) {
    for (const entry of fs.readdirSync(RESEARCH_PROBLEMS_DIR, { withFileTypes: true })) {
      if (entry.isDirectory()) slugs.add(entry.name)
    }
  }

  if (fs.existsSync(JSON_PROBLEMS_DIR)) {
    for (const entry of fs.readdirSync(JSON_PROBLEMS_DIR, { withFileTypes: true })) {
      if (entry.isFile() && entry.name.endsWith('.json')) {
        slugs.add(entry.name.slice(0, -'.json'.length))
      }
    }
  }

  return slugs
}

function validateMarkdown(slug: string): Finding[] {
  const filePath = path.join(RESEARCH_PROBLEMS_DIR, slug, 'problem.md')
  if (!fs.existsSync(filePath)) return []

  const findings: Finding[] = []
  const lines = fs.readFileSync(filePath, 'utf-8').split('\n')

  lines.forEach((line, index) => {
    const trimmed = line.trim()
    if (EXACT_PLACEHOLDERS.has(trimmed)) {
      findings.push({
        filePath,
        line: index + 1,
        message: `template placeholder line remains: ${trimmed}`,
      })
    }
  })

  return findings
}

function validateJson(slug: string): Finding[] {
  const filePath = path.join(JSON_PROBLEMS_DIR, `${slug}.json`)
  if (!fs.existsSync(filePath)) return []

  let parsed: unknown
  try {
    parsed = JSON.parse(fs.readFileSync(filePath, 'utf-8'))
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error)
    return [{ filePath, message: `invalid JSON: ${message}` }]
  }

  if (!isRecord(parsed)) {
    return [{ filePath, message: 'expected top-level JSON object' }]
  }

  const findings: Finding[] = []
  const title = getStringField(parsed, 'title').trim()
  if (title === TITLE_PLACEHOLDER) {
    findings.push({ filePath, message: `title is still ${TITLE_PLACEHOLDER}` })
  }

  const problemStatement = parsed.problemStatement
  if (isRecord(problemStatement)) {
    const formal = getStringField(problemStatement, 'formal')
    const plain = getStringField(problemStatement, 'plain').trim()

    if (formal.includes(LATEX_PLACEHOLDER)) {
      findings.push({ filePath, message: `problemStatement.formal contains ${LATEX_PLACEHOLDER}` })
    }
    if (plain === PLAIN_PLACEHOLDER) {
      findings.push({ filePath, message: `problemStatement.plain is still ${PLAIN_PLACEHOLDER}` })
    }
  }

  return findings
}

function validateSlug(slug: string): Finding[] {
  return [
    ...validateMarkdown(slug),
    ...validateJson(slug),
  ]
}

function printHelp(): void {
  console.log(`Validate Seeker research stubs for unfilled template placeholders.

Usage:
  npx tsx scripts/research/validate-seeker-stubs.ts <slug> [slug...]
  npx tsx scripts/research/validate-seeker-stubs.ts --staged
  npx tsx scripts/research/validate-seeker-stubs.ts --changed
  npx tsx scripts/research/validate-seeker-stubs.ts --all

Options:
  --staged   Validate slugs touched by staged research files.
  --changed  Validate slugs touched by changed or untracked research files.
  --all      Validate every research slug on disk.
  --help     Show this help.
`)
}

function main(): void {
  const args = process.argv.slice(2)
  if (args.includes('--help') || args.includes('-h')) {
    printHelp()
    return
  }

  const modes = args.filter(arg => ['--all', '--changed', '--staged'].includes(arg))
  if (modes.length > 1) {
    console.error(`Choose only one mode: ${modes.join(', ')}`)
    process.exit(2)
  }

  const explicitSlugs = args.filter(arg => !arg.startsWith('-'))
  let slugs: Set<string>

  if (explicitSlugs.length > 0) {
    slugs = new Set(explicitSlugs)
  } else if (args.includes('--all')) {
    slugs = allSlugs()
  } else if (args.includes('--staged')) {
    slugs = changedSlugs(true)
  } else {
    slugs = changedSlugs(false)
  }

  const findings = [...slugs].sort().flatMap(validateSlug)

  if (findings.length > 0) {
    console.error(`FAIL: found ${findings.length} unfilled Seeker placeholder(s).`)
    for (const finding of findings) {
      const location = finding.line === undefined
        ? relative(finding.filePath)
        : `${relative(finding.filePath)}:${finding.line}`
      console.error(`- ${location}: ${finding.message}`)
    }
    process.exit(1)
  }

  console.log(`PASS: ${slugs.size} research slug(s) have no Seeker template placeholders.`)
}

main()
