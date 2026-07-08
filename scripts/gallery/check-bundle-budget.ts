#!/usr/bin/env npx tsx
/**
 * Bundle budget guard (issue #35117, Track A item 5).
 *
 * Runs after `vite build` and fails the build if any emitted JS chunk in
 * `dist/assets/` exceeds the budget (minified, pre-compression bytes).
 *
 * Rationale: phases 1-3 of the build-perf work (#20992, #20993, #35117)
 * repeatedly regressed because growing JSON datasets were silently inlined
 * into eager chunks — listings.json alone reached 4.9 MB inside the UserMenu
 * chunk. The budget is set above the largest legitimate chunk (vendor-katex,
 * ~570 KB) but far below any dataset-inlining accident, so a phase-4
 * recurrence fails the build instead of shipping.
 *
 * Usage: tsx scripts/gallery/check-bundle-budget.ts [--budget-kb <n>]
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __dirname = path.dirname(fileURLToPath(import.meta.url))
const DIST_ASSETS = path.join(__dirname, '../../dist/assets')

const DEFAULT_BUDGET_KB = 600

function parseBudget(): number {
  const args = process.argv.slice(2)
  const idx = args.indexOf('--budget-kb')
  if (idx !== -1 && args[idx + 1]) {
    const parsed = Number(args[idx + 1])
    if (Number.isFinite(parsed) && parsed > 0) return parsed
  }
  return DEFAULT_BUDGET_KB
}

const budgetKb = parseBudget()

if (!fs.existsSync(DIST_ASSETS)) {
  console.error(`Bundle budget check: ${DIST_ASSETS} not found — run \`vite build\` first`)
  process.exit(1)
}

const chunks = fs
  .readdirSync(DIST_ASSETS)
  .filter((f) => f.endsWith('.js'))
  .map((f) => ({
    file: f,
    kb: fs.statSync(path.join(DIST_ASSETS, f)).size / 1024,
  }))
  .sort((a, b) => b.kb - a.kb)

if (chunks.length === 0) {
  console.error('Bundle budget check: no JS chunks found in dist/assets')
  process.exit(1)
}

const over = chunks.filter((c) => c.kb > budgetKb)

console.log(`\nBundle budget check (${chunks.length} JS chunks, budget ${budgetKb} KB minified):`)
for (const c of chunks.slice(0, 10)) {
  const flag = c.kb > budgetKb ? 'OVER  ' : 'ok    '
  console.log(`  ${flag}${c.kb.toFixed(1).padStart(9)} KB  ${c.file}`)
}
if (chunks.length > 10) {
  console.log(`  ... ${chunks.length - 10} smaller chunks all within budget`)
}

if (over.length > 0) {
  console.error(
    `\nFAIL: ${over.length} chunk(s) exceed the ${budgetKb} KB budget. ` +
      `A large dataset was probably inlined into the JS graph — keep bulk JSON ` +
      `in public/data/ runtime fetches (see issue #35117 and the header of ` +
      `src/data/proofs/index.ts).`
  )
  process.exit(1)
}

console.log('All chunks within budget.\n')
