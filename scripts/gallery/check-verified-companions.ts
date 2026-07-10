#!/usr/bin/env npx tsx
/**
 * Verified-entry companion-file hygiene guard (issue #35854).
 *
 * A gallery entry marked `status: "verified"` claims 0 sorries. Its headline
 * proof (proofRepoPath / leanFile.path) is genuinely sorry-clean. But an entry
 * can ALSO advertise supporting Lean files in `additionalFiles` (top-level) and
 * `leanFile.additionalFiles`. When one of those listed companions carries a
 * `sorry`, a reader inspecting "the Lean files for this verified proof" hits a
 * sorry — undermining the verified / 0-sorries claim (manifest-hygiene defect).
 *
 * PR #35627 fixed one such entry (shannon-entropy-oq-03) by dropping the
 * companion from both manifest arrays, but a later unrelated meta-regeneration
 * silently re-added it. PR #35862 then cleaned 19 entries the same way. Both
 * fixes REGRESS because meta-regeneration re-associates every
 * `Proofs/<Slug>*.lean` file with the slug. This check turns that regression
 * into a build failure so per-entry manifest edits stick.
 *
 * Rule enforced: no `status: "verified"` entry may list, in either
 * `additionalFiles` or `leanFile.additionalFiles`, a Lean file that contains a
 * `sorry` once block- and line-comments are stripped. (A `sorry` appearing only
 * inside a docstring/comment — e.g. a "previously contained sorry" status note —
 * does NOT count, matching the auditor's detector.)
 *
 * Fix when this fails: drop the offending companion from the entry's manifest
 * arrays (the file stays on disk; it just is not advertised as part of a
 * verified entry). Aristotle proof-search scaffolds (`*Aristotle.lean`) are
 * sorry-by-design and must not be listed under verified entries either.
 *
 * Usage: tsx scripts/gallery/check-verified-companions.ts
 */

import * as fs from 'fs'
import * as path from 'path'
import { fileURLToPath } from 'url'

const __dirname = path.dirname(fileURLToPath(import.meta.url))
const REPO_ROOT = path.join(__dirname, '../..')
const PROOFS_DIR = path.join(REPO_ROOT, 'src/data/proofs')
const LEAN_ROOT = path.join(REPO_ROOT, 'proofs')

/** Strip Lean block comments (/- ... -/) and line comments (-- ...). */
function stripComments(src: string): string {
  return src.replace(/\/-[\s\S]*?-\//g, '').replace(/--.*/g, '')
}

/** Count real (non-comment) `sorry` tokens in a Lean file. */
function countSorry(filePath: string): number {
  const src = stripComments(fs.readFileSync(filePath, 'utf-8'))
  return (src.match(/\bsorry\b/g) || []).length
}

/** Resolve a manifest-listed path (may be repo-relative or proofs-relative). */
function resolveLeanFile(rel: string): string | null {
  for (const cand of [path.join(REPO_ROOT, rel), path.join(LEAN_ROOT, rel)]) {
    if (fs.existsSync(cand)) return cand
  }
  return null
}

/** Pull file paths from an additionalFiles array (strings or {path}/{file} objects). */
function collectFiles(arr: unknown): string[] {
  if (!Array.isArray(arr)) return []
  const out: string[] = []
  for (const f of arr) {
    if (typeof f === 'string') out.push(f)
    else if (f && typeof f === 'object') {
      const p = (f as Record<string, unknown>).path ?? (f as Record<string, unknown>).file
      if (typeof p === 'string') out.push(p)
    }
  }
  return out
}

interface Offense {
  slug: string
  file: string
  sorries: number
  where: string
}

const offenses: Offense[] = []
let verifiedCount = 0

for (const slug of fs.readdirSync(PROOFS_DIR).sort()) {
  const metaPath = path.join(PROOFS_DIR, slug, 'meta.json')
  if (!fs.existsSync(metaPath)) continue

  let meta: Record<string, unknown>
  try {
    meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'))
  } catch {
    continue // meta-shape validation is another check's job
  }

  const metaBlock = (meta.meta as Record<string, unknown>) || {}
  if (metaBlock.status !== 'verified') continue
  verifiedCount++

  const leanFile = (meta.leanFile as Record<string, unknown>) || {}
  const metaFiles = collectFiles(meta.additionalFiles)
  const lfFiles = collectFiles(leanFile.additionalFiles)

  for (const rel of new Set([...metaFiles, ...lfFiles])) {
    const resolved = resolveLeanFile(rel)
    if (!resolved) continue // missing files are not this check's concern
    const n = countSorry(resolved)
    if (n > 0) {
      const where = [
        metaFiles.includes(rel) ? 'additionalFiles' : null,
        lfFiles.includes(rel) ? 'leanFile.additionalFiles' : null,
      ]
        .filter(Boolean)
        .join(' + ')
      offenses.push({ slug, file: rel, sorries: n, where })
    }
  }
}

if (offenses.length > 0) {
  console.error(
    `FAIL: ${offenses.length} verified entr${offenses.length === 1 ? 'y advertises a' : 'ies advertise'} ` +
      `sorry-carrying companion file(s) (issue #35854):`
  )
  for (const o of offenses) {
    console.error(
      `  ${o.slug}: ${o.file} has ${o.sorries} sorry(ies) — listed in ${o.where}`
    )
  }
  console.error(
    `\nFix: drop each offending companion from the entry's additionalFiles / ` +
      `leanFile.additionalFiles (the file stays on disk; it is just not advertised as ` +
      `part of a verified proof). See #35854 / PR #35862.`
  )
  process.exit(1)
}

console.log(
  `ok: ${verifiedCount} verified entries — no advertised companion carries a sorry (#35854).`
)
