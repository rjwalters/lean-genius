/**
 * Normalize annotation `type` and `significance` values to the canonical
 * enums declared in `src/types/proof.ts` (and mirrored in
 * `scripts/annotations/types.ts`):
 *
 *   AnnotationType         = theorem | lemma | definition | tactic | concept | insight | warning
 *   AnnotationSignificance = critical | key | supporting
 *
 * Background (issue #31246): ~1/3 of `src/data/proofs/<slug>/annotations.json`
 * files were written with illustrative values like `technique`, `context`,
 * `key-step`, `central`, or even full sentences that were never valid enum
 * members. The runtime loader passes them through unchanged, producing blank
 * significance badges and raw-string type labels in the gallery UI.
 *
 * This script encodes the deterministic remediation map from #31246 and
 * rewrites every annotation file in place. It is idempotent: running it twice
 * is a no-op on the second pass.
 *
 * Modes:
 *   (default)   rewrite files in place, report what changed
 *   --check     dry run; exit 1 if any invalid value remains (CI guard)
 *   --verbose   list every file/field changed
 *
 * Usage:
 *   pnpm annotations:normalize          # apply
 *   pnpm annotations:normalize-check    # CI guard (no writes)
 */

import { readFileSync, writeFileSync, readdirSync, existsSync } from 'node:fs';
import { join } from 'node:path';

const VALID_TYPES = new Set([
  'theorem',
  'lemma',
  'definition',
  'tactic',
  'concept',
  'insight',
  'warning',
]);

const VALID_SIGNIFICANCE = new Set(['critical', 'key', 'supporting']);

/**
 * Canonicalize a raw value for map lookup: lowercase, trim, and collapse
 * `_` / whitespace runs into a single `-` so that `key_step`, `key step`, and
 * `key-step` all resolve to the same key.
 */
function canon(value: string): string {
  return value
    .trim()
    .toLowerCase()
    .replace(/[\s_]+/g, '-');
}

/** Deterministic type remediation map (keys are canonicalized). */
const TYPE_MAP: Record<string, string> = {
  // → tactic (how a step is carried out)
  technique: 'tactic',
  'proof-technique': 'tactic',
  'key-technique': 'tactic',
  computation: 'tactic',
  verification: 'tactic',
  inductive: 'tactic',
  // → concept (surrounding context / examples / notes)
  context: 'concept',
  example: 'concept',
  application: 'concept',
  observation: 'concept',
  note: 'concept',
  // → insight (a key idea or proof step)
  'key-step': 'insight',
  'proof-step': 'insight',
  step: 'insight',
  proof: 'insight',
  'key-insight': 'insight',
  'key-idea': 'insight',
  keystep: 'insight',
  key: 'insight',
  // → theorem (a result / corollary)
  result: 'theorem',
  'key-result': 'theorem',
  'main-result': 'theorem',
  corollary: 'theorem',
  // → definition (constructions / axioms)
  axiom: 'definition',
  construction: 'definition',
  // → warning (caveats / remarks)
  caveat: 'warning',
  remark: 'warning',
};

/** Deterministic significance remediation map (keys are canonicalized). */
const SIGNIFICANCE_MAP: Record<string, string> = {
  // → critical (core / foundational results)
  central: 'critical',
  core: 'critical',
  foundational: 'critical',
  fundamental: 'critical',
  essential: 'critical',
  'main-result': 'critical',
  'central-result': 'critical',
  'core-result': 'critical',
  // → key (important but not load-bearing)
  important: 'key',
  high: 'key',
  major: 'key',
  primary: 'key',
  'key-step': 'key',
  'key-technique': 'key',
  'key-result': 'key',
  'key-insight': 'key',
  'key-corollary': 'key',
  'core-step': 'key',
  'core-technique': 'key',
  // → supporting (context / technical / illustrative)
  context: 'supporting',
  technical: 'supporting',
  standard: 'supporting',
  medium: 'supporting',
  low: 'supporting',
  illustrative: 'supporting',
  illustration: 'supporting',
  useful: 'supporting',
  informational: 'supporting',
  insight: 'supporting',
  concept: 'supporting',
  technique: 'supporting',
  result: 'supporting',
};

/** Fallbacks for anything not explicitly mapped (and not already valid). */
const TYPE_DEFAULT = 'concept';
const SIGNIFICANCE_DEFAULT = 'supporting';

/**
 * A significance string with more than three whitespace-separated words is a
 * sentence that landed in the wrong field (a generation bug). The prose is
 * preserved in the annotation's `content`/`summary`, so we only need to demote
 * the significance itself to `supporting`.
 */
function isSentence(value: string): boolean {
  return value.trim().split(/\s+/).length > 3;
}

function mapType(raw: unknown): string | null {
  if (typeof raw !== 'string') return null;
  if (VALID_TYPES.has(raw)) return null; // already valid
  const key = canon(raw);
  return TYPE_MAP[key] ?? TYPE_DEFAULT;
}

function mapSignificance(raw: unknown): string | null {
  if (typeof raw !== 'string') return null;
  if (VALID_SIGNIFICANCE.has(raw)) return null; // already valid
  if (isSentence(raw)) return SIGNIFICANCE_DEFAULT;
  const key = canon(raw);
  return SIGNIFICANCE_MAP[key] ?? SIGNIFICANCE_DEFAULT;
}

interface Stats {
  filesScanned: number;
  filesChanged: number;
  typeFixes: Record<string, number>;
  sigFixes: Record<string, number>;
  unmappedTypes: Record<string, number>;
  unmappedSigs: Record<string, number>;
}

function run(): number {
  const check = process.argv.includes('--check');
  const verbose = process.argv.includes('--verbose');

  const repoRoot = process.cwd();
  const proofsDir = join(repoRoot, 'src/data/proofs');
  const files = readdirSync(proofsDir, { withFileTypes: true })
    .filter((d) => d.isDirectory())
    .map((d) => join(proofsDir, d.name, 'annotations.json'))
    .filter((p) => existsSync(p))
    .sort();

  const stats: Stats = {
    filesScanned: 0,
    filesChanged: 0,
    typeFixes: {},
    sigFixes: {},
    unmappedTypes: {},
    unmappedSigs: {},
  };

  // Match a whole line that is solely a `"type"` / `"significance"` field with
  // a simple (quote-free) string value. Every such field in the gallery data
  // sits on its own line with no internal quotes (verified across all 4163
  // files), and `"type"` only ever names an AnnotationType — there are no
  // nested anchor `type` keys here. Operating on raw lines preserves each
  // file's original formatting, so the diff is exactly the values that change.
  const TYPE_LINE = /^(\s*"type"\s*:\s*")([^"]*)("\s*,?\s*)$/;
  const SIG_LINE = /^(\s*"significance"\s*:\s*")([^"]*)("\s*,?\s*)$/;

  for (const file of files) {
    stats.filesScanned++;
    const raw = readFileSync(file, 'utf8');

    // Guard: only edit well-formed JSON.
    try {
      JSON.parse(raw);
    } catch {
      console.error(`✗ could not parse ${file}`);
      continue;
    }

    const eol = raw.includes('\r\n') ? '\r\n' : '\n';
    const lines = raw.split(/\r?\n/);
    let changed = false;

    for (let i = 0; i < lines.length; i++) {
      const tm = lines[i].match(TYPE_LINE);
      if (tm) {
        const newType = mapType(tm[2]);
        if (newType !== null) {
          if (!(canon(tm[2]) in TYPE_MAP) && !isSentence(tm[2])) {
            stats.unmappedTypes[tm[2]] = (stats.unmappedTypes[tm[2]] ?? 0) + 1;
          }
          stats.typeFixes[`${tm[2]} → ${newType}`] =
            (stats.typeFixes[`${tm[2]} → ${newType}`] ?? 0) + 1;
          if (verbose) console.log(`  ${file}: type ${tm[2]} → ${newType}`);
          lines[i] = `${tm[1]}${newType}${tm[3]}`;
          changed = true;
        }
        continue;
      }

      const sm = lines[i].match(SIG_LINE);
      if (sm) {
        const newSig = mapSignificance(sm[2]);
        if (newSig !== null) {
          const label = isSentence(sm[2]) ? '<sentence>' : sm[2];
          if (!isSentence(sm[2]) && !(canon(sm[2]) in SIGNIFICANCE_MAP)) {
            stats.unmappedSigs[sm[2]] = (stats.unmappedSigs[sm[2]] ?? 0) + 1;
          }
          stats.sigFixes[`${label} → ${newSig}`] =
            (stats.sigFixes[`${label} → ${newSig}`] ?? 0) + 1;
          if (verbose) console.log(`  ${file}: significance ${label} → ${newSig}`);
          lines[i] = `${sm[1]}${newSig}${sm[3]}`;
          changed = true;
        }
      }
    }

    if (changed) {
      stats.filesChanged++;
      if (!check) {
        const out = lines.join(eol);
        writeFileSync(file, out);
        // Re-validate the result is still parseable JSON.
        try {
          JSON.parse(out);
        } catch {
          console.error(`✗ rewrite produced invalid JSON: ${file}`);
        }
      }
    }
  }

  // Report
  console.log(`\nScanned ${stats.filesScanned} annotation files.`);
  console.log(
    `${check ? 'Would change' : 'Changed'} ${stats.filesChanged} files.`,
  );

  const fmt = (m: Record<string, number>) =>
    Object.entries(m)
      .sort((a, b) => b[1] - a[1])
      .map(([k, v]) => `    ${k}  (${v})`)
      .join('\n');

  if (Object.keys(stats.typeFixes).length) {
    console.log(`\n  type fixes:\n${fmt(stats.typeFixes)}`);
  }
  if (Object.keys(stats.sigFixes).length) {
    console.log(`\n  significance fixes:\n${fmt(stats.sigFixes)}`);
  }
  if (Object.keys(stats.unmappedTypes).length) {
    console.log(
      `\n  ⚠ unmapped types (fell back to '${TYPE_DEFAULT}'):\n${fmt(stats.unmappedTypes)}`,
    );
  }
  if (Object.keys(stats.unmappedSigs).length) {
    console.log(
      `\n  ⚠ unmapped significance (fell back to '${SIGNIFICANCE_DEFAULT}'):\n${fmt(stats.unmappedSigs)}`,
    );
  }

  if (check && stats.filesChanged > 0) {
    console.error(
      `\n✗ ${stats.filesChanged} files still contain non-canonical enum values. ` +
        `Run \`pnpm annotations:normalize\` to fix.`,
    );
    return 1;
  }

  console.log(check ? '\n✅ All annotation enums are canonical.' : '\n✅ Normalization complete.');
  return 0;
}

process.exit(run());
