#!/usr/bin/env npx tsx
/**
 * One-off codemod for build-perf phase 1 (issue #20992).
 *
 * Removes the `*.lean?raw` wiring from every per-proof shim under
 * `src/data/proofs/<slug>/index.ts`. After this runs, the shims still import and
 * export their `meta.json` / `annotations.json` / `proofData`, but no longer pull
 * the Lean source into the vite/Rollup module graph. The Lean source is instead
 * emitted to `public/data/proofs/<slug>/source.lean` (see scripts/annotations/build.ts)
 * and fetched by slug at runtime in `src/data/proofs/index.ts`.
 *
 * Two shim shapes exist in the tree (verified disjoint):
 *
 *   Pattern A — dynamic-import factory (~1344 files):
 *     const leanSource = () => import('../../../../proofs/Proofs/Foo.lean?raw')
 *     ...
 *     export async function getProofSource(): Promise<string> { ... await leanSource() ... }
 *   The proof object already sets `source: ''` (loaded dynamically). We delete the
 *   `leanSource` const and the entire `getProofSource` function (inline or block form).
 *
 *   Pattern B — static raw import (~1091 files):
 *     import sourceRaw from '../../../../proofs/Proofs/Foo.lean?raw'
 *     ... source: sourceRaw ...
 *   We delete the `import sourceRaw ... ?raw` line and replace `source: sourceRaw`
 *   with `source: ''`.
 *
 * The codemod is deterministic and idempotent: re-running it on already-migrated
 * files is a no-op (nothing matches). It fails loudly if, after rewriting, any
 * `lean?raw`, `leanSource`, `sourceRaw`, or `getProofSource` token survives.
 *
 * Usage:
 *   pnpm tsx scripts/codemod/strip-lean-raw-imports.ts          # apply
 *   pnpm tsx scripts/codemod/strip-lean-raw-imports.ts --dry-run # report only
 */

import * as fs from 'fs';
import * as path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const PROOFS_DATA_DIR = path.join(__dirname, '../../src/data/proofs');

const dryRun = process.argv.includes('--dry-run');

/**
 * Strip the Lean `?raw` wiring from a single shim's source text.
 * Returns the rewritten text (unchanged if nothing matched).
 */
export function transform(src: string): string {
  let out = src;

  // --- Pattern A: dynamic-import factory ------------------------------------

  // Remove the `const leanSource = () => import('...lean?raw')` line, including a
  // trailing newline and any immediately-preceding `// Import the Lean source file`
  // style comment line. Tolerant of single/double quotes and surrounding blank lines.
  out = out.replace(
    /(?:^[ \t]*\/\/[^\n]*\n)?^[ \t]*const leanSource\s*=\s*\(\)\s*=>\s*import\([^\n]*lean\?raw[^\n]*\)[ \t]*\n/m,
    ''
  );

  // Remove the `getProofSource` block form:
  //   export async function getProofSource(): Promise<string> {
  //     ... (any lines that reference leanSource) ...
  //   }
  out = out.replace(
    /^[ \t]*export\s+async\s+function\s+getProofSource\s*\([^)]*\)\s*:\s*Promise<string>\s*\{[\s\S]*?\n[ \t]*\}[ \t]*\n/m,
    ''
  );

  // Remove the `getProofSource` single-line form:
  //   export async function getProofSource(): Promise<string> { ... }
  out = out.replace(
    /^[ \t]*export\s+async\s+function\s+getProofSource\s*\([^)]*\)\s*:\s*Promise<string>\s*\{[^\n]*\}[ \t]*\n/m,
    ''
  );

  // --- Pattern B: static raw import -----------------------------------------

  // Remove the `import sourceRaw from '...?raw'` line.
  out = out.replace(
    /^[ \t]*import\s+sourceRaw\s+from\s+['"][^'"]*\?raw['"][ \t]*\n/m,
    ''
  );

  // Replace `source: sourceRaw` with `source: ''` wherever it appears (inline
  // object or its own line). Preserves any trailing comma/brace via the lookahead.
  out = out.replace(/source:\s*sourceRaw\b/g, "source: ''");

  // Collapse any 3+ consecutive blank lines left behind into a single blank line.
  out = out.replace(/\n{3,}/g, '\n\n');

  return out;
}

function main(): void {
  const dirs = fs
    .readdirSync(PROOFS_DATA_DIR)
    .filter((d) => fs.statSync(path.join(PROOFS_DATA_DIR, d)).isDirectory());

  let changed = 0;
  let untouched = 0;
  const failures: string[] = [];

  for (const dir of dirs) {
    const file = path.join(PROOFS_DATA_DIR, dir, 'index.ts');
    if (!fs.existsSync(file)) continue;

    const before = fs.readFileSync(file, 'utf-8');
    if (!before.includes('lean?raw')) {
      untouched++;
      continue;
    }

    const after = transform(before);

    // Sanity: no raw-source token may survive in a rewritten file.
    if (/lean\?raw|leanSource|sourceRaw|getProofSource/.test(after)) {
      failures.push(dir);
      continue;
    }

    if (after !== before) {
      if (!dryRun) fs.writeFileSync(file, after);
      changed++;
    } else {
      untouched++;
    }
  }

  console.log(
    `${dryRun ? '[dry-run] ' : ''}codemod complete: ${changed} rewritten, ${untouched} untouched, ${failures.length} failures`
  );
  if (failures.length > 0) {
    console.error('FAILED to fully strip raw wiring from:');
    for (const f of failures) console.error(`  - ${f}`);
    process.exit(1);
  }
}

main();
