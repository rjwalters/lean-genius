#!/usr/bin/env npx tsx
/**
 * Build-time annotation processing
 *
 * This script is run during build to:
 * 1. Resolve anchor-based annotations to line numbers
 * 2. Validate line-based annotations (for non-migrated proofs)
 * 3. Generate resolved annotation files for the frontend
 *
 * Exit codes:
 *   0 - Success
 *   1 - Resolution/validation failures (build should fail)
 */

import * as fs from 'fs';
import * as path from 'path';
import { execSync } from 'node:child_process';
import { fileURLToPath } from 'url';
import { resolveAnnotations, resolveSections, validateLineAnnotations } from './resolver.js';
import type { SourceAnnotation, SourceSection, ResolvedAnnotation, ResolvedSection } from './types.js';
import { cacheDisabled, inputHashOf, recordRun, shouldSkip } from '../lib/build-cache.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const PROOFS_DATA_DIR = path.join(__dirname, '../../src/data/proofs');
const PROOFS_SOURCE_DIR = path.join(__dirname, '../../proofs/Proofs');
const REPO_ROOT = path.join(__dirname, '../..');
// Build-generated static asset tree (gitignored). Lean source is copied here so
// it can be fetched by slug at runtime instead of being pulled into the
// vite/Rollup module graph as a `?raw` import — the single biggest contributor
// to the ~40min build stall. See issue #20992 (build-perf phase 1).
const PUBLIC_PROOFS_DIR = path.join(__dirname, '../../public/data/proofs');

/**
 * Build a single-shot map of repo-relative path -> most-recent commit ISO
 * timestamp by running ONE `git log` over the two interesting trees instead
 * of one subprocess per listing.
 *
 * The map is keyed by both:
 *   1. Each touched file path (e.g. `src/data/proofs/erdos-12/meta.json`)
 *   2. Each ancestor directory of every touched file. This lets callers
 *      look up by directory (e.g. `src/data/proofs/erdos-12`) and get the
 *      latest touch under that subtree — matching the original semantics of
 *      `git log -- <dir>`.
 *
 * Returns undefined when git is unavailable; lookups then fall back to
 * undefined for every listing (same behavior as the previous per-call try/catch).
 *
 * Performance: trades ~2435 subprocess fork/execs for a single git log call
 * that returns in ~1-2 seconds on a warm git cache. See issue #20850.
 */
function buildTouchedMap(): Map<string, string> | undefined {
  try {
    const out = execSync(
      `git log --pretty=format:'%cI%x09%H' --name-only -- 'src/data/proofs/' 'proofs/Proofs/'`,
      {
        encoding: 'utf8',
        cwd: REPO_ROOT,
        stdio: ['ignore', 'pipe', 'ignore'],
        maxBuffer: 200 * 1024 * 1024,
      }
    );
    // Parse the stream. Format per commit:
    //   <iso>\t<sha>          <- header line
    //   path/to/file           <- one path per following line
    //   <blank>                <- separator before next commit
    // git log is newest-first, so the first time we see a path it IS the latest.
    const latest = new Map<string, string>();
    let currentTs: string | undefined;
    for (const line of out.split('\n')) {
      if (!line) continue;
      if (line.includes('\t')) {
        // Header: capture timestamp; sha is ignored.
        currentTs = line.split('\t', 1)[0];
        continue;
      }
      if (!currentTs) continue;
      // Record for the exact file path and every ancestor directory so that
      // a lookup by directory (the original lastTouched call pattern) returns
      // the latest touch anywhere under that subtree.
      let p = line;
      while (true) {
        if (!latest.has(p)) latest.set(p, currentTs);
        const slash = p.lastIndexOf('/');
        if (slash <= 0) break;
        p = p.slice(0, slash);
      }
    }
    return latest;
  } catch {
    return undefined;
  }
}

/**
 * Return the most recent commit ISO timestamp touching any of the supplied
 * repo-relative paths (files or directories), or undefined if no lookup hits.
 *
 * Uses the pre-built map from `buildTouchedMap()` to avoid per-call subprocesses.
 * Preserves the original semantics: when given a directory, returns the latest
 * commit touching anything under that subtree.
 */
function lastTouched(
  paths: string[],
  touched: Map<string, string> | undefined
): string | undefined {
  if (!touched || paths.length === 0) return undefined;
  let best: string | undefined;
  for (const p of paths) {
    const t = touched.get(p);
    if (t && (!best || t > best)) best = t;
  }
  return best;
}

interface ProofConfig {
  id: string;
  dataDir: string;
  leanPath: string;
  useAnchors: boolean;  // Whether this proof has been migrated to anchors
}

/**
 * Find all proofs and their configurations
 */
function discoverProofs(): ProofConfig[] {
  const proofs: ProofConfig[] = [];

  const proofDirs = fs.readdirSync(PROOFS_DATA_DIR).filter((d) => {
    const stat = fs.statSync(path.join(PROOFS_DATA_DIR, d));
    return stat.isDirectory();
  });

  for (const proofDir of proofDirs) {
    const dataDir = path.join(PROOFS_DATA_DIR, proofDir);
    const metaPath = path.join(dataDir, 'meta.json');

    if (!fs.existsSync(metaPath)) continue;

    const meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'));

    // Find the Lean source file
    let leanPath: string | null = null;

    // Check for proofRepoPath in meta
    if (meta.meta?.proofRepoPath) {
      leanPath = path.join(__dirname, '../../proofs', meta.meta.proofRepoPath);
    }

    // Fall back to naming convention
    if (!leanPath || !fs.existsSync(leanPath)) {
      // Convert kebab-case to PascalCase
      const pascalName = proofDir
        .split('-')
        .map((w) => w.charAt(0).toUpperCase() + w.slice(1))
        .join('');
      const candidatePath = path.join(PROOFS_SOURCE_DIR, `${pascalName}.lean`);
      if (fs.existsSync(candidatePath)) {
        leanPath = candidatePath;
      }
    }

    // Check for source.lean in data dir (fallback)
    if (!leanPath || !fs.existsSync(leanPath)) {
      const localSource = path.join(dataDir, 'source.lean');
      if (fs.existsSync(localSource)) {
        leanPath = localSource;
      }
    }

    if (!leanPath || !fs.existsSync(leanPath)) {
      console.warn(`Warning: No Lean source found for ${proofDir}`);
      continue;
    }

    // Check if this proof uses anchor-based annotations
    const hasAnchors = fs.existsSync(path.join(dataDir, 'annotations.source.json'));

    proofs.push({
      id: proofDir,
      dataDir,
      leanPath,
      useAnchors: hasAnchors,
    });
  }

  return proofs;
}

/**
 * Process a proof with anchor-based annotations
 */
function processAnchorBased(config: ProofConfig): { success: boolean; errors: string[] } {
  const errors: string[] = [];

  const sourcePath = path.join(config.dataDir, 'annotations.source.json');
  const outputPath = path.join(config.dataDir, 'annotations.json');

  const sourceAnnotations: SourceAnnotation[] = JSON.parse(fs.readFileSync(sourcePath, 'utf-8'));
  const leanSource = fs.readFileSync(config.leanPath, 'utf-8');

  // Resolve annotations
  const results = resolveAnnotations(sourceAnnotations, leanSource, config.leanPath);
  const resolved = results.filter((r) => r.resolved).map((r) => r.resolved as ResolvedAnnotation);
  const failed = results.filter((r) => r.error);

  for (const f of failed) {
    errors.push(`[${config.id}] Annotation "${f.annotation.id}": ${f.error}`);
  }

  // Check for sections in meta.json
  const metaPath = path.join(config.dataDir, 'meta.json');
  const meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'));

  if (meta.sourceSections) {
    const sectionResults = resolveSections(meta.sourceSections, leanSource, config.leanPath);
    for (const err of sectionResults.errors) {
      errors.push(`[${config.id}] ${err}`);
    }

    // Update meta.json with resolved sections
    meta.sections = sectionResults.resolved;
    delete meta.sourceSections;
    fs.writeFileSync(metaPath, JSON.stringify(meta, null, 2) + '\n');
  }

  // Write resolved annotations (without _anchor field for production)
  const cleanResolved = resolved.map(({ _anchor, ...rest }) => rest);
  fs.writeFileSync(outputPath, JSON.stringify(cleanResolved, null, 2) + '\n');

  return { success: errors.length === 0, errors };
}

/**
 * Process a proof with line-based annotations (validate only)
 */
function processLineBased(config: ProofConfig): { success: boolean; errors: string[] } {
  const errors: string[] = [];

  const annotationsPath = path.join(config.dataDir, 'annotations.json');
  if (!fs.existsSync(annotationsPath)) {
    return { success: true, errors: [] };
  }

  const result = validateLineAnnotations(annotationsPath, config.leanPath);

  for (const m of result.misaligned) {
    errors.push(`[${config.id}] Annotation "${m.id}": ${m.reason}`);
  }

  return { success: errors.length === 0, errors };
}

/**
 * Emit each proof's Lean source to the build-generated public asset tree at
 * `public/data/proofs/<slug>/source.lean`. At runtime the proof detail page
 * fetches this file by slug instead of importing it through the vite/Rollup
 * module graph (`*.lean?raw`). This removes ~1339 large raw-text modules from
 * the graph and is the core of the build-perf phase-1 fix. See issue #20992.
 *
 * `discoverProofs()` has already resolved each proof's `leanPath` (via the same
 * proofRepoPath -> naming-convention -> local source.lean fallback chain), so
 * we just copy that resolved file. Proofs with no resolvable Lean source were
 * already skipped/warned during discovery; here we additionally warn and skip
 * (never fail the build) on any copy error.
 */
function emitStaticSource(proofs: ProofConfig[]): void {
  let emitted = 0;
  let failed = 0;

  for (const proof of proofs) {
    try {
      if (!fs.existsSync(proof.leanPath)) {
        console.warn(`   ⚠ Lean source missing for ${proof.id} (${proof.leanPath}); skipping source.lean emit`);
        failed++;
        continue;
      }
      const destDir = path.join(PUBLIC_PROOFS_DIR, proof.id);
      fs.mkdirSync(destDir, { recursive: true });
      fs.copyFileSync(proof.leanPath, path.join(destDir, 'source.lean'));
      emitted++;
    } catch (e) {
      console.warn(`   ⚠ Failed to emit source.lean for ${proof.id}: ${e instanceof Error ? e.message : e}`);
      failed++;
    }
  }

  console.log(`\n📄 Emitted source.lean for ${emitted} proofs to public/data/proofs/ (${failed} skipped)`);
}

/**
 * Generate lightweight listings.json for HomePage
 */
function generateListings(proofs: ProofConfig[]): void {
  interface ProofListing {
    id: string;
    title: string;
    slug: string;
    description: string;
    status: 'verified' | 'pending' | 'disputed';
    badge?: string;
    tags: string[];
    dateAdded?: string;
    updatedAt?: string;
    wiedijkNumber?: number;
    hilbertNumber?: number;
    millenniumProblem?: string;
    erdosNumber?: number;
    mathlibCount?: number;
    sorries?: number;
    annotationCount: number;
  }

  const listings: ProofListing[] = [];

  // Pre-build the map of repo-relative path -> latest commit timestamp once,
  // up front. This is the critical perf fix: the previous implementation
  // spawned one `git log` per listing (~2435 subprocesses), which pushed
  // `pnpm build` past the 20-minute deploy cap. See issue #20850.
  const buildTouchedStart = Date.now();
  const touched = buildTouchedMap();
  const buildTouchedMs = Date.now() - buildTouchedStart;
  if (touched) {
    console.log(`   Built git touch map: ${touched.size} paths in ${buildTouchedMs}ms`);
  } else {
    console.log(`   Skipping git touch map (git unavailable); listings will have no updatedAt`);
  }

  for (const proof of proofs) {
    const metaPath = path.join(proof.dataDir, 'meta.json');
    const annotationsPath = path.join(proof.dataDir, 'annotations.json');

    if (!fs.existsSync(metaPath)) continue;

    const meta = JSON.parse(fs.readFileSync(metaPath, 'utf-8'));

    // Count annotations
    let annotationCount = 0;
    if (fs.existsSync(annotationsPath)) {
      const annotations = JSON.parse(fs.readFileSync(annotationsPath, 'utf-8'));
      annotationCount = Array.isArray(annotations) ? annotations.length : 0;
    }

    // Compute updatedAt: most recent commit touching either the proof's
    // data directory or its Lean source file. Both paths are repo-relative
    // and passed in a single git log invocation. Falls back to undefined if
    // git is unavailable or the proof was never committed.
    const dataDirRel = path.relative(REPO_ROOT, proof.dataDir);
    const trackedPaths: string[] = [dataDirRel];
    const proofRepoPath: string | undefined = meta.meta?.proofRepoPath;
    if (proofRepoPath) {
      trackedPaths.push(`proofs/${proofRepoPath}`);
    }
    const updatedAt = lastTouched(trackedPaths, touched);

    listings.push({
      id: meta.id || proof.id,
      title: meta.title || proof.id,
      slug: meta.slug || proof.id,
      description: meta.description || '',
      status: meta.meta?.status || 'pending',
      badge: meta.meta?.badge,
      tags: meta.meta?.tags || [],
      dateAdded: meta.meta?.dateAdded,
      updatedAt,
      wiedijkNumber: meta.meta?.wiedijkNumber,
      hilbertNumber: meta.meta?.hilbertNumber,
      millenniumProblem: meta.meta?.millenniumProblem,
      erdosNumber: meta.meta?.erdosNumber,
      mathlibCount: meta.meta?.mathlibDependencies?.length,
      sorries: meta.meta?.sorries,
      annotationCount,
    });
  }

  const outputPath = path.join(PROOFS_DATA_DIR, 'listings.json');
  fs.writeFileSync(outputPath, JSON.stringify(listings, null, 2) + '\n');
  console.log(`\n📋 Generated listings.json (${listings.length} proofs, ${Math.round(fs.statSync(outputPath).size / 1024)}KB)`);
}

/**
 * Compute a deterministic input-fingerprint for the annotation build.
 *
 * Inputs (per issue #22149 Strategy B):
 *   - Every meta.json and annotations.json under src/data/proofs/
 *   - Every Lean source under proofs/Proofs/
 *   - This script's own source (so logic changes invalidate the cache)
 *
 * Skipping is safe because the outputs (annotations.json files, listings.json,
 * public/data/proofs/<slug>/source.lean) are deterministic functions of these
 * inputs. The first run after `rm -rf .build-cache/` always executes fully.
 */
function computeInputHash(): string {
  return inputHashOf(
    {
      dirs: [
        { dir: PROOFS_DATA_DIR, suffixes: ['.json', '.lean'] },
        { dir: PROOFS_SOURCE_DIR, suffixes: ['.lean'] },
      ],
      files: [__filename],
    },
    REPO_ROOT
  );
}

/**
 * Main build function
 */
function build(options: { strict: boolean; verbose: boolean }): boolean {
  // Strategy B skip-gate: bail out fast when inputs are byte-for-byte
  // identical to the last successful run. This is the common case in the
  // deployer's persistent worktree, where most cycles change no proof data.
  const inputHash = cacheDisabled() ? '' : computeInputHash();
  if (!cacheDisabled() && shouldSkip('annotations-build', inputHash, REPO_ROOT)) {
    console.log('🔍 annotations:build — Cached — inputs unchanged since last run');
    return true;
  }

  console.log('🔍 Discovering proofs...');
  const proofs = discoverProofs();
  console.log(`   Found ${proofs.length} proofs\n`);

  const allErrors: string[] = [];
  let anchorProofs = 0;
  let lineProofs = 0;

  for (const proof of proofs) {
    if (options.verbose) {
      console.log(`Processing ${proof.id}...`);
    }

    if (proof.useAnchors) {
      anchorProofs++;
      const result = processAnchorBased(proof);
      allErrors.push(...result.errors);
      if (options.verbose && result.success) {
        console.log(`  ✓ Resolved anchor-based annotations`);
      }
    } else {
      lineProofs++;
      const result = processLineBased(proof);
      allErrors.push(...result.errors);
      if (options.verbose && result.success) {
        console.log(`  ✓ Validated line-based annotations`);
      }
    }
  }

  // Generate lightweight listings for HomePage
  generateListings(proofs);

  // Emit Lean source to the build-generated public asset tree (fetched by slug
  // at runtime instead of imported via `*.lean?raw`). See issue #20992.
  emitStaticSource(proofs);

  console.log(`\n📊 Summary:`);
  console.log(`   Anchor-based: ${anchorProofs} proofs`);
  console.log(`   Line-based:   ${lineProofs} proofs`);

  if (allErrors.length > 0) {
    console.log(`\n❌ ${allErrors.length} errors found:\n`);
    for (const err of allErrors) {
      console.log(`   ${err}`);
    }

    if (options.strict) {
      console.log(`\n💡 To fix these errors:`);
      console.log(`   1. Run: npx tsx scripts/annotations/resolver.ts migrate <annotations.json> <source.lean>`);
      console.log(`   2. Or manually update the line numbers in annotations.json`);
      return false;
    } else {
      console.log(`\n⚠️  Continuing despite errors (non-strict mode)`);
    }
  } else {
    console.log(`\n✅ All annotations validated successfully!`);
  }

  // Record successful completion so the next identical-inputs invocation
  // can skip. Failed runs (return false above) are intentionally NOT cached
  // so the next run retries from scratch.
  if (!cacheDisabled() && inputHash) {
    recordRun('annotations-build', inputHash, REPO_ROOT);
  }

  return true;
}

// CLI
const args = process.argv.slice(2);
const strict = args.includes('--strict');
const verbose = args.includes('--verbose') || args.includes('-v');

if (args.includes('--help') || args.includes('-h')) {
  console.log('Annotation Build Script');
  console.log('');
  console.log('Usage: npx tsx scripts/annotations/build.ts [options]');
  console.log('');
  console.log('Options:');
  console.log('  --strict    Fail build on any annotation errors');
  console.log('  --verbose   Show detailed processing info');
  console.log('  --help      Show this help');
  process.exit(0);
}

const success = build({ strict, verbose });
process.exit(success ? 0 : 1);
