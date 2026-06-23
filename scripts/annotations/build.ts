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
import { createHash } from 'node:crypto';
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
 *
 * Per-proof incremental caching (issue #22150): when the destination already
 * exists and its mtime is at least the git-commit timestamp of the Lean
 * source, the copy is skipped. We pin the destination's mtime to the git
 * commit time (not wall-clock) on every emit so the comparison is meaningful
 * across `git checkout` and fresh-worktree creation — both of which produce
 * arbitrary disk mtimes that do not reflect content changes. Note: when the
 * whole-script input-hash cache (issue #22149) short-circuits the build, this
 * function isn't called at all; the incremental skip below kicks in on cache
 * MISSES where only a subset of proofs actually changed (e.g. 5 of 2435).
 *
 * Fallback policy: if `touchedMap` lookup misses (e.g. brand-new uncommitted
 * Lean file not yet in `git log`), or if no touchedMap is available, we
 * unconditionally copy. Over-copying is safer than under-emitting.
 */
function emitStaticSource(
  proofs: ProofConfig[],
  touchedMap: Map<string, string> | undefined
): void {
  let updated = 0;
  let cached = 0;
  let skipped = 0;

  for (const proof of proofs) {
    try {
      if (!fs.existsSync(proof.leanPath)) {
        console.warn(`   ⚠ Lean source missing for ${proof.id} (${proof.leanPath}); skipping source.lean emit`);
        skipped++;
        continue;
      }
      const destDir = path.join(PUBLIC_PROOFS_DIR, proof.id);
      const destPath = path.join(destDir, 'source.lean');

      // Look up the git commit timestamp for the Lean source path. The map
      // is keyed by repo-relative paths, so we convert the absolute leanPath
      // here. A miss returns undefined (brand-new file, git unavailable,
      // etc.) which is handled below as "always copy".
      const leanRel = path.relative(REPO_ROOT, proof.leanPath);
      const sourceTouchedAt = touchedMap?.get(leanRel);

      // Skip-when-fresh check: destination exists AND its mtime is at least
      // the source's git commit timestamp. We use throwIfNoEntry:false so a
      // missing destination cleanly falls through to the copy path.
      const destStat = fs.statSync(destPath, { throwIfNoEntry: false });
      if (destStat && sourceTouchedAt) {
        const destMtimeIso = new Date(destStat.mtime).toISOString();
        if (destMtimeIso >= sourceTouchedAt) {
          cached++;
          continue;
        }
      }

      fs.mkdirSync(destDir, { recursive: true });
      fs.copyFileSync(proof.leanPath, destPath);

      // Pin the destination's mtime to the source's git commit timestamp so
      // the next run can make a meaningful skip decision. Without this pin,
      // the destination's mtime would be the wall-clock time of THIS copy,
      // which always exceeds the source's commit timestamp — making the
      // skip path correct by accident. The pin makes it correct by design,
      // and also makes the file robust to `git checkout` (which would
      // otherwise reset the SOURCE's disk mtime and break comparisons).
      if (sourceTouchedAt) {
        const touchedDate = new Date(sourceTouchedAt);
        if (!Number.isNaN(touchedDate.getTime())) {
          try {
            fs.utimesSync(destPath, new Date(), touchedDate);
          } catch {
            // Non-fatal: missing utimes support shouldn't break the build.
          }
        }
      }
      updated++;
    } catch (e) {
      console.warn(`   ⚠ Failed to emit source.lean for ${proof.id}: ${e instanceof Error ? e.message : e}`);
      skipped++;
    }
  }

  console.log(`\n📄 Emitted source.lean: ${updated} updated, ${cached} cached, ${skipped} skipped`);
}

/**
 * Compute the first 8 hex chars of sha256 over a file's contents. Used as the
 * `?v=<hash>` cache-buster in the runtime data manifest so that any edit to a
 * proof's meta/annotations/source busts CDN + browser caches on the next
 * deploy. 8 chars = 32 bits of entropy — comfortably more than enough for the
 * <3000 proof × 3 files = <10K unique values at stake.
 */
function sha8(filePath: string): string {
  const h = createHash('sha256');
  h.update(fs.readFileSync(filePath));
  return h.digest('hex').slice(0, 8);
}

/**
 * Emit each proof's meta.json + annotations.json to the build-generated public
 * asset tree at `public/data/proofs/<slug>/`. The runtime loader in
 * `src/data/proofs/index.ts` fetches these by slug instead of importing them
 * through the vite/Rollup module graph. This collapses ~7300 per-proof data
 * modules (2435 index.ts shims + 2435 meta.json + 2435 annotations.json)
 * down to a handful of app modules, restoring the build toward its documented
 * ~5–10s vite stage baseline and making it O(1) in gallery size. See issue
 * #20993 (build-perf phase 2).
 *
 * Per-proof incremental caching: same touchedMap pattern as `emitStaticSource()`.
 * When the destination already exists and its mtime is at least the git-commit
 * timestamp of the source data dir, the copy is skipped. We pin the destination's
 * mtime to the git commit time so the comparison stays meaningful across
 * `git checkout` and fresh-worktree creation. Note: when the whole-script
 * input-hash cache (issue #22149) short-circuits the build, this function is
 * not called at all; the incremental skip below kicks in on cache MISSES
 * where only a subset of proofs actually changed.
 *
 * Fallback policy: if `touchedMap` lookup misses (e.g. brand-new uncommitted
 * file not yet in `git log`), or if no touchedMap is available, we
 * unconditionally copy. Over-copying is safer than under-emitting.
 *
 * Returns nothing; the manifest emit step reads the destination files
 * directly to compute hashes.
 */
function emitStaticData(
  proofs: ProofConfig[],
  touchedMap: Map<string, string> | undefined
): void {
  let updated = 0;
  let cached = 0;
  let skipped = 0;

  for (const proof of proofs) {
    try {
      const srcMeta = path.join(proof.dataDir, 'meta.json');
      const srcAnn = path.join(proof.dataDir, 'annotations.json');
      const destDir = path.join(PUBLIC_PROOFS_DIR, proof.id);
      const destMeta = path.join(destDir, 'meta.json');
      const destAnn = path.join(destDir, 'annotations.json');

      // Look up the git commit timestamp for the proof's data dir. The map
      // is keyed by repo-relative paths.
      const dataDirRel = path.relative(REPO_ROOT, proof.dataDir);
      const dataTouchedAt = touchedMap?.get(dataDirRel);

      // Skip-when-fresh check: for each source file, the destination exists
      // AND its mtime is at least max(git-commit-ts-of-dir, source-disk-mtime).
      // Including the source's disk mtime catches uncommitted local edits to
      // a tracked file (e.g. an enricher run that hasn't committed yet, or a
      // cache-bust verification edit). Without it, the skip would wrongly
      // pass through on local edits that haven't reached git yet.
      const metaSrcStat = fs.existsSync(srcMeta) ? fs.statSync(srcMeta) : undefined;
      const annSrcStat = fs.existsSync(srcAnn) ? fs.statSync(srcAnn) : undefined;
      const metaDestStat = metaSrcStat ? fs.statSync(destMeta, { throwIfNoEntry: false }) : undefined;
      const annDestStat = annSrcStat ? fs.statSync(destAnn, { throwIfNoEntry: false }) : undefined;

      const metaFresh = !metaSrcStat || (
        metaDestStat &&
        metaDestStat.mtime.getTime() >= metaSrcStat.mtime.getTime() &&
        (!dataTouchedAt || metaDestStat.mtime.toISOString() >= dataTouchedAt)
      );
      const annFresh = !annSrcStat || (
        annDestStat &&
        annDestStat.mtime.getTime() >= annSrcStat.mtime.getTime() &&
        (!dataTouchedAt || annDestStat.mtime.toISOString() >= dataTouchedAt)
      );

      if (metaFresh && annFresh) {
        cached++;
        continue;
      }

      fs.mkdirSync(destDir, { recursive: true });

      // Copy meta.json
      if (fs.existsSync(srcMeta)) {
        fs.copyFileSync(srcMeta, destMeta);
        if (dataTouchedAt) {
          const touchedDate = new Date(dataTouchedAt);
          if (!Number.isNaN(touchedDate.getTime())) {
            try {
              fs.utimesSync(destMeta, new Date(), touchedDate);
            } catch {
              // Non-fatal: missing utimes support shouldn't break the build.
            }
          }
        }
      }

      // Copy annotations.json (it's optional — some proofs have no annotations)
      if (fs.existsSync(srcAnn)) {
        fs.copyFileSync(srcAnn, destAnn);
        if (dataTouchedAt) {
          const touchedDate = new Date(dataTouchedAt);
          if (!Number.isNaN(touchedDate.getTime())) {
            try {
              fs.utimesSync(destAnn, new Date(), touchedDate);
            } catch {
              // Non-fatal.
            }
          }
        }
      }

      updated++;
    } catch (e) {
      console.warn(`   ⚠ Failed to emit static data for ${proof.id}: ${e instanceof Error ? e.message : e}`);
      skipped++;
    }
  }

  console.log(`📦 Emitted meta+annotations: ${updated} updated, ${cached} cached, ${skipped} skipped`);
}

/**
 * Emit `src/data/proofs/data-manifest.json` — a small JSON map of
 * `{ slug: { meta: <sha8>, ann: <sha8>, src: <sha8> } }` consumed by the
 * runtime loader to generate `?v=<hash>` query params on each fetch.
 *
 * This is the ONLY per-proof data still imported into the vite/Rollup module
 * graph after phase 2. It's a single module (~2435 short entries; under
 * ~200KB), bundled with normal content-hashing, so a deploy that changes any
 * proof busts the importing chunk hash automatically.
 *
 * The manifest is computed AFTER emissions complete (so it reflects the
 * latest state). Hashes are read from the destinations under `public/data/`
 * because those are the bytes the runtime will actually serve.
 *
 * If the on-disk manifest matches what we'd write byte-for-byte, we skip the
 * write to avoid pointlessly invalidating the manifest chunk's content hash
 * on no-op builds.
 *
 * Sort order: keys are sorted lexicographically for cross-platform determinism.
 */
function emitDataManifest(proofs: ProofConfig[]): boolean {
  type ManifestEntry = { meta: string; ann: string; src: string };
  const manifest: Record<string, ManifestEntry> = {};

  // Sort proof IDs for deterministic output
  const sorted = [...proofs].sort((a, b) => (a.id < b.id ? -1 : a.id > b.id ? 1 : 0));

  for (const proof of sorted) {
    const destDir = path.join(PUBLIC_PROOFS_DIR, proof.id);
    const destMeta = path.join(destDir, 'meta.json');
    const destAnn = path.join(destDir, 'annotations.json');
    const destSrc = path.join(destDir, 'source.lean');

    const entry: ManifestEntry = {
      meta: fs.existsSync(destMeta) ? sha8(destMeta) : '',
      ann: fs.existsSync(destAnn) ? sha8(destAnn) : '',
      src: fs.existsSync(destSrc) ? sha8(destSrc) : '',
    };
    manifest[proof.id] = entry;
  }

  const manifestPath = path.join(PROOFS_DATA_DIR, 'data-manifest.json');
  const next = JSON.stringify(manifest, null, 2) + '\n';

  // No-op write avoidance: keeps the manifest's chunk content hash stable
  // across builds that genuinely changed nothing.
  if (fs.existsSync(manifestPath)) {
    const prior = fs.readFileSync(manifestPath, 'utf-8');
    if (prior === next) {
      console.log(`🗂  data-manifest.json unchanged (${sorted.length} proofs)`);
      return false;
    }
  }

  fs.writeFileSync(manifestPath, next);
  console.log(`🗂  data-manifest.json written (${sorted.length} proofs, ${Math.round(fs.statSync(manifestPath).size / 1024)}KB)`);
  return true;
}

/**
 * Generate lightweight listings.json for HomePage. Accepts a pre-built
 * touchedMap so callers can share it with `emitStaticSource()` rather than
 * paying for two passes over the (large) `git log` output. See issue #22150.
 */
function generateListings(
  proofs: ProofConfig[],
  touched: Map<string, string> | undefined
): void {
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

  // Pre-build the map of repo-relative path -> latest commit timestamp once,
  // up front. This is the critical perf fix: the previous implementation
  // spawned one `git log` per listing (~2435 subprocesses), which pushed
  // `pnpm build` past the 20-minute deploy cap. See issue #20850. The same
  // map drives the incremental skip in `emitStaticSource()` (issue #22150),
  // so we share it across both consumers rather than building it twice.
  const buildTouchedStart = Date.now();
  const touched = buildTouchedMap();
  const buildTouchedMs = Date.now() - buildTouchedStart;
  if (touched) {
    console.log(`   Built git touch map: ${touched.size} paths in ${buildTouchedMs}ms`);
  } else {
    console.log(`   Skipping git touch map (git unavailable); listings will have no updatedAt and source.lean will always re-emit`);
  }

  // Generate lightweight listings for HomePage
  generateListings(proofs, touched);

  // Emit Lean source to the build-generated public asset tree (fetched by slug
  // at runtime instead of imported via `*.lean?raw`). See issue #20992. With
  // touchedMap, this is now incremental — unchanged proofs are skipped via
  // mtime comparison. See issue #22150.
  emitStaticSource(proofs, touched);

  // Emit each proof's meta.json + annotations.json to public/data/proofs/<slug>/
  // (phase-2 sibling of source.lean). The runtime loader fetches them by slug
  // instead of importing through `import.meta.glob`. See issue #20993.
  emitStaticData(proofs, touched);

  // Emit the hashed manifest that the runtime loader imports. This is the
  // ONLY per-proof data still in the vite module graph after phase 2 (one
  // small module, ~2435 short entries). See issue #20993.
  emitDataManifest(proofs);

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
