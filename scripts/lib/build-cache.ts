/**
 * Build cache helpers — Strategy B per-script skip gates.
 *
 * The deployer runs `pnpm build` every cycle (~35s) but most cycles change
 * <10 files out of ~12,000. These helpers let each per-stage script hash its
 * inputs and skip the heavy work when the hash matches the prior run, while
 * still always producing the same outputs on cache miss.
 *
 * Cache layout (gitignored):
 *   .build-cache/<script-name>.hash    Single line: sha256 hex of inputs.
 *
 * Correctness:
 *   - We hash file CONTENT, not mtime. `git checkout` and worktree creation
 *     produce fresh mtimes that don't reflect content changes; mtime caching
 *     would silently produce wrong skip decisions. Content hashing is a few
 *     hundred ms for ~3500 small JSON+Lean files — well within budget.
 *   - File paths are sorted before hashing for determinism across platforms
 *     and FS readdir orders.
 *   - The cache key includes each path so a renamed-but-identical file
 *     correctly invalidates.
 *
 * See issue #22149.
 */

import { createHash } from 'node:crypto';
import * as fs from 'node:fs';
import * as path from 'node:path';

/** Directory (relative to CWD / repo root) where per-script hashes are stored. */
export const CACHE_DIR = '.build-cache';

/**
 * Recursively collect all files under `dir` matching the provided suffix
 * predicate. Returns absolute paths.
 *
 * Skips dot-prefixed directories (e.g. .git, .build-cache) and `node_modules`
 * so the walk stays bounded.
 */
function walk(dir: string, accept: (relPath: string) => boolean, out: string[] = []): string[] {
  let entries: fs.Dirent[];
  try {
    entries = fs.readdirSync(dir, { withFileTypes: true });
  } catch {
    return out;
  }
  for (const ent of entries) {
    if (ent.name.startsWith('.')) continue;
    if (ent.name === 'node_modules') continue;
    const full = path.join(dir, ent.name);
    if (ent.isDirectory()) {
      walk(full, accept, out);
    } else if (ent.isFile() && accept(full)) {
      out.push(full);
    }
  }
  return out;
}

/**
 * Collect the absolute file paths matched by the supplied spec.
 *
 * Spec entries:
 *   - { dir, suffixes }  — recursive walk under dir, keep files whose name
 *                          ends with any provided suffix
 *   - { file }           — explicit single file (skipped if missing)
 */
export interface FileSetSpec {
  /** One or more directory walks. */
  dirs?: Array<{ dir: string; suffixes: string[] }>;
  /** Explicit files to also include. */
  files?: string[];
}

export function collectFiles(spec: FileSetSpec): string[] {
  const out: string[] = [];
  for (const d of spec.dirs ?? []) {
    if (!fs.existsSync(d.dir)) continue;
    walk(d.dir, (p) => d.suffixes.some((s) => p.endsWith(s)), out);
  }
  for (const f of spec.files ?? []) {
    if (fs.existsSync(f)) out.push(f);
  }
  return out;
}

/**
 * Compute a deterministic sha256 hash of the contents (and relative paths)
 * of the supplied files.
 *
 * `repoRoot` is used to convert each absolute path to a stable repo-relative
 * path so the hash is portable across worktree locations.
 */
export function hashFiles(files: string[], repoRoot: string): string {
  const h = createHash('sha256');
  // Sort by repo-relative path for determinism (readdir order is not stable
  // across filesystems).
  const sorted = files
    .map((f) => ({ abs: f, rel: path.relative(repoRoot, f) }))
    .sort((a, b) => (a.rel < b.rel ? -1 : a.rel > b.rel ? 1 : 0));

  for (const { abs, rel } of sorted) {
    h.update(rel);
    h.update('\0');
    try {
      h.update(fs.readFileSync(abs));
    } catch {
      // File vanished between collect + read — treat as "modified" by mixing
      // a sentinel into the hash so the next run re-evaluates.
      h.update('<missing>');
    }
    h.update('\0');
  }
  return h.digest('hex');
}

/**
 * Convenience wrapper: collect + hash in one call.
 */
export function inputHashOf(spec: FileSetSpec, repoRoot: string): string {
  return hashFiles(collectFiles(spec), repoRoot);
}

/**
 * Resolve cache directory. By default it lives at `<repoRoot>/.build-cache`
 * so multiple worktrees of the same repo each maintain their own cache (the
 * deployer's persistent worktree is what we're optimizing for).
 */
function cacheDirFor(repoRoot: string): string {
  return path.join(repoRoot, CACHE_DIR);
}

function cachePathFor(repoRoot: string, scriptName: string): string {
  return path.join(cacheDirFor(repoRoot), `${scriptName}.hash`);
}

/**
 * Returns true if the prior recorded hash for `scriptName` exactly matches
 * the supplied `inputHash`. Any read error (missing file, permission, etc.)
 * returns false so the script proceeds normally — fresh worktrees never
 * false-skip.
 */
export function shouldSkip(scriptName: string, inputHash: string, repoRoot: string): boolean {
  try {
    const prior = fs.readFileSync(cachePathFor(repoRoot, scriptName), 'utf8').trim();
    return prior === inputHash;
  } catch {
    return false;
  }
}

/**
 * Record that `scriptName` completed successfully against `inputHash`. Best
 * effort — write errors are logged to stderr but do not fail the build.
 */
export function recordRun(scriptName: string, inputHash: string, repoRoot: string): void {
  try {
    fs.mkdirSync(cacheDirFor(repoRoot), { recursive: true });
    fs.writeFileSync(cachePathFor(repoRoot, scriptName), inputHash + '\n');
  } catch (e) {
    console.warn(
      `   ⚠ build-cache: failed to record hash for ${scriptName}: ${e instanceof Error ? e.message : e}`
    );
  }
}

/**
 * Returns true if the env var `DISABLE_BUILD_CACHE=1` is set, allowing the
 * caller to bypass skip-gates. Mirrors the SKIP_* knobs in sync-and-deploy.sh.
 */
export function cacheDisabled(): boolean {
  return process.env.DISABLE_BUILD_CACHE === '1';
}
