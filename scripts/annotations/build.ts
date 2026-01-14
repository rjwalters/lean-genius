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
import { fileURLToPath } from 'url';
import { parseLeanFile, findConstructAtLine } from './lean-parser.js';
import { resolveAnnotations, resolveSections, validateLineAnnotations } from './resolver.js';
import type { SourceAnnotation, SourceSection, ResolvedAnnotation, ResolvedSection } from './types.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const PROOFS_DATA_DIR = path.join(__dirname, '../../src/data/proofs');
const PROOFS_SOURCE_DIR = path.join(__dirname, '../../proofs/Proofs');

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

    if (!leanPath) {
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

    listings.push({
      id: meta.id || proof.id,
      title: meta.title || proof.id,
      slug: meta.slug || proof.id,
      description: meta.description || '',
      status: meta.meta?.status || 'pending',
      badge: meta.meta?.badge,
      tags: meta.meta?.tags || [],
      dateAdded: meta.meta?.dateAdded,
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
 * Main build function
 */
function build(options: { strict: boolean; verbose: boolean }): boolean {
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
