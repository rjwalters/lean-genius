#!/usr/bin/env npx tsx
/**
 * Fix common anchor issues in source annotation files
 *
 * Common issues:
 * - Pattern anchors with -- line comments (not parsed)
 * - Empty doc-comment anchors
 * - Pattern anchors that don't match
 */

import * as fs from 'fs';
import * as path from 'path';
import { parseLeanFile, findByAnchor } from './lean-parser.js';
import type { SourceAnnotation, AnnotationAnchor, ParsedLeanFile, LeanConstruct } from './types.js';

const PROOFS_DATA_DIR = 'src/data/proofs';

interface FixResult {
  proofId: string;
  fixed: number;
  unfixable: string[];
}

function findNearestDeclaration(parsed: ParsedLeanFile, lineNum: number): LeanConstruct | null {
  // Find declaration closest to or containing the line
  let best: LeanConstruct | null = null;
  let bestDistance = Infinity;

  for (const c of parsed.constructs) {
    if (c.type !== 'declaration') continue;

    const start = c.docCommentStart ?? c.startLine;
    const end = c.endLine;

    // If line is within the construct
    if (lineNum >= start && lineNum <= end) {
      return c;
    }

    // Find closest
    const distance = Math.min(Math.abs(lineNum - start), Math.abs(lineNum - end));
    if (distance < bestDistance) {
      bestDistance = distance;
      best = c;
    }
  }

  return bestDistance <= 10 ? best : null;
}

function fixAnchor(
  anchor: AnnotationAnchor,
  parsed: ParsedLeanFile,
  originalRange?: { startLine: number; endLine: number }
): AnnotationAnchor | null {
  // Check if current anchor resolves
  const resolved = findByAnchor(parsed, anchor);
  if (resolved) return anchor;  // Already works

  // Try to fix based on anchor type
  if (anchor.type === 'pattern') {
    // Pattern anchors often fail - try to find a nearby declaration
    // Extract line number hint from the pattern if we have original range
    if (originalRange) {
      const decl = findNearestDeclaration(parsed, originalRange.startLine);
      if (decl && decl.name) {
        return {
          type: 'declaration',
          name: decl.name,
          kind: decl.kind,
        };
      }
    }
  }

  if (anchor.type === 'doc-comment' && !anchor.contains) {
    // Empty doc-comment - can't fix without more info
    return null;
  }

  return null;
}

function fixProof(proofDir: string, leanPath: string): FixResult {
  const sourceFile = path.join(proofDir, 'annotations.source.json');
  const originalFile = path.join(proofDir, 'annotations.json');

  if (!fs.existsSync(sourceFile)) {
    return { proofId: path.basename(proofDir), fixed: 0, unfixable: [] };
  }

  const leanSource = fs.readFileSync(leanPath, 'utf-8');
  const parsed = parseLeanFile(leanSource, leanPath);

  const annotations: SourceAnnotation[] = JSON.parse(fs.readFileSync(sourceFile, 'utf-8'));

  // Try to get original line ranges for hints
  let originalRanges: Map<string, { startLine: number; endLine: number }> = new Map();
  if (fs.existsSync(originalFile)) {
    try {
      const original = JSON.parse(fs.readFileSync(originalFile, 'utf-8'));
      for (const ann of original) {
        if (ann.range) {
          originalRanges.set(ann.id, ann.range);
        }
      }
    } catch {}
  }

  let fixed = 0;
  const unfixable: string[] = [];

  for (const ann of annotations) {
    const resolved = findByAnchor(parsed, ann.anchor);
    if (resolved) continue;  // Already works

    const originalRange = originalRanges.get(ann.id);
    const fixedAnchor = fixAnchor(ann.anchor, parsed, originalRange);

    if (fixedAnchor) {
      ann.anchor = fixedAnchor;
      fixed++;
    } else {
      unfixable.push(ann.id);
    }
  }

  if (fixed > 0) {
    fs.writeFileSync(sourceFile, JSON.stringify(annotations, null, 2) + '\n');
  }

  return {
    proofId: path.basename(proofDir),
    fixed,
    unfixable,
  };
}

// Main
const mappings = fs.readFileSync('/tmp/proof_mappings.txt', 'utf-8')
  .trim().split('\n')
  .map(line => {
    const [dir, lean] = line.split('|');
    return { dir, lean };
  });

console.log('Fixing anchor issues...\n');

let totalFixed = 0;
let totalUnfixable = 0;

for (const { dir, lean } of mappings) {
  const proofDir = path.join(PROOFS_DATA_DIR, dir);
  const leanPath = `proofs/Proofs/${lean}.lean`;

  if (!fs.existsSync(leanPath)) continue;

  const result = fixProof(proofDir, leanPath);

  if (result.fixed > 0 || result.unfixable.length > 0) {
    console.log(`${result.proofId}: ${result.fixed} fixed, ${result.unfixable.length} unfixable`);
    if (result.unfixable.length > 0) {
      console.log(`  Unfixable: ${result.unfixable.join(', ')}`);
    }
  }

  totalFixed += result.fixed;
  totalUnfixable += result.unfixable.length;
}

console.log(`\nTotal: ${totalFixed} fixed, ${totalUnfixable} unfixable`);
