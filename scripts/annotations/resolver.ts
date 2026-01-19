/**
 * Annotation Resolver
 *
 * Resolves anchor-based annotations to line numbers at build time.
 * This is the core of the annotation alignment system.
 */

import * as fs from 'fs';
import * as path from 'path';
import {
  parseLeanFile,
  findByAnchor,
  findConstructAtLine,
  generateAnchor,
} from './lean-parser.js';
import type {
  SourceAnnotation,
  ResolvedAnnotation,
  SourceSection,
  ResolvedSection,
  AnnotationAnchor,
  ResolutionResult,
  ResolutionReport,
  ParsedLeanFile,
  LeanConstruct,
} from './types.js';

/**
 * Resolve a single annotation anchor to line numbers
 */
export function resolveAnchor(
  parsed: ParsedLeanFile,
  anchor: AnnotationAnchor
): { startLine: number; endLine: number } | null {
  const construct = findByAnchor(parsed, anchor);
  if (!construct) return null;

  let startLine = construct.startLine;
  let endLine = construct.endLine;

  // Include doc comment if requested (default true for declarations)
  if (
    construct.type === 'declaration' &&
    anchor.includeDocComment !== false &&
    construct.docCommentStart
  ) {
    startLine = construct.docCommentStart;
  }

  // Apply extensions
  if (anchor.extendBefore) {
    startLine = Math.max(1, startLine - anchor.extendBefore);
  }
  if (anchor.extendAfter) {
    endLine = Math.min(parsed.lines.length, endLine + anchor.extendAfter);
  }

  return { startLine, endLine };
}

/**
 * Resolve all annotations for a proof
 */
export function resolveAnnotations(
  sourceAnnotations: SourceAnnotation[],
  leanSource: string,
  leanPath: string
): ResolutionResult[] {
  const parsed = parseLeanFile(leanSource, leanPath);
  const results: ResolutionResult[] = [];

  for (const annotation of sourceAnnotations) {
    const range = resolveAnchor(parsed, annotation.anchor);

    if (range) {
      results.push({
        annotation,
        resolved: {
          id: annotation.id,
          proofId: annotation.proofId,
          range,
          type: annotation.type,
          title: annotation.title,
          content: annotation.content,
          mathContext: annotation.mathContext,
          significance: annotation.significance,
          prerequisites: annotation.prerequisites,
          relatedConcepts: annotation.relatedConcepts,
          _anchor: annotation.anchor,
        },
      });
    } else {
      results.push({
        annotation,
        error: `Could not resolve anchor: ${JSON.stringify(annotation.anchor)}`,
      });
    }
  }

  return results;
}

/**
 * Resolve sections with anchors
 */
export function resolveSections(
  sourceSections: SourceSection[],
  leanSource: string,
  leanPath: string
): { resolved: ResolvedSection[]; errors: string[] } {
  const parsed = parseLeanFile(leanSource, leanPath);
  const resolved: ResolvedSection[] = [];
  const errors: string[] = [];

  for (const section of sourceSections) {
    const range = resolveAnchor(parsed, section.anchor);

    if (range) {
      resolved.push({
        id: section.id,
        title: section.title,
        startLine: range.startLine,
        endLine: range.endLine,
        summary: section.summary,
        _anchor: section.anchor,
      });
    } else {
      errors.push(`Section "${section.id}": Could not resolve anchor: ${JSON.stringify(section.anchor)}`);
    }
  }

  return { resolved, errors };
}

/**
 * Generate a full resolution report for a proof
 */
export function generateReport(
  proofId: string,
  sourceAnnotations: SourceAnnotation[],
  sourceSections: SourceSection[] | undefined,
  leanSource: string,
  leanPath: string
): ResolutionReport {
  const annotationResults = resolveAnnotations(sourceAnnotations, leanSource, leanPath);

  const report: ResolutionReport = {
    proofId,
    sourcePath: leanPath,
    totalAnnotations: sourceAnnotations.length,
    resolved: annotationResults.filter((r) => r.resolved).length,
    failed: annotationResults.filter((r) => r.error).length,
    results: annotationResults,
  };

  if (sourceSections) {
    const sectionResults = resolveSections(sourceSections, leanSource, leanPath);
    report.sections = {
      total: sourceSections.length,
      resolved: sectionResults.resolved.length,
      failed: sectionResults.errors.length,
    };
  }

  return report;
}

/**
 * Convert existing line-based annotation to anchor-based
 */
export function migrateAnnotationToAnchor(
  annotation: { range: { startLine: number; endLine: number } },
  leanSource: string,
  leanPath: string
): AnnotationAnchor | null {
  const parsed = parseLeanFile(leanSource, leanPath);

  // Find construct at the start line
  const construct = findConstructAtLine(parsed, annotation.range.startLine);
  if (!construct) {
    // Fall back to pattern-based anchor
    const lines = parsed.lines.slice(
      annotation.range.startLine - 1,
      annotation.range.endLine
    );
    const firstLine = lines[0]?.trim();
    if (firstLine && firstLine.length > 5) {
      return {
        type: 'pattern',
        pattern: escapeRegex(firstLine.slice(0, 40)),
      };
    }
    return null;
  }

  return generateAnchor(construct) as AnnotationAnchor;
}

/**
 * Migrate all annotations in a file from line-based to anchor-based
 */
export function migrateAnnotationsFile(
  annotationsPath: string,
  leanSourcePath: string
): { migrated: SourceAnnotation[]; failures: { id: string; error: string }[] } {
  const annotationsJson = JSON.parse(fs.readFileSync(annotationsPath, 'utf-8'));
  const leanSource = fs.readFileSync(leanSourcePath, 'utf-8');

  const migrated: SourceAnnotation[] = [];
  const failures: { id: string; error: string }[] = [];

  for (const ann of annotationsJson) {
    if (!ann.range) {
      failures.push({ id: ann.id, error: 'No range field' });
      continue;
    }

    const anchor = migrateAnnotationToAnchor(ann, leanSource, leanSourcePath);
    if (!anchor) {
      failures.push({ id: ann.id, error: `Could not generate anchor for lines ${ann.range.startLine}-${ann.range.endLine}` });
      continue;
    }

    migrated.push({
      id: ann.id,
      proofId: ann.proofId,
      anchor,
      type: ann.type,
      title: ann.title,
      content: ann.content,
      mathContext: ann.mathContext,
      significance: ann.significance,
      prerequisites: ann.prerequisites,
      relatedConcepts: ann.relatedConcepts,
    });
  }

  return { migrated, failures };
}

/**
 * Validate existing line-based annotations against current source
 * Returns annotations that are misaligned
 */
export function validateLineAnnotations(
  annotationsPath: string,
  leanSourcePath: string
): { valid: number; misaligned: { id: string; reason: string }[] } {
  const annotationsJson = JSON.parse(fs.readFileSync(annotationsPath, 'utf-8'));
  const leanSource = fs.readFileSync(leanSourcePath, 'utf-8');
  const parsed = parseLeanFile(leanSource, leanSourcePath);

  let valid = 0;
  const misaligned: { id: string; reason: string }[] = [];

  for (const ann of annotationsJson) {
    if (!ann.range) continue;

    const { startLine, endLine } = ann.range;

    // Check if lines exist
    if (startLine < 1 || endLine > parsed.lines.length) {
      misaligned.push({
        id: ann.id,
        reason: `Lines ${startLine}-${endLine} out of bounds (file has ${parsed.lines.length} lines)`,
      });
      continue;
    }

    // Check if there's a meaningful construct at these lines
    const construct = findConstructAtLine(parsed, startLine);
    if (!construct) {
      misaligned.push({
        id: ann.id,
        reason: `No Lean construct found at line ${startLine}`,
      });
      continue;
    }

    // Check if the construct matches what we expect based on annotation type
    // Note: 'example' is an anonymous theorem, so we allow 'theorem' type annotations to match
    const typeMatches =
      (ann.type === 'theorem' && (construct.kind === 'theorem' || construct.kind === 'example')) ||
      (ann.type === 'lemma' && construct.kind === 'lemma') ||
      (ann.type === 'definition' && (construct.kind === 'def' || construct.kind === 'abbrev' || construct.kind === 'structure')) ||
      (ann.type === 'axiom' && construct.kind === 'axiom') ||
      (ann.type === 'inductive' && construct.kind === 'inductive') ||
      (ann.type === 'structure' && construct.kind === 'structure') ||
      (ann.type === 'def' && construct.kind === 'def') ||
      (ann.type === 'example' && construct.kind === 'example') ||
      ann.type === 'concept' ||
      ann.type === 'insight' ||
      ann.type === 'tactic' ||
      ann.type === 'warning';

    if (!typeMatches && construct.type === 'declaration') {
      misaligned.push({
        id: ann.id,
        reason: `Annotation type "${ann.type}" but found "${construct.kind}" at line ${startLine}`,
      });
      continue;
    }

    valid++;
  }

  return { valid, misaligned };
}

function escapeRegex(str: string): string {
  return str.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

// CLI interface
function main() {
  const args = process.argv.slice(2);
  const command = args[0];

  if (command === 'validate') {
    // Validate line-based annotations
    const annotationsPath = args[1];
    const leanPath = args[2];

    if (!annotationsPath || !leanPath) {
      console.error('Usage: resolver.ts validate <annotations.json> <source.lean>');
      process.exit(1);
    }

    const result = validateLineAnnotations(annotationsPath, leanPath);
    console.log(`Validation results:`);
    console.log(`  Valid: ${result.valid}`);
    console.log(`  Misaligned: ${result.misaligned.length}`);

    if (result.misaligned.length > 0) {
      console.log('\nMisaligned annotations:');
      for (const m of result.misaligned) {
        console.log(`  - ${m.id}: ${m.reason}`);
      }
      process.exit(1);
    }
  } else if (command === 'migrate') {
    // Migrate to anchor-based format
    const annotationsPath = args[1];
    const leanPath = args[2];
    const outputPath = args[3];

    if (!annotationsPath || !leanPath) {
      console.error('Usage: resolver.ts migrate <annotations.json> <source.lean> [output.json]');
      process.exit(1);
    }

    const result = migrateAnnotationsFile(annotationsPath, leanPath);
    console.log(`Migration results:`);
    console.log(`  Migrated: ${result.migrated.length}`);
    console.log(`  Failed: ${result.failures.length}`);

    if (result.failures.length > 0) {
      console.log('\nFailed migrations:');
      for (const f of result.failures) {
        console.log(`  - ${f.id}: ${f.error}`);
      }
    }

    const output = outputPath || annotationsPath.replace('.json', '.source.json');
    fs.writeFileSync(output, JSON.stringify(result.migrated, null, 2));
    console.log(`\nWritten to: ${output}`);
  } else if (command === 'resolve') {
    // Resolve anchor-based to line-based
    const sourcePath = args[1];
    const leanPath = args[2];
    const outputPath = args[3];

    if (!sourcePath || !leanPath) {
      console.error('Usage: resolver.ts resolve <annotations.source.json> <source.lean> [output.json]');
      process.exit(1);
    }

    const sourceAnnotations = JSON.parse(fs.readFileSync(sourcePath, 'utf-8'));
    const leanSource = fs.readFileSync(leanPath, 'utf-8');

    const results = resolveAnnotations(sourceAnnotations, leanSource, leanPath);
    const resolved = results.filter((r) => r.resolved).map((r) => r.resolved);
    const failed = results.filter((r) => r.error);

    console.log(`Resolution results:`);
    console.log(`  Resolved: ${resolved.length}`);
    console.log(`  Failed: ${failed.length}`);

    if (failed.length > 0) {
      console.log('\nFailed resolutions:');
      for (const f of failed) {
        console.log(`  - ${f.annotation.id}: ${f.error}`);
      }
      process.exit(1);
    }

    const output = outputPath || sourcePath.replace('.source.json', '.json');
    fs.writeFileSync(output, JSON.stringify(resolved, null, 2));
    console.log(`\nWritten to: ${output}`);
  } else if (command === 'parse') {
    // Parse and dump Lean file structure
    const leanPath = args[1];

    if (!leanPath) {
      console.error('Usage: resolver.ts parse <source.lean>');
      process.exit(1);
    }

    const leanSource = fs.readFileSync(leanPath, 'utf-8');
    const parsed = parseLeanFile(leanSource, leanPath);

    console.log(`Parsed ${parsed.constructs.length} constructs:\n`);
    for (const c of parsed.constructs) {
      const range = `${c.startLine}-${c.endLine}`;
      const docNote = c.docCommentStart ? ` (doc: ${c.docCommentStart})` : '';
      if (c.type === 'declaration') {
        console.log(`  ${c.kind} ${c.name} @ ${range}${docNote}`);
      } else if (c.type === 'namespace') {
        console.log(`  namespace ${c.name} @ ${range}`);
      } else {
        const preview = c.content.split('\n')[0].slice(0, 60);
        console.log(`  ${c.type} @ ${range}: ${preview}...`);
      }
    }
  } else {
    console.log('Annotation Resolver');
    console.log('');
    console.log('Commands:');
    console.log('  validate <annotations.json> <source.lean>');
    console.log('    Check if line-based annotations are still aligned');
    console.log('');
    console.log('  migrate <annotations.json> <source.lean> [output.json]');
    console.log('    Convert line-based annotations to anchor-based format');
    console.log('');
    console.log('  resolve <annotations.source.json> <source.lean> [output.json]');
    console.log('    Resolve anchor-based annotations to line numbers');
    console.log('');
    console.log('  parse <source.lean>');
    console.log('    Parse and display Lean file structure');
  }
}

// Run if this is the main module
main();
