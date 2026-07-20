#!/usr/bin/env npx tsx
/**
 * Problem Extractor for Mathematical Research
 *
 * Extracts open problems from the lean-genius proof gallery:
 * - openQuestions from meta.json files
 * - Incomplete proofs (sorries > 0)
 * - Millennium/Hilbert problems
 * - WIP and conditional proofs
 *
 * Usage:
 *   npx tsx .lean/scripts/extract-problems.ts
 *   npx tsx .lean/scripts/extract-problems.ts --json
 *   npx tsx .lean/scripts/extract-problems.ts --category=extension
 */

import { readFileSync, writeFileSync, readdirSync, existsSync } from 'fs';
import { join } from 'path';

// ---------------------------------------------------------------------------
// OQ-recursion-depth policy (issue #39827 / #39821)
//
// Open-question children are named `<parent>-oq-NN`. The depth-first tier
// recurses into a result's open questions indefinitely, producing degenerate
// chains up to 11 levels deep. Cap it AT THE SOURCE: a proof whose id already
// has `maxOqDepth` `-oq-` segments does not contribute further OQ children, so
// no problem beyond the cap is ever extracted into the pool.
//
// Configuration precedence: MAX_OQ_DEPTH env var > .lean/config/oq-policy.json
// > built-in default (3).
// ---------------------------------------------------------------------------
const OQ_POLICY_DEFAULT_DEPTH = 3;

function resolveMaxOqDepth(): number {
  const fromEnv = process.env.MAX_OQ_DEPTH;
  if (fromEnv !== undefined && /^\d+$/.test(fromEnv.trim())) {
    return parseInt(fromEnv.trim(), 10);
  }
  try {
    const configPath = join(process.cwd(), '.lean/config/oq-policy.json');
    if (existsSync(configPath)) {
      const cfg = JSON.parse(readFileSync(configPath, 'utf-8'));
      if (typeof cfg.maxOqDepth === 'number' && Number.isFinite(cfg.maxOqDepth)) {
        return cfg.maxOqDepth;
      }
    }
  } catch {
    // Fall through to default on any parse/read error.
  }
  return OQ_POLICY_DEFAULT_DEPTH;
}

// Number of `-oq-NN` segments in a slug/id (its OQ-recursion depth).
function oqDepth(id: string): number {
  return (id.match(/-oq-\d+/g) || []).length;
}

const MAX_OQ_DEPTH = resolveMaxOqDepth();

// Types
interface ProofMeta {
  id: string;
  title: string;
  slug: string;
  description: string;
  meta: {
    status: 'verified' | 'axiom-based' | 'partial' | 'conditional' | 'disputed';
    badge: 'original' | 'mathlib' | 'pedagogical' | 'wip' | 'conjecture' | 'fallacy';
    tags: string[];
    sorries: number;
    wiedijkNumber?: number;
    hilbertNumber?: number;
    millenniumProblem?: string;
  };
  conclusion?: {
    // Legacy entries are plain strings; enriched entries are {id, question, significance} objects.
    openQuestions?: Array<string | { id?: string; question?: string; significance?: string }>;
  };
}

interface ExtractedProblem {
  id: string;
  title: string;
  description: string;
  source: {
    proofId: string;
    proofTitle: string;
    type: 'open-question' | 'incomplete' | 'millennium' | 'hilbert' | 'wip' | 'conditional';
  };
  category: 'extension' | 'generalization' | 'connection' | 'technique' | 'open-conjecture' | 'completion';
  tractability: 'tractable' | 'challenging' | 'hard' | 'moonshot';
  tags: string[];
  relatedProofs: string[];
}

// Problem categorization heuristics
function categorizeQuestion(question: string): ExtractedProblem['category'] {
  const q = question.toLowerCase();

  if (q.includes('generalize') || q.includes('extend to') || q.includes('n-th') || q.includes('higher')) {
    return 'generalization';
  }
  if (q.includes('connect') || q.includes('relationship') || q.includes('related to')) {
    return 'connection';
  }
  if (q.includes('what about') || q.includes('can we') || q.includes('is there')) {
    return 'extension';
  }
  if (q.includes('technique') || q.includes('method') || q.includes('approach')) {
    return 'technique';
  }

  return 'extension'; // default
}

// Tractability assessment heuristics
function assessTractability(
  question: string,
  meta: ProofMeta['meta']
): ExtractedProblem['tractability'] {
  const q = question.toLowerCase();

  // Moonshot indicators
  if (meta.millenniumProblem) return 'moonshot';
  if (q.includes('open problem') || q.includes('unsolved') || q.includes('conjecture')) {
    return 'moonshot';
  }

  // Hard indicators
  if (meta.hilbertNumber && meta.hilbertNumber < 10) return 'hard';
  if (q.includes('prove') && q.includes('harder')) return 'hard';
  if (q.includes('requires') && (q.includes('algebraic geometry') || q.includes('advanced'))) {
    return 'hard';
  }

  // Tractable indicators
  if (q.includes('generalize') && q.includes('straightforward')) return 'tractable';
  if (q.includes('similar proof') || q.includes('same technique')) return 'tractable';
  if (meta.sorries === 0 && meta.status === 'verified') {
    // Extensions of verified proofs are more tractable
    if (q.includes('what about') || q.includes('can we show')) return 'challenging';
  }

  return 'challenging'; // default
}

// Generate a unique problem ID
function generateProblemId(proofId: string, index: number, type: string): string {
  return `${proofId}-${type}-${String(index + 1).padStart(2, '0')}`;
}

// Extract title from question
function extractTitle(question: string): string {
  // Take first sentence or first 80 chars
  const firstSentence = question.split(/[.?!]/)[0];
  // Split on Unicode code points (not UTF-16 units) so astral-plane characters
  // such as 𝔽 (U+1D53D = 𝔽) are never truncated mid-surrogate-pair,
  // which would otherwise emit a lone surrogate and produce invalid JSON.
  const chars = Array.from(firstSentence);
  if (chars.length <= 80) return firstSentence;
  return chars.slice(0, 77).join('') + '...';
}

// Main extraction function
function extractProblems(proofsDir: string): ExtractedProblem[] {
  const problems: ExtractedProblem[] = [];
  let cappedChains = 0; // proofs whose OQ children were suppressed by the cap

  // Get all proof directories
  const proofDirs = readdirSync(proofsDir, { withFileTypes: true })
    .filter(d => d.isDirectory())
    .map(d => d.name);

  for (const proofDir of proofDirs) {
    const metaPath = join(proofsDir, proofDir, 'meta.json');

    if (!existsSync(metaPath)) continue;

    try {
      const meta: ProofMeta = JSON.parse(readFileSync(metaPath, 'utf-8'));

      // OQ depth cap (issue #39827): a proof already at/over the cap must not
      // spawn a deeper `-oq-` child. Its own open questions are dropped so the
      // chain stops descending; the parent entry itself is untouched.
      const parentDepth = oqDepth(meta.id);
      const oqChildrenAllowed = parentDepth < MAX_OQ_DEPTH;

      // 1. Extract from openQuestions (only when below the depth cap)
      if (oqChildrenAllowed && meta.conclusion?.openQuestions) {
        meta.conclusion.openQuestions.forEach((rawQuestion, index) => {
          // openQuestions entries may be plain strings (legacy) or
          // {id, question, significance} objects (enriched). Normalize to a string.
          const question =
            typeof rawQuestion === 'string'
              ? rawQuestion
              : (rawQuestion?.question ?? String(rawQuestion ?? ''));
          problems.push({
            id: generateProblemId(meta.id, index, 'oq'),
            title: extractTitle(question),
            description: question,
            source: {
              proofId: meta.id,
              proofTitle: meta.title,
              type: 'open-question'
            },
            category: categorizeQuestion(question),
            tractability: assessTractability(question, meta.meta),
            tags: [...meta.meta.tags],
            relatedProofs: [meta.id]
          });
        });
      } else if (!oqChildrenAllowed && (meta.conclusion?.openQuestions?.length ?? 0) > 0) {
        // Chain has reached the depth cap: suppress its OQ children so it stops
        // descending, and record it for the summary telemetry line below.
        cappedChains += 1;
        console.error(
          `OQ-cap: suppressing ${meta.conclusion!.openQuestions!.length} open-question child(ren) of ${meta.id} ` +
          `(depth ${parentDepth} >= cap ${MAX_OQ_DEPTH})`
        );
      }

      // 2. Incomplete proofs (sorries > 0, but not fallacy/pedagogical)
      if (meta.meta.sorries > 0 &&
          meta.meta.badge !== 'fallacy' &&
          meta.meta.badge !== 'pedagogical') {
        problems.push({
          id: generateProblemId(meta.id, 0, 'incomplete'),
          title: `Complete proof of ${meta.title}`,
          description: `This proof has ${meta.meta.sorries} sorry statements that need to be filled in.`,
          source: {
            proofId: meta.id,
            proofTitle: meta.title,
            type: 'incomplete'
          },
          category: 'completion',
          tractability: meta.meta.sorries > 5 ? 'hard' : 'challenging',
          tags: [...meta.meta.tags, 'incomplete'],
          relatedProofs: [meta.id]
        });
      }

      // 3. Millennium problems
      if (meta.meta.millenniumProblem) {
        problems.push({
          id: generateProblemId(meta.id, 0, 'millennium'),
          title: `${meta.title} (Millennium Prize)`,
          description: `One of the seven Millennium Prize Problems: ${meta.meta.millenniumProblem}`,
          source: {
            proofId: meta.id,
            proofTitle: meta.title,
            type: 'millennium'
          },
          category: 'open-conjecture',
          tractability: 'moonshot',
          tags: [...meta.meta.tags, 'millennium-prize'],
          relatedProofs: [meta.id]
        });
      }

      // 4. WIP proofs
      if (meta.meta.badge === 'wip') {
        problems.push({
          id: generateProblemId(meta.id, 0, 'wip'),
          title: `Complete ${meta.title} (Work in Progress)`,
          description: `This proof is marked as work in progress and needs completion.`,
          source: {
            proofId: meta.id,
            proofTitle: meta.title,
            type: 'wip'
          },
          category: 'completion',
          tractability: 'challenging',
          tags: [...meta.meta.tags, 'wip'],
          relatedProofs: [meta.id]
        });
      }

      // 5. Conditional proofs
      if (meta.meta.status === 'conditional' || meta.meta.status === 'partial') {
        problems.push({
          id: generateProblemId(meta.id, 0, 'conditional'),
          title: `Strengthen ${meta.title} to unconditional`,
          description: `This proof is ${meta.meta.status}. Can it be made unconditional?`,
          source: {
            proofId: meta.id,
            proofTitle: meta.title,
            type: 'conditional'
          },
          category: 'extension',
          tractability: 'hard',
          tags: [...meta.meta.tags, meta.meta.status],
          relatedProofs: [meta.id]
        });
      }

    } catch (e) {
      console.error(`Error processing ${metaPath}:`, e);
    }
  }

  if (cappedChains > 0) {
    console.error(
      `OQ-cap: capped OQ recursion for ${cappedChains} chain(s) at depth >= ${MAX_OQ_DEPTH} ` +
      `(set MAX_OQ_DEPTH or .lean/config/oq-policy.json to adjust)`
    );
  }

  return problems;
}

// Rank problems for research selection
function rankProblems(problems: ExtractedProblem[]): ExtractedProblem[] {
  const tractabilityScore: Record<ExtractedProblem['tractability'], number> = {
    'tractable': 4,
    'challenging': 3,
    'hard': 2,
    'moonshot': 1
  };

  const categoryScore: Record<ExtractedProblem['category'], number> = {
    'extension': 4,
    'generalization': 4,
    'completion': 3,
    'connection': 3,
    'technique': 2,
    'open-conjecture': 1
  };

  return [...problems].sort((a, b) => {
    const scoreA = tractabilityScore[a.tractability] + categoryScore[a.category];
    const scoreB = tractabilityScore[b.tractability] + categoryScore[b.category];
    return scoreB - scoreA;
  });
}

// Group problems by category
function groupByCategory(problems: ExtractedProblem[]): Record<string, ExtractedProblem[]> {
  const groups: Record<string, ExtractedProblem[]> = {};

  for (const problem of problems) {
    const key = problem.category;
    if (!groups[key]) groups[key] = [];
    groups[key].push(problem);
  }

  return groups;
}

// Format for console output
function formatProblem(p: ExtractedProblem): string {
  const tractIcon: Record<string, string> = {
    'tractable': '🟢',
    'challenging': '🟡',
    'hard': '🟠',
    'moonshot': '🔴'
  };

  return `${tractIcon[p.tractability]} [${p.category}] ${p.title}
   Source: ${p.source.proofTitle}
   ID: ${p.id}`;
}

// Main
const args = process.argv.slice(2);
const outputJson = args.includes('--json');
const categoryFilter = args.find(a => a.startsWith('--category='))?.split('=')[1];
const tractabilityFilter = args.find(a => a.startsWith('--tractability='))?.split('=')[1];

const proofsDir = join(process.cwd(), 'src/data/proofs');
const outputPath = join(process.cwd(), '.lean/research/problems.json');

console.log('Extracting problems from proof gallery...');
console.log(`OQ-recursion cap: maxOqDepth=${MAX_OQ_DEPTH} (override with MAX_OQ_DEPTH env)\n`);

let problems = extractProblems(proofsDir);

// Apply filters
if (categoryFilter) {
  problems = problems.filter(p => p.category === categoryFilter);
}
if (tractabilityFilter) {
  problems = problems.filter(p => p.tractability === tractabilityFilter);
}

// Rank problems
problems = rankProblems(problems);

if (outputJson) {
  // Write to file
  writeFileSync(outputPath, JSON.stringify(problems, null, 2));
  console.log(`Wrote ${problems.length} problems to ${outputPath}`);
} else {
  // Console output
  const grouped = groupByCategory(problems);

  console.log(`Found ${problems.length} open problems across ${Object.keys(grouped).length} categories\n`);

  for (const [category, categoryProblems] of Object.entries(grouped)) {
    console.log(`\n## ${category.toUpperCase()} (${categoryProblems.length})\n`);
    for (const p of categoryProblems.slice(0, 5)) {
      console.log(formatProblem(p));
      console.log('');
    }
    if (categoryProblems.length > 5) {
      console.log(`   ... and ${categoryProblems.length - 5} more\n`);
    }
  }

  console.log('\n---');
  console.log('Top 10 Most Tractable Problems:\n');
  for (const p of problems.slice(0, 10)) {
    console.log(formatProblem(p));
    console.log('');
  }

  console.log('\nRun with --json to export full list to .lean/research/problems.json');
}
