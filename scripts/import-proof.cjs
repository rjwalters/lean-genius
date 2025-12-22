#!/usr/bin/env node
/**
 * Import proof data from lean-genius-proofs repository
 *
 * This script fetches processed LeanInk data from the proofs repo
 * and converts it to the format expected by the frontend.
 *
 * Usage:
 *   node scripts/import-proof.cjs <proof-name>
 *   node scripts/import-proof.cjs --all
 *   node scripts/import-proof.cjs --list
 *
 * Examples:
 *   node scripts/import-proof.cjs Sqrt2Irrational
 *   node scripts/import-proof.cjs --all
 *
 * Environment:
 *   PROOFS_REPO_PATH - Path to local lean-genius-proofs clone
 *                      (default: ~/Projects/lean-genius-proofs)
 */

const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

const PROOFS_REPO_URL = 'https://github.com/rjwalters/lean-genius-proofs.git';
const DEFAULT_PROOFS_PATH = path.join(process.env.HOME, 'Projects/lean-genius-proofs');
const PROOFS_REPO_PATH = process.env.PROOFS_REPO_PATH || DEFAULT_PROOFS_PATH;

// Mapping from Lean file names to frontend slug names
const PROOF_MAPPING = {
  'Sqrt2Irrational': 'sqrt2-irrational',
  'OnePlusOne': 'russell-1-plus-1',
  'FundamentalTheoremCalculus': 'fundamental-theorem-calculus',
  'InfinitudePrimes': 'infinitude-primes',
  // Add more mappings as proofs are added:
  // 'CantorDiagonalization': 'cantor-diagonalization',
};

function ensureProofsRepo() {
  if (!fs.existsSync(PROOFS_REPO_PATH)) {
    console.log(`Cloning proofs repo to ${PROOFS_REPO_PATH}...`);
    execSync(`git clone ${PROOFS_REPO_URL} "${PROOFS_REPO_PATH}"`, { stdio: 'inherit' });
  } else {
    console.log(`Updating proofs repo at ${PROOFS_REPO_PATH}...`);
    execSync('git pull', { cwd: PROOFS_REPO_PATH, stdio: 'inherit' });
  }
}

function listAvailableProofs() {
  ensureProofsRepo();
  const proofsDir = path.join(PROOFS_REPO_PATH, 'Proofs');
  const files = fs.readdirSync(proofsDir);

  const leanInkFiles = files.filter(f => f.endsWith('.leanInk'));

  console.log('\nAvailable proofs with LeanInk output:');
  for (const file of leanInkFiles) {
    const name = file.replace('.lean.leanInk', '');
    const slug = PROOF_MAPPING[name] || toSlug(name);
    const mapped = PROOF_MAPPING[name] ? '(mapped)' : '(auto-slug)';
    console.log(`  - ${name} -> ${slug} ${mapped}`);
  }

  console.log('\nLean files without LeanInk output:');
  const leanFiles = files.filter(f => f.endsWith('.lean'));
  for (const file of leanFiles) {
    const name = file.replace('.lean', '');
    const hasLeanInk = leanInkFiles.includes(`${file}.leanInk`);
    if (!hasLeanInk) {
      console.log(`  - ${name} (run LeanInk to generate)`);
    }
  }
}

function toSlug(name) {
  // Convert CamelCase to kebab-case
  return name
    .replace(/([a-z])([A-Z])/g, '$1-$2')
    .replace(/([A-Z]+)([A-Z][a-z])/g, '$1-$2')
    .toLowerCase();
}

function getContentsString(contents) {
  if (typeof contents === 'string') {
    return contents;
  }
  if (Array.isArray(contents)) {
    return contents.map(t => t.raw || '').join('');
  }
  return '';
}

function convertLeanInkToTacticStates(leanInkData) {
  const tacticStates = [];
  let currentLine = 1;

  for (const item of leanInkData) {
    if (item._type === 'text') {
      const content = getContentsString(item.contents);
      currentLine += (content.match(/\n/g) || []).length;
    }

    if (item._type === 'sentence' && item.goals && item.goals.length > 0) {
      const tactic = getContentsString(item.contents).trim();

      if (!tactic || tactic === '' || /^\s*$/.test(tactic)) {
        const content = getContentsString(item.contents);
        currentLine += (content.match(/\n/g) || []).length;
        continue;
      }

      const isAccomplished = item.goals.some(g =>
        g.conclusion?.includes('Goals accomplished') ||
        g.conclusion?.includes('🐙')
      );

      const goals = item.goals
        .filter(g => !g.conclusion?.includes('Goals accomplished'))
        .map(g => ({
          name: g.name || undefined,
          hypotheses: (g.hypotheses || []).map(h => ({
            names: h.names || [],
            type: h.type || ''
          })),
          conclusion: g.conclusion || ''
        }));

      if (goals.length > 0 || isAccomplished) {
        tacticStates.push({
          line: currentLine,
          tactic: tactic.replace(/\n/g, ' ').trim(),
          goalsBefore: goals,
          goalsAfter: isAccomplished ? [] : goals
        });
      }

      const content = getContentsString(item.contents);
      currentLine += (content.match(/\n/g) || []).length;
    }
  }

  // Deduplicate consecutive identical entries
  const deduped = [];
  for (const state of tacticStates) {
    const last = deduped[deduped.length - 1];
    if (!last || last.tactic !== state.tactic || last.line !== state.line) {
      deduped.push(state);
    }
  }

  return deduped;
}

function importProof(proofName) {
  ensureProofsRepo();

  const slug = PROOF_MAPPING[proofName] || toSlug(proofName);
  const leanInkPath = path.join(PROOFS_REPO_PATH, 'Proofs', `${proofName}.lean.leanInk`);
  const targetDir = path.join(process.cwd(), 'src/data/proofs', slug);

  if (!fs.existsSync(leanInkPath)) {
    console.error(`Error: LeanInk output not found at ${leanInkPath}`);
    console.error(`Run LeanInk on the proof first: lake exe leanink ${proofName}.lean`);
    process.exit(1);
  }

  if (!fs.existsSync(targetDir)) {
    console.error(`Error: Target directory not found at ${targetDir}`);
    console.error(`Create the proof structure first with meta.json, source.lean, etc.`);
    process.exit(1);
  }

  console.log(`Importing ${proofName} -> ${slug}...`);

  // Read and convert LeanInk data
  const leanInkData = JSON.parse(fs.readFileSync(leanInkPath, 'utf-8'));
  const tacticStates = convertLeanInkToTacticStates(leanInkData);

  // Write tactic states
  const outputPath = path.join(targetDir, 'tacticStates.json');
  fs.writeFileSync(outputPath, JSON.stringify(tacticStates, null, 2));

  console.log(`  Written ${tacticStates.length} tactic states to ${outputPath}`);
  return { proofName, slug, count: tacticStates.length };
}

function importAll() {
  ensureProofsRepo();
  const proofsDir = path.join(PROOFS_REPO_PATH, 'Proofs');
  const files = fs.readdirSync(proofsDir);

  const leanInkFiles = files.filter(f => f.endsWith('.leanInk'));
  const results = [];

  for (const file of leanInkFiles) {
    const name = file.replace('.lean.leanInk', '');
    const slug = PROOF_MAPPING[name] || toSlug(name);
    const targetDir = path.join(process.cwd(), 'src/data/proofs', slug);

    if (fs.existsSync(targetDir)) {
      try {
        results.push(importProof(name));
      } catch (err) {
        console.error(`  Error importing ${name}: ${err.message}`);
      }
    } else {
      console.log(`  Skipping ${name}: no frontend directory at ${targetDir}`);
    }
  }

  console.log('\nImport summary:');
  for (const r of results) {
    console.log(`  ${r.proofName} -> ${r.slug}: ${r.count} tactic states`);
  }
}

// Main
const args = process.argv.slice(2);

if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
  console.log(`
Usage:
  node scripts/import-proof.cjs <proof-name>  Import a specific proof
  node scripts/import-proof.cjs --all         Import all available proofs
  node scripts/import-proof.cjs --list        List available proofs

Environment:
  PROOFS_REPO_PATH   Path to lean-genius-proofs clone
                     (default: ~/Projects/lean-genius-proofs)
`);
  process.exit(0);
}

if (args.includes('--list')) {
  listAvailableProofs();
} else if (args.includes('--all')) {
  importAll();
} else {
  importProof(args[0]);
}
