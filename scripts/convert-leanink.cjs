#!/usr/bin/env node
/**
 * Convert LeanInk JSON output to frontend TacticState format
 *
 * Usage: node scripts/convert-leanink.js proofs/Proofs/Sqrt2Irrational.lean.leanInk
 */

const fs = require('fs');
const path = require('path');

function convertLeanInkToTacticStates(leanInkData) {
  const tacticStates = [];
  let currentLine = 1;

  for (const item of leanInkData) {
    // Track line numbers from raw content
    if (item._type === 'text') {
      const content = typeof item.contents === 'string'
        ? item.contents
        : item.contents?.map(t => t.raw || '').join('') || '';
      currentLine += (content.match(/\n/g) || []).length;
    }

    // Extract tactic info from sentences
    if (item._type === 'sentence' && item.goals && item.goals.length > 0) {
      const tactic = item.contents
        ?.map(t => t.raw || '')
        .join('')
        .trim() || '';

      // Skip empty tactics or whitespace-only
      if (!tactic || tactic === '' || /^\s*$/.test(tactic)) {
        const content = item.contents?.map(t => t.raw || '').join('') || '';
        currentLine += (content.match(/\n/g) || []).length;
        continue;
      }

      // Skip if goals show "accomplished"
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
          goalsAfter: isAccomplished ? [] : goals // Simplified - ideally we'd track state changes
        });
      }

      const content = item.contents?.map(t => t.raw || '').join('') || '';
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

// Main
const args = process.argv.slice(2);
if (args.length === 0) {
  console.error('Usage: node convert-leanink.js <file.leanInk> [--output <file.json>]');
  process.exit(1);
}

const inputFile = args[0];
const outputIndex = args.indexOf('--output');
const outputFile = outputIndex !== -1 ? args[outputIndex + 1] : null;

try {
  const data = JSON.parse(fs.readFileSync(inputFile, 'utf-8'));
  const tacticStates = convertLeanInkToTacticStates(data);

  const output = JSON.stringify(tacticStates, null, 2);

  if (outputFile) {
    fs.writeFileSync(outputFile, output);
    console.log(`Written ${tacticStates.length} tactic states to ${outputFile}`);
  } else {
    console.log(output);
  }
} catch (err) {
  console.error('Error:', err.message);
  process.exit(1);
}
