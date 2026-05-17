#!/usr/bin/env tsx
/**
 * Export research database to merge-friendly SQL files.
 *
 * This exports each table to a separate SQL file with INSERT statements.
 * These files can be checked into git and merged by multiple contributors.
 *
 * Usage: pnpm db:export
 */

import * as fs from 'fs';
import * as path from 'path';

const DB_PATH = 'research/db/knowledge.db';
const DATA_DIR = 'research/db/data';

// Tables to export (in dependency order)
const TABLES = [
  'problems',
  'sessions',
  'insights',
  'built_items',
  'mathlib_gaps',
  'next_steps',
  'refs',
  'approaches',
  'approach_insights',
  'decisions',
  'gap_dependencies'
];

type ExportDb = {
  prepare: (sql: string) => { all: () => unknown[] };
  close: () => void;
};

function printUsage(): void {
  console.log(`Usage: pnpm db:export

Export research/db/knowledge.db into merge-friendly SQL files.

Options:
  --help, -h  Show this help message`);
}

function escapeSQL(value: unknown): string {
  if (value === null || value === undefined) {
    return 'NULL';
  }
  if (typeof value === 'number') {
    return String(value);
  }
  if (typeof value === 'string') {
    // Escape single quotes by doubling them
    return `'${value.replace(/'/g, "''")}'`;
  }
  return `'${String(value)}'`;
}

function exportTable(db: ExportDb, tableName: string): string {
  const rows = db.prepare(`SELECT * FROM ${tableName}`).all();

  if (rows.length === 0) {
    return `-- No data in ${tableName}\n`;
  }

  const columns = Object.keys(rows[0] as object);
  const lines: string[] = [
    `-- ${tableName}: ${rows.length} rows`,
    `-- Exported: ${new Date().toISOString()}`,
    ''
  ];

  for (const row of rows) {
    const values = columns.map(col => escapeSQL((row as Record<string, unknown>)[col]));
    lines.push(`INSERT INTO ${tableName} (${columns.join(', ')}) VALUES (${values.join(', ')});`);
  }

  lines.push('');
  return lines.join('\n');
}

async function main() {
  const args = process.argv.slice(2);
  if (args.includes('--help') || args.includes('-h')) {
    printUsage();
    return;
  }

  console.log('Exporting research database to SQL files...\n');

  // Ensure data directory exists
  fs.mkdirSync(DATA_DIR, { recursive: true });

  // Open database
  const { default: Database } = await import('better-sqlite3');
  const db = new Database(DB_PATH, { readonly: true });

  let totalRows = 0;

  for (const table of TABLES) {
    try {
      const sql = exportTable(db, table);
      const filePath = path.join(DATA_DIR, `${table}.sql`);
      fs.writeFileSync(filePath, sql);

      const rowCount = (sql.match(/^INSERT/gm) || []).length;
      totalRows += rowCount;
      console.log(`  ${table}: ${rowCount} rows -> ${filePath}`);
    } catch (err) {
      // Table might not exist
      console.log(`  ${table}: skipped (${(err as Error).message})`);
    }
  }

  db.close();

  console.log(`\n✅ Exported ${totalRows} total rows to ${DATA_DIR}/`);
  console.log('\nNext steps:');
  console.log('  git add research/db/data/*.sql');
  console.log('  git commit -m "Export research database"');
}

main().catch((err) => {
  console.error('Export failed:', err);
  process.exit(1);
});
