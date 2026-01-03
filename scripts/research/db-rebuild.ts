#!/usr/bin/env tsx
/**
 * Rebuild research database from SQL files.
 *
 * This creates a fresh knowledge.db from:
 * 1. schema.sql - table definitions
 * 2. data/*.sql - INSERT statements
 *
 * Usage: pnpm db:rebuild
 */

import Database from 'better-sqlite3';
import * as fs from 'fs';
import * as path from 'path';

const DB_PATH = 'research/db/knowledge.db';
const SCHEMA_PATH = 'research/db/schema.sql';
const DATA_DIR = 'research/db/data';

// Tables to import (in dependency order - foreign keys matter)
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

function main() {
  console.log('Rebuilding research database from SQL files...\n');

  // Backup existing database if it exists
  if (fs.existsSync(DB_PATH)) {
    const backupPath = `${DB_PATH}.bak`;
    fs.copyFileSync(DB_PATH, backupPath);
    console.log(`  Backed up existing database to ${backupPath}`);
    fs.unlinkSync(DB_PATH);
  }

  // Create new database
  const db = new Database(DB_PATH);

  // Enable foreign keys
  db.pragma('foreign_keys = ON');

  // Load schema
  if (!fs.existsSync(SCHEMA_PATH)) {
    console.error(`❌ Schema file not found: ${SCHEMA_PATH}`);
    process.exit(1);
  }

  console.log(`  Loading schema from ${SCHEMA_PATH}`);
  const schema = fs.readFileSync(SCHEMA_PATH, 'utf-8');
  db.exec(schema);

  // Load data files
  let totalRows = 0;

  for (const table of TABLES) {
    const dataPath = path.join(DATA_DIR, `${table}.sql`);

    if (!fs.existsSync(dataPath)) {
      console.log(`  ${table}: no data file`);
      continue;
    }

    const sql = fs.readFileSync(dataPath, 'utf-8');
    const insertCount = (sql.match(/^INSERT/gm) || []).length;

    if (insertCount === 0) {
      console.log(`  ${table}: empty`);
      continue;
    }

    try {
      db.exec(sql);
      totalRows += insertCount;
      console.log(`  ${table}: ${insertCount} rows`);
    } catch (err) {
      console.error(`  ${table}: ERROR - ${(err as Error).message}`);
    }
  }

  db.close();

  console.log(`\n✅ Rebuilt database with ${totalRows} total rows`);
  console.log(`   Location: ${DB_PATH}`);
}

main();
