import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';

test('packaging preserves reviewed allowlists and rejects stale files and portable path collisions', () => {
  const result = spawnSync('python3', ['tests/publication_packaging.py'], { encoding: 'utf8' });
  assert.equal(result.status, 0, result.stderr || result.stdout);
});
