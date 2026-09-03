#!/usr/bin/env node
const assert = require('node:assert/strict');
const { evaluateFreezeDiff } = require('../.github/scripts/tmverifier-freeze-policy.js');

assert.equal(evaluateFreezeDiff([{ filename: 'README.md' }], []).ok, true);
assert.equal(
  evaluateFreezeDiff([{ filename: 'pnp3/Complexity/TMVerifier/X.lean' }], []).ok,
  false,
);
assert.equal(
  evaluateFreezeDiff([{ filename: 'archive/X.lean', previous_filename: 'pnp3/Complexity/TMVerifier/X.lean' }], []).ok,
  false,
);
assert.equal(
  evaluateFreezeDiff([{ filename: 'scripts/check_tmverifier_freeze.py' }], []).ok,
  false,
);
assert.equal(
  evaluateFreezeDiff(
    [{ filename: 'pnp3/Complexity/TMVerifier/X.lean' }],
    ['tmverifier-unfreeze'],
    { changedFiles: 1, ownerAttestedHead: false },
  ).ok,
  false,
);
assert.equal(
  evaluateFreezeDiff(
    [{ filename: 'pnp3/Complexity/TMVerifier/X.lean' }],
    ['tmverifier-unfreeze'],
    { changedFiles: 1, ownerAttestedHead: true },
  ).ok,
  true,
);
assert.equal(
  evaluateFreezeDiff(
    Array.from({ length: 2999 }, (_, i) => ({ filename: `bulk/${i}` })),
    [],
    { changedFiles: 3000, ownerAttestedHead: false },
  ).ok,
  false,
);
console.log('[tmverifier-freeze-policy-test] OK: rename, head attestation, and API completeness');
