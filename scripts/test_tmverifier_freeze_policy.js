#!/usr/bin/env node
const assert = require('node:assert/strict');
const { evaluateFreezeDiff } = require('../.github/scripts/tmverifier-freeze-policy.js');

const complete = { changedFiles: 1, ownerAttestedHead: false };

assert.equal(evaluateFreezeDiff([{ filename: 'README.md' }], [], complete).ok, true);
assert.equal(
  evaluateFreezeDiff(
    [{ filename: 'pnp3/Complexity/TMVerifier/X.lean' }], [], complete
  ).ok,
  false,
);
assert.equal(
  evaluateFreezeDiff([{
    filename: 'archive/X.lean',
    previous_filename: 'pnp3/Complexity/TMVerifier/X.lean',
  }], [], complete).ok,
  false,
);
assert.equal(
  evaluateFreezeDiff([{ filename: 'scripts/check_tmverifier_freeze.py' }], [], complete).ok,
  false,
);
assert.equal(
  evaluateFreezeDiff(
    [{ filename: 'lakefile.lean' }], [],
    { changedFiles: 1, ownerAttestedHead: false, lakefileComplete: true },
  ).ok,
  true,
);
assert.equal(
  evaluateFreezeDiff(
    [{ filename: 'lakefile.lean' }], [],
    { changedFiles: 1, ownerAttestedHead: false, lakefileComplete: false },
  ).ok,
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
