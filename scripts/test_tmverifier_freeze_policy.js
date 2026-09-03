#!/usr/bin/env node
const assert = require('node:assert/strict');
const {
  evaluateFreezeDiff,
  lakefileIncludesModules,
} = require('../.github/scripts/tmverifier-freeze-policy.js');

const complete = { changedFiles: 1, ownerAttestedHead: false };
const lake = body => `lean_lib PnP3 where\n  globs := #[\n${body}  ]\n`;

assert.equal(lakefileIncludesModules(lake('  Glob.one `A.B,\n'), ['A.B']), true);
assert.equal(lakefileIncludesModules(lake('  -- Glob.one `A.B,\n'), ['A.B']), false);
assert.equal(lakefileIncludesModules(lake('  /- Glob.one `A.B, -/\n'), ['A.B']), false);
assert.equal(
  lakefileIncludesModules(
    'lean_lib PnP3 where\n  globs := #[\n  ]\ndef decoy := #[\n  Glob.one `A.B,\n]\n',
    ['A.B'],
  ),
  false,
);
assert.equal(
  lakefileIncludesModules(
    'lean_lib PnP3 where\n  globs := #[\n  ]\ndef decoy := r#"Glob.one `A.B,"#\n',
    ['A.B'],
  ),
  false,
);
assert.equal(
  lakefileIncludesModules(
    'lean_lib PnP3 where\n  globs := #[\n    #[\n      Glob.one `A.B,\n    ]\n  ]\n',
    ['A.B'],
  ),
  false,
);
assert.equal(
  lakefileIncludesModules(
    'lean_lib PnP3 where\n  roots := (let _ := {\n  globs := #[\n    Glob.one `A.B,\n  ]\n  }; #[])\n',
    ['A.B'],
  ),
  false,
);

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
