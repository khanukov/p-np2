'use strict';

const PROTECTED_EXACT = new Set([
  'spec/tmverifier_freeze.json',
  'spec/version_manifest.toml',
  'scripts/check.sh',
  'scripts/check_tmverifier_freeze.py',
  'scripts/check_tmverifier_freeze.sh',
  'scripts/test_tmverifier_freeze.py',
  'scripts/test_tmverifier_freeze.sh',
  'scripts/test_tmverifier_freeze_policy.js',
  'pnp3/Docs/TMVERIFIER_FREEZE.md',
  '.github/scripts/tmverifier-freeze-policy.js',
  '.github/workflows/tmverifier-freeze.yml',
  '.github/workflows/ci.yml',
  '.github/workflows/lean.yml',
  '.github/workflows/nightly-unconditional.yml',
  '.github/CODEOWNERS',
  '.gitattributes',
]);

function isProtected(path) {
  return path.startsWith('pnp3/Complexity/TMVerifier/') || PROTECTED_EXACT.has(path);
}

function stripLeanComments(text) {
  let output = '';
  let index = 0;
  let blockDepth = 0;
  let lineComment = false;
  let string = false;
  while (index < text.length) {
    const pair = text.slice(index, index + 2);
    const char = text[index];
    if (lineComment) {
      if (char === '\n') {
        lineComment = false;
        output += char;
      } else output += ' ';
    } else if (blockDepth) {
      if (pair === '/-') {
        blockDepth += 1;
        output += '  ';
        index += 1;
      } else if (pair === '-/') {
        blockDepth -= 1;
        output += '  ';
        index += 1;
      } else output += char === '\n' ? '\n' : ' ';
    } else if (string) {
      output += char === '\n' ? '\n' : ' ';
      if (char === '\\' && index + 1 < text.length) {
        output += ' ';
        index += 1;
      } else if (char === '"') string = false;
    } else if (pair === '--') {
      lineComment = true;
      output += '  ';
      index += 1;
    } else if (pair === '/-') {
      blockDepth = 1;
      output += '  ';
      index += 1;
    } else if (char === '"') {
      string = true;
      output += ' ';
    } else output += char;
    index += 1;
  }
  return output;
}

function lakefileIncludesModules(text, modules) {
  const active = stripLeanComments(text);
  return modules.every(module => {
    const escaped = module.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    return new RegExp('^[ \\t]*Glob\\.one `' + escaped + ',[ \\t]*$', 'm').test(active);
  });
}

function evaluateFreezeDiff(files, labels, options = {}) {
  const changedFiles = options.changedFiles;
  const ownerAttestedHead = options.ownerAttestedHead ?? false;
  if (!Number.isInteger(changedFiles) || files.length >= 3000 || files.length !== changedFiles) {
    return {
      ok: false,
      protectedFiles: [],
      message: `PR file list is incomplete (${files.length}/${changedFiles}); freeze diff cannot be proven complete.`,
    };
  }
  const paths = files.flatMap(file =>
    [file.filename, file.previous_filename].filter(path => typeof path === 'string')
  );
  const protectedFiles = [...new Set(paths.filter(isProtected))];
  if (paths.includes('lakefile.lean') && options.lakefileComplete !== true) {
    protectedFiles.push('lakefile.lean');
  }
  protectedFiles.sort();
  const unfreeze = labels.includes('tmverifier-unfreeze') && ownerAttestedHead;
  if (protectedFiles.length && !unfreeze) {
    return {
      ok: false,
      protectedFiles,
      message: "Frozen paths require 'tmverifier-unfreeze' plus owner attestation for the current head SHA.",
    };
  }
  return {
    ok: true,
    protectedFiles,
    message: protectedFiles.length
      ? 'Explicit unfreeze review requested.'
      : 'No frozen TMVerifier or freeze-policy paths changed.',
  };
}

module.exports = { evaluateFreezeDiff, lakefileIncludesModules };
