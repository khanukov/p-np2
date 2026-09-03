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
  let rawEnd = null;
  while (index < text.length) {
    const pair = text.slice(index, index + 2);
    const char = text[index];
    if (rawEnd !== null) {
      if (text.startsWith(rawEnd, index)) {
        output += ' '.repeat(rawEnd.length);
        index += rawEnd.length - 1;
        rawEnd = null;
      } else output += char === '\n' ? '\n' : ' ';
    } else if (lineComment) {
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
    } else if (char === 'r') {
      let cursor = index + 1;
      while (cursor < text.length && text[cursor] === '#') cursor += 1;
      if (cursor < text.length && text[cursor] === '"') {
        rawEnd = '"' + text.slice(index + 1, cursor);
        output += ' '.repeat(cursor - index + 1);
        index = cursor;
      } else output += char;
    } else if (char === '"') {
      string = true;
      output += ' ';
    } else output += char;
    index += 1;
  }
  return output;
}

function pnp3GlobsArray(text) {
  const active = stripLeanComments(text);
  const headers = [...active.matchAll(/^[ \t]*lean_lib[ \t]+PnP3[ \t]+where[ \t]*$/gm)];
  if (headers.length !== 1) return null;
  const start = headers[0].index + headers[0][0].length;
  const rest = active.slice(start);
  const nextLibrary = /^[ \t]*lean_lib[ \t]+/m.exec(rest);
  const end = nextLibrary ? start + nextLibrary.index : active.length;
  const block = active.slice(start, end);
  const lines = block.split('\n').filter(line => line.trim());
  if (!lines.length || lines.some(line => line.startsWith('\t'))) return null;
  const topIndent = Math.min(...lines.map(line => line.length - line.trimStart().length));
  const depths = [];
  let parens = 0;
  let brackets = 0;
  let braces = 0;
  for (const char of block) {
    depths.push([parens, brackets, braces]);
    if (char === '(') parens += 1;
    else if (char === ')') parens -= 1;
    else if (char === '[') brackets += 1;
    else if (char === ']') brackets -= 1;
    else if (char === '{') braces += 1;
    else if (char === '}') braces -= 1;
    if (Math.min(parens, brackets, braces) < 0) return null;
  }
  const declarations = [...block.matchAll(/^([ ]+)globs[ \t]*:=[ \t]*#\[/gm)]
    .filter(match => match[1].length === topIndent &&
      depths[match.index].every(depth => depth === 0));
  if (declarations.length !== 1) return null;
  const openBracket = start + declarations[0].index + declarations[0][0].length - 1;
  let depth = 1;
  let output = '';
  for (let index = openBracket + 1; index < end; index += 1) {
    const char = active[index];
    if (char === '[') {
      depth += 1;
      output += ' ';
    } else if (char === ']') {
      if (depth === 1) return output;
      depth -= 1;
      output += ' ';
    } else output += depth === 1 ? char : (char === '\n' ? '\n' : ' ');
  }
  return null;
}

function lakefileIncludesModules(text, modules) {
  const active = pnp3GlobsArray(text);
  if (active === null) return false;
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
