#!/usr/bin/env node
"use strict";

/*
 * Exact GF(16) counterexample audit for the complement-balanced bad-mask
 * certificate at n=4, m=tailBits=1.
 *
 * This is bounded external computation, not a Lean theorem.  It constructs
 * a literal Boolean function on the full 16-bit input cube:
 *
 *   g(x) = chi_a(x) q(<h_0,x>,...,<h_6,x>),   f(x) = (1+g(x))/2,
 *
 * where h_0,...,h_6 span the structured dual H and a=0x003c is outside H.
 * Hence f is {0,1}-valued, has uniform and structured conditional mass 1/2,
 * and its nonconstant Fourier spectrum is the fully-high nonzero-syndrome
 * coset a+H.  If W is the unnormalized Walsh transform of q, then
 *
 *   coefficient(f, a+h_z) = W(z)/256.
 *
 * The script evaluates, over all 512 distinct masks in the t=1 structured
 * mask code, the exact certificate functional
 *
 *   B = D_avg + (1/512) sum_{bad masks} (1-D_mask),
 *
 * with bad meaning E_mask/2 > D_mask.  All accumulated rational arithmetic
 * uses BigInt.
 *
 * Run from the repository root:
 *
 *   node scripts/check_selector_complement_balanced_rank7.js
 */

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function popcount(value) {
  let current = value >>> 0;
  let count = 0;
  while (current !== 0) {
    current = (current & (current - 1)) >>> 0;
    count += 1;
  }
  return count;
}

function parity(value) {
  return popcount(value) & 1;
}

function gcd(left, right) {
  let a = left < 0n ? -left : left;
  let b = right < 0n ? -right : right;
  while (b !== 0n) [a, b] = [b, a % b];
  return a;
}

function reducedFraction(numerator, denominator) {
  const divisor = gcd(numerator, denominator);
  return [numerator / divisor, denominator / divisor];
}

function assertFraction(
  numerator,
  denominator,
  expectedNumerator,
  expectedDenominator,
  label,
) {
  const [actualNumerator, actualDenominator] = reducedFraction(
    numerator,
    denominator,
  );
  assert(
    actualNumerator === expectedNumerator &&
      actualDenominator === expectedDenominator,
    `${label}: expected ${expectedNumerator}/${expectedDenominator}, ` +
      `got ${actualNumerator}/${actualDenominator}`,
  );
}

function span(basis) {
  const words = [];
  for (let encoded = 0; encoded < 2 ** basis.length; encoded += 1) {
    let word = 0;
    for (let index = 0; index < basis.length; index += 1) {
      if (((encoded >>> index) & 1) !== 0) word ^= basis[index];
    }
    words.push(word);
  }
  return words;
}

function distribution(values) {
  const result = new Map();
  for (const value of values) {
    result.set(value, (result.get(value) || 0) + 1);
  }
  return [...result].sort((left, right) => left[0] - right[0]);
}

function assertDistribution(actual, expected, label) {
  assert(
    JSON.stringify(actual) === JSON.stringify(expected),
    `${label}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`,
  );
}

// Generator bases of the binary trace-evaluation mask code C=[16,9,4]
// and its structured dual H=[16,7,6], in the polynomial basis used by the
// other exact GF(16) selector audits.
const maskCodeBasis = [
  0x003c, 0x00c3, 0x0365, 0x05af, 0x0906,
  0x14e4, 0x2d4b, 0x441e, 0x8d7d,
];
const structuredDualBasis = [
  0x00ff, 0x036a, 0x0c65, 0x144e, 0x2417, 0x411b, 0x814d,
];

const masks = span(maskCodeBasis);
const structuredDual = span(structuredDualBasis);
assert(new Set(masks).size === 512, "mask code must have dimension 9");
assert(new Set(structuredDual).size === 128, "structured dual must have dimension 7");
for (const mask of masks) {
  for (const dualWord of structuredDual) {
    assert(parity(mask & dualWord) === 0, "C and H must be orthogonal");
  }
}
assertDistribution(
  distribution(masks.map(popcount)),
  [[0, 1], [4, 20], [6, 160], [8, 150], [10, 160], [12, 20], [16, 1]],
  "mask-code weight distribution",
);
assertDistribution(
  distribution(structuredDual.map(popcount)),
  [[0, 1], [6, 48], [8, 30], [10, 48], [16, 1]],
  "structured-dual weight distribution",
);

const offset = 0x003c;
const structuredDualSet = new Set(structuredDual);
assert(!structuredDualSet.has(offset), "offset must have nonzero syndrome");
const packet = structuredDual.map((word) => offset ^ word);
assert(new Set(packet).size === 128, "packet must be one full H-coset");
assert(
  Math.min(...packet.map(popcount)) === 4,
  "packet must be fully high above cutoff 2",
);

const plusIndices = new Set([
  3, 7, 14, 15, 17, 18, 23, 29, 30, 31, 33, 35, 36, 39, 40,
  42, 44, 45, 46, 47, 48, 49, 51, 60, 62, 63, 65, 67, 68, 71,
  72, 73, 76, 80, 82, 83, 84, 92, 93, 94, 95, 96, 99, 107, 109,
  110, 111, 112, 113, 115, 119, 120, 121, 122, 124, 126,
]);
const truth = Array.from({ length: 128 }, (_, index) =>
  plusIndices.has(index) ? 1 : -1,
);

// Verify the advertised construction is literally Boolean on all 2^16
// ambient inputs and balanced.
let trueCount = 0;
const signedAmbientTruth = new Int8Array(2 ** 16);
for (let input = 0; input < 2 ** 16; input += 1) {
  let localInput = 0;
  for (let index = 0; index < structuredDualBasis.length; index += 1) {
    localInput |= parity(structuredDualBasis[index] & input) << index;
  }
  const character = parity(offset & input) === 0 ? 1 : -1;
  const signedValue = character * truth[localInput];
  signedAmbientTruth[input] = signedValue;
  const booleanValue = (1 + signedValue) / 2;
  assert(booleanValue === 0 || booleanValue === 1, "f must be Boolean");
  trueCount += booleanValue;
}
assert(trueCount === 2 ** 15, "f must have uniform mass 1/2");

const walsh = [];
for (let support = 0; support < 128; support += 1) {
  let value = 0;
  for (let input = 0; input < 128; input += 1) {
    value += truth[input] * (parity(input & support) === 0 ? 1 : -1);
  }
  walsh.push(value);
}
const parsevalNumerator = walsh.reduce(
  (total, value) => total + BigInt(value * value),
  0n,
);
assert(parsevalNumerator === 16384n, "Walsh Parseval numerator must be 128^2");

// Directly verify every advertised ambient Fourier coefficient.  For g the
// unnormalized 16-cube numerator is 512*W(z); passing to f=(1+g)/2 and
// dividing by 2^16 gives W(z)/256.  The packet energy plus the constant
// coefficient already exhausts Parseval for Boolean f, so every coefficient
// outside {empty} union packet is zero.
for (let index = 0; index < packet.length; index += 1) {
  let ambientFourierNumerator = 0;
  for (let input = 0; input < 2 ** 16; input += 1) {
    ambientFourierNumerator +=
      signedAmbientTruth[input] * (parity(packet[index] & input) === 0 ? 1 : -1);
  }
  assert(
    ambientFourierNumerator === 512 * walsh[index],
    "ambient Fourier coefficient must equal the packet Walsh coefficient",
  );
}

// C=H^perp has complementary dimension, so all characters from the nonzero
// coset a+H average to zero on the structured base code.  Consequently every
// fixed-mask structured-base mass is the constant coefficient 1/2.
for (const support of packet) {
  let characterSum = 0;
  for (const base of masks) {
    characterSum += parity(support & base) === 0 ? 1 : -1;
  }
  assert(characterSum === 0, "packet support must vanish on structured averaging");
}

const coefficientDenominatorSq = 65536n; // 256^2
const maskCount = 512n;
const commonDenominator = maskCount * coefficientDenominatorSq;
let diagonalNumerator = 0n;
let energyNumerator = 0n;
let badAdjustmentNumerator = 0n;
let badCount = 0;
const badIntersectionSizes = new Map();
const intersectionSizes = new Map();

for (const frozenSet of masks) {
  const surviving = [];
  for (let index = 0; index < packet.length; index += 1) {
    if ((packet[index] & (~frozenSet & 0xffff)) === 0) surviving.push(index);
  }
  intersectionSizes.set(
    surviving.length,
    (intersectionSizes.get(surviving.length) || 0) + 1,
  );

  let coefficientSumNumerator = 0n;
  let diagonalAtMaskNumerator = 0n;
  for (const index of surviving) {
    const coefficientNumerator = BigInt(walsh[index]);
    coefficientSumNumerator += coefficientNumerator;
    diagonalAtMaskNumerator += coefficientNumerator * coefficientNumerator;
  }
  const energyAtMaskNumerator =
    coefficientSumNumerator * coefficientSumNumerator;
  assert(
    diagonalAtMaskNumerator <= coefficientDenominatorSq / 4n,
    "every fixed-mask diagonal must be at most total nonconstant energy 1/4",
  );
  diagonalNumerator += diagonalAtMaskNumerator;
  energyNumerator += energyAtMaskNumerator;

  // p=1/2, so p E_mask > D_mask iff E-numerator > 2 D-numerator.
  if (energyAtMaskNumerator > 2n * diagonalAtMaskNumerator) {
    badCount += 1;
    badIntersectionSizes.set(
      surviving.length,
      (badIntersectionSizes.get(surviving.length) || 0) + 1,
    );
    badAdjustmentNumerator +=
      coefficientDenominatorSq - diagonalAtMaskNumerator;
  }
}

// This is the minimum admissible exceptional set: every seed producing one
// of these violating masks must be bad.  Since D_mask<=1/4, every additional
// bad seed has positive charge 1-D_mask, so a larger bad set cannot repair
// the failed budget.

assertDistribution(
  [...intersectionSizes].sort((left, right) => left[0] - right[0]),
  [[0, 377], [1, 28], [2, 6], [4, 96], [16, 4], [128, 1]],
  "packet/mask intersection distribution",
);
assert(badCount === 88, "expected exactly 88 bad masks");
assertDistribution(
  [...badIntersectionSizes].sort((left, right) => left[0] - right[0]),
  [[4, 84], [16, 4]],
  "bad-mask intersection distribution",
);

assertFraction(
  diagonalNumerator,
  commonDenominator,
  1581n,
  524288n,
  "D_avg",
);
assertFraction(
  energyNumerator,
  commonDenominator,
  6843n,
  1048576n,
  "E_avg",
);
assertFraction(
  badAdjustmentNumerator,
  commonDenominator,
  44629n,
  262144n,
  "bad adjustment",
);

const certificateNumerator = diagonalNumerator + badAdjustmentNumerator;
assertFraction(
  certificateNumerator,
  commonDenominator,
  90839n,
  524288n,
  "complement-balanced certificate functional",
);
assert(
  8n * certificateNumerator > commonDenominator,
  "certificate functional must exceed the 1/8 budget",
);
assert(
  4n * energyNumerator < commonDenominator,
  "the witness must not refute the separate absolute E<=1/4 target",
);

const excessNumerator = 8n * certificateNumerator - commonDenominator;
const excessDenominator = 8n * commonDenominator;
assertFraction(
  excessNumerator,
  excessDenominator,
  25303n,
  524288n,
  "excess over 1/8",
);

console.log("selector complement-balanced rank-7 exact audit: PASS");
console.log("function: literal Boolean f=(1+chi_a*q(linear dual coordinates))/2");
console.log("packet: a+H, a=0x003c, |H|=128, minimum support weight=4");
console.log("mask intersections: 0:377, 1:28, 2:6, 4:96, 16:4, 128:1");
console.log("bad masks: 88 (84 four-point, 4 sixteen-point)");
console.log("D_avg=1581/524288");
console.log("E_avg=6843/1048576 < 1/4");
console.log("bad adjustment=44629/262144");
console.log("B=90839/524288 > 1/8 by 25303/524288");
