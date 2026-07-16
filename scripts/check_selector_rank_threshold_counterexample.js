#!/usr/bin/env node
"use strict";

/*
 * Exact finite obstruction to a universal rank-threshold selector lemma.
 *
 * Parameters are m = 1, tailBits = 1, n = 6, so N = 64 and the
 * structured independence is q = 4m+1 = 5.  For one exposed field
 * coordinate, the degree-<5 evaluation source is the binary trace code
 *
 *   C = { (Tr(a*x + b*x^3) + c)_{x in GF(64)} :
 *         a,b in GF(64), c in GF(2) }.
 *
 * The trace form is basis-independent.  Every nonzero GF(2)-linear field
 * coordinate is Tr(lambda * -), and the coefficients absorb lambda.  Trace
 * invariance under Frobenius folds the degree-2 and degree-4 terms into the
 * degree-1 term, leaving exactly the displayed a*x + b*x^3 form.
 *
 * We enumerate only the 2^13 codewords of C.  We deliberately do NOT
 * enumerate the Boolean set A inside the 2^64-element truth-table cube.
 * Instead, all bounds on A use exact dimension/cardinality inequalities.
 *
 * Define L_M to be the coordinate subspace supported on a mask M, let
 *
 *   S = { M in C : |M| <= 32 },
 *   A = union_{M in S} (C + L_M).
 *
 * A one-round output is B + (M & U), with B,M uniform in C and U uniform.
 * Hence a selected mask always produces an output in A.  On the other hand,
 * for nonzero M in C we have M in C intersect L_M, so
 *
 *   dim(C + L_M) <= dim(C) + |M| - 1 <= 44.
 *
 * This gives an exact generator/uniform distinguishing gap without building
 * A.  Low-degree cancellation and the existing diagonal estimate then force
 * a violation of DualFarBound.  Finally, the exact Abel bridge forces some
 * intermediate cumulative rank sum C(level), level in {5,...,12}, above 4.
 *
 * This script is a bounded exact audit, not a Lean theorem and not a
 * counterexample to a selector lemma that additionally uses quantitative
 * near-linear one-tape transition geometry.
 */

const MAGNIFICATION_M = 1;
const TAIL_BITS = 1;
const STRUCTURED_INDEPENDENCE = 4 * MAGNIFICATION_M + 1;
const CUTOFF = 2 * MAGNIFICATION_M;
const FIELD_DEGREE = 6;
const FIELD_SIZE = 1 << FIELD_DEGREE;
const FIELD_MODULUS = 0b1000011; // x^6 + x + 1
const CODE_DIMENSION = 13;
const CODE_SIZE = 1 << CODE_DIMENSION;
const MIN_ALIAS_RANK = STRUCTURED_INDEPENDENCE * TAIL_BITS;
const FULL_CODE_RANK = CODE_DIMENSION;

assert(MAGNIFICATION_M === 1, "this finite audit is specialized to m=1");
assert(TAIL_BITS === 1, "this finite audit is specialized to tailBits=1");
assert(STRUCTURED_INDEPENDENCE === 5, "wrong structured independence");
assert(CUTOFF === 2, "wrong high-degree cutoff");
assert(MIN_ALIAS_RANK === 5, "wrong minimum distinct-alias rank");

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function gcd(left, right) {
  let a = left < 0n ? -left : left;
  let b = right < 0n ? -right : right;
  while (b !== 0n) [a, b] = [b, a % b];
  return a;
}

class Fraction {
  constructor(numerator, denominator = 1n) {
    assert(denominator !== 0n, "fraction denominator must be nonzero");
    let num = BigInt(numerator);
    let den = BigInt(denominator);
    if (den < 0n) {
      num = -num;
      den = -den;
    }
    const divisor = gcd(num, den);
    this.numerator = num / divisor;
    this.denominator = den / divisor;
  }

  subtract(other) {
    return new Fraction(
      this.numerator * other.denominator -
        other.numerator * this.denominator,
      this.denominator * other.denominator,
    );
  }

  multiply(other) {
    return new Fraction(
      this.numerator * other.numerator,
      this.denominator * other.denominator,
    );
  }

  divide(other) {
    assert(other.numerator !== 0n, "division by zero fraction");
    return new Fraction(
      this.numerator * other.denominator,
      this.denominator * other.numerator,
    );
  }

  compare(other) {
    const difference =
      this.numerator * other.denominator -
      other.numerator * this.denominator;
    return difference < 0n ? -1 : difference > 0n ? 1 : 0;
  }

  equals(other) {
    return this.compare(other) === 0;
  }

  toString() {
    return this.denominator === 1n
      ? `${this.numerator}`
      : `${this.numerator}/${this.denominator}`;
  }

  toDecimal(digits = 12) {
    return (Number(this.numerator) / Number(this.denominator)).toFixed(digits);
  }
}

function powTwo(exponent) {
  return 1n << BigInt(exponent);
}

function polynomialDegree(polynomial) {
  let value = polynomial;
  let degree = -1;
  while (value !== 0) {
    value >>>= 1;
    degree += 1;
  }
  return degree;
}

function polynomialRemainder(dividend, divisor) {
  let value = dividend;
  const divisorDegree = polynomialDegree(divisor);
  while (value !== 0 && polynomialDegree(value) >= divisorDegree) {
    value ^= divisor << (polynomialDegree(value) - divisorDegree);
  }
  return value;
}

function modulusIsIrreducible() {
  // A reducible polynomial of degree six has a factor of degree at most three.
  for (let degree = 1; degree <= 3; degree += 1) {
    for (let lower = 0; lower < 1 << degree; lower += 1) {
      const candidate = (1 << degree) | lower;
      if (polynomialRemainder(FIELD_MODULUS, candidate) === 0) return false;
    }
  }
  return true;
}

function fieldMultiply(left, right) {
  let a = left;
  let b = right;
  let result = 0;
  while (b !== 0) {
    if ((b & 1) !== 0) result ^= a;
    b >>>= 1;
    a <<= 1;
    if ((a & FIELD_SIZE) !== 0) a ^= FIELD_MODULUS;
  }
  return result & (FIELD_SIZE - 1);
}

function fieldTrace(value) {
  let current = value;
  let result = 0;
  for (let index = 0; index < FIELD_DEGREE; index += 1) {
    result ^= current;
    current = fieldMultiply(current, current);
  }
  assert(result === 0 || result === 1, "GF(64) trace did not land in GF(2)");
  return result;
}

const traceTable = Array.from({ length: FIELD_SIZE }, (_, value) =>
  fieldTrace(value),
);
const cubeTable = Array.from({ length: FIELD_SIZE }, (_, value) =>
  fieldMultiply(fieldMultiply(value, value), value),
);

function traceCodeword(a, b, constant) {
  let word = 0n;
  for (let point = 0; point < FIELD_SIZE; point += 1) {
    const value =
      fieldMultiply(a, point) ^ fieldMultiply(b, cubeTable[point]);
    const bit = traceTable[value] ^ constant;
    if (bit !== 0) word |= 1n << BigInt(point);
  }
  return word;
}

function popcount(value) {
  let current = value;
  let count = 0;
  while (current !== 0n) {
    current &= current - 1n;
    count += 1;
  }
  return count;
}

function highestSetBit(value) {
  return value.toString(2).length - 1;
}

function binaryRank(rows) {
  const pivots = new Map();
  for (const original of rows) {
    let value = original;
    while (value !== 0n) {
      const pivot = highestSetBit(value);
      if (pivots.has(pivot)) value ^= pivots.get(pivot);
      else {
        pivots.set(pivot, value);
        break;
      }
    }
  }
  return pivots.size;
}

function binomial(n, k) {
  let result = 1;
  for (let index = 1; index <= k; index += 1) {
    result = (result * (n - k + index)) / index;
  }
  return result;
}

function verifyNoDualWordOfWeightAtMostFive(generatorWords) {
  const columns = Array.from({ length: FIELD_SIZE }, (_, coordinate) => {
    let syndrome = 0;
    for (let row = 0; row < generatorWords.length; row += 1) {
      if (((generatorWords[row] >> BigInt(coordinate)) & 1n) !== 0n) {
        syndrome |= 1 << row;
      }
    }
    return syndrome;
  });

  let checked = 0;
  function checkSubsets(start, remaining, syndrome) {
    if (remaining === 0) {
      checked += 1;
      assert(syndrome !== 0, "found a dual word of weight at most five");
      return;
    }
    for (
      let coordinate = start;
      coordinate <= FIELD_SIZE - remaining;
      coordinate += 1
    ) {
      checkSubsets(
        coordinate + 1,
        remaining - 1,
        syndrome ^ columns[coordinate],
      );
    }
  }

  let expected = 0;
  for (let weight = 1; weight <= 5; weight += 1) {
    checkSubsets(0, weight, 0);
    expected += binomial(FIELD_SIZE, weight);
  }
  assert(checked === expected, "did not exhaust every support of size at most five");
  return checked;
}

assert(modulusIsIrreducible(), "x^6+x+1 must be irreducible over GF(2)");

const naturalGenerators = [];
for (let bit = 0; bit < FIELD_DEGREE; bit += 1) {
  naturalGenerators.push(traceCodeword(1 << bit, 0, 0));
}
for (let bit = 0; bit < FIELD_DEGREE; bit += 1) {
  naturalGenerators.push(traceCodeword(0, 1 << bit, 0));
}
naturalGenerators.push(traceCodeword(0, 0, 1));
assert(
  binaryRank(naturalGenerators) === CODE_DIMENSION,
  "the thirteen trace-code generators must be independent",
);

const codewords = new Set();
const weightDistribution = new Map();
let selectedMasks = 0;
for (let a = 0; a < FIELD_SIZE; a += 1) {
  for (let b = 0; b < FIELD_SIZE; b += 1) {
    for (let constant = 0; constant <= 1; constant += 1) {
      const word = traceCodeword(a, b, constant);
      codewords.add(word);
      const weight = popcount(word);
      weightDistribution.set(weight, (weightDistribution.get(weight) || 0) + 1);
      if (weight <= FIELD_SIZE / 2) selectedMasks += 1;
    }
  }
}

assert(codewords.size === CODE_SIZE, "trace parametrization must be injective");
assert(selectedMasks === 5167, "wrong number of selected masks");

const expectedWeightDistribution = new Map([
  [0, 1],
  [24, 336],
  [28, 2688],
  [32, 2142],
  [36, 2688],
  [40, 336],
  [64, 1],
]);
assert(
  JSON.stringify([...weightDistribution].sort((x, y) => x[0] - y[0])) ===
    JSON.stringify([...expectedWeightDistribution]),
  "wrong GF(64) trace-code weight distribution",
);

const supportsChecked = verifyNoDualWordOfWeightAtMostFive(naturalGenerators);

const selectedNonzeroMasks = selectedMasks - 1;
const maximumSelectedNonzeroWeight = 32;
const maximumSelectedSumDimension =
  CODE_DIMENSION + maximumSelectedNonzeroWeight - 1;
assert(maximumSelectedSumDimension === 44, "wrong C+L_M dimension cap");

const generatorMassLower = new Fraction(BigInt(selectedMasks), powTwo(CODE_DIMENSION));
const uniformMassUpper = new Fraction(
  powTwo(CODE_DIMENSION) +
    BigInt(selectedNonzeroMasks) * powTwo(maximumSelectedSumDimension),
  powTwo(FIELD_SIZE),
);
const gapLower = generatorMassLower.subtract(uniformMassUpper);

assert(
  gapLower.equals(
    new Fraction(1409200244654079n, 2251799813685248n),
  ),
  "wrong exact distinguishing-gap lower bound",
);
assert(gapLower.compare(new Fraction(1n, 2n)) > 0, "gap must exceed one half");

// Cauchy: secondMoment >= |E highTail|^2 >= gapLower^2.
const secondMomentLower = gapLower.multiply(gapLower);

// For p=1/2, the exact diagonal theorem gives p^(cutoff+1).
const diagonalUpper = new Fraction(1n, powTwo(CUTOFF + 1));
const dualFarLower = secondMomentLower.subtract(diagonalUpper);
const dualFarBudget = new Fraction(1n, powTwo(2 * MAGNIFICATION_M + 1));
assert(
  dualFarLower.equals(
    new Fraction(
      1352020029419001408470019735553n,
      5070602400912917605986812821504n,
    ),
  ),
  "wrong exact DualFar lower bound",
);
assert(
  dualFarLower.compare(dualFarBudget) > 0,
  "DualFar lower bound must exceed the required 1/8 budget",
);

/*
 * The mask-constraint rank is at most dim(C)=13.  Since A is invariant under
 * addition by C, its Fourier support lies in D=C^perp.  The verified dual
 * distance is at least six, so the only degree-<=2 support in D is empty.
 * Also 0 belongs to A.  If mu is the uniform density of A, the terminal
 * cumulative form is exactly
 *
 *   (1-mu)^2 - (mu-mu^2) = 1 - 3mu + 2mu^2 <= 1.
 *
 * Combining all Abel coefficients at levels >=13 gives terminal weight
 * 2^-13.  The total weight on levels 5,...,12 is 2^-5 - 2^-13.
 */
const terminalWeight = new Fraction(1n, powTwo(FULL_CODE_RANK));
const intermediateWeight = new Fraction(1n, powTwo(MIN_ALIAS_RANK)).subtract(
  terminalWeight,
);
const terminalCumulativeUpper = new Fraction(1n);
const forcedIntermediateCumulativeLower = dualFarLower
  .subtract(terminalWeight.multiply(terminalCumulativeUpper))
  .divide(intermediateWeight);

assert(
  forcedIntermediateCumulativeLower.equals(
    new Fraction(
      1351401059399358718332570173441n,
      157837355008885985049638338560n,
    ),
  ),
  "wrong forced cumulative-rank lower bound",
);
assert(
  forcedIntermediateCumulativeLower.compare(new Fraction(4n)) > 0,
  "some intermediate cumulative rank sum must exceed four",
);

console.log("Exact GF(64) selector rank-threshold counterexample audit");
console.log(`  modulus: x^6+x+1 (irreducible)`);
console.log(`  code: |C|=${codewords.size}=2^${CODE_DIMENSION}, rank=${CODE_DIMENSION}`);
console.log(
  `  weights: ${[...weightDistribution]
    .sort((left, right) => left[0] - right[0])
    .map(([weight, count]) => `${weight}^${count}`)
    .join(", ")}`,
);
console.log(
  `  dual-distance audit: ${supportsChecked} nonempty supports of size <=5 checked; none is dual`,
);
console.log(`  selected masks |M|<=32: ${selectedMasks}/${CODE_SIZE}`);
console.log(
  `  proof-only set A is NOT enumerated; dim(C+L_M)<=${maximumSelectedSumDimension} for selected M!=0`,
);
console.log(
  `  generator mass lower: ${generatorMassLower} = ${generatorMassLower.toDecimal()}`,
);
console.log(
  `  uniform mass upper:   ${uniformMassUpper} = ${uniformMassUpper.toDecimal()}`,
);
console.log(`  gap lower g:           ${gapLower} = ${gapLower.toDecimal()}`);
console.log(
  `  second-moment lower:  ${secondMomentLower} = ${secondMomentLower.toDecimal()}`,
);
console.log(
  `  DualFar lower:        ${dualFarLower} = ${dualFarLower.toDecimal()}`,
);
console.log(`  DualFar budget:       ${dualFarBudget} = ${dualFarBudget.toDecimal()}`);
console.log(
  `  Abel weights: levels 5..12 have ${intermediateWeight}; terminal rank>=13 has ${terminalWeight}`,
);
console.log(
  `  forced max C(level), level in {5,...,12}: >= ${forcedIntermediateCumulativeLower}`,
);
console.log(
  `  decimal forced lower: ${forcedIntermediateCumulativeLower.toDecimal()} > 4`,
);
console.log(
  "PASS: universal Boolean cumulative-four and premise-free DualFar bounds are refuted at n=6; no claim is made against a quantitatively near-linear one-tape selector lemma.",
);
