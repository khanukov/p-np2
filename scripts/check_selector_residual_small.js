#!/usr/bin/env node
"use strict";

/*
 * Exact finite check for the structured selector residual-mass frontier.
 *
 * Scope:
 *   - n = 3, 4, m = 1: enumerate every degree-<5 polynomial seed, every
 *     Fourier support, and (for n=4,t=2) every multiplicative orbit of
 *     codimension-two prefix-zero subspaces.  All arithmetic used in the
 *     asserted inequalities is integral/BigInt arithmetic.
 *   - n = 5, m = 1, t = 1: verify the first large positive-row barrier and
 *     two exact linear-code indicator probes.
 *
 * This is bounded computational evidence, not a Lean theorem and not an
 * extrapolation to arbitrary n.  The polynomial-basis representatives use
 * x^3+x+1, x^4+x+1, and x^5+x^2+1.  Changing the chosen GF(2)-basis merely
 * permutes evaluation nodes.  For prefix-zero false sets, scalar
 * multiplication is transitive for dimensions 0, 1, n-1, and n; in the one
 * exceptional case used here (n=4,t=2), all three scalar orbits are checked.
 *
 * Run from the repository root:
 *
 *   node scripts/check_selector_residual_small.js
 */

const startedAt = Date.now();

function assert(condition, message) {
  if (!condition) throw new Error(message);
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

function popcountNumber(value) {
  let current = value >>> 0;
  let count = 0;
  while (current !== 0) {
    current = (current & (current - 1)) >>> 0;
    count += 1;
  }
  return count;
}

function popcountBigInt(value) {
  let current = value;
  let count = 0;
  while (current !== 0n) {
    current &= current - 1n;
    count += 1;
  }
  return count;
}

function parityBigInt(value) {
  return popcountBigInt(value) & 1;
}

function degreeBigInt(value) {
  let current = value;
  let degree = -1;
  while (current !== 0n) {
    current >>= 1n;
    degree += 1;
  }
  return degree;
}

function makeField(n, modulus) {
  const cardinality = 2 ** n;
  const multiplication = Array.from(
    { length: cardinality },
    () => new Uint8Array(cardinality),
  );

  function multiplyRaw(left, right) {
    let a = left;
    let b = right;
    let result = 0;
    while (b !== 0) {
      if ((b & 1) !== 0) result ^= a;
      b >>>= 1;
      a <<= 1;
      if ((a & cardinality) !== 0) a ^= modulus;
    }
    return result & (cardinality - 1);
  }

  for (let left = 0; left < cardinality; left += 1) {
    for (let right = 0; right < cardinality; right += 1) {
      multiplication[left][right] = multiplyRaw(left, right);
    }
  }

  function power(base, exponent) {
    let result = 1;
    let factor = base;
    let remaining = exponent;
    while (remaining !== 0) {
      if ((remaining & 1) !== 0) result = multiplication[result][factor];
      factor = multiplication[factor][factor];
      remaining >>>= 1;
    }
    return result;
  }

  return { n, cardinality, multiplication, power };
}

function evaluatePolynomial(field, coefficients, point) {
  let value = 0;
  for (let index = coefficients.length - 1; index >= 0; index -= 1) {
    value = field.multiplication[value][point] ^ coefficients[index];
  }
  return value;
}

function scalarOrbitOfFalseSet(field, falseSet) {
  const orbit = new Set();
  for (let scalar = 1; scalar < field.cardinality; scalar += 1) {
    let scaled = 0;
    for (let value = 0; value < field.cardinality; value += 1) {
      if ((falseSet & (1 << value)) !== 0) {
        scaled |= 1 << field.multiplication[scalar][value];
      }
    }
    orbit.add(scaled);
  }
  return orbit;
}

function assertFalseSetOrbitCoverage() {
  const gfEight = makeField(3, 0b1011);
  assert(
    scalarOrbitOfFalseSet(gfEight, 0x55).size === 7,
    "GF(8): the hyperplane representative must cover all 7 hyperplanes",
  );
  assert(
    scalarOrbitOfFalseSet(gfEight, 0x03).size === 7,
    "GF(8): the line representative must cover all 7 lines",
  );
  assert(
    scalarOrbitOfFalseSet(gfEight, 0x01).size === 1,
    "GF(8): the zero subspace must be unique",
  );

  const gfSixteen = makeField(4, 0b10011);
  assert(
    scalarOrbitOfFalseSet(gfSixteen, 0x5555).size === 15,
    "GF(16): the hyperplane representative must cover all 15 hyperplanes",
  );
  const planeOrbits = [0x000f, 0x0033, 0x00c3].map((falseSet) =>
    scalarOrbitOfFalseSet(gfSixteen, falseSet),
  );
  assert(
    JSON.stringify(planeOrbits.map((orbit) => orbit.size).sort((a, b) => a - b)) ===
      JSON.stringify([5, 15, 15]),
    "GF(16): wrong codimension-two scalar-orbit sizes",
  );
  const allPlanes = new Set(planeOrbits.flatMap((orbit) => [...orbit]));
  assert(
    allPlanes.size === 35,
    "GF(16): the three representatives must cover all 35 two-planes",
  );
  assert(
    scalarOrbitOfFalseSet(gfSixteen, 0x0003).size === 15,
    "GF(16): the line representative must cover all 15 lines",
  );
  assert(
    scalarOrbitOfFalseSet(gfSixteen, 0x0001).size === 1,
    "GF(16): the zero subspace must be unique",
  );
}

function structuredDualSupports(field, independence) {
  const coordinateCount = field.cardinality;
  const supportCount = 2 ** coordinateCount;
  const dual = [];

  for (let support = 0; support < supportCount; support += 1) {
    let isDual = true;
    for (let exponent = 0; exponent < independence && isDual; exponent += 1) {
      let powerSum = 0;
      for (let point = 0; point < coordinateCount; point += 1) {
        if ((support & (1 << point)) !== 0) {
          powerSum ^= exponent === 0 ? 1 : field.power(point, exponent);
        }
      }
      isDual = powerSum === 0;
    }
    if (isDual) dual.push(support);
  }

  return dual;
}

function polynomialMaskCounts(field, independence, falseSets) {
  const coordinateCount = field.cardinality;
  const supportCount = 2 ** coordinateCount;
  const totalSeeds = coordinateCount ** independence;
  const counts = falseSets.map(() => new Int32Array(supportCount));
  const coefficientMask = coordinateCount - 1;

  for (let encoded = 0; encoded < totalSeeds; encoded += 1) {
    let remaining = encoded;
    const coefficients = [];
    for (let index = 0; index < independence; index += 1) {
      coefficients.push(remaining & coefficientMask);
      remaining >>>= field.n;
    }

    const patterns = falseSets.map(() => 0);
    for (let point = 0; point < coordinateCount; point += 1) {
      const value = evaluatePolynomial(field, coefficients, point);
      for (let source = 0; source < falseSets.length; source += 1) {
        const isFalse = (falseSets[source] & (1 << value)) !== 0;
        if (!isFalse) patterns[source] |= 1 << point;
      }
    }
    for (let source = 0; source < counts.length; source += 1) {
      counts[source][patterns[source]] += 1;
    }
  }

  return { counts, totalSeeds };
}

function subsetZetaTransform(counts, coordinateCount) {
  const transformed = Int32Array.from(counts);
  const full = 2 ** coordinateCount - 1;
  for (let bit = 0; bit < coordinateCount; bit += 1) {
    const singleton = 1 << bit;
    for (let mask = 0; mask <= full; mask += 1) {
      if ((mask & singleton) !== 0) {
        transformed[mask] += transformed[mask ^ singleton];
      }
    }
  }
  return transformed;
}

function maxHighFourierRowNumerator(zeta, dual, coordinateCount, cutoff) {
  const full = 2 ** coordinateCount - 1;
  let maximum = -1;
  let maximizingSupport = 0;

  for (let left = 0; left <= full; left += 1) {
    if (popcountNumber(left) <= cutoff) continue;
    let row = 0;
    for (const difference of dual) {
      const right = left ^ difference;
      if (popcountNumber(right) <= cutoff) continue;
      row += zeta[full ^ (left | right)];
    }
    if (row > maximum) {
      maximum = row;
      maximizingSupport = left;
    }
  }
  return { maximum, maximizingSupport };
}

function checkMOneRows({ n, modulus, falseSets, expected }) {
  const field = makeField(n, modulus);
  const independence = 5;
  const dual = structuredDualSupports(field, independence);
  const { counts, totalSeeds } = polynomialMaskCounts(
    field,
    independence,
    falseSets,
  );

  assert(dual.length === expected.dualSize, `n=${n}: wrong dual size`);
  if (expected.dualWeightDistribution) {
    const distribution = new Map();
    for (const support of dual) {
      const weight = popcountNumber(support);
      distribution.set(weight, (distribution.get(weight) || 0) + 1);
    }
    assert(
      JSON.stringify([...distribution].sort((a, b) => a[0] - b[0])) ===
        JSON.stringify(expected.dualWeightDistribution),
      `n=${n}: wrong dual weight distribution`,
    );
  }

  const results = [];
  for (let source = 0; source < counts.length; source += 1) {
    const zeta = subsetZetaTransform(counts[source], field.cardinality);
    const row = maxHighFourierRowNumerator(
      zeta,
      dual,
      field.cardinality,
      2,
    );
    const wanted = expected.rows[source];
    assert(
      row.maximum === wanted.numerator,
      `${wanted.label}: expected numerator ${wanted.numerator}, got ${row.maximum}`,
    );
    assertFraction(
      BigInt(row.maximum),
      BigInt(totalSeeds),
      wanted.reducedNumerator,
      wanted.reducedDenominator,
      wanted.label,
    );
    const inducedL2Numerator = BigInt(row.maximum);
    const inducedL2Denominator = 4n * BigInt(totalSeeds);
    const targetDenominator = 1n << BigInt(2 * wanted.tailBits);
    assert(
      inducedL2Numerator * targetDenominator <= inducedL2Denominator,
      `${wanted.label}: row-sum/Boolean-energy bound misses the residual target`,
    );
    if (wanted.zeroMultiplicity !== undefined) {
      assert(
        counts[source][0] === wanted.zeroMultiplicity,
        `${wanted.label}: wrong all-false multiplicity`,
      );
    }
    const [l2Numerator, l2Denominator] = reducedFraction(
      inducedL2Numerator,
      inducedL2Denominator,
    );
    results.push({
      label: wanted.label,
      row: `${wanted.reducedNumerator}/${wanted.reducedDenominator}`,
      inducedBooleanL2Bound: `${l2Numerator}/${l2Denominator}`,
      target: `1/${targetDenominator}`,
      maximizingSupport: `0x${row.maximizingSupport.toString(16)}`,
    });
  }
  return results;
}

function reduceBigIntRows(rows) {
  const pivots = [];
  for (const original of rows) {
    let value = original;
    for (const pivot of pivots) {
      const degree = degreeBigInt(pivot);
      if (((value >> BigInt(degree)) & 1n) !== 0n) value ^= pivot;
    }
    if (value === 0n) continue;
    const degree = degreeBigInt(value);
    for (let index = 0; index < pivots.length; index += 1) {
      if (((pivots[index] >> BigInt(degree)) & 1n) !== 0n) {
        pivots[index] ^= value;
      }
    }
    pivots.push(value);
    pivots.sort((left, right) => degreeBigInt(right) - degreeBigInt(left));
  }
  return pivots;
}

function rankBigIntRows(rows) {
  return reduceBigIntRows(rows).length;
}

function rankNumberRows(rows) {
  const pivots = [];
  for (const original of rows) {
    let value = original >>> 0;
    for (const pivot of pivots) {
      const degree = 31 - Math.clz32(pivot);
      if (((value >>> degree) & 1) !== 0) value = (value ^ pivot) >>> 0;
    }
    if (value === 0) continue;
    const degree = 31 - Math.clz32(value);
    for (let index = 0; index < pivots.length; index += 1) {
      if (((pivots[index] >>> degree) & 1) !== 0) {
        pivots[index] = (pivots[index] ^ value) >>> 0;
      }
    }
    pivots.push(value);
    pivots.sort(
      (left, right) =>
        31 - Math.clz32(right) - (31 - Math.clz32(left)),
    );
  }
  return pivots.length;
}

function kernelCodewords(basis, zeroOn) {
  const pivots = [];
  const dependencies = [];
  for (let index = 0; index < basis.length; index += 1) {
    let value = basis[index] & zeroOn;
    let combination = 1 << index;
    for (const pivot of pivots) {
      const degree = degreeBigInt(pivot.value);
      if (((value >> BigInt(degree)) & 1n) !== 0n) {
        value ^= pivot.value;
        combination ^= pivot.combination;
      }
    }
    if (value === 0n) {
      dependencies.push(combination);
      continue;
    }
    const degree = degreeBigInt(value);
    for (const pivot of pivots) {
      if (((pivot.value >> BigInt(degree)) & 1n) !== 0n) {
        pivot.value ^= value;
        pivot.combination ^= combination;
      }
    }
    pivots.push({ value, combination });
    pivots.sort(
      (left, right) => degreeBigInt(right.value) - degreeBigInt(left.value),
    );
  }

  return dependencies.map((combination) => {
    let word = 0n;
    for (let index = 0; index < basis.length; index += 1) {
      if (((combination >>> index) & 1) !== 0) word ^= basis[index];
    }
    return word;
  });
}

function structuredBaseCodeBasis(field, independence) {
  const rows = [];
  const coordinateCount = field.cardinality;
  for (let exponent = 0; exponent < independence; exponent += 1) {
    for (let coefficientBit = 0; coefficientBit < field.n; coefficientBit += 1) {
      let row = 0n;
      const coefficient = 1 << coefficientBit;
      for (let point = 0; point < coordinateCount; point += 1) {
        const value = field.multiplication[coefficient][field.power(point, exponent)];
        if ((value & 1) !== 0) row |= 1n << BigInt(point);
      }
      rows.push(row);
    }
  }
  return reduceBigIntRows(rows);
}

function enumerateLinearCode(basis) {
  const words = [0n];
  const count = 2 ** basis.length;
  for (let encoded = 1; encoded < count; encoded += 1) {
    const lowBit = encoded & -encoded;
    const index = 31 - Math.clz32(lowBit);
    words[encoded] = words[encoded ^ lowBit] ^ basis[index];
  }
  return words;
}

function checkNFiveBarrierAndCodeProbes() {
  const field = makeField(5, 0b100101); // x^5 + x^2 + 1
  const coordinateCount = field.cardinality;
  const full = (1n << BigInt(coordinateCount)) - 1n;
  const basis = structuredBaseCodeBasis(field, 5);
  const rank = basis.length;
  const dualDimension = coordinateCount - rank;
  const codewords = enumerateLinearCode(basis);

  assert(rank === 11, `n=5: expected base-code rank 11, got ${rank}`);
  assert(dualDimension === 21, "n=5: expected dual dimension 21");

  const maskData = codewords.map((mask) => {
    const zeroSet = full ^ mask;
    const shortenedDualDimension =
      popcountBigInt(zeroSet) -
      rankBigIntRows(basis.map((row) => row & zeroSet));
    return { mask, shortenedDualDimension };
  });

  function isDual(word) {
    return basis.every((row) => parityBigInt(row & word) === 0);
  }

  const lowSupports = [0n];
  for (let first = 0; first < coordinateCount; first += 1) {
    lowSupports.push(1n << BigInt(first));
  }
  for (let first = 0; first < coordinateCount; first += 1) {
    for (let second = first + 1; second < coordinateCount; second += 1) {
      lowSupports.push(
        (1n << BigInt(first)) | (1n << BigInt(second)),
      );
    }
  }

  let minimumRowNumerator = null;
  let maximumRowNumerator = null;
  let maximizingSupport = 0n;
  for (let first = 0; first < coordinateCount; first += 1) {
    for (let second = first + 1; second < coordinateCount; second += 1) {
      for (let third = second + 1; third < coordinateCount; third += 1) {
        const support =
          (1n << BigInt(first)) |
          (1n << BigInt(second)) |
          (1n << BigInt(third));
        const excludedDifferences = lowSupports
          .map((right) => support ^ right)
          .filter(isDual);
        let rowNumerator = 0n;
        for (const { mask, shortenedDualDimension } of maskData) {
          if ((mask & support) !== 0n) continue;
          let surviving = 1n << BigInt(shortenedDualDimension);
          for (const difference of excludedDifferences) {
            if ((mask & difference) === 0n) surviving -= 1n;
          }
          rowNumerator += surviving;
        }
        if (
          minimumRowNumerator === null ||
          rowNumerator < minimumRowNumerator
        ) {
          minimumRowNumerator = rowNumerator;
        }
        if (
          maximumRowNumerator === null ||
          rowNumerator > maximumRowNumerator
        ) {
          maximumRowNumerator = rowNumerator;
          maximizingSupport = support;
        }
      }
    }
  }

  assert(
    minimumRowNumerator === maximumRowNumerator,
    "n=5: size-three row sums should be identical",
  );
  assertFraction(
    maximumRowNumerator,
    BigInt(codewords.length),
    277699n,
    256n,
    "n=5 positive-row barrier",
  );

  let baseCodeIndicatorNumerator = 0n;
  let dualCodeIndicatorNumerator = 0n;
  for (const mask of codewords) {
    const zeroSet = full ^ mask;

    const dualShorteningDimension =
      popcountBigInt(zeroSet) -
      rankBigIntRows(basis.map((row) => row & zeroSet));
    const baseDeviationNumerator =
      (1n << BigInt(dualShorteningDimension)) - 1n;
    baseCodeIndicatorNumerator +=
      baseDeviationNumerator * baseDeviationNumerator;

    const shortenedBaseBasis = kernelCodewords(basis, mask);
    const shortenedBaseDimension = shortenedBaseBasis.length;
    const pairingRows = shortenedBaseBasis.map((shortenedWord) => {
      let pairingRow = 0;
      for (let index = 0; index < rank; index += 1) {
        if (parityBigInt(shortenedWord & basis[index]) !== 0) {
          pairingRow |= 1 << index;
        }
      }
      return pairingRow;
    });
    const pairingRank = rankNumberRows(pairingRows);
    const orthogonalBaseWords = 1n << BigInt(rank - pairingRank);
    const nonorthogonalBaseWords =
      (1n << BigInt(rank)) - orthogonalBaseWords;
    const dualDeviationNumerator =
      (1n << BigInt(shortenedBaseDimension)) - 1n;
    dualCodeIndicatorNumerator +=
      orthogonalBaseWords *
        dualDeviationNumerator *
        dualDeviationNumerator +
      nonorthogonalBaseWords;
  }

  const baseCodeIndicatorDenominator =
    1n << BigInt(rank + 2 * dualDimension);
  const dualCodeIndicatorDenominator = 1n << BigInt(4 * rank);
  assertFraction(
    baseCodeIndicatorNumerator,
    baseCodeIndicatorDenominator,
    4398565582975n,
    9007199254740992n,
    "n=5 base-code indicator L2",
  );
  assertFraction(
    dualCodeIndicatorNumerator,
    dualCodeIndicatorDenominator,
    4192255n,
    8589934592n,
    "n=5 dual-code indicator L2",
  );

  assert(
    4n * baseCodeIndicatorNumerator < baseCodeIndicatorDenominator,
    "n=5 base-code indicator should satisfy the 1/4 target",
  );
  assert(
    4n * dualCodeIndicatorNumerator < dualCodeIndicatorDenominator,
    "n=5 dual-code indicator should satisfy the 1/4 target",
  );

  return {
    barrier: "277699/256",
    maximizingSupport: `0x${maximizingSupport.toString(16)}`,
    baseCodeIndicator: "4398565582975/9007199254740992",
    dualCodeIndicator: "4192255/8589934592",
  };
}

assertFalseSetOrbitCoverage();

const nThree = checkMOneRows({
  n: 3,
  modulus: 0b1011, // x^3 + x + 1
  falseSets: [0x55, 0x03, 0x01],
  expected: {
    dualSize: 2,
    dualWeightDistribution: [[0, 1], [8, 1]],
    rows: [
      {
        label: "n=3,t=1",
        tailBits: 1,
        numerator: 4352,
        reducedNumerator: 17n,
        reducedDenominator: 128n,
        zeroMultiplicity: 256,
      },
      {
        label: "n=3,t=2",
        tailBits: 2,
        numerator: 528,
        reducedNumerator: 33n,
        reducedDenominator: 2048n,
        zeroMultiplicity: 16,
      },
      {
        label: "n=3,t=3",
        tailBits: 3,
        numerator: 65,
        reducedNumerator: 65n,
        reducedDenominator: 32768n,
        zeroMultiplicity: 1,
      },
    ],
  },
});

const nFour = checkMOneRows({
  n: 4,
  modulus: 0b10011, // x^4 + x + 1
  falseSets: [0x5555, 0x000f, 0x0033, 0x00c3, 0x0003, 0x0001],
  expected: {
    dualSize: 128,
    dualWeightDistribution: [[0, 1], [6, 48], [8, 30], [10, 48], [16, 1]],
    rows: [
      {
        label: "n=4,t=1",
        tailBits: 1,
        numerator: 851968,
        reducedNumerator: 13n,
        reducedDenominator: 16n,
        zeroMultiplicity: 2048,
      },
      {
        label: "n=4,t=2 orbit 1",
        tailBits: 2,
        numerator: 30080,
        reducedNumerator: 235n,
        reducedDenominator: 8192n,
        zeroMultiplicity: 64,
      },
      {
        label: "n=4,t=2 orbit 2",
        tailBits: 2,
        numerator: 30080,
        reducedNumerator: 235n,
        reducedDenominator: 8192n,
        zeroMultiplicity: 64,
      },
      {
        label: "n=4,t=2 orbit 3",
        tailBits: 2,
        numerator: 29696,
        reducedNumerator: 29n,
        reducedDenominator: 1024n,
        zeroMultiplicity: 64,
      },
      {
        label: "n=4,t=3",
        tailBits: 3,
        numerator: 2428,
        reducedNumerator: 607n,
        reducedDenominator: 262144n,
        zeroMultiplicity: 2,
      },
      {
        label: "n=4,t=4",
        tailBits: 4,
        numerator: 383,
        reducedNumerator: 383n,
        reducedDenominator: 1048576n,
        zeroMultiplicity: 1,
      },
    ],
  },
});

const nFive = checkNFiveBarrierAndCodeProbes();

console.log("selector residual small-instance exact check: PASS");
console.log(JSON.stringify({ nThree, nFour, nFive }, null, 2));
console.log(`runtime_ms=${Date.now() - startedAt}`);
