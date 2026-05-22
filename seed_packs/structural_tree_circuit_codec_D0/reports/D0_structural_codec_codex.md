# D0 structural TreeCircuitWitnessCodec design report

## 1. Executive verdict

**GREEN_OPEN_STRUCTURAL_CODEC_L0**

The finite-index one-hot codec is useful for interface plumbing, but it is not
an appropriate long-term witness representation for SearchMCSP lower-bound
feasibility. A compact structural codec is feasible and should be pursued.

---

## 2. Encoding layout

We propose a **fixed-width preorder node stream** with explicit arity tags.
Let:

- `T := threshold n`
- `N := n` (input variable count)
- `idxWidth := Nat.log2 (N + 1) + 1`
- `nodeWidth := 3 + idxWidth`
- `maxNodes := T`

### Node tag (3 bits)

Use 3-bit tags:

- `000` = padding/empty slot
- `001` = const false
- `010` = const true
- `011` = input
- `100` = not
- `101` = and
- `110` = or
- `111` = reserved/invalid

### Payload

- For `input`, payload stores input index in `idxWidth` bits.
- For non-input tags, payload bits are zero-filled.

### Global layout

Witness is:

1. `lenWidth := Nat.log2 (T + 1) + 1` bits for declared node count `m`.
2. `maxNodes * nodeWidth` bits for node slots.

Hence:

`structuralWitnessBits threshold n := lenWidth + T * nodeWidth`.

### Tree structure rule

Decoder reads first `m` nodes and recursively rebuilds tree in preorder:

- `const` / `input` consume one node.
- `not` consumes one node + one subtree.
- `and` / `or` consume one node + two subtrees.

Padding slots after `m` are ignored.

---

## 3. Size budget

Proposed:

`structuralWitnessBits threshold n = (log2(T+1)+1) + T * (3 + (log2(n+1)+1))`.

Properties:

- polynomial in `T` and `log n` (hence polynomial in `T,n`);
- **not** proportional to `card(circuitsOfSizeAtMost n T)`;
- dramatically smaller than finite-index one-hot for realistic `T`.

This is compatible with the D0 requirement for compactness.

---

## 4. Encode algorithm

For circuit `c : Circuit n` with `c.size ≤ T`:

1. Traverse `c` in preorder and emit node descriptors (tag + payload).
2. Let resulting descriptor list length be `m`.
3. Encode `m` in `lenWidth` bits.
4. Write descriptors into first `m` slots of size `nodeWidth`.
5. Fill remaining `T-m` slots with padding tag `000` and zero payload.

If `c.size > T`, encoder may still output a canonical invalid/padding witness,
but the codec theorem only needs the bounded case.

---

## 5. Decode algorithm

Given witness bits:

1. Parse `m` from length header; reject if `m > T`.
2. Parse first `m` descriptors into a list.
3. Run recursive parser `parseTree : List Desc → Option (Circuit n × List Desc)`:
   - for leaf tags (`const`,`input`) create node;
   - for unary/binary tags recursively parse child(ren);
   - fail on invalid tags (`111`) or malformed input index (`idx ≥ n`).
4. Accept only if parser consumes all `m` descriptors exactly.

Output `some circuit` on success; otherwise `none`.

---

## 6. Round-trip theorem target

Target theorem shape:

```lean
theorem decode_encode_structural
  (threshold : Nat → Nat) (n : Nat) (c : Pnp3.Models.Circuit n)
  (hc : c.size ≤ threshold n) :
  decodeCircuit threshold n (encodeCircuit threshold n c) = some c
```

where `decodeCircuit` / `encodeCircuit` are the structural codec functions.

---

## 7. Complexity / naturalness audit

Why this is more natural than finite-index one-hot:

1. **Syntax-directed representation**: witness mirrors the circuit AST rather
   than choosing an arbitrary index in an overapproximation set.
2. **Compactness**: size scales with circuit-size budget and input-index width,
   not with enumeration cardinality.
3. **Robustness**: relation correctness remains semantic (`ComputesTruthTable`),
   but representation no longer bakes in combinatorial explosion.
4. **Magnification relevance**: if `hWeak` eventually holds, it is less likely to
   be dismissed as a pure encoding artifact.

---

## 8. Failure modes (expected Lean blockers)

1. **Recursive parser proof engineering**
   - proving total-consumption and uniqueness lemmas for preorder parse.
2. **Fixed-width bit slicing arithmetic**
   - index offsets for header/slots, especially with dependent `Fin` bounds.
3. **Input index validity proof**
   - convert payload nat to `Fin n` with clean error handling.
4. **Padding invariants**
   - show padding does not affect decode when `m` is valid.
5. **Round-trip strengthening lemmas**
   - likely need intermediate theorem: parser round-trip on descriptor lists
     before bit-level serialization round-trip.

---

## Recommended L0 implementation slice (next immediate move)

Implement only a **base-node codec probe** first:

- descriptor tag encode/decode round-trip;
- constant/input node encode/decode round-trip;
- fixed-width index payload encode/decode round-trip;
- no recursion yet.

This minimizes risk and creates reusable lemmas for full structural decoder.
