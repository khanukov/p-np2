import Pnp4.Frontier.SearchMCSPConcreteTargets

namespace Pnp4
namespace Frontier
namespace ContractExpansion

/-!
# Concrete-codec feasibility: the self-delimiting-encoder gap

Block 12a of the downstream extraction effort — a **precise blocker module** for
building a concrete `TreeCircuitWitnessCodec`, with the one tractable reduction
proved.

## Audit summary

`TreeCircuitWitnessCodec threshold` (`SearchMCSPConcreteTargets.lean`) asks for a
*fixed-width* serialization of circuits:

```
witnessBits : Nat → Nat
encode      : ∀ n, Circuit n → BitVec (witnessBits n)
decode      : ∀ n, BitVec (witnessBits n) → Option (Circuit n)
decode_encode : ∀ n c, size c ≤ threshold n → decode n (encode n c) = some c
```

* `Pnp3.Models.Circuit n` is a 5-constructor inductive (`input`/`const`/`not`/`and`/`or`)
  with `DecidableEq`; `size` counts gates.
* `AlgorithmsToLowerBounds.BitVec n = Fin n → Bool`, so `witnessBits n` is a width
  fixed by `n` alone.
* **A prefix-free encoder already exists** in the pnp3 TM-verifier toolkit
  (`Complexity/TMVerifier/TuringToolkit/Encoding.lean`): `encodeCircuitTree` /
  `decodeCircuitTreeAtDepth` for an *isomorphic* `CircuitTree` type, with a proven
  round-trip `decode (encode c ++ rest) = some (c, rest)` and a **lower** length
  bound (`3·size ≤ length`).

## What is missing (the precise blocker)

A concrete codec is **not** a small build.  Three pieces are missing, captured
exactly as the fields of `SelfDelimitingCircuitCode` below:

1. a *native* `Circuit` prefix-free encoder/decoder with the round-trip (the
   `CircuitTree` proof transfers mechanically — same constructors — but no bridge
   exists yet);
2. an **upper** length bound `(enc c).length ≤ witnessBits n` for every size-bounded
   circuit (only the lower bound exists; this is what fixes a width `witnessBits n`);
3. the fixed-length packing of a variable-length codeword into `BitVec (witnessBits n)`.

## What this module proves

Piece (3) — the packing — is the one tractable step, and it is **proved here**:
a self-delimiting (prefix-free) encoder with a width bound yields a fixed-length
codec by **zero-padding** (clean precisely because a prefix-free decoder ignores the
trailing pad).  `SelfDelimitingCircuitCode.toCodec` is a verified
`SelfDelimitingCircuitCode threshold → TreeCircuitWitnessCodec threshold`.

So the remaining work is reduced to pieces (1)–(2): build the native `Circuit`
encoder and prove its length upper bound; this module confirms those obligations are
**sufficient**.

Scope discipline — blocker interface + packing reduction only:

* **no** concrete encoder is built and **no** length bound is proved here — those are
  the explicit obligation fields, left open;
* **no** lower-bound proof, **no** NP-verifier construction, **no**
  `SearchMCSPMagnificationContract` change, **no** endpoint.
-/

variable {threshold : Nat → Nat}

/-- Pack a bit-list into a fixed-width bit vector by indexed lookup, padding short
lists with `false` (out-of-range indices read the default). -/
def listToFixedBitVec (l : List Bool) (L : Nat) : AlgorithmsToLowerBounds.BitVec L :=
  fun i => l.getD i.1 false

/-- Reading back a `listToFixedBitVec` packing recovers the original list followed by
a `false` pad, provided the list fits in the width. -/
theorem ofFn_listToFixedBitVec
    (l : List Bool) (L : Nat) (hL : l.length ≤ L) :
    List.ofFn (listToFixedBitVec l L)
      = l ++ List.replicate (L - l.length) false := by
  unfold listToFixedBitVec
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn]
    show l.getD i false = (l ++ List.replicate (L - l.length) false)[i]
    rw [List.getD_eq_getElem?_getD]
    by_cases hi : i < l.length
    · rw [List.getElem_append_left hi, List.getElem?_eq_getElem hi, Option.getD_some]
    · push_neg at hi
      rw [List.getElem_append_right hi, List.getElem_replicate,
        List.getElem?_eq_none_iff.mpr hi, Option.getD_none]

/--
The remaining obligations for a concrete tree-circuit codec, phrased natively over
`Pnp3.Models.Circuit`: a self-delimiting (prefix-free) encoder/decoder with a
round-trip, plus a width bound on the encodings of size-bounded circuits.

These are exactly the pieces *not yet built* (pieces (1)–(2) above); the prefix-free
`CircuitTree` machinery in the pnp3 TM-verifier toolkit is the intended source for
`enc`/`dec`/`dec_enc`, and `enc_len_le` is the missing encoding-length upper bound.
-/
structure SelfDelimitingCircuitCode (threshold : Nat → Nat) where
  /-- Fixed serialization width per input count. -/
  witnessBits : Nat → Nat
  /-- Variable-length self-delimiting encoder. -/
  enc : ∀ n, Pnp3.Models.Circuit n → List Bool
  /-- Prefix-free decoder: consumes exactly one codeword, returns it and the tail. -/
  dec : ∀ n, List Bool → Option (Pnp3.Models.Circuit n × List Bool)
  /-- Round-trip: a codeword followed by any tail decodes to the circuit and that
  untouched tail (this is the defining prefix-free property). -/
  dec_enc : ∀ n (c : Pnp3.Models.Circuit n) (rest : List Bool),
    dec n (enc n c ++ rest) = some (c, rest)
  /-- The encoding of every size-bounded circuit fits in the fixed width. -/
  enc_len_le : ∀ n (c : Pnp3.Models.Circuit n),
    Pnp3.Models.Circuit.size c ≤ threshold n → (enc n c).length ≤ witnessBits n

/--
**Packing reduction (the proved bridge).**  A self-delimiting circuit encoder with a
width bound yields a concrete `TreeCircuitWitnessCodec`: `encode` zero-pads the
codeword to the fixed width, and `decode` runs the prefix-free decoder (which ignores
the pad), so the round-trip survives for every size-bounded circuit.
-/
def SelfDelimitingCircuitCode.toCodec
    (S : SelfDelimitingCircuitCode threshold) :
    TreeCircuitWitnessCodec threshold where
  witnessBits := S.witnessBits
  encode := fun n c => listToFixedBitVec (S.enc n c) (S.witnessBits n)
  decode := fun n bits => (S.dec n (List.ofFn bits)).map Prod.fst
  decode_encode := by
    intro n c hsize
    show (S.dec n (List.ofFn (listToFixedBitVec (S.enc n c) (S.witnessBits n)))).map Prod.fst
        = some c
    rw [ofFn_listToFixedBitVec (S.enc n c) (S.witnessBits n) (S.enc_len_le n c hsize)]
    simp [S.dec_enc]

end ContractExpansion
end Frontier
end Pnp4
