import Pnp4.Frontier.SearchMCSPConcreteTargets
import Complexity.TMVerifier.TuringToolkit.Encoding

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-!
# Circuit ↔ CircuitTree bridge and a native prefix-free `Circuit` encoder

Block 12b of the downstream extraction effort — the first of the two obligations the
concrete-codec blocker (#1516, `ConcreteCodecGap.lean`) reduced the codec to.

The pnp3 TM-verifier toolkit
(`Complexity/TMVerifier/TuringToolkit/Encoding.lean`) provides a prefix-free
encoder `encodeCircuitTree` / depth-budgeted decoder `decodeCircuitTreeAtDepth` for
its own `CircuitTree` type, with a proven round-trip
`decodeCircuitTreeAtDepth_encodeCircuitTree`.  `CircuitTree` is *structurally
identical* to `Pnp3.Models.Circuit` (the same `input`/`const`/`not`/`and`/`or`
constructors).

This file builds the obvious bridge `toTree` / `fromTree` (a structural
isomorphism), ports the encoder/decoder to native `Pnp3.Models.Circuit` through it,
and **proves the native round-trip** `decodeCircuit (encodeCircuit c ++ rest) =
some (c, rest)` for `size c ≤ d`.

Scope discipline — bridge + native round-trip only:

* the **encoding-length upper bound** (the second obligation, needed to choose
  `witnessBits n`) is **not** proved here — it is the next brick;
* **no** `SelfDelimitingCircuitCode` is assembled (that needs the length bound);
* **no** lower-bound proof, **no** NP-verifier construction, **no**
  `SearchMCSPMagnificationContract` / `VerifiedNPDAGLowerBoundSource` change, **no**
  endpoint.
-/

/-- Forward bridge: a native `Circuit` maps to the structurally-identical
`CircuitTree`. -/
def toTree {n : Nat} : Pnp3.Models.Circuit n → CircuitTree n
  | .input i => .input i
  | .const b => .const b
  | .not c => .not (toTree c)
  | .and a b => .and (toTree a) (toTree b)
  | .or a b => .or (toTree a) (toTree b)

/-- Backward bridge. -/
def fromTree {n : Nat} : CircuitTree n → Pnp3.Models.Circuit n
  | .input i => .input i
  | .const b => .const b
  | .not c => .not (fromTree c)
  | .and a b => .and (fromTree a) (fromTree b)
  | .or a b => .or (fromTree a) (fromTree b)

/-- The bridge is a left inverse: `fromTree ∘ toTree = id`. -/
theorem fromTree_toTree {n : Nat} (c : Pnp3.Models.Circuit n) :
    fromTree (toTree c) = c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | not c ih => simp only [toTree, fromTree, ih]
  | and a b iha ihb => simp only [toTree, fromTree, iha, ihb]
  | or a b iha ihb => simp only [toTree, fromTree, iha, ihb]

/-- The bridge is also a right inverse: `toTree ∘ fromTree = id`. -/
theorem toTree_fromTree {n : Nat} (t : CircuitTree n) :
    toTree (fromTree t) = t := by
  induction t with
  | input i => rfl
  | const b => rfl
  | not c ih => simp only [toTree, fromTree, ih]
  | and a b iha ihb => simp only [toTree, fromTree, iha, ihb]
  | or a b iha ihb => simp only [toTree, fromTree, iha, ihb]

/-- The bridge preserves gate count. -/
theorem size_toTree {n : Nat} (c : Pnp3.Models.Circuit n) :
    (toTree c).size = Pnp3.Models.Circuit.size c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | not c ih =>
      simp only [toTree, CircuitTree.size, Pnp3.Models.Circuit.size, ih]
  | and a b iha ihb =>
      simp only [toTree, CircuitTree.size, Pnp3.Models.Circuit.size, iha, ihb]
  | or a b iha ihb =>
      simp only [toTree, CircuitTree.size, Pnp3.Models.Circuit.size, iha, ihb]

/-- Native self-delimiting encoder for `Pnp3.Models.Circuit`, via the bridge. -/
def encodeCircuit {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (c : Pnp3.Models.Circuit n) : List Bool :=
  encodeCircuitTree width h_width (toTree c)

/-- Native prefix-free (depth-budgeted) decoder for `Pnp3.Models.Circuit`, via the
bridge. -/
def decodeCircuit (n : Nat) (width : Nat) (d : Nat)
    (bits : List Bool) : Option (Pnp3.Models.Circuit n × List Bool) :=
  (decodeCircuitTreeAtDepth n width d bits).map (fun p => (fromTree p.1, p.2))

/--
**Native round-trip.**  Decoding the native encoding of a circuit (followed by any
tail) recovers the circuit and the untouched tail, provided the depth budget covers
its size.  Inherited from the `CircuitTree` round-trip through the bridge.
-/
theorem decodeCircuit_encodeCircuit (n : Nat) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c : Pnp3.Models.Circuit n)
    (d : Nat) (h_d : Pnp3.Models.Circuit.size c ≤ d) (rest : List Bool) :
    decodeCircuit n width d (encodeCircuit width h_width c ++ rest)
      = some (c, rest) := by
  unfold decodeCircuit encodeCircuit
  rw [decodeCircuitTreeAtDepth_encodeCircuitTree width h_width (toTree c) d
        (by rw [size_toTree c]; exact h_d) rest]
  simp [fromTree_toTree]

end ContractExpansion
end Frontier
end Pnp4
