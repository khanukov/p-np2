import Pnp4.Frontier.ContractExpansion.CircuitTreeBridge

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-!
# Encoding-length upper bound for the native `Circuit` encoder

Block 12c of the downstream extraction effort — the **second** of the two
obligations the concrete-codec blocker (#1516) reduced the codec to (after the
bridge + round-trip, #1517).

`ConcreteCodecGap.lean` showed a self-delimiting `Circuit` encoder with an
encoding-length **upper bound** (`enc_len_le`) yields a fixed-width
`TreeCircuitWitnessCodec` by zero-padding.  The bridge (#1517) gave the native
encoder `encodeCircuit` and its round-trip.  This file supplies the missing upper
bound: every node of the prefix-free code contributes at most `width + 4` bits
(`input` → `3 + width`, `const` → `4`, `not`/`and`/`or` → `3` + children), so

```
(encodeCircuit width h_width c).length ≤ (width + 4) * Circuit.size c.
```

The existing `Encoding.lean` only had the matching *lower* bound (`3·size ≤ length`);
this is the complementary upper bound, proved by structural induction and lifted
through the bridge.

With this, the two concrete-codec obligations are both in hand at the encoder level;
**assembling** `SelfDelimitingCircuitCode` still needs a width choice and the
elimination of the decoder's depth budget, so it is intentionally **not** done here.

Scope discipline — encoding-length bound only:

* the bound is a standalone theorem; **no** `SelfDelimitingCircuitCode` is assembled;
* **no** lower-bound proof, **no** NP-verifier construction, **no**
  `SearchMCSPMagnificationContract` / `VerifiedNPDAGLowerBoundSource` change, **no**
  endpoint.
-/

/-- Per-node upper bound for the prefix-free `CircuitTree` encoder: each gate emits a
tag of at most `width + 4` bits (`input` tags carry a `width`-bit index; `const`
carries one payload bit; the connectives carry only a 3-bit tag), so the total length
is at most `(width + 4) · size`. -/
theorem length_encodeCircuitTree_le {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (t : CircuitTree n) :
    (encodeCircuitTree width h_width t).length ≤ (width + 4) * CircuitTree.size t := by
  induction t with
  | input i =>
      simp only [encodeCircuitTree, CircuitTree.size, List.length_append, List.length_cons,
        List.length_nil, encodeFin_length, mul_one]
      omega
  | const b =>
      simp only [encodeCircuitTree, CircuitTree.size, List.length_cons, List.length_nil, mul_one]
      omega
  | not c ih =>
      simp only [encodeCircuitTree, CircuitTree.size, List.length_append, List.length_cons,
        List.length_nil, mul_add, mul_one]
      omega
  | and c1 c2 ih1 ih2 =>
      simp only [encodeCircuitTree, CircuitTree.size, List.length_append, List.length_cons,
        List.length_nil, mul_add, mul_one]
      omega
  | or c1 c2 ih1 ih2 =>
      simp only [encodeCircuitTree, CircuitTree.size, List.length_append, List.length_cons,
        List.length_nil, mul_add, mul_one]
      omega

/-- **Encoding-length upper bound for the native encoder.**  The native `Circuit`
encoding has length at most `(width + 4) · size c`.  Lifted from the `CircuitTree`
bound through the bridge (`size_toTree`). -/
theorem length_encodeCircuit_le {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (c : Pnp3.Models.Circuit n) :
    (encodeCircuit width h_width c).length ≤ (width + 4) * Pnp3.Models.Circuit.size c := by
  unfold encodeCircuit
  rw [← size_toTree c]
  exact length_encodeCircuitTree_le width h_width (toTree c)

end ContractExpansion
end Frontier
end Pnp4
