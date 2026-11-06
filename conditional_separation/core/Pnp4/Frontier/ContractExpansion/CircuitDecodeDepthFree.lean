import Pnp4.Frontier.ContractExpansion.CircuitEncodingLength

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-!
# Depth-budget elimination for the native `Circuit` decoder

Block 12d (partial) of the downstream extraction effort — toward assembling a
concrete `TreeCircuitWitnessCodec`.

The bridge decoder `decodeCircuit` (#1517) carries an explicit depth budget `d` and
round-trips only when `size c ≤ d`.  A `SelfDelimitingCircuitCode.dec`
(`ConcreteCodecGap.lean`) is **depth-free** (`List Bool → Option (… × …)`).  This
file removes the external budget by taking `d := bits.length`: since a prefix-free
codeword has length `≥ 3·size` (the existing lower bound, lifted here), `bits.length`
always covers the size, so the round-trip survives.

* `length_encodeCircuit_ge` — the native encoding-length **lower** bound
  `3·size c ≤ (encodeCircuit …).length` (the complement of #1518's upper bound),
  lifted from `encodeCircuitTree_length_ge` through the bridge.
* `decodeCircuitFull` — the depth-free decoder `bits ↦ decodeCircuit … bits.length bits`.
* `decodeCircuitFull_encodeCircuit` — its round-trip, with no `size ≤ d` side
  condition.

## The `n = 0` obstacle is now resolved

Earlier this decoder (via the pnp3 `decodeCircuitTreeAtDepth`) carried a vestigial
`h_pos : 0 < n` that made it *uncallable* at `n = 0`, even though the body never used
it (the `input` branch guards on a runtime `i_fin.val < n` check).  That parameter has
since been removed: the pnp3 decoder now takes `n` as a plain explicit argument, so
`decodeCircuit` / `decodeCircuitFull` decode for **all** `n`, including `n = 0`.

Together with the encoder, the round-trip, and both length bounds (upper #1518, lower
here), every *encoder-level* ingredient for a full `∀ n` `SelfDelimitingCircuitCode`
is now in hand.  Only the **final assembly** — choosing a width / `witnessBits`
schedule and packaging via `SelfDelimitingCircuitCode.toCodec` — remains, and is left
to a separate PR.

Scope discipline — depth elimination + lower bound only:

* **no** full `SelfDelimitingCircuitCode` / `TreeCircuitWitnessCodec` is assembled
  (final assembly is a separate PR);
* **no** lower-bound proof, **no** NP-verifier construction, **no**
  `SearchMCSPMagnificationContract` change, **no** endpoint.
-/

/-- **Encoding-length lower bound for the native encoder** (complement of
`length_encodeCircuit_le`): `3 · size c ≤ (encodeCircuit …).length`, lifted from
`encodeCircuitTree_length_ge` through the bridge. -/
theorem length_encodeCircuit_ge {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (c : Pnp3.Models.Circuit n) :
    3 * Pnp3.Models.Circuit.size c ≤ (encodeCircuit width h_width c).length := by
  unfold encodeCircuit
  rw [← size_toTree c]
  exact encodeCircuitTree_length_ge width h_width (toTree c)

/-- Depth-free native decoder: use the input length itself as the depth budget. -/
def decodeCircuitFull (n : Nat) (width : Nat)
    (bits : List Bool) : Option (Pnp3.Models.Circuit n × List Bool) :=
  decodeCircuit n width bits.length bits

/--
**Depth-free round-trip.**  With the budget taken to be the input length, decoding
the native encoding (followed by any tail) recovers the circuit and the untouched
tail — with **no** `size ≤ d` side condition, because `(encodeCircuit … c ++ rest).length
≥ 3 · size c ≥ size c`.
-/
theorem decodeCircuitFull_encodeCircuit (n : Nat) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c : Pnp3.Models.Circuit n) (rest : List Bool) :
    decodeCircuitFull n width (encodeCircuit width h_width c ++ rest)
      = some (c, rest) := by
  unfold decodeCircuitFull
  have hge : 3 * Pnp3.Models.Circuit.size c ≤ (encodeCircuit width h_width c).length :=
    length_encodeCircuit_ge width h_width c
  have hlen : Pnp3.Models.Circuit.size c
      ≤ (encodeCircuit width h_width c ++ rest).length := by
    rw [List.length_append]; omega
  exact decodeCircuit_encodeCircuit n width h_width c
    (encodeCircuit width h_width c ++ rest).length hlen rest

end ContractExpansion
end Frontier
end Pnp4
