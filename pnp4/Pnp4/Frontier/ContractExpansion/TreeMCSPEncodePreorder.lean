import Pnp4.Frontier.ContractExpansion.TreeMCSPDriveStack

/-!
# `encodePreorder` — D2t-5b: the certificate **is** the encoded preorder token stream

The on-tape D2t-5b driver reads the certificate (`encodeCircuitTree`, a preorder serialisation) token by
token, its abstract state tracking the **unread** tokens as a `List (PreToken n)` (`drive`/`DriveState`).
To relate a running tape configuration to that abstract token list — the certificate region of the driver
configuration invariant — we need the per-token tape codec and the fact that it reproduces
`encodeCircuitTree` exactly.

This module supplies both:

* `encodePreToken` — one preorder token's tape image, matching `encodeCircuitTree`'s tag bits: nodes
  `tnot = [0,1,0]`, `tand = [0,1,1]`, `tor = [1,0,0]`; leaves `input i = [0,0,0] ++ encodeFin width i`,
  `const b = [0,0,1,b]`.  (The `notGate`/`andGate`/`orGate` leaves never occur in a `preorder` stream —
  they are produced by `settle`, not read from the certificate — so they map to `[]`.)
* `encodePreorder` — the token list's tape image, the tokens' images concatenated.
* `encodePreorder_append` — the image distributes over list append.
* **`encodePreorder_preorder`** — `encodePreorder width h (preorder c) = encodeCircuitTree width h c`: the
  certificate is exactly the encoded preorder token stream, so the driver's abstract `toks = preorder c`
  corresponds cell-for-cell to the on-tape certificate.

**Progress classification (AGENTS.md): Infrastructure** — a tape-format codec proven against the verified
`encodeCircuitTree`; builds no machine and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- One preorder token's tape image — the same bits `encodeCircuitTree` writes for that node/leaf.  The
`notGate`/`andGate`/`orGate` leaves are unreachable in a `preorder` stream (produced by `settle`, not the
certificate), so they map to `[]`. -/
def encodePreToken {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width) : PreToken n → List Bool
  | .node ITag.tnot => [false, true, false]
  | .node ITag.tand => [false, true, true]
  | .node ITag.tor => [true, false, false]
  | .leaf (SLGate.input i) =>
      [false, false, false] ++ encodeFin width ⟨i.val, lt_of_lt_of_le i.isLt h_width⟩
  | .leaf (SLGate.const b) => [false, false, true, b]
  -- `notGate`/`andGate`/`orGate` leaves never occur in a `preorder` stream (they are produced by `settle`,
  -- not read from the certificate).  Listed explicitly (rather than a wildcard) so a future `SLGate`
  -- constructor forces an exhaustiveness error here instead of silently encoding as `[]`.
  | .leaf (SLGate.notGate _) => []
  | .leaf (SLGate.andGate _ _) => []
  | .leaf (SLGate.orGate _ _) => []

/-- The tape image of a preorder token list: the tokens' images concatenated. -/
def encodePreorder {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width) : List (PreToken n) → List Bool
  | [] => []
  | t :: ts => encodePreToken width h_width t ++ encodePreorder width h_width ts

@[simp] theorem encodePreorder_nil {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width) :
    encodePreorder width h_width ([] : List (PreToken n)) = [] := rfl

@[simp] theorem encodePreorder_cons {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (t : PreToken n) (ts : List (PreToken n)) :
    encodePreorder width h_width (t :: ts)
      = encodePreToken width h_width t ++ encodePreorder width h_width ts := rfl

/-- The token-stream image distributes over list append (the concatenation is a `foldr (· ++ ·)`). -/
theorem encodePreorder_append {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (l1 l2 : List (PreToken n)) :
    encodePreorder width h_width (l1 ++ l2)
      = encodePreorder width h_width l1 ++ encodePreorder width h_width l2 := by
  induction l1 with
  | nil => simp
  | cons t ts ih => simp [ih, List.append_assoc]

/-- **The certificate is the encoded preorder token stream.**  `encodePreorder width h (preorder c)`
equals `encodeCircuitTree width h c` cell for cell — so the driver's abstract unread-token list
`toks = preorder c` decodes the on-tape certificate exactly.  Induction on the tree, matching each node's
tag bits and recursing via `encodePreorder_append` at the binary nodes. -/
theorem encodePreorder_preorder {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width) (c : CircuitTree n) :
    encodePreorder width h_width (preorder c) = encodeCircuitTree width h_width c := by
  induction c with
  | input i => simp [preorder, encodePreToken, encodeCircuitTree]
  | const b => simp [preorder, encodePreToken, encodeCircuitTree]
  | not c ih => simp [preorder, encodePreToken, encodeCircuitTree, ih]
  | and a b iha ihb =>
      simp [preorder, encodePreToken, encodeCircuitTree, encodePreorder_append, iha, ihb]
  | or a b iha ihb =>
      simp [preorder, encodePreToken, encodeCircuitTree, encodePreorder_append, iha, ihb]

end ContractExpansion
end Frontier
end Pnp4
