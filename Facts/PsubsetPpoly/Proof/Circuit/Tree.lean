import Proof.Bitstring

/-!
# Minimal Boolean-circuit interface

The standalone `P ⊆ P/poly` proof only requires the bare-bones circuit syntax
and its evaluation semantics to talk about the tree-shaped gadgets appearing in
the simulation.  We therefore keep exactly those ingredients here and omit the
canonicalisation and counting infrastructure of the original development.

As part of the collision clean-up we nest the whole development under
`Facts.PsubsetPpoly` so the exported symbols remain distinct from their
`Pnp2` counterparts.
-/

namespace Facts
namespace PsubsetPpoly

namespace Boolcube

/--
Boolean circuits with `n` input bits.  The constructors mirror the usual
straightforward syntax: variables, Boolean constants and the three basic
connectives.  This compact datatype suffices for the simulation arguments in
`Simulation.lean` where circuits are manipulated structurally.
-/
inductive Circuit (n : ℕ) where
  | var   : Fin n → Circuit n
  | const : Bool → Circuit n
  | not   : Circuit n → Circuit n
  | and   : Circuit n → Circuit n → Circuit n
  | or    : Circuit n → Circuit n → Circuit n
  deriving DecidableEq

namespace Circuit

/--
Evaluate a tree-shaped Boolean circuit.  The definition follows the structure of
`Circuit` directly and will be unfolded repeatedly in the combinatorial proofs
about the gadgets that encode Turing-machine configurations.
-/
noncomputable def eval {n : ℕ} : Circuit n → Point n → Bool
  | var i, x      => x i
  | const b, _    => b
  | not c, x      => !(eval c x)
  | and c₁ c₂, x  => eval c₁ x && eval c₂ x
  | or c₁ c₂, x   => eval c₁ x || eval c₂ x

end Circuit

end Boolcube

end PsubsetPpoly
end Facts
