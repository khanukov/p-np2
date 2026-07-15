import Pnp4.Frontier.OneTapeMagnification.DPTWFiniteBooleanPrimitives

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Polynomial-size Boolean heads for a finite-field coordinate decoder

This standalone probe isolates the circuit-locality part of the usual
polynomial-evaluation bounded-independence source.  A multiplication table in
a fixed `GF(2)` basis is represented by a Boolean bilinear tensor.  For every
output bit, the file constructs a constant-free AND/OR/NOT DAG for

`coefficient XOR sum_{i,j} tensor i j output * left_i * right_j`.

The gate bound is at most `6 + 6 * d * d` per output bit.  Bundling all `d`
bits therefore costs at most `d * (6 + 6 * d * d)` gates for one Horner step.
The shared-bundle substitution below adds this cost to the preceding state;
it does not copy the preceding state once per output bit.

For the first useful dyadic case, a second explicit DAG outputs the OR of `t`
selected result bits, and its gate count is at most `2 + t`.  Its false event
is exactly that every selected result bit is zero.  For the canonical
injective prefix of a uniformly distributed field element this has false mass
`p = 2^-t`; that distributional fact is proved in the structured-field bridge,
not here.  The generic `positions` parameter below may contain repetitions.

This file deliberately does not identify a tensor with Mathlib's opaque
`GaloisField 2 d` representation.  The basis-compatible Boolean encoding of
field addition and multiplication lives in the separate
`GaloisBilinearTensorBridge` module; the final reindexing and Horner
identification are likewise kept out of this circuit-only probe.  Hence this
is circuit infrastructure, not a lower bound and not P-vs-NP mainline
progress.
-/

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit
open StreamingMagnification
open StreamingMagnification.StandardDAG
open StreamingMagnification.TotalSearch
open DPTWFiniteBooleanPrimitives

namespace DPTWBilinearCoordinateCircuitProbe

/-! ## Constant-free Boolean composition heads -/

/-- A four-gate DAG for `left XOR right` with shared input wires. -/
def xorHead : DagCircuit 2 where
  gates := 4
  gate := fun gate =>
    Fin.cases
      (DagGate.or
        (DagWire.input (0 : Fin 2))
        (DagWire.input (1 : Fin 2)))
      (fun gate1 : Fin 3 =>
        Fin.cases
          (DagGate.and
            (DagWire.input (0 : Fin 2))
            (DagWire.input (1 : Fin 2)))
          (fun gate2 : Fin 2 =>
            Fin.cases
              (DagGate.not (DagWire.gate (1 : Fin 2)))
              (fun gate3 : Fin 1 =>
                Fin.cases
                  (DagGate.and
                    (DagWire.gate (0 : Fin 3))
                    (DagWire.gate (2 : Fin 3)))
                  (fun impossible : Fin 0 => Fin.elim0 impossible)
                  gate3)
              gate2)
          gate1)
      gate
  output := DagWire.gate (3 : Fin 4)

@[simp] theorem xorHead_gates : xorHead.gates = 4 := rfl

@[simp] theorem eval_xorHead (left right : Bool) :
    DagCircuit.eval xorHead ![left, right] = Bool.xor left right := by
  let input : Bitstring 2 := ![left, right]
  have hEval0 (h : 0 < xorHead.gates) :
      DagCircuit.eval.evalGateAt xorHead input 0 h = (left || right) := by
    rw [DagCircuit.eval.evalGateAt.eq_1]
    rfl
  have hEval1 (h : 1 < xorHead.gates) :
      DagCircuit.eval.evalGateAt xorHead input 1 h = (left && right) := by
    rw [DagCircuit.eval.evalGateAt.eq_1]
    rfl
  have hEval2 (h : 2 < xorHead.gates) :
      DagCircuit.eval.evalGateAt xorHead input 2 h = !(left && right) := by
    rw [DagCircuit.eval.evalGateAt.eq_1]
    have hGate2 : xorHead.gate ⟨2, h⟩ =
        DagGate.not (DagWire.gate (1 : Fin 2)) := by rfl
    rw [hGate2]
    change (!(DagCircuit.eval.evalGateAt xorHead input 1 _)) = _
    rw [hEval1]
  rw [DagCircuit.eval.eq_1]
  change DagCircuit.eval.evalGateAt xorHead input 3 _ = _
  rw [DagCircuit.eval.evalGateAt.eq_1]
  have hGate3 (h : 3 < xorHead.gates) : xorHead.gate ⟨3, h⟩ =
      DagGate.and (DagWire.gate (0 : Fin 3))
        (DagWire.gate (2 : Fin 3)) := by rfl
  rw [hGate3]
  change
    (DagCircuit.eval.evalGateAt xorHead input 0 _ &&
      DagCircuit.eval.evalGateAt xorHead input 2 _) = _
  rw [hEval0, hEval2]
  cases left <;> cases right <;> rfl

theorem xorHead_noConst :
    forall gate, noConstDAGGate (xorHead.gate gate) := by
  intro gate
  fin_cases gate <;> trivial

private def binaryInputs {inputBits : Nat}
    (left right : DagCircuit inputBits) : Fin 2 -> DagCircuit inputBits :=
  fun input => Fin.cases left (fun _ => right) input

/-- Share `left` and `right` once, then append the four-gate XOR head. -/
def xorDAG {inputBits : Nat}
    (left right : DagCircuit inputBits) : DagCircuit inputBits :=
  substInputs xorHead (binaryInputs left right)

@[simp] theorem eval_xorDAG {inputBits : Nat}
    (left right : DagCircuit inputBits) (input : Bitstring inputBits) :
    DagCircuit.eval (xorDAG left right) input =
      Bool.xor (DagCircuit.eval left input) (DagCircuit.eval right input) := by
  rw [xorDAG, eval_substInputs]
  have hinputs :
      (fun index => DagCircuit.eval (binaryInputs left right index) input) =
        ![DagCircuit.eval left input, DagCircuit.eval right input] := by
    funext index
    fin_cases index <;> rfl
  rw [hinputs, eval_xorHead]

@[simp] theorem xorDAG_gates {inputBits : Nat}
    (left right : DagCircuit inputBits) :
    (xorDAG left right).gates = left.gates + right.gates + 4 := by
  change (bundleOfFamily 2 (binaryInputs left right)).gates + xorHead.gates = _
  rw [bundleOfFamily_gates]
  simp [binaryInputs, Fin.sum_univ_succ]

theorem xorDAG_noConst {inputBits : Nat}
    (left right : DagCircuit inputBits)
    (hleft : forall gate, noConstDAGGate (left.gate gate))
    (hright : forall gate, noConstDAGGate (right.gate gate)) :
    forall gate, noConstDAGGate ((xorDAG left right).gate gate) := by
  apply substInputs_noConst
  · exact xorHead_noConst
  · intro input gate
    fin_cases input
    · exact hleft gate
    · exact hright gate

/-- A one-gate conjunction of two selected inputs. -/
def andProjectionDAG {inputBits : Nat}
    (left right : Fin inputBits) : DagCircuit inputBits where
  gates := 1
  gate := fun _ => DagGate.and (DagWire.input left) (DagWire.input right)
  output := DagWire.gate (0 : Fin 1)

@[simp] theorem andProjectionDAG_gates {inputBits : Nat}
    (left right : Fin inputBits) :
    (andProjectionDAG left right).gates = 1 := rfl

@[simp] theorem eval_andProjectionDAG {inputBits : Nat}
    (left right : Fin inputBits) (input : Bitstring inputBits) :
    DagCircuit.eval (andProjectionDAG left right) input =
      (input left && input right) := by
  rw [DagCircuit.eval.eq_1]
  change DagCircuit.eval.evalGateAt
    (andProjectionDAG left right) input 0 _ = _
  rw [DagCircuit.eval.evalGateAt.eq_1]
  rfl

theorem andProjectionDAG_noConst {inputBits : Nat}
    (left right : Fin inputBits) :
    forall gate,
      noConstDAGGate ((andProjectionDAG left right).gate gate) := by
  intro gate
  fin_cases gate
  trivial

/-! ## A linear-size parity fold -/

/-- Semantic fold matching `xorFamilyDAG`. -/
def xorFamilyValue : (count : Nat) -> (Fin count -> Bool) -> Bool
  | 0, _ => false
  | count + 1, family =>
      Bool.xor
        (xorFamilyValue count (fun index => family (Fin.castAdd 1 index)))
        (family (Fin.natAdd count (0 : Fin 1)))

/-- Fold a finite family with shared four-gate XOR heads.  The positive-input
hypothesis is only needed for the two-gate constant-false base case. -/
def xorFamilyDAG (inputBits : Nat) (hpositive : 0 < inputBits) :
    (count : Nat) -> (Fin count -> DagCircuit inputBits) -> DagCircuit inputBits
  | 0, _ => paperBasisConstantDAG inputBits hpositive false
  | count + 1, family =>
      xorDAG
        (xorFamilyDAG inputBits hpositive count
          (fun index => family (Fin.castAdd 1 index)))
        (family (Fin.natAdd count (0 : Fin 1)))

@[simp] theorem eval_xorFamilyDAG
    (inputBits : Nat) (hpositive : 0 < inputBits) :
    forall (count : Nat) (family : Fin count -> DagCircuit inputBits)
      (input : Bitstring inputBits),
      DagCircuit.eval (xorFamilyDAG inputBits hpositive count family) input =
        xorFamilyValue count (fun index => DagCircuit.eval (family index) input)
  | 0, family, input => by simp [xorFamilyDAG, xorFamilyValue]
  | count + 1, family, input => by
      simp only [xorFamilyDAG, eval_xorDAG, xorFamilyValue]
      rw [eval_xorFamilyDAG]

/-- If every member has at most two gates, the parity fold has at most
`2 + 6 * count` gates. -/
theorem xorFamilyDAG_gates_le
    (inputBits : Nat) (hpositive : 0 < inputBits) :
    forall (count : Nat) (family : Fin count -> DagCircuit inputBits),
      (forall index, (family index).gates <= 2) ->
      (xorFamilyDAG inputBits hpositive count family).gates <= 2 + 6 * count
  | 0, family, hfamily => by simp [xorFamilyDAG]
  | count + 1, family, hfamily => by
      simp only [xorFamilyDAG, xorDAG_gates]
      have hprefix := xorFamilyDAG_gates_le inputBits hpositive count
        (fun index => family (Fin.castAdd 1 index))
        (fun index => hfamily (Fin.castAdd 1 index))
      have hlast := hfamily (Fin.natAdd count (0 : Fin 1))
      omega

theorem xorFamilyDAG_noConst
    (inputBits : Nat) (hpositive : 0 < inputBits) :
    forall (count : Nat) (family : Fin count -> DagCircuit inputBits),
      (forall index gate,
        noConstDAGGate ((family index).gate gate)) ->
      forall gate,
        noConstDAGGate
          ((xorFamilyDAG inputBits hpositive count family).gate gate)
  | 0, family, hfamily =>
      paperBasisConstantDAG_noConst inputBits hpositive false
  | count + 1, family, hfamily => by
      apply xorDAG_noConst
      · exact xorFamilyDAG_noConst inputBits hpositive count
          (fun index => family (Fin.castAdd 1 index))
          (fun index gate => hfamily (Fin.castAdd 1 index) gate)
      · exact hfamily (Fin.natAdd count (0 : Fin 1))

/-! ## One bilinear finite-field output bit -/

/-- Compile-time multiplication tensor in a fixed Boolean basis. -/
abbrev BilinearTensor (d : Nat) := Fin d -> Fin d -> Fin d -> Bool

/-- Layout of one affine multiplication head: `left`, then `right`, then one
coefficient bit. -/
abbrev affineHeadInputBits (d : Nat) := d + (d + 1)

theorem affineHeadInputBits_pos (d : Nat) (hpositive : 0 < d) :
    0 < affineHeadInputBits d := by
  unfold affineHeadInputBits
  omega

def affineLeftInput {d : Nat} (index : Fin d) : Fin (affineHeadInputBits d) :=
  Fin.castAdd (d + 1) index

def affineRightInput {d : Nat} (index : Fin d) : Fin (affineHeadInputBits d) :=
  Fin.natAdd d (Fin.castAdd 1 index)

def affineCoefficientInput (d : Nat) : Fin (affineHeadInputBits d) :=
  Fin.natAdd d (Fin.natAdd d (0 : Fin 1))

/-- One tensor-selected quadratic monomial.  A zero tensor entry is compiled
to a two-gate constant-false gadget, not a forbidden constant gate. -/
def bilinearTermDAG
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) (term : Fin (d * d)) :
    DagCircuit (affineHeadInputBits d) :=
  let pair := finProdFinEquiv.symm term
  if tensor pair.1 pair.2 output then
    andProjectionDAG (affineLeftInput pair.1) (affineRightInput pair.2)
  else
    paperBasisConstantDAG (affineHeadInputBits d)
      (affineHeadInputBits_pos d hpositive) false

theorem bilinearTermDAG_gates_le
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) (term : Fin (d * d)) :
    (bilinearTermDAG d hpositive tensor output term).gates <= 2 := by
  cases hentry : tensor term.divNat term.modNat output <;>
    simp [bilinearTermDAG, hentry]

theorem bilinearTermDAG_noConst
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) (term : Fin (d * d)) :
    forall gate,
      noConstDAGGate
        ((bilinearTermDAG d hpositive tensor output term).gate gate) := by
  unfold bilinearTermDAG
  dsimp
  by_cases hentry : tensor term.divNat term.modNat output = true
  · rw [if_pos hentry]
    exact andProjectionDAG_noConst _ _
  · rw [if_neg hentry]
    exact paperBasisConstantDAG_noConst _ _ false

/-- The semantic tensor parity for one product coordinate. -/
def bilinearBitValue
    (d : Nat) (tensor : BilinearTensor d) (output : Fin d)
    (input : Bitstring (affineHeadInputBits d)) : Bool :=
  xorFamilyValue (d * d) (fun term =>
    let pair := finProdFinEquiv.symm term
    tensor pair.1 pair.2 output &&
      input (affineLeftInput pair.1) && input (affineRightInput pair.2))

/-- Explicit AND/OR/NOT DAG for one coordinate of a bilinear product. -/
def bilinearBitDAG
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) : DagCircuit (affineHeadInputBits d) :=
  xorFamilyDAG (affineHeadInputBits d)
    (affineHeadInputBits_pos d hpositive) (d * d)
    (bilinearTermDAG d hpositive tensor output)

@[simp] theorem eval_bilinearTermDAG
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) (term : Fin (d * d))
    (input : Bitstring (affineHeadInputBits d)) :
    DagCircuit.eval (bilinearTermDAG d hpositive tensor output term) input =
      let pair := finProdFinEquiv.symm term
      tensor pair.1 pair.2 output &&
        input (affineLeftInput pair.1) && input (affineRightInput pair.2) := by
  cases hentry : tensor term.divNat term.modNat output <;>
    simp [bilinearTermDAG, hentry]

@[simp] theorem eval_bilinearBitDAG
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) (input : Bitstring (affineHeadInputBits d)) :
    DagCircuit.eval (bilinearBitDAG d hpositive tensor output) input =
      bilinearBitValue d tensor output input := by
  simp [bilinearBitDAG, bilinearBitValue]

theorem bilinearBitDAG_gates_le
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) :
    (bilinearBitDAG d hpositive tensor output).gates <= 2 + 6 * (d * d) := by
  apply xorFamilyDAG_gates_le
  exact bilinearTermDAG_gates_le d hpositive tensor output

theorem bilinearBitDAG_noConst
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) :
    forall gate,
      noConstDAGGate ((bilinearBitDAG d hpositive tensor output).gate gate) := by
  apply xorFamilyDAG_noConst
  exact bilinearTermDAG_noConst d hpositive tensor output

/-- One Horner-coordinate head: a product coordinate XOR one coefficient bit. -/
def bilinearAffineBitDAG
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) : DagCircuit (affineHeadInputBits d) :=
  xorDAG
    (bilinearBitDAG d hpositive tensor output)
    (inputProj (affineCoefficientInput d))

@[simp] theorem eval_bilinearAffineBitDAG
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) (input : Bitstring (affineHeadInputBits d)) :
    DagCircuit.eval (bilinearAffineBitDAG d hpositive tensor output) input =
      Bool.xor (bilinearBitValue d tensor output input)
        (input (affineCoefficientInput d)) := by
  simp [bilinearAffineBitDAG]

theorem bilinearAffineBitDAG_gates_le
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) :
    (bilinearAffineBitDAG d hpositive tensor output).gates <=
      6 + 6 * (d * d) := by
  rw [bilinearAffineBitDAG, xorDAG_gates]
  have hmul := bilinearBitDAG_gates_le d hpositive tensor output
  simp only [inputProj]
  omega

theorem bilinearAffineBitDAG_noConst
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) :
    forall gate,
      noConstDAGGate
        ((bilinearAffineBitDAG d hpositive tensor output).gate gate) := by
  apply xorDAG_noConst
  · exact bilinearBitDAG_noConst d hpositive tensor output
  · intro gate
    exact Fin.elim0 gate

/-- Flat paper-basis form of one affine multiplication coordinate. -/
def bilinearAffineBitCircuit
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) : FlatCircuit (affineHeadInputBits d) :=
  FlatCircuit.ofDag (bilinearAffineBitDAG d hpositive tensor output)

theorem bilinearAffineBitCircuit_usesOnlyAndOrNot
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) :
    (bilinearAffineBitCircuit d hpositive tensor output).UsesOnlyAndOrNot := by
  apply ofDag_usesOnlyAndOrNot_of_noConst
  exact bilinearAffineBitDAG_noConst d hpositive tensor output

theorem bilinearAffineBitCircuit_gateCount_le
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) :
    (bilinearAffineBitCircuit d hpositive tensor output).gateCount <=
      6 + 6 * (d * d) :=
  bilinearAffineBitDAG_gates_le d hpositive tensor output

@[simp] theorem eval_bilinearAffineBitCircuit
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) (input : Bitstring (affineHeadInputBits d)) :
    (bilinearAffineBitCircuit d hpositive tensor output).eval input =
      Bool.xor (bilinearBitValue d tensor output input)
        (input (affineCoefficientInput d)) := by
  unfold bilinearAffineBitCircuit FlatCircuit.eval
  rw [FlatCircuit.toDag_ofDag]
  exact eval_bilinearAffineBitDAG d hpositive tensor output input

/-- Input layout for a complete Horner step: old state, evaluation point, and
the next coefficient, all as `d`-bit vectors. -/
abbrev hornerHeadInputBits (d : Nat) := d + (d + d)

/-- Relabel the one-output affine head so output bit `output` reads its own
coefficient bit from the full coefficient vector. -/
def affineBitToHornerRelabel
    {d : Nat} (output : Fin d) :
    Fin (affineHeadInputBits d) -> Fin (hornerHeadInputBits d) :=
  Fin.addCases
    (fun left => Fin.castAdd (d + d) left)
    (fun rightOrCoefficient =>
      Fin.addCases
        (fun right => Fin.natAdd d (Fin.castAdd d right))
        (fun _ => Fin.natAdd d (Fin.natAdd d output))
        rightOrCoefficient)

@[simp] theorem affineBitToHornerRelabel_left
    {d : Nat} (output index : Fin d) :
    affineBitToHornerRelabel output (affineLeftInput index) =
      Fin.castAdd (d + d) index := by
  unfold affineBitToHornerRelabel affineLeftInput
  rw [Fin.addCases_left]

@[simp] theorem affineBitToHornerRelabel_right
    {d : Nat} (output index : Fin d) :
    affineBitToHornerRelabel output (affineRightInput index) =
      Fin.natAdd d (Fin.castAdd d index) := by
  unfold affineBitToHornerRelabel affineRightInput
  rw [Fin.addCases_right, Fin.addCases_left]

@[simp] theorem affineBitToHornerRelabel_coefficient
    {d : Nat} (output : Fin d) :
    affineBitToHornerRelabel output (affineCoefficientInput d) =
      Fin.natAdd d (Fin.natAdd d output) := by
  unfold affineBitToHornerRelabel affineCoefficientInput
  rw [Fin.addCases_right, Fin.addCases_right]

/-- All `d` Horner output coordinates on one shared gate list.  Each output
uses the matching bit of the full coefficient vector. -/
def bilinearAffineHeadBundle
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d) :
    DagBundle (hornerHeadInputBits d) d :=
  bundleOfFamily d (fun output =>
    relabelInputs (affineBitToHornerRelabel output)
      (bilinearAffineBitDAG d hpositive tensor output))

theorem bilinearAffineHeadBundle_gates_le
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d) :
    (bilinearAffineHeadBundle d hpositive tensor).gates <=
      d * (6 + 6 * (d * d)) := by
  rw [bilinearAffineHeadBundle, bundleOfFamily_gates]
  calc
    (∑ output : Fin d,
        (relabelInputs (affineBitToHornerRelabel output)
          (bilinearAffineBitDAG d hpositive tensor output)).gates) <=
        ∑ _output : Fin d, (6 + 6 * (d * d)) := by
      exact Finset.sum_le_sum (fun output _ =>
        bilinearAffineBitDAG_gates_le d hpositive tensor output)
    _ = d * (6 + 6 * (d * d)) := by simp

theorem relabelInputs_noConst {n m : Nat}
    (relabel : Fin n -> Fin m) (circuit : DagCircuit n)
    (hcircuit : forall gate, noConstDAGGate (circuit.gate gate)) :
    forall gate,
      noConstDAGGate ((relabelInputs relabel circuit).gate gate) := by
  intro gate
  change noConstDAGGate (mapGateInputs relabel (circuit.gate gate))
  have hgate := hcircuit gate
  cases h : circuit.gate gate with
  | const value =>
      rw [h] at hgate
      exact False.elim hgate
  | not wire => trivial
  | and left right => trivial
  | or left right => trivial

theorem bilinearAffineHeadBundle_noConst
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d) :
    forall gate,
      noConstDAGGate
        ((bilinearAffineHeadBundle d hpositive tensor).gate gate) := by
  apply bundleOfFamily_noConst
  intro output gate
  apply relabelInputs_noConst
  exact bilinearAffineBitDAG_noConst d hpositive tensor output

/-- Tensor multiplication semantics on Boolean basis coordinates. -/
def bilinearVectorValue
    (d : Nat) (tensor : BilinearTensor d)
    (left right : Bitstring d) : Bitstring d :=
  fun output =>
    xorFamilyValue (d * d) (fun term =>
      let pair := finProdFinEquiv.symm term
      tensor pair.1 pair.2 output && left pair.1 && right pair.2)

/-- One vector Horner step: `left * point + coefficient`, with addition in
characteristic two represented by XOR. -/
def bilinearAffineVectorValue
    (d : Nat) (tensor : BilinearTensor d)
    (left point coefficient : Bitstring d) : Bitstring d :=
  fun output => Bool.xor
    (bilinearVectorValue d tensor left point output) (coefficient output)

@[simp] theorem evalOutput_bilinearAffineHeadBundle
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) (input : Bitstring (hornerHeadInputBits d)) :
    (bilinearAffineHeadBundle d hpositive tensor).evalOutput output input =
      Bool.xor
        (bilinearBitValue d tensor output
          (fun index => input (affineBitToHornerRelabel output index)))
        (input (Fin.natAdd d (Fin.natAdd d output))) := by
  rw [bilinearAffineHeadBundle, evalOutput_bundleOfFamily,
    eval_relabelInputs, eval_bilinearAffineBitDAG]
  rw [affineBitToHornerRelabel_coefficient]

/-- The complete generic head bundle computes the tensor-affine vector map. -/
theorem evalOutput_bilinearAffineHeadBundle_eq_vectorValue
    (d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (output : Fin d) (input : Bitstring (hornerHeadInputBits d)) :
    (bilinearAffineHeadBundle d hpositive tensor).evalOutput output input =
      bilinearAffineVectorValue d tensor
        (fun bit => input (Fin.castAdd (d + d) bit))
        (fun bit => input (Fin.natAdd d (Fin.castAdd d bit)))
        (fun bit => input (Fin.natAdd d (Fin.natAdd d bit))) output := by
  rw [evalOutput_bilinearAffineHeadBundle]
  unfold bilinearAffineVectorValue bilinearVectorValue bilinearBitValue
  congr 1
  apply congrArg (xorFamilyValue (d * d))
  funext term
  simp

/-! ## Shared multi-output substitution -/

/-- Substitute one shared input bundle into one shared outer bundle.  This is
the multi-output counterpart of `substInputsWithBundle`. -/
def substDagBundle {n m outputs : Nat}
    (outer : DagBundle n outputs) (inputs : DagBundle m n) :
    DagBundle m outputs where
  gates := inputs.gates + outer.gates
  gate := Fin.addCases (motive := fun index => DagGate m index.1)
    (fun index => inputs.gate index)
    (fun index => substGateWithBundle inputs (outer.gate index))
  output := fun output => substWireWithBundle inputs (outer.output output)

@[simp] theorem substDagBundle_gates {n m outputs : Nat}
    (outer : DagBundle n outputs) (inputs : DagBundle m n) :
    (substDagBundle outer inputs).gates = inputs.gates + outer.gates := rfl

@[simp] theorem evalOutput_substDagBundle {n m outputs : Nat}
    (outer : DagBundle n outputs) (inputs : DagBundle m n)
    (output : Fin outputs) (input : Bitstring m) :
    (substDagBundle outer inputs).evalOutput output input =
      outer.evalOutput output
        (fun index => inputs.evalOutput index input) := by
  change DagCircuit.eval
      (substInputsWithBundle (outer.asCircuit output) inputs) input = _
  rw [eval_substInputsWithBundle]
  rfl

theorem substDagBundle_noConst {n m outputs : Nat}
    (outer : DagBundle n outputs) (inputs : DagBundle m n)
    (houter : forall gate, noConstDAGGate (outer.gate gate))
    (hinputs : forall gate, noConstDAGGate (inputs.gate gate)) :
    forall gate,
      noConstDAGGate ((substDagBundle outer inputs).gate gate) := by
  intro gate
  refine Fin.addCases
    (motive := fun gate =>
      noConstDAGGate ((substDagBundle outer inputs).gate gate))
    (fun inputGate => by
      simpa [substDagBundle] using hinputs inputGate)
    (fun outerGate => by
      simpa [substDagBundle] using
        noConst_substGateWithBundle inputs (outer.gate outerGate)
          (houter outerGate))
    gate

/-- Relabel all real inputs of a multi-output bundle without changing its gate
count or output sharing. -/
def relabelDagBundleInputs {n m outputs : Nat}
    (relabel : Fin n -> Fin m) (bundle : DagBundle n outputs) :
    DagBundle m outputs where
  gates := bundle.gates
  gate := fun gate => mapGateInputs relabel (bundle.gate gate)
  output := fun output => mapWireInputs relabel (bundle.output output)

@[simp] theorem relabelDagBundleInputs_gates {n m outputs : Nat}
    (relabel : Fin n -> Fin m) (bundle : DagBundle n outputs) :
    (relabelDagBundleInputs relabel bundle).gates = bundle.gates := rfl

@[simp] theorem evalOutput_relabelDagBundleInputs {n m outputs : Nat}
    (relabel : Fin n -> Fin m) (bundle : DagBundle n outputs)
    (output : Fin outputs) (input : Bitstring m) :
    (relabelDagBundleInputs relabel bundle).evalOutput output input =
      bundle.evalOutput output (fun index => input (relabel index)) := by
  change DagCircuit.eval
      (relabelInputs relabel (bundle.asCircuit output)) input = _
  rw [eval_relabelInputs]
  rfl

theorem relabelDagBundleInputs_noConst {n m outputs : Nat}
    (relabel : Fin n -> Fin m) (bundle : DagBundle n outputs)
    (hbundle : forall gate, noConstDAGGate (bundle.gate gate)) :
    forall gate,
      noConstDAGGate ((relabelDagBundleInputs relabel bundle).gate gate) := by
  intro gate
  change noConstDAGGate (mapGateInputs relabel (bundle.gate gate))
  have hgate := hbundle gate
  cases h : bundle.gate gate with
  | const value =>
      rw [h] at hgate
      exact False.elim hgate
  | not wire => trivial
  | and left right => trivial
  | or left right => trivial

/-- Apply a multi-output transition head to real inputs plus the outputs of a
shared state bundle.  Its gate cost is exactly additive. -/
def sharedBundleStep {m stateBits : Nat}
    (state : DagBundle m stateBits)
    (head : DagBundle (m + stateBits) stateBits) : DagBundle m stateBits :=
  substDagBundle head (passthroughBundle state)

@[simp] theorem sharedBundleStep_gates {m stateBits : Nat}
    (state : DagBundle m stateBits)
    (head : DagBundle (m + stateBits) stateBits) :
    (sharedBundleStep state head).gates = state.gates + head.gates := by
  simp [sharedBundleStep]

@[simp] theorem evalOutput_sharedBundleStep {m stateBits : Nat}
    (state : DagBundle m stateBits)
    (head : DagBundle (m + stateBits) stateBits)
    (output : Fin stateBits) (input : Bitstring m) :
    (sharedBundleStep state head).evalOutput output input =
      head.evalOutput output
        (Fin.addCases input (fun index => state.evalOutput index input)) := by
  rw [sharedBundleStep, evalOutput_substDagBundle]
  apply congrArg (head.evalOutput output)
  funext index
  refine Fin.addCases
    (motive := fun index =>
      (passthroughBundle state).evalOutput index input =
        Fin.addCases input (fun i => state.evalOutput i input) index)
    (fun realInput => by simp)
    (fun stateOutput => by simp)
    index

theorem sharedBundleStep_noConst {m stateBits : Nat}
    (state : DagBundle m stateBits)
    (head : DagBundle (m + stateBits) stateBits)
    (hstate : forall gate, noConstDAGGate (state.gate gate))
    (hhead : forall gate, noConstDAGGate (head.gate gate)) :
    forall gate,
      noConstDAGGate ((sharedBundleStep state head).gate gate) := by
  apply substDagBundle_noConst
  · exact hhead
  · exact hstate

/-- Iterate shared multi-output transition heads.  The previous state appears
once in the gate list at every step. -/
def sharedBundleIterate {m stateBits : Nat}
    (initial : DagBundle m stateBits) :
    (steps : Nat) ->
      (Fin steps -> DagBundle (m + stateBits) stateBits) ->
      DagBundle m stateBits
  | 0, _ => initial
  | steps + 1, heads =>
      sharedBundleStep
        (sharedBundleIterate initial steps
          (fun step => heads (Fin.castAdd 1 step)))
        (heads (Fin.natAdd steps (0 : Fin 1)))

/-- Exact additive gate recurrence for shared Horner-style iteration. -/
theorem sharedBundleIterate_gates {m stateBits : Nat}
    (initial : DagBundle m stateBits) :
    forall (steps : Nat)
      (heads : Fin steps -> DagBundle (m + stateBits) stateBits),
      (sharedBundleIterate initial steps heads).gates =
        initial.gates + ∑ step, (heads step).gates
  | 0, heads => by simp [sharedBundleIterate]
  | steps + 1, heads => by
      rw [sharedBundleIterate, sharedBundleStep_gates,
        sharedBundleIterate_gates]
      have hcast (step : Fin steps) :
          Fin.castAdd 1 step = step.castSucc := Fin.ext rfl
      simp_rw [hcast]
      have hlast : Fin.natAdd steps (0 : Fin 1) = Fin.last steps :=
        Fin.ext rfl
      rw [hlast]
      rw [Fin.sum_univ_castSucc]
      omega

theorem sharedBundleIterate_noConst {m stateBits : Nat}
    (initial : DagBundle m stateBits)
    (hinitial : forall gate, noConstDAGGate (initial.gate gate)) :
    forall (steps : Nat)
      (heads : Fin steps -> DagBundle (m + stateBits) stateBits),
      (forall step gate, noConstDAGGate ((heads step).gate gate)) ->
      forall gate,
        noConstDAGGate
          ((sharedBundleIterate initial steps heads).gate gate)
  | 0, heads, hheads => hinitial
  | steps + 1, heads, hheads => by
      apply sharedBundleStep_noConst
      · exact sharedBundleIterate_noConst initial hinitial steps
          (fun step => heads (Fin.castAdd 1 step))
          (fun step gate => hheads (Fin.castAdd 1 step) gate)
      · exact hheads (Fin.natAdd steps (0 : Fin 1))

/-! ## A complete shared Horner circuit on `GF(2)^d` coordinates -/

/-- Joint input layout for a degree-at-most-`steps` polynomial: `steps + 1`
coefficient blocks of `d` bits, followed by the `d`-bit evaluation point. -/
abbrev polynomialJointInputBits (steps d : Nat) := (steps + 1) * d + d

def polynomialCoefficientInput
    (steps d : Nat) (coefficient : Fin (steps + 1)) (bit : Fin d) :
    Fin (polynomialJointInputBits steps d) :=
  Fin.castAdd d (finProdFinEquiv (coefficient, bit))

def polynomialPointInput
    (steps d : Nat) (bit : Fin d) :
    Fin (polynomialJointInputBits steps d) :=
  Fin.natAdd ((steps + 1) * d) bit

/-- Wire the generic `state + point + coefficient` head to one coefficient
block of the fixed joint polynomial input and to the current shared state. -/
def polynomialHornerStageRelabel
    (steps d : Nat) (coefficient : Fin (steps + 1)) :
    Fin (hornerHeadInputBits d) ->
      Fin (polynomialJointInputBits steps d + d) :=
  Fin.addCases
    (fun state => Fin.natAdd (polynomialJointInputBits steps d) state)
    (fun pointOrCoefficient =>
      Fin.addCases
        (fun point => Fin.castAdd d (polynomialPointInput steps d point))
        (fun coefficientBit =>
          Fin.castAdd d
            (polynomialCoefficientInput steps d coefficient coefficientBit))
        pointOrCoefficient)

@[simp] theorem polynomialHornerStageRelabel_state
    (steps d : Nat) (coefficient : Fin (steps + 1)) (state : Fin d) :
    polynomialHornerStageRelabel steps d coefficient
        (Fin.castAdd (d + d) state) =
      Fin.natAdd (polynomialJointInputBits steps d) state := by
  unfold polynomialHornerStageRelabel
  rw [Fin.addCases_left]

@[simp] theorem polynomialHornerStageRelabel_point
    (steps d : Nat) (coefficient : Fin (steps + 1)) (point : Fin d) :
    polynomialHornerStageRelabel steps d coefficient
        (Fin.natAdd d (Fin.castAdd d point)) =
      Fin.castAdd d (polynomialPointInput steps d point) := by
  unfold polynomialHornerStageRelabel
  rw [Fin.addCases_right, Fin.addCases_left]

@[simp] theorem polynomialHornerStageRelabel_coefficient
    (steps d : Nat) (coefficient : Fin (steps + 1)) (bit : Fin d) :
    polynomialHornerStageRelabel steps d coefficient
        (Fin.natAdd d (Fin.natAdd d bit)) =
      Fin.castAdd d
        (polynomialCoefficientInput steps d coefficient bit) := by
  unfold polynomialHornerStageRelabel
  rw [Fin.addCases_right, Fin.addCases_right]

/-- One coefficient-specific shared Horner head over the fixed joint input. -/
def polynomialHornerStageBundle
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (coefficient : Fin (steps + 1)) :
    DagBundle (polynomialJointInputBits steps d + d) d :=
  relabelDagBundleInputs
    (polynomialHornerStageRelabel steps d coefficient)
    (bilinearAffineHeadBundle d hpositive tensor)

theorem polynomialHornerStageBundle_gates_le
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (coefficient : Fin (steps + 1)) :
    (polynomialHornerStageBundle steps d hpositive tensor coefficient).gates <=
      d * (6 + 6 * (d * d)) := by
  exact bilinearAffineHeadBundle_gates_le d hpositive tensor

theorem polynomialHornerStageBundle_noConst
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (coefficient : Fin (steps + 1)) :
    forall gate,
      noConstDAGGate
        ((polynomialHornerStageBundle steps d hpositive tensor coefficient).gate gate) := by
  apply relabelDagBundleInputs_noConst
  exact bilinearAffineHeadBundle_noConst d hpositive tensor

/-- Exact semantics of one coefficient-specific stage on a joint
`(real input, old state)` tape. -/
theorem evalOutput_polynomialHornerStageBundle
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (coefficient : Fin (steps + 1)) (output : Fin d)
    (input : Bitstring (polynomialJointInputBits steps d + d)) :
    (polynomialHornerStageBundle steps d hpositive tensor coefficient).evalOutput
        output input =
      bilinearAffineVectorValue d tensor
        (fun bit => input
          (Fin.natAdd (polynomialJointInputBits steps d) bit))
        (fun bit => input
          (Fin.castAdd d (polynomialPointInput steps d bit)))
        (fun bit => input
          (Fin.castAdd d
            (polynomialCoefficientInput steps d coefficient bit))) output := by
  rw [polynomialHornerStageBundle, evalOutput_relabelDagBundleInputs,
    evalOutput_bilinearAffineHeadBundle_eq_vectorValue]
  simp only [polynomialHornerStageRelabel_state,
    polynomialHornerStageRelabel_point]
  apply congrArg (fun coefficientBits : Bitstring d =>
    bilinearAffineVectorValue d tensor
      (fun bit => input
        (Fin.natAdd (polynomialJointInputBits steps d) bit))
      (fun bit => input
        (Fin.castAdd d (polynomialPointInput steps d bit)))
      coefficientBits output)
  funext bit
  apply congrArg input
  exact polynomialHornerStageRelabel_coefficient
    steps d coefficient bit

/-- The top coefficient is the zero-gate initial Horner state. -/
def polynomialHornerInitialBundle
    (steps d : Nat) : DagBundle (polynomialJointInputBits steps d) d :=
  bundleOfFamily d (fun bit =>
    inputProj (polynomialCoefficientInput steps d (Fin.last steps) bit))

@[simp] theorem polynomialHornerInitialBundle_gates
    (steps d : Nat) :
    (polynomialHornerInitialBundle steps d).gates = 0 := by
  rw [polynomialHornerInitialBundle, bundleOfFamily_gates]
  simp [inputProj]

@[simp] theorem evalOutput_polynomialHornerInitialBundle
    (steps d : Nat) (bit : Fin d)
    (input : Bitstring (polynomialJointInputBits steps d)) :
    (polynomialHornerInitialBundle steps d).evalOutput bit input =
      input (polynomialCoefficientInput steps d (Fin.last steps) bit) := by
  simp [polynomialHornerInitialBundle]

theorem polynomialHornerInitialBundle_noConst
    (steps d : Nat) :
    forall gate,
      noConstDAGGate ((polynomialHornerInitialBundle steps d).gate gate) := by
  apply bundleOfFamily_noConst
  intro bit gate
  exact Fin.elim0 gate

/-- The `steps` remaining coefficients are consumed from high to low. -/
def polynomialHornerHeads
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d) :
    Fin steps -> DagBundle (polynomialJointInputBits steps d + d) d :=
  fun stage =>
    polynomialHornerStageBundle steps d hpositive tensor
      (Fin.castSucc (Fin.rev stage))

/-- Shared DAG bundle evaluating all `d` coordinates of a polynomial with
`steps + 1` coefficient blocks at the final `d` input bits. -/
def polynomialHornerBundle
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d) :
    DagBundle (polynomialJointInputBits steps d) d :=
  sharedBundleIterate
    (polynomialHornerInitialBundle steps d) steps
    (polynomialHornerHeads steps d hpositive tensor)

/-- Quantitative locality theorem: the complete polynomial evaluator has
`(steps + 1) * d` seed bits, `d` index bits, and at most
`steps * d * (6 + 6*d^2)` gates. -/
theorem polynomialHornerBundle_gates_le
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d) :
    (polynomialHornerBundle steps d hpositive tensor).gates <=
      steps * (d * (6 + 6 * (d * d))) := by
  rw [polynomialHornerBundle, sharedBundleIterate_gates,
    polynomialHornerInitialBundle_gates, zero_add]
  calc
    (∑ stage : Fin steps,
        (polynomialHornerHeads steps d hpositive tensor stage).gates) <=
        ∑ _stage : Fin steps, d * (6 + 6 * (d * d)) := by
      exact Finset.sum_le_sum (fun stage _ =>
        polynomialHornerStageBundle_gates_le steps d hpositive tensor _)
    _ = steps * (d * (6 + 6 * (d * d))) := by simp

theorem polynomialHornerBundle_noConst
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d) :
    forall gate,
      noConstDAGGate
        ((polynomialHornerBundle steps d hpositive tensor).gate gate) := by
  apply sharedBundleIterate_noConst
  · exact polynomialHornerInitialBundle_noConst steps d
  · intro stage gate
    exact polynomialHornerStageBundle_noConst steps d hpositive tensor _ gate

/-! ### Exact recursive evaluation semantics -/

/-- Pure Boolean tensor-Horner iteration, in the same left-to-right order as
`sharedBundleIterate`. -/
def bilinearAffineIterateValue
    (d : Nat) (tensor : BilinearTensor d) (point initial : Bitstring d) :
    (steps : Nat) -> (Fin steps -> Bitstring d) -> Bitstring d
  | 0, _ => initial
  | steps + 1, coefficients =>
      bilinearAffineVectorValue d tensor
        (bilinearAffineIterateValue d tensor point initial steps
          (fun step => coefficients (Fin.castAdd 1 step)))
        point
        (coefficients (Fin.natAdd steps (0 : Fin 1)))

/-- Generic correctness theorem for a shared iterate whose heads implement
the tensor-affine recurrence on the current state. -/
theorem evalOutput_sharedBundleIterate_eq_bilinearAffineIterateValue
    {m d : Nat} (tensor : BilinearTensor d)
    (initial : DagBundle m d) (input : Bitstring m)
    (point initialValue : Bitstring d)
    (hinitial : forall output,
      initial.evalOutput output input = initialValue output) :
    forall (steps : Nat)
      (heads : Fin steps -> DagBundle (m + d) d)
      (coefficients : Fin steps -> Bitstring d),
      (forall stage state output,
        (heads stage).evalOutput output (Fin.addCases input state) =
          bilinearAffineVectorValue d tensor state point
            (coefficients stage) output) ->
      forall output,
        (sharedBundleIterate initial steps heads).evalOutput output input =
          bilinearAffineIterateValue d tensor point initialValue
            steps coefficients output
  | 0, heads, coefficients, hheads, output => by
      simpa [sharedBundleIterate, bilinearAffineIterateValue] using
        hinitial output
  | steps + 1, heads, coefficients, hheads, output => by
      rw [sharedBundleIterate, evalOutput_sharedBundleStep]
      rw [hheads (Fin.natAdd steps (0 : Fin 1))]
      unfold bilinearAffineIterateValue
      apply congrArg (fun state : Bitstring d =>
        bilinearAffineVectorValue d tensor state point
          (coefficients (Fin.natAdd steps (0 : Fin 1))) output)
      funext bit
      exact evalOutput_sharedBundleIterate_eq_bilinearAffineIterateValue
        tensor initial input point initialValue hinitial steps
        (fun stage => heads (Fin.castAdd 1 stage))
        (fun stage => coefficients (Fin.castAdd 1 stage))
        (fun stage state output =>
          hheads (Fin.castAdd 1 stage) state output)
        bit

def polynomialCoefficientValue
    (steps d : Nat) (input : Bitstring (polynomialJointInputBits steps d))
    (coefficient : Fin (steps + 1)) : Bitstring d :=
  fun bit => input (polynomialCoefficientInput steps d coefficient bit)

def polynomialPointValue
    (steps d : Nat) (input : Bitstring (polynomialJointInputBits steps d)) :
    Bitstring d :=
  fun bit => input (polynomialPointInput steps d bit)

/-- Pure recursive tensor-Horner value for the structured coefficient-block
seed layout. -/
def polynomialHornerValue
    (steps d : Nat) (tensor : BilinearTensor d)
    (input : Bitstring (polynomialJointInputBits steps d)) : Bitstring d :=
  bilinearAffineIterateValue d tensor
    (polynomialPointValue steps d input)
    (polynomialCoefficientValue steps d input (Fin.last steps))
    steps
    (fun stage => polynomialCoefficientValue steps d input
      (Fin.castSucc (Fin.rev stage)))

/-- Capstone circuit-correctness theorem: every output of the complete shared
Horner bundle is exactly the corresponding recursive tensor-Horner bit. -/
theorem evalOutput_polynomialHornerBundle
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (input : Bitstring (polynomialJointInputBits steps d)) (output : Fin d) :
    (polynomialHornerBundle steps d hpositive tensor).evalOutput output input =
      polynomialHornerValue steps d tensor input output := by
  unfold polynomialHornerBundle polynomialHornerValue
  apply evalOutput_sharedBundleIterate_eq_bilinearAffineIterateValue
  · intro bit
    exact evalOutput_polynomialHornerInitialBundle steps d bit input
  · intro stage state bit
    have hstage := evalOutput_polynomialHornerStageBundle
      steps d hpositive tensor (Fin.castSucc (Fin.rev stage)) bit
      (Fin.addCases input state)
    simpa [polynomialHornerHeads, polynomialPointValue,
      polynomialCoefficientValue] using hstage

/-! ## A selected-coordinate zero-prefix decoder -/

/-- A one-gate disjunction head. -/
def orHead : DagCircuit 2 where
  gates := 1
  gate := fun _ => DagGate.or
    (DagWire.input (0 : Fin 2)) (DagWire.input (1 : Fin 2))
  output := DagWire.gate (0 : Fin 1)

@[simp] theorem eval_orHead (left right : Bool) :
    DagCircuit.eval orHead ![left, right] = (left || right) := by
  rw [DagCircuit.eval.eq_1]
  change DagCircuit.eval.evalGateAt orHead ![left, right] 0 _ = _
  rw [DagCircuit.eval.evalGateAt.eq_1]
  rfl

theorem orHead_noConst :
    forall gate, noConstDAGGate (orHead.gate gate) := by
  intro gate
  fin_cases gate
  trivial

def orDAG {inputBits : Nat}
    (left right : DagCircuit inputBits) : DagCircuit inputBits :=
  substInputs orHead (binaryInputs left right)

@[simp] theorem eval_orDAG {inputBits : Nat}
    (left right : DagCircuit inputBits) (input : Bitstring inputBits) :
    DagCircuit.eval (orDAG left right) input =
      (DagCircuit.eval left input || DagCircuit.eval right input) := by
  rw [orDAG, eval_substInputs]
  have hinputs :
      (fun index => DagCircuit.eval (binaryInputs left right index) input) =
        ![DagCircuit.eval left input, DagCircuit.eval right input] := by
    funext index
    fin_cases index <;> rfl
  rw [hinputs, eval_orHead]

@[simp] theorem orDAG_gates {inputBits : Nat}
    (left right : DagCircuit inputBits) :
    (orDAG left right).gates = left.gates + right.gates + 1 := by
  change (bundleOfFamily 2 (binaryInputs left right)).gates + orHead.gates = _
  rw [bundleOfFamily_gates]
  simp [binaryInputs, Fin.sum_univ_succ, orHead]

theorem orDAG_noConst {inputBits : Nat}
    (left right : DagCircuit inputBits)
    (hleft : forall gate, noConstDAGGate (left.gate gate))
    (hright : forall gate, noConstDAGGate (right.gate gate)) :
    forall gate, noConstDAGGate ((orDAG left right).gate gate) := by
  apply substInputs_noConst
  · exact orHead_noConst
  · intro input gate
    fin_cases input
    · exact hleft gate
    · exact hright gate

def zeroPrefixDAG
    (d : Nat) (hpositive : 0 < d) :
    (t : Nat) -> (Fin t -> Fin d) -> DagCircuit d
  | 0, _ => paperBasisConstantDAG d hpositive false
  | t + 1, positions =>
      orDAG
        (zeroPrefixDAG d hpositive t
          (fun index => positions (Fin.castAdd 1 index)))
        (inputProj (positions (Fin.natAdd t (0 : Fin 1))))

theorem zeroPrefixDAG_gates_le
    (d : Nat) (hpositive : 0 < d) :
    forall (t : Nat) (positions : Fin t -> Fin d),
      (zeroPrefixDAG d hpositive t positions).gates <= 2 + t
  | 0, positions => by simp [zeroPrefixDAG]
  | t + 1, positions => by
      simp only [zeroPrefixDAG, orDAG_gates, inputProj]
      have ih := zeroPrefixDAG_gates_le d hpositive t
        (fun index => positions (Fin.castAdd 1 index))
      omega

theorem zeroPrefixDAG_noConst
    (d : Nat) (hpositive : 0 < d) :
    forall (t : Nat) (positions : Fin t -> Fin d),
      forall gate,
        noConstDAGGate ((zeroPrefixDAG d hpositive t positions).gate gate)
  | 0, positions => paperBasisConstantDAG_noConst d hpositive false
  | t + 1, positions => by
      apply orDAG_noConst
      · exact zeroPrefixDAG_noConst d hpositive t
          (fun index => positions (Fin.castAdd 1 index))
      · intro gate
        exact Fin.elim0 gate

/-- The zero-prefix decoder is false exactly when all selected bits are false. -/
theorem eval_zeroPrefixDAG_eq_false_iff
    (d : Nat) (hpositive : 0 < d) :
    forall (t : Nat) (positions : Fin t -> Fin d) (input : Bitstring d),
      DagCircuit.eval (zeroPrefixDAG d hpositive t positions) input = false <->
        forall index, input (positions index) = false
  | 0, positions, input => by simp [zeroPrefixDAG]
  | t + 1, positions, input => by
      rw [zeroPrefixDAG, eval_orDAG, Bool.or_eq_false_iff]
      rw [eval_zeroPrefixDAG_eq_false_iff]
      constructor
      · intro h index
        refine Fin.addCases
          (motive := fun index => input (positions index) = false)
          (fun old => h.1 old)
          (fun last => by
            have hlast : last = (0 : Fin 1) := Subsingleton.elim last 0
            subst hlast
            simpa using h.2)
          index
      · intro h
        constructor
        · intro old
          exact h (Fin.castAdd 1 old)
        · simpa using h (Fin.natAdd t (0 : Fin 1))

/-! ## Composing Horner with the selected-coordinate decoder -/

theorem substInputsWithBundle_noConst_probe {n m : Nat}
    (outer : DagCircuit n) (inputs : DagBundle m n)
    (houter : forall gate, noConstDAGGate (outer.gate gate))
    (hinputs : forall gate, noConstDAGGate (inputs.gate gate)) :
    forall gate,
      noConstDAGGate ((substInputsWithBundle outer inputs).gate gate) := by
  intro gate
  refine Fin.addCases
    (motive := fun gate =>
      noConstDAGGate ((substInputsWithBundle outer inputs).gate gate))
    (fun inputGate => by
      simpa only [substInputsWithBundle_gate_left] using hinputs inputGate)
    (fun outerGate => by
      simpa only [substInputsWithBundle_gate_right] using
        noConst_substGateWithBundle inputs (outer.gate outerGate)
          (houter outerGate))
    gate

/-- Complete joint DAG: evaluate the structured polynomial and output true
unless every selected result coordinate is zero. -/
def polynomialZeroPrefixDAG
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (t : Nat) (positions : Fin t -> Fin d) :
    DagCircuit (polynomialJointInputBits steps d) :=
  substInputsWithBundle
    (zeroPrefixDAG d hpositive t positions)
    (polynomialHornerBundle steps d hpositive tensor)

theorem polynomialZeroPrefixDAG_gates_le
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (t : Nat) (positions : Fin t -> Fin d) :
    (polynomialZeroPrefixDAG steps d hpositive tensor t positions).gates <=
      steps * (d * (6 + 6 * (d * d))) + (2 + t) := by
  change
    (polynomialHornerBundle steps d hpositive tensor).gates +
        (zeroPrefixDAG d hpositive t positions).gates <= _
  have hhorner := polynomialHornerBundle_gates_le
    steps d hpositive tensor
  have hprefix := zeroPrefixDAG_gates_le d hpositive t positions
  omega

theorem polynomialZeroPrefixDAG_noConst
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (t : Nat) (positions : Fin t -> Fin d) :
    forall gate,
      noConstDAGGate
        ((polynomialZeroPrefixDAG steps d hpositive tensor t positions).gate gate) := by
  apply substInputsWithBundle_noConst_probe
  · exact zeroPrefixDAG_noConst d hpositive t positions
  · exact polynomialHornerBundle_noConst steps d hpositive tensor

/-- Exact semantics of the complete decoder: false iff all selected recursive
tensor-Horner coordinates are zero. -/
theorem eval_polynomialZeroPrefixDAG_eq_false_iff
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (t : Nat) (positions : Fin t -> Fin d)
    (input : Bitstring (polynomialJointInputBits steps d)) :
    DagCircuit.eval
        (polynomialZeroPrefixDAG steps d hpositive tensor t positions) input =
        false <->
      forall selected,
        polynomialHornerValue steps d tensor input (positions selected) = false := by
  unfold polynomialZeroPrefixDAG
  rw [eval_substInputsWithBundle]
  rw [eval_zeroPrefixDAG_eq_false_iff]
  simp only [evalOutput_polynomialHornerBundle]

/-- Flat paper-basis presentation of the complete polynomial decoder. -/
def polynomialZeroPrefixCircuit
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (t : Nat) (positions : Fin t -> Fin d) :
    FlatCircuit (polynomialJointInputBits steps d) :=
  FlatCircuit.ofDag
    (polynomialZeroPrefixDAG steps d hpositive tensor t positions)

theorem polynomialZeroPrefixCircuit_usesOnlyAndOrNot
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (t : Nat) (positions : Fin t -> Fin d) :
    FlatCircuit.UsesOnlyAndOrNot
      (polynomialZeroPrefixCircuit steps d hpositive tensor t positions) := by
  apply ofDag_usesOnlyAndOrNot_of_noConst
  exact polynomialZeroPrefixDAG_noConst
    steps d hpositive tensor t positions

theorem polynomialZeroPrefixCircuit_gateCount_le
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (t : Nat) (positions : Fin t -> Fin d) :
    (polynomialZeroPrefixCircuit steps d hpositive tensor t positions).gateCount <=
      steps * (d * (6 + 6 * (d * d))) + (2 + t) :=
  polynomialZeroPrefixDAG_gates_le
    steps d hpositive tensor t positions

/-- Generator computed by the complete joint circuit.  Its first
`(steps + 1) * d` inputs are the structured coefficient seed and its last `d`
inputs are the truth-table index bits. -/
def polynomialZeroPrefixGenerate
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (t : Nat) (positions : Fin t -> Fin d) :
    FiniteBitTape ((steps + 1) * d) -> TruthTable d :=
  fun seed index =>
    DagCircuit.eval
      (polynomialZeroPrefixDAG steps d hpositive tensor t positions)
      (Fin.addCases seed (lexInput d index))

/-- A genuine small `DPTWCoordinatePrimitive` for the structured tensor-Horner
source.  The finite-field law still requires the external, explicit premise
that `tensor` is multiplication in a chosen `GF(2)` basis. -/
def polynomialZeroPrefixPrimitive
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (t : Nat) (positions : Fin t -> Fin d) :
    DPTWCoordinatePrimitive d ((steps + 1) * d) where
  generate := polynomialZeroPrefixGenerate
    steps d hpositive tensor t positions
  jointCircuit := polynomialZeroPrefixCircuit
    steps d hpositive tensor t positions
  usesOnlyAndOrNot := polynomialZeroPrefixCircuit_usesOnlyAndOrNot
    steps d hpositive tensor t positions
  jointCircuit_eval := by
    intro seed index
    unfold polynomialZeroPrefixCircuit polynomialZeroPrefixGenerate
    unfold FlatCircuit.eval
    rw [FlatCircuit.toDag_ofDag]

theorem polynomialZeroPrefixPrimitive_jointCircuit_gateCount_le
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (t : Nat) (positions : Fin t -> Fin d) :
    (polynomialZeroPrefixPrimitive steps d hpositive tensor t positions).jointCircuit.gateCount <=
      steps * (d * (6 + 6 * (d * d))) + (2 + t) :=
  polynomialZeroPrefixCircuit_gateCount_le
    steps d hpositive tensor t positions

theorem polynomialZeroPrefixPrimitive_generate_eq_false_iff
    (steps d : Nat) (hpositive : 0 < d) (tensor : BilinearTensor d)
    (t : Nat) (positions : Fin t -> Fin d)
    (seed : FiniteBitTape ((steps + 1) * d)) (index : Fin (2 ^ d)) :
    (polynomialZeroPrefixPrimitive steps d hpositive tensor t positions).generate
        seed index = false <->
      forall selected,
        polynomialHornerValue steps d tensor
          (Fin.addCases seed (lexInput d index)) (positions selected) = false := by
  exact eval_polynomialZeroPrefixDAG_eq_false_iff
    steps d hpositive tensor t positions
      (Fin.addCases seed (lexInput d index))

end DPTWBilinearCoordinateCircuitProbe

end OneTapeMagnification
end Frontier
end Pnp4
