import FullIngressClosure.Frame
import Complexity.PrivateInterfaceLookupCoreFullIngress
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private def lookupContracts_0 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  let frame := PartAPrivateLookupCore.reference `FullIngressClosure.Frame `FullIngressClosure.InstallerFrame
  let ready := PartAPrivateLookupCore.reference `FullIngressClosure.Frame `FullIngressClosure.ready
  return [
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame, `FullIngressClosure.Frame, 0,
      ← `((R S z n p g W Q : Nat) → (Fin S → Bool) → (Nat → Option Bool) → Prop), `InstallerFrame),
    (`FullIngressClosure.Frame, `FullIngressClosure.ready, `FullIngressClosure.Frame, 2,
      ← `((Nat → Option Bool) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option Bool), `ready),
    (`FullIngressClosure.Frame, `FullIngressClosure.accepted_frame, `FullIngressClosure.Frame, 3,
      ← `(∀ (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m),
      PartAEndpoint.thresholdContentWitnessRelation k a m x w = true → ∀ (pr : AcceptedBody.Parsed k),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = some pr →
      ∀ (z : Nat), FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z →
      let S := a+m; let R := pairLength a m; let B := FixedRawLengthFence.allocation R
      let n := pr.2.n; let L := S+z+2; let F := FixedRawLengthFence.fencePos R
      let p := min (9+2*z+2^n) S; let r := S-p
      let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
      let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
      let I := $ready V L n F r (n^k+k) (Cursor.Target.W k n)
      p < S → bitLength n ≤ r → Cursor.Target.W k n ≤ r →
      $frame R S z n p (n^k+k) (Cursor.Target.W k n) (2^n) (Fin.append x w) I ∧
      Cursor.Target.M k n z = p+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n ∧
      SerializedBody.sourceMode (Fin.append x w) (Cursor.Target.M k n z) =
      SerializedBody.sourceMode (Fin.append x w) (p+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n)), `accepted_frame),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.positive, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → 1 ≤ R), `fr_positive)]
private def lookupContracts_1 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  let frame := PartAPrivateLookupCore.reference `FullIngressClosure.Frame `FullIngressClosure.InstallerFrame
  return [
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.sourceWidth, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → S ≤ R), `fr_sourceWidth),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.width, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → n ≤ R), `fr_width),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.physical, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → p < S), `fr_physical),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.gFits, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → g ≤ S-p), `fr_gFits)]
private def lookupContracts_2 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  let frame := PartAPrivateLookupCore.reference `FullIngressClosure.Frame `FullIngressClosure.InstallerFrame
  return [
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.wFits, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → W ≤ S-p), `fr_wFits),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.ellFits, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → bitLength n ≤ S-p), `fr_ellFits),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.paid, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → 0 < Q), `fr_paid),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.arena, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → S+z+n+3+Q < FixedRawLengthFence.fencePos R), `fr_arena)]
private def lookupContracts_3 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  let frame := PartAPrivateLookupCore.reference `FullIngressClosure.Frame `FullIngressClosure.InstallerFrame
  return [
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.sourceCells, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ i, p ≤ i → ∀ hi : i < S, T i = some (source ⟨i,hi⟩)), `fr_sourceCells),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.eof, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → T S = none), `fr_eof),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.register, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ i, S < i → i < S+z+2 → T i = some false), `fr_register),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.separator, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → T (S+z+2) = none), `fr_separator)]
private def lookupContracts_4 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  let frame := PartAPrivateLookupCore.reference `FullIngressClosure.Frame `FullIngressClosure.InstallerFrame
  return [
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.headBlank, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → T (S+z+n+3) = none), `fr_headBlank),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.assignment, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ j : Fin n, T (S+z+n+3-1-j.val) = some false), `fr_assignment),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.marks, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ i, S+z+n+3 < i → i ≤ S+z+n+3+Q → T i = some true), `fr_marks),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.gap, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ i, S+z+n+3+Q < i → i < FixedRawLengthFence.fencePos R → T i = none), `fr_gap)]
private def lookupContracts_5 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  let frame := PartAPrivateLookupCore.reference `FullIngressClosure.Frame `FullIngressClosure.InstallerFrame
  return [
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.fence, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → T (FixedRawLengthFence.fencePos R) = some false), `fr_fence),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.delimiters, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ j, j ≤ 6 → T (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) (S-p) n j) = none), `fr_delimiters),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.bank0, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ i, FixedRawLengthFence.fencePos R+1 < i → i < FixedRawLengthFence.fencePos R+(S-p)+2 → T i = some (decide (i-(FixedRawLengthFence.fencePos R+1) ≤ g))), `fr_bank0),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.bank1, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ i, FixedRawLengthFence.fencePos R+(S-p)+2 < i → i < FixedRawLengthFence.fencePos R+(S-p)+n+3 → T i = some false), `fr_bank1)]
private def lookupContracts_6 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  let frame := PartAPrivateLookupCore.reference `FullIngressClosure.Frame `FullIngressClosure.InstallerFrame
  return [
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.bank2, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ i, FixedRawLengthFence.fencePos R+(S-p)+n+3 < i → i < FixedRawLengthFence.fencePos R+2*(S-p)+n+4 → T i = some (decide (i-(FixedRawLengthFence.fencePos R+(S-p)+n+3) ≤ bitLength W))), `fr_bank2),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.bank34, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ i, FixedRawLengthFence.fencePos R+2*(S-p)+n+4 < i → i < FixedRawLengthFence.fencePos R+4*(S-p)+n+6 → i ≠ FixedRawLengthFence.fencePos R+3*(S-p)+n+5 → T i = some false), `fr_bank34),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.bank5, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ i, FixedRawLengthFence.fencePos R+4*(S-p)+n+6 < i → i < FixedRawLengthFence.fencePos R+5*(S-p)+n+7 → T i = some (decide (i-(FixedRawLengthFence.fencePos R+4*(S-p)+n+6) ≤ W))), `fr_bank5),
    (`FullIngressClosure.Frame, `FullIngressClosure.InstallerFrame.fresh, `FullIngressClosure.Frame, 3,
      ← `(∀ {R S z n p g W Q : Nat} {source : Fin S → Bool} {T : Nat → Option Bool},
      $frame R S z n p g W Q source T → ∀ i, FixedRawLengthFence.fencePos R+5*(S-p)+n+7 < i → i ≤ SerializedBody.delimiter (FixedRawLengthFence.fencePos R) (S-p) n 12 → T i = none), `fr_fresh)]
private def lookupContracts_7 : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  return [
    (`BodyIngress.Transport, `BodyIngress.step_lift, `BodyIngress.Transport, 3,
      ← `(∀ {k N B : Nat} (c : Config (CarryWindow.machine k).stateCount N B),
      c.state ≠ CarryWindow.ready k → (BodyIngress.machine k).stepConfig (BodyIngress.config k c) =
      BodyIngress.config k ((CarryWindow.machine k).stepConfig c)), `oldStep)]
end FullIngressClosure

open Lean Elab Command
namespace PartAPrivateInstallerFrame
def contracts : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)) := do
  return (← FullIngressClosure.lookupContracts_0) ++ (← FullIngressClosure.lookupContracts_1) ++ (← FullIngressClosure.lookupContracts_2) ++ (← FullIngressClosure.lookupContracts_3) ++ (← FullIngressClosure.lookupContracts_4) ++ (← FullIngressClosure.lookupContracts_5) ++ (← FullIngressClosure.lookupContracts_6) ++ (← FullIngressClosure.lookupContracts_7)
#check (contracts : CommandElabM (List (Name × Name × Name × Nat × Syntax × Name)))
#print axioms contracts
end PartAPrivateInstallerFrame

namespace PartAPrivateInstallerFrameFeasibility
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let entries ← PartAPrivateInstallerFrame.contracts
  unless entries.length == 29 do throwError "finite shared table size"
  PartAPrivateLookupCore.installChecked entries
  for (owner,user,_,_,_,_) in entries do
    let n := mkPrivateNameCore owner user
    let axs := (← collectAxioms n).toList
    unless axs.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "nonstandard frame feasibility root"
    logInfo m!"frame-feasibility-root|{n}|axioms={axs}"
end PartAPrivateInstallerFrameFeasibility
