import IngressAllocation.Target
import Complexity.PrivateInterfaceLookupResolvedHeader
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let owner := `IngressRepair.Header
  PartAPrivateResolved.install [
    (owner,`IngressRepair.source,owner,false,[],`headerSource),
    (owner,`IngressRepair.source_eq,owner,true,[],`sourceEq),
    (owner,`IngressRepair.put,owner,false,[],`headerPut),
    (owner,`IngressRepair.gamma_path,owner,true,[],`gammaPath),
    (owner,`IngressRepair.read_path,owner,true,[],`readPath),
    (owner,`IngressRepair.Path.append,owner,true,[],`appendPath),
    (owner,`IngressRepair.Path.execute,owner,true,[],`executePath)]
private theorem missing_time_bound (a m z : Nat) (short : a+m=9+z) :
    FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7+5*z+10
      ≤ 12*(pairLength a m+1)^2:=by
  have positive : pairLength a m ≠ 0:=by dsimp only [pairLength];omega
  simp only [FixedRawLengthFence.installClock]
  rw [if_neg positive]
  simp only [FixedRawLengthFence.contentClock,pairLength]
  nlinarith only [short,Nat.zero_le (a*m),Nat.zero_le (a*a),Nat.zero_le (m*m),Nat.zero_le a,Nat.zero_le m]
set_option maxRecDepth 4000 in
private theorem header_positive {a m : Nat} (x : Bitstring a) (w : Bitstring m) (z : Nat)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) (pos : 0 < z) :
    ∃ h : 9+z < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
      SmallIngress.producer.run
        (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7+(5*z+9))
        (initialConfig SmallIngress.producer (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
        ⟨SmallIngress.q 138,⟨9+z,h⟩,fun i=>headerPut (headerPut (headerSource x w) 7 none) 8 none i.val⟩:=by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let T:=headerSource x w
  obtain ⟨support,term,zero⟩:=(FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma
  have hS : 9+z ≤ a+m:=by omega
  have ltF : a+m < FixedRawLengthFence.fencePos R:=by
    dsimp only [FixedRawLengthFence.fencePos,R,pairLength];omega
  obtain ⟨_,_,_,_,_,_,_,_,iffTag,_⟩:=FixedContentTagGate.tag_contract (Fin.append x w)
  have six : T 6=some true:=by
    dsimp only [T]
    rw [sourceEq x w 6 (by change 6 < FixedRawLengthFence.fencePos R;omega)]
    exact iffTag.mp tag ⟨6,by decide⟩
  have seven : T 7=some false:=by
    dsimp only [T]
    rw [sourceEq x w 7 (by change 7 < FixedRawLengthFence.fencePos R;omega)]
    exact iffTag.mp tag ⟨7,by decide⟩
  have zeros (j : Nat) (hj : j < z) : T (8+j)=some false:=by
    dsimp only [T]
    rw [sourceEq x w _ (by change _ < FixedRawLengthFence.fencePos R;omega)]
    exact zero j hj
  have terminator : T (8+z)=some true:=by
    dsimp only [T]
    rw [sourceEq x w _ (by change _ < FixedRawLengthFence.fencePos R;omega)]
    exact term
  have room : 9+z < tapeLength R B:=by
    have h:=(FixedRawLengthFence.resource_bounds R).1
    dsimp only [B]
    simp only [tapeLength,R,pairLength] at *
    omega
  have path:=appendPath (gammaPath T z six seven zeros terminator) (readPath T z pos zeros terminator)
  have run:=executePath (N:=R) (B:=B) path room
  have time : 3*z+6+(2*z+3)=5*z+9:=by omega
  change SmallIngress.producer.run (3*z+6+(2*z+3))
    (⟨SmallIngress.q 124,⟨8,by omega⟩,fun i=>T i.val⟩ : Config SmallIngress.producer.stateCount R B)=
    ⟨SmallIngress.q 138,⟨9+z,room⟩,fun i=>headerPut (headerPut T 7 none) 8 none i.val⟩ at run
  rw [time] at run
  refine ⟨room,?_⟩
  rw [UniformTM.run_add,SmallIngress.raw_gamma_start x w tag]
  exact run
end IngressAllocation
