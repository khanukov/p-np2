import VirtualFinalClosure.StreamActiveOrbit
import VirtualFinalClosure.RawSourceFrame
namespace VirtualFinalClosure.StreamObservationMeaning
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.StreamActiveOrbit","VirtualFinalClosure.StreamActiveOrbit","bits","bits",(0:Nat)),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","folded","folded",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","matched","matched",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","whole_table","wholeTable",1),
      ("VirtualFinalClosure.RawSourceFrame","VirtualFinalClosure.RawSourceFrame","table_source","tableSource",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong executed stream/source correspondence term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique executed stream/source correspondence term {mod}/{key}"
/-- The finite mode actually read by the native Stream orbit corresponds to
occupied SomeBool or sticky EOF. This is not a runtime source lookup. -/
private theorem observed (S A j : Nat) (word : Bitstring S) (U : Nat → Option Bool)
    (source : ∀ i,A≤ i → ∀ hi : i < S,U i=some (word ⟨i,hi⟩)) :
    bits U A S j=padRead word (A+j):=by
  by_cases inside : A+j < S
  · have cell:=source (A+j) (by omega) inside
    dsimp only [bits,Stream.Target.cursor]
    rw [Nat.min_eq_left inside.le]
    rw [show padRead word (A+j)=word ⟨A+j,inside⟩ from dif_pos inside]
    cases bit : word ⟨A+j,inside⟩ <;>
      simp [Stream.Target.mode,show A+j≠S by omega,cell,bit]
  · have beyond : S≤A+j:=by omega
    dsimp only [bits,Stream.Target.cursor]
    rw [Nat.min_eq_right beyond]
    rw [padRead_ge word beyond]
    simp [Stream.Target.mode]
private theorem whole (S A n : Nat) (word : Bitstring S) (U : Nat → Option Bool)
    (source : ∀ i,A≤ i → ∀ hi : i < S,U i=some (word ⟨i,hi⟩)) :
    (folded (bits U A S) (2^n)).val%2=1 ↔
      ∀ j : Fin (2^n),padRead word (A+j.val)=Nat.testBit j.val 0:=by
  have matchedFact:=wholeTable n (bits U A S)
  simpa only [matched,beq_iff_eq,observed S A _ word U source] using matchedFact
/-- Authoritative raw source, including consumed gamma and n0 hole7 history;
no supplied decoded AST or successful relation is needed for these cells. -/
private theorem raw_source {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z) :
    let C:=FixedRawLengthFence.allocation (pairLength a m)
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) (a+m+z+2) n)
    ∀ i,9+2*z≤ i → ∀ hi : i < a+m,U i=some ((Fin.append x w) ⟨i,hi⟩):=by
  intro C U i lo hi
  have raw:=tableSource x w gamma cap i lo hi
  change Stream.Target.image U (a+m) z n (9+2*z) (2^n) (2^n) false i=some ((Fin.append x w) ⟨i,hi⟩) at raw
  dsimp only [Stream.Target.image] at raw
  rw [if_neg (by omega),if_neg (by omega)] at raw
  exact raw
#print axioms observed
#print axioms whole
#print axioms raw_source
end VirtualFinalClosure.StreamObservationMeaning
