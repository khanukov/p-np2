import NormalFinalClosure.BufferProcess2
import NormalFinalClosure.BufferAppend2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","Grid","RouteR","RouteL","Grid.goR","Grid.goL","Grid.cells","put","dest","keep","hop","sweepL"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["blanks","mono"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing full comparison path API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing comparison path owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong comparison path owner"
      logInfo m!"native-comparison-path-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous (leaf.splitOn ".").getLast!) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing comparison Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing comparison Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong comparison Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private def RetreatRows (entry out : Fin M.stateCount) : Prop :=
  ∃ retreat left : Fin M.stateCount,Safe entry ∧ Safe retreat ∧
    (∀ b,M.step entry (some b)=(retreat,some b,.left)) ∧
    (∀ b,M.step retreat (some b)=(retreat,some b,.left)) ∧
    M.step retreat none=(left,none,.stay) ∧ RouteL M Safe 10 0 left out
private theorem retreat_run {D T P entry out} (g:Grid D T) (room:D 13 ≤ P)
    (head : Nat) (lo:D 10 < head) (hi:head < D 11) (code:RetreatRows (Safe:=Safe) entry out) :
    Path M Safe P (head-D 10+1+(D 10-D 0+10)) (node entry head T) (node out (D 0) T) := by
  obtain ⟨retreat,left,se,sr,enter,loop,stop,back⟩:=code
  have hp:head ≤ P:=by have h:=(mono g 11 13 (by decide) le_rfl).trans room;omega
  obtain ⟨b,hb⟩:=cells g 10 head (by decide) lo (by change head < D 11;exact hi)
  have first:=keep entry retreat head (head-1) T .left (P:=P) hp (by omega) se
    (by rw [hb];exact enter b) (by simp only [dest])
  have mid:=sweepL retreat T (D 10) (head-D 10-1) (P:=P) (by omega) sr (by
    intro i low high
    obtain ⟨b,hb⟩:=cells g 10 i (by decide) low (by change i < D 11;omega)
    rw [hb];exact loop b)
  rw [show D 10+(head-D 10-1)=head-1 by omega] at mid
  have last:=keep retreat left (D 10) (D 10) T .stay (P:=P) (by omega) (by omega) sr
    (by rw [blanks g 10 (by decide)];exact stop) rfl
  have finish:=goL g back (by decide) room
  have path:=first.append (mid.append (last.append finish))
  convert path using 1
  omega
private def CycleRows (first second third : Fin M.stateCount) : Prop :=
  Safe first ∧ Safe second ∧ Safe third ∧
    M.step first (some false)=(second,some false,.right) ∧
    M.step second (some true)=(third,some true,.right) ∧
    M.step third (some true)=(first,some true,.right)
private theorem cycle_walk {T P first second third} (code:CycleRows (Safe:=Safe) first second third)
    (base count : Nat) (fit:base+3*count ≤ P)
    (bits:∀ j,j < count → T (base+3*j)=some false ∧ T (base+3*j+1)=some true ∧ T (base+3*j+2)=some true) :
    Path M Safe P (3*count) (node first base T) (node first (base+3*count) T) := by
  obtain ⟨sf,ss,st,r1,r2,r3⟩:=code
  induction count generalizing base with
  | zero=>simpa only [Nat.mul_zero,Nat.add_zero] using (Path.nil (node first base T) (by change base ≤ P;omega))
  | succ count ih=>
    obtain ⟨b0,b1,b2⟩:=bits 0 (by omega)
    simp only [Nat.mul_zero,Nat.add_zero] at b0 b1 b2
    have one:=keep first second base (base+1) T .right (P:=P) (by omega) (by omega) sf (by rw [b0];exact r1) rfl
    have two:=keep second third (base+1) (base+2) T .right (P:=P) (by omega) (by omega) ss (by rw [b1];exact r2) rfl
    have three:=keep third first (base+2) (base+3) T .right (P:=P) (by omega) (by omega) st (by rw [b2];exact r3) rfl
    have tail:=ih (base+3) (by omega) (by
      intro j hj
      simpa only [show base+3+3*j=base+3*(j+1) by omega] using bits (j+1) (by omega))
    have path:=one.append (two.append (three.append tail))
    rw [show base+3*(count+1)=base+3+3*count by omega,show 3*(count+1)=1+(1+(1+3*count)) by omega]
    exact path
private def CompareRows (entry good done bad : Fin M.stateCount) (value : Bool) : Prop :=
  ∃ enter first second third0 third1 write2 back ret rd rb : Fin M.stateCount,
    RouteR M Safe 0 10 entry enter ∧ RouteL M Safe 10 0 ret good ∧
    Safe enter ∧ Safe first ∧ Safe second ∧ Safe third0 ∧ Safe third1 ∧ Safe write2 ∧ Safe back ∧
    M.step enter none=(first,none,.right) ∧
    M.step first (some true)=(rd,some true,.stay) ∧
    M.step first (some false)=(second,some false,.right) ∧
    (∀ b,M.step second (some b)=(if b then third1 else third0,some b,.right)) ∧
    M.step third0 (some false)=(rd,some false,.stay) ∧
    M.step third1 (some true)=(first,some true,.right) ∧
    (∀ bit,M.step (if bit then third1 else third0) (some (!bit))=
      if bit=value then (write2,some true,.left) else (rb,some (!bit),.stay)) ∧
    (∀ b,M.step write2 (some b)=(back,some true,.left)) ∧
    (∀ b,M.step back (some b)=(back,some b,.left)) ∧ M.step back none=(ret,none,.stay) ∧
    RetreatRows (Safe:=Safe) rd done ∧ RetreatRows (Safe:=Safe) rb bad
end NormalFinalClosure
