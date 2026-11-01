import NormalFinalClosure.Navigation2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","keep","hop","put","dest","sweepL","sweepR","FromHRows","from_H"]),
    (`NormalFinalClosure.Navigation2,`NormalFinalClosure,["HToSRows","SToHRows","DToHRows","h_to_s","s_to_h","d_to_h"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing exact literal source API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing source API owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong source API owner"
      let kind:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|.inductInfo _=>"inductive"|_=>"other"
      unless kind != "other" do throwError "Wrong source API kind"
      logInfo m!"literal-source-exact-interface|{name}|{kind}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing source Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing source Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong source Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
/-- Static lower-tape geometry. In particular occupied false source cells and
EOF none are distinct, and n=0 may have adjacent assignment delimiters. -/
private structure LowFrame (T : Nat → Option Bool) (S z n F : Nat) : Prop where
  room : S+z+2+n+2 < F
  eof : T S=none
  left : T (S+z+2)=none
  right : T (S+z+2+n+1)=none
  registers : ∀ i,S < i → i < S+z+2 → ∃ b,T i=some b
  assignment : ∀ i,S+z+2 < i → i < S+z+2+n+1 → ∃ b,T i=some b
  paid : T (S+z+2+n+2)=some true
  gap : ∀ i,S+z+2+n+2 < i → i < F → T i=none
  fence : T F=some false
  d0 : T (F+1)=none
private def DSToRows (entry out : Fin M.stateCount) : Prop :=
  ∃ mid,DToHRows (Safe:=Safe) entry mid ∧ HToSRows (Safe:=Safe) mid out
private def SDToRows (entry out : Fin M.stateCount) : Prop :=
  ∃ mid,SToHRows (Safe:=Safe) entry mid ∧ FromHRows (Safe:=Safe) mid out
private theorem ds {T S z n F P entry out} (fr:LowFrame T S z n F) (fit:F+1 ≤ P)
    (code:DSToRows (Safe:=Safe) entry out) :
    Path M Safe P (F-S+3) (node entry (F+1) T) (node out S T) := by
  obtain ⟨mid,a,b⟩:=code
  have first:=d_to_h fr.room fit fr.d0 fr.right fr.fence fr.paid fr.gap a
  have last:=h_to_s (P:=P) (by have h:=fr.room;omega) fr.eof fr.left fr.right fr.registers fr.assignment b
  have path:=first.append last
  convert path using 1
  have h:=fr.room
  omega
private theorem sd {T S z n F P entry out} (fr:LowFrame T S z n F) (fit:F+1 ≤ P)
    (code:SDToRows (Safe:=Safe) entry out) :
    Path M Safe P (F-S+2) (node entry S T) (node out (F+1) T) := by
  obtain ⟨mid,a,b⟩:=code
  have first:=s_to_h (P:=P) (by have h:=fr.room;omega) fr.eof fr.left fr.right fr.registers fr.assignment a
  have last:=from_H (Q:=1) (by decide) (by have h:=fr.room;omega) fit fr.fence fr.right
    (by
      intro i lo hi
      have eq:i=S+z+2+n+2:=by omega
      rw [eq]
      exact fr.paid) fr.gap b
  have path:=first.append last
  convert path using 1
  have h:=fr.room
  omega
private def LocateRows (entry out : Fin M.stateCount) : Prop :=
  ∃ atS scan : Fin M.stateCount,DSToRows (Safe:=Safe) entry atS ∧ Safe atS ∧ Safe scan ∧
    M.step atS none=(scan,none,.left) ∧
    (∀ b,M.step scan (some b)=(scan,some b,.left)) ∧ M.step scan none=(out,none,.stay)
/-- Locates the unique live hole by actual finite scans from D0 via H and EOF.
Gamma holes below c are never visited. No proof address is runtime input. -/
private theorem locate {T S z n F P c entry out} (fr:LowFrame T S z n F)
    (fit:F+1 ≤ P) (physical:c < S) (hole:T c=none)
    (source:∀ i,c < i → i < S → ∃ b,T i=some b)
    (code:LocateRows (Safe:=Safe) entry out) :
    Path M Safe P (F-c+4) (node entry (F+1) T) (node out c T) := by
  obtain ⟨atS,scan,route,ss,sc,enter,loop,stop⟩:=code
  have begin:=ds fr fit route
  have one:=keep atS scan S (S-1) T .left (P:=P) (by have h:=fr.room;omega) (by have h:=fr.room;omega)
    ss (by rw [fr.eof];exact enter) rfl
  have middle:=sweepL scan T c (S-1-c) (P:=P) (by have h:=fr.room;omega) sc (by
    intro i lo hi
    obtain ⟨b,hb⟩:=source i lo (by omega)
    rw [hb];exact loop b)
  rw [show c+(S-1-c)=S-1 by omega] at middle
  have last:=keep scan out c c T .stay (P:=P) (by have h:=fr.room;omega) (by have h:=fr.room;omega)
    sc (by rw [hole];exact stop) rfl
  have path:=begin.append (one.append (middle.append last))
  convert path using 1
  have h:=fr.room
  omega
private theorem low_put {T S z n F c b} (fr:LowFrame T S z n F) (below:c < S) :
    LowFrame (put T c b) S z n F := by
  refine ⟨fr.room,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [put,show S≠c by omega,if_false];exact fr.eof
  · simp only [put,show S+z+2≠c by omega,if_false];exact fr.left
  · simp only [put,show S+z+2+n+1≠c by omega,if_false];exact fr.right
  · intro i lo hi
    simp only [put,show i≠c by omega,if_false]
    exact fr.registers i lo hi
  · intro i lo hi
    simp only [put,show i≠c by omega,if_false]
    exact fr.assignment i lo hi
  · simp only [put,show S+z+2+n+2≠c by omega,if_false];exact fr.paid
  · intro i lo hi
    simp only [put,show i≠c by omega,if_false]
    exact fr.gap i lo hi
  · have h:=fr.room
    simp only [put,show F≠c by omega,if_false];exact fr.fence
  · have h:=fr.room
    simp only [put,show F+1≠c by omega,if_false];exact fr.d0
private def RestoreRows (entry out : Fin M.stateCount) (b : Bool) : Prop :=
  ∃ hole scan atS : Fin M.stateCount,LocateRows (Safe:=Safe) entry hole ∧ Safe hole ∧ Safe scan ∧
    M.step hole none=(scan,some b,.right) ∧
    (∀ v,M.step scan (some v)=(scan,some v,.right)) ∧ M.step scan none=(atS,none,.stay) ∧
    SDToRows (Safe:=Safe) atS out
/-- Restores exactly the carried bit and returns to D0, keeping every other
source/assignment/workspace/exterior cell. This path has no virtual erase. -/
private theorem restore {T S z n F P c entry out b} (fr:LowFrame T S z n F)
    (fit:F+1 ≤ P) (physical:c < S) (hole:T c=none)
    (source:∀ i,c < i → i < S → ∃ v,T i=some v)
    (code:RestoreRows (Safe:=Safe) entry out b) :
    Path M Safe P (2*(F+1-c)+5) (node entry (F+1) T)
      (node out (F+1) (put T c (some b))) := by
  obtain ⟨holeState,scan,atS,find,sh,ss,write,loop,stop,back⟩:=code
  have begin:=locate fr fit physical hole source find
  have one:=hop holeState scan c (c+1) T (some b) .right (P:=P)
    (by have h:=fr.room;omega) (by have h:=fr.room;omega) sh (by rw [hole];exact write) rfl
  let E:=put T c (some b)
  have frE:LowFrame E S z n F:=low_put fr physical
  have middle:=sweepR scan E (c+1) (S-(c+1)) (P:=P) (by have h:=fr.room;omega) ss (by
    intro i lo hi
    obtain ⟨v,hv⟩:=source i (by omega) (by omega)
    change M.step scan (put T c (some b) i)=(scan,put T c (some b) i,.right)
    rw [show put T c (some b) i=T i by simp only [put,show i≠c by omega,if_false],hv]
    exact loop v)
  rw [show c+1+(S-(c+1))=S by omega] at middle
  have stay:=keep scan atS S S E .stay (P:=P) (by have h:=fr.room;omega) (by have h:=fr.room;omega)
    ss (by rw [frE.eof];exact stop) rfl
  have last:=sd frE fit back
  have path:=begin.append (one.append (middle.append (stay.append last)))
  convert path using 1
  have h:=fr.room
  omega
end NormalFinalClosure
