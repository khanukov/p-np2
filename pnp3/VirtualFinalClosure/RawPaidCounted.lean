import VirtualFinalClosure.RawPaidStream
import VirtualFinalClosure.CountedReplay
import AllArityWorkspace.Runtime
namespace VirtualFinalClosure.RawPaidCounted
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawPaidStream","VirtualFinalClosure.RawPaidStream","raw_paid","rawPaid",(1:Nat)),
      ("VirtualFinalClosure.CountedReplay","VirtualFinalClosure.CountedReplay","prepared","counted",1),
      ("VirtualFinalClosure.CountedReplay","VirtualFinalClosure.CountedReplay","q_value","qValue",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","q","q",0),
      ("VirtualFinalClosure.StreamActiveOrbit","VirtualFinalClosure.StreamActiveOrbit","bits","bits",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","folded","folded",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong real raw paid/count connection {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique real raw paid/count connection {mod}/{key}"
private theorem price (R S p u g t : Nat) (sr : S ≤ R) (gp : g ≤ 128*(R+1)^2)
    (tp : t ≤ 144*(R+1)^2) (up : u ≤ 4096*(R+1)^2) :
    g+t+u+(2+(S-p)*(2*((3*R+2)-p)+6)) ≤ 8192*(R+1)^2:=by
  have rBound : S-p ≤ R:=(Nat.sub_le _ _).trans sr
  have fBound : (3*R+2)-p ≤ 3*R+2:=Nat.sub_le _ _
  have product:=Nat.mul_le_mul rBound (show 2*((3*R+2)-p)+6 ≤ 2*(3*R+2)+6 by omega)
  nlinarith only [gp,tp,up,product,Nat.zero_le R,Nat.zero_le (R^2)]
/-- Actual raw origin, complete native paid table fold, then the physical
suffix count. The SAME finite folded flag survives every literal counting edge.
No relation=true or preinstalled unary suffix is supplied by the caller. -/
private theorem raw_counted (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let F:=3*R+2;let A:=9+2*z;let Q:=2^n
    let p:=Stream.Target.cursor A S Q;let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) (S+z+2) n)
    let V:=Stream.Target.image U S z n A Q Q false
    let f:=folded (bits U (min A S) S) Q
    let c:=initialConfig (machine k) B (encodePair x w)
    ∃ (t : Nat) (hS : S < tapeLength R B),t ≤ 8192*(R+1)^2 ∧
      (machine k).run t c=⟨control k (tableControl k 98) ⟨8+f.val,by have h:=f.isLt;omega⟩,
        ⟨S,hS⟩,fun i=>SuffixCap.Target.image V F r i.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u c).head.val ≤ 12*(R+1)^2) ∧
      (f.val%2=1 ↔ ∀ j : Fin Q,padRead (Fin.append x w) (A+j.val)=Nat.testBit j.val 0):=by
  intro S R C B F A Q p r U V f c
  obtain ⟨g,t,u,hp,gp,tp,up,atStream,heads,meaning⟩:=rawPaid k x w canonical header tag gamma firstPhysical cap rows
  obtain ⟨cells,oldFit,fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨arena,source,eof,reg,sep,assn,right,marks,gap,fence⟩:=cells
  change F+r+2 < tapeLength R C at oldFit
  have budget : C ≤ B:=smallBudget k R
  have finite : F+r+2 < tapeLength R B:=by dsimp only [tapeLength] at oldFit ⊢;omega
  have sr : S ≤ R:=by dsimp only [S,R,pairLength];omega
  have ps : p < S:=physical
  have pp : 0 < p:=by dsimp only [p,Stream.Target.cursor,A];have h:=Nat.two_pow_pos n;omega
  have src (i : Nat) (lo : p ≤  i) (hi : i < S) : ∃ b,V i=some b:=by
    have aBound : A ≤ p:=by dsimp only [p,Stream.Target.cursor];have h:=Nat.two_pow_pos n;omega
    exact source i (aBound.trans lo) hi
  have clean (i : Nat) (lo : F < i) (hi : i ≤ F+r+2) : V i=none:=
    fresh ⟨i,lt_of_le_of_lt hi oldFit⟩ lo
  let md : Fin 144:=⟨8+f.val,by have h:=f.isLt;omega⟩
  obtain ⟨countRun,every,countHeads⟩:=counted k R B p S z n Q F V md pp ps (Nat.two_pow_pos n)
    arena src eof reg sep assn right marks gap fence clean finite
  have start : (machine k).run (g+t+u) c=
      lift k md (⟨Cursor.q k 58,⟨p,hp⟩,fun i=>V i.val⟩ : Config (Cursor.machine k).stateCount R B):=by
    have selected : (if p=S then 57 else 58)=58:=if_neg (Nat.ne_of_lt ps)
    change (machine k).run (g+t+u) c=
      ⟨q k f (if p=S then 57 else 58),⟨p,hp⟩,fun i=>V i.val⟩ at atStream
    rw [selected] at atStream
    refine atStream.trans ?_
    apply Config.ext_parts
    · change control k (tableControl k 58) md=control k (tableControl k (Cursor.q k 58).val) md
      rw [qValue k 58 (by omega)]
    · rfl
    · rfl
  have envelope : F+r+2 ≤ 12*(R+1)^2:=by
    have rr : r ≤ R:=(Nat.sub_le _ _).trans sr
    dsimp only [F]
    nlinarith only [rr,Nat.zero_le R,Nat.zero_le (R^2)]
  refine ⟨g+t+u+(2+r*(2*(F-p)+6)),by omega,price R S p u g t sr gp tp up,?_,?_,meaning⟩
  · rw [UniformTM.run_add,start]
    exact countRun
  · intro v hv
    by_cases early : v ≤ g+t+u
    · exact heads v early
    · rw [show v=(g+t+u)+(v-(g+t+u)) by omega,UniformTM.run_add,start]
      have bound : v-(g+t+u) ≤ 2+(S-p)*(2*(F-p)+6):=by
        change v ≤ g+t+u+(2+(S-p)*(2*(F-p)+6)) at hv
        omega
      exact (countHeads (v-(g+t+u)) bound).trans envelope
#print axioms price
#print axioms raw_counted
end VirtualFinalClosure.RawPaidCounted
