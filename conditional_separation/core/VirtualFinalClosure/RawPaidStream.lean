import VirtualFinalClosure.RawStreamStart
import VirtualFinalClosure.StreamComplete
import VirtualFinalClosure.StreamObservationMeaning
import TotalIngressClosure.StreamFrame
namespace VirtualFinalClosure.RawPaidStream
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawStreamStart","VirtualFinalClosure.RawStreamStart","raw_start","rawStart",(1:Nat)),
      ("VirtualFinalClosure.StreamComplete","VirtualFinalClosure.StreamComplete","prepared","completeStream",1),
      ("VirtualFinalClosure.StreamActiveOrbit","VirtualFinalClosure.StreamActiveOrbit","ended","ended",0),
      ("VirtualFinalClosure.StreamActiveOrbit","VirtualFinalClosure.StreamActiveOrbit","bits","bits",0),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","q","q",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","folded","folded",0),
      ("VirtualFinalClosure.StreamObservationMeaning","VirtualFinalClosure.StreamObservationMeaning","whole","whole",1),
      ("VirtualFinalClosure.StreamObservationMeaning","VirtualFinalClosure.StreamObservationMeaning","raw_source","rawSource",1),
      ("TotalIngressClosure.StreamFrame","TotalIngressClosure","source_frame","sourceFrame",1),
      ("SmallOrbit.Runtime","SmallOrbit","clear_extend","clearExtend",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual raw paid-orbit term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual raw paid-orbit term {mod}/{key}"
private theorem clipped_cursor (A S j : Nat) :
    Stream.Target.cursor (min A S) S j=Stream.Target.cursor A S j:=by
  dsimp only [Stream.Target.cursor]
  omega
private theorem clipped_read (S A j : Nat) (word : Bitstring S) :
    padRead word (min A S+j)=padRead word (A+j):=by
  by_cases full : A≤S
  · rw [Nat.min_eq_left full]
  · rw [Nat.min_eq_right (by omega)]
    rw [padRead_ge word (by omega),padRead_ge word (by omega)]
private theorem restored_image (U : Nat → Option Bool) (S z n A D r marks : Nat) :
    Stream.Target.image U S z n A r marks false=Stream.Target.image U S z n D r marks false:=by
  funext i
  dsimp only [Stream.Target.image]
  simp only [Bool.false_eq_true,false_and,ite_false]
private theorem price (R S z n A Q u : Nat) (sr : S≤R) (nz : n≤3*R) (zz : z≤R)
    (qr : Q≤3*R+2) (up : u≤n+2+InputRead.readClock n z (S-A)+Q*(8*(3*R+2)+16)) :
    u≤4096*(R+1)^2:=by
  have dist : S-A≤R:=(Nat.sub_le _ _).trans sr
  have rowBound:=Nat.mul_le_mul_right (8*(3*R+2)+16) qr
  dsimp only [InputRead.readClock] at up
  nlinarith only [up,nz,zz,rowBound,dist,Nat.zero_le R,Nat.zero_le (R^2)]
/-- The physical raw parser/guard/producer followed by EVERY native paid row.
The finite metadata flag is the actual fold of precisely those observations,
not a proof-side tag attached at the endpoint. This is the supported branch
component; the unconditional classifier and final verdict are separate. -/
private theorem raw_paid (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z<a+m) (cap : n<FixedRawLengthFence.capacity a m z)
    (rows : 2^n≤FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let A:=9+2*z;let Q:=2^n
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) (S+z+2) n)
    let f:=folded (bits U (min A S) S) Q
    let c:=initialConfig (machine k) B (encodePair x w)
    ∃ (g t u : Nat) (hp : Stream.Target.cursor A S Q<tapeLength R B),
      g≤128*(R+1)^2 ∧ t≤144*(R+1)^2 ∧ u≤4096*(R+1)^2 ∧
      (machine k).run (g+t+u) c=
        ⟨q k f (if Stream.Target.cursor A S Q=S then 57 else 58),
          ⟨Stream.Target.cursor A S Q,hp⟩,fun i=>Stream.Target.image U S z n A Q Q false i.val⟩ ∧
      (∀ v,v≤g+t+u → ((machine k).run v c).head.val≤12*(R+1)^2) ∧
      (f.val%2=1 ↔ ∀ j : Fin Q,padRead (Fin.append x w) (A+j.val)=Nat.testBit j.val 0):=by
  intro S R C B A Q U f c
  let F:=3*R+2
  let T:=Body.extend (SmallIngress.prepared C x w z n)
  obtain ⟨g,t,hL,gp,tp,start,initialHeads⟩:=rawStart k x w canonical header tag gamma firstPhysical cap
  have frame:=sourceFrame x w header gamma firstPhysical cap
  obtain ⟨room,_scratch,finite,_fence⟩:=Stream.raw_budget_cells x w gamma cap
  change S+z+n+3<F at room
  change F<tapeLength R C at finite
  have budget : C≤B:=smallBudget k R
  have fit : F<tapeLength R B:=by dsimp only [tapeLength] at finite ⊢;omega
  have cleared : Body.clear T (S+z+3) n=U:=
    clearExtend (SmallIngress.prepared C x w z n) (S+z+2) n (by
      change (S+z+2)+n+1<tapeLength R C
      omega)
  obtain ⟨u,up,path⟩:=completeStream k S z n (min A S) F T frame rows
  rw [cleared] at path
  have run:=execute path (N:=R) (B:=B) fit
  have sr : S≤R:=by dsimp only [S,R,pairLength];omega
  have nz : n≤3*R:=by
    dsimp only [FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos] at cap
    change n<(3*R+2)-(a+m+3+z) at cap
    omega
  have gammaBound:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  have zz : z≤R:=by omega
  have qr : Q≤3*R+2:=by change Q≤F-(S+z+n+3)-1 at rows;dsimp only [F] at rows;omega
  have bound : F≤12*(R+1)^2:=by dsimp only [F];nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
  refine ⟨g,t,u,by have hp:=Nat.min_le_right (A+Q) S;dsimp only [Stream.Target.cursor];omega,gp,tp,
    price R S z n (min A S) Q u sr nz zz qr up,?_,?_,?_⟩
  · rw [UniformTM.run_add,start]
    simpa only [ended,clipped_cursor,restored_image U S z n (min A S) A Q Q] using run
  · intro v hv
    by_cases early : v≤g+t
    · exact initialHeads v early
    · rw [show v=(g+t)+(v-(g+t)) by omega,UniformTM.run_add,start]
      exact (through path fit (v-(g+t)) (by omega)).trans bound
  · have source (i : Nat) (lo : min A S≤ i) (hi : i<S) : U i=some ((Fin.append x w) ⟨i,hi⟩):=by
      have original:=rawSource x w gamma cap
      by_cases full : A≤S
      · rw [Nat.min_eq_left full] at lo
        exact original i lo hi
      · rw [Nat.min_eq_right (by omega)] at lo
        omega
    have table:=whole S (min A S) n (Fin.append x w) U source
    simpa only [clipped_read] using table
#print axioms clipped_cursor
#print axioms clipped_read
#print axioms restored_image
#print axioms price
#print axioms raw_paid
end VirtualFinalClosure.RawPaidStream
