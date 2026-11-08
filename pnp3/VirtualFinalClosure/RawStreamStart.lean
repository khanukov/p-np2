import VirtualFinalClosure.QuietLow
import VirtualFinalClosure.LengthPrefix
import VirtualFinalClosure.StreamActivePaths
import TotalIngressClosure.ProducerSuccess
import VirtualFinalClosure.HeadFields
namespace VirtualFinalClosure.RawStreamStart
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("TotalIngressClosure.ProducerSuccess","TotalIngressClosure","repaired_entry","repairedEntry",(1:Nat)),
      ("VirtualFinalClosure.RawLengthLift","VirtualFinalClosure.RawLengthLift","early_body","earlyBody",1),
      ("VirtualFinalClosure.RawLengthLift","VirtualFinalClosure.RawLengthLift","embed_state","embedState",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","extend_body","extendBody",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("VirtualFinalClosure.PairPrefix","VirtualFinalClosure.PairPrefix","raw_entry","pairPrefix",1),
      ("VirtualFinalClosure.QuietLow","VirtualFinalClosure.QuietLow","run_prefix","quietPrefix",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","guarded","guardedState",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","total","totalState",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","extension","extensionState",1),
      ("VirtualFinalClosure.EventValues","VirtualFinalClosure.EventValues","embedded_table","embeddedTable",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","guarded","guardedHead",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","total","totalHead",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","extension","extensionHead",1),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","q","q",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong literal raw-to-Stream start term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal raw-to-Stream start term {mod}/{key}"
private theorem config_head (k : Nat) {N B : Nat} (f : Fin 144)
    (c : Config (CertificateGuardClosure.machine k).stateCount N B) :
    (config k f c).head.val=c.head.val:=rfl
/-- SAME actual raw source through repaired producer and the physical exact
certificate guard, to Stream start with its genuine initial finite flag1.
No paid table observation has happened, and no relation/AST premise is used. -/
private theorem raw_start (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z) :
    let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R;let B:=allocation k R
    let L:=a+m+z+2;let c:=initialConfig (machine k) B (encodePair x w)
    let T:=Body.extend (SmallIngress.prepared C x w z n)
    ∃ (g t : Nat) (hL : L < tapeLength R B),
      g≤128*(R+1)^2 ∧ t≤144*(R+1)^2 ∧
      (machine k).run (g+t) c=⟨q k ⟨1,by decide⟩ 0,⟨L,hL⟩,fun i=>T i.val⟩ ∧
      (∀ u,u≤g+t → ((machine k).run u c).head.val≤12*(R+1)^2):=by
  intro R C B L c T
  let y:=encodePair x w
  let A:=AllArityCursor.machine k
  let small:=initialConfig A C y
  let old:=initialConfig (CertificateGuardClosure.machine k) B y
  obtain ⟨t,hL,tp,repaired,heads,lower⟩:=repairedEntry k x w header tag gamma firstPhysical cap
  have same (u : Nat) : (IngressRepair.machine k).run u
      (initialConfig (IngressRepair.machine k) C y)=A.run u small:=
    IngressRepair.supported_transport k x w z tag gamma firstPhysical u
  have initialLow (u : Nat) (hu : u < t) : (A.run u small).state.val < 288:=by
    rw [←same u]
    exact lower u hu
  have arrival : A.run t small=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 0,⟨L,hL⟩,SmallIngress.prepared C x w z n⟩:=by
    rw [←same t]
    exact repaired
  have bodyEvery:=earlyBody k x w z tag gamma firstPhysical t (by intro u hu;exact (Nat.le_of_lt (initialLow u hu)).trans (by decide))
  have bodyHeads (u : Nat) (hu : u≤t) : ((BodyIngress.machine k).run u
      (initialConfig (BodyIngress.machine k) C y)).head.val≤12*(R+1)^2:=by
    rw [bodyEvery u hu]
    change (A.run u small).head.val≤12*(R+1)^2
    rw [←same u]
    exact heads u hu
  have large:=extendBody k R t y bodyHeads
  have budget : C≤B:=smallBudget k R
  have smallRoom : 2*R+3 < tapeLength R C:=by
    dsimp only [tapeLength,C,FixedRawLengthFence.allocation]
    nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
  have room : 2*R+3 < tapeLength R B:=by simp only [tapeLength] at smallRoom ⊢;omega
  have parserRoom : FixedPairParser.clock R≤B:=by
    have smallClock : FixedPairParser.clock R≤C:=by
      change 2*R+1≤16*(R+1)^2
      nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
    exact smallClock.trans budget
  obtain ⟨g,gp,pairLow,pairHeads,rawBody⟩:=pairPrefix k B x w canonical room parserRoom
  have oldLow (u : Nat) (hu : u≤g+t) : ((CertificateGuardClosure.machine k).run u old).state.val≤375:=by
    by_cases early : u < g
    · exact (Nat.le_of_lt (pairLow u early)).trans (by decide)
    · rw [show u=g+(u-g) by omega,rawBody,large (u-g) (by omega),bodyEvery (u-g) (by omega),guardedState,totalState,extensionState,embedState]
      by_cases before : u-g < t
      · have h : ((AllArityCursor.machine k).run (u-g)
            (initialConfig (AllArityCursor.machine k) C y)).state.val<288:=initialLow (u-g) before
        dsimp only [C,R,y] at h
        omega
      · have eq : u-g=t:=by omega
        rw [eq,arrival]
        change 77+(10+(288+(0%Cursor.stateCount k)))≤375
        simp
  have active:=quietPrefix k R B (g+t) y oldLow
  have hLB : L < tapeLength R B:=by
    change L < tapeLength R C at hL
    dsimp only [tapeLength] at hL ⊢
    omega
  refine ⟨g,t,hLB,gp,tp,?_,?_⟩
  · rw [active (g+t) le_rfl,rawBody,large t le_rfl,bodyEvery t le_rfl,arrival]
    apply Config.ext_parts
    · have eq:=embeddedTable k (Cursor.q k 0) ⟨L,hL⟩ (SmallIngress.prepared C x w z n)
      change control k _ ⟨9,by decide⟩=q k ⟨1,by decide⟩ 0
      have ext : (IngressAllocation.extendConfig budget
          (BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k
            (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k 0,⟨L,hL⟩,SmallIngress.prepared C x w z n⟩))))).state=
          (BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k
            (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k 0,⟨L,hL⟩,SmallIngress.prepared C x w z n⟩)))).state:=rfl
      change control k (CertificateGuardClosure.old k (TotalIngressClosure.old k _)) _=_
      rw [ext]
      exact congrArg (fun s=>control k s ⟨9,by decide⟩) eq
    · rfl
    · funext i
      change (if h : i.val < tapeLength R C then SmallIngress.prepared C x w z n ⟨i.val,h⟩ else none)=T i.val
      rfl
  · intro u hu
    rw [active u hu,config_head]
    by_cases early : u≤g
    · exact pairHeads u early
    · rw [show u=g+(u-g) by omega,rawBody,large (u-g) (by omega),guardedHead,totalHead,extensionHead]
      exact bodyHeads (u-g) (by omega)
#print axioms config_head
#print axioms raw_start
end VirtualFinalClosure.RawStreamStart
