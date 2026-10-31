import VirtualFinalClosure.NormalImage
import VirtualFinalClosure.PairPrefix
import VirtualFinalClosure.NormalRun
import TotalIngressClosure.NormalTotal
import TotalIngressClosure.FirstEvents
namespace VirtualFinalClosure.OldNormal
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("TotalIngressClosure.NormalTotal","TotalIngressClosure","normal_consumer_heads","bodyNormal",(1:Nat)),
      ("TotalIngressClosure.FirstEvents","TotalIngressClosure","normal_first","bodyFirst",1),
      ("TotalIngressClosure.Header","TotalIngressClosure","table_budget_width","tableWidth",1),
      ("IngressAllocation.Geometry","IngressAllocation","old_le_new","bodyBudget",1),
      ("IngressAllocation.Geometry","IngressAllocation","twelve_fields_bound","twelveBound",1),
      ("IngressAllocation.Extension","IngressAllocation","trace_of_room","traceRoom",1),
      ("IngressAllocation.Extension","IngressAllocation","extend_unique","uniqueExtension",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_room","smallRoom",1),
      ("VirtualFinalClosure.PairPrefix","VirtualFinalClosure.PairPrefix","raw_entry","pairPrefix",1),
      ("VirtualFinalClosure.NormalImage","VirtualFinalClosure.NormalImage","high_blank","imageHigh",1),
      ("VirtualFinalClosure.NormalImage","VirtualFinalClosure.NormalImage","extended_tape","extendTape",1),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","old_room","oldRoom",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","guarded","guardedState",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","total","totalState",1),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","extension","extendState",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","guarded","guardedHead",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","total","totalHead",1),
      ("VirtualFinalClosure.HeadFields","VirtualFinalClosure.HeadFields","extension","extendHead",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","guarded_old","guardedOld",1),
      ("VirtualFinalClosure.StateFields","VirtualFinalClosure.StateFields","total_old","totalOld",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","bodyControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong exact old normal raw component {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact old normal raw component {mod}/{key}"
private theorem body_value (k : Nat) (mode : Fin 3) :
    (bodyControl k mode).val=87+(BodyIngress.body k (SerializedBody.entry mode)).val:=by
  dsimp only [bodyControl]
  rw [guardedOld,totalOld]
  omega
private theorem state_value (k : Nat) {N C B : Nat} (h:C ≤ B) (c:Config (BodyIngress.machine k).stateCount N C) :
    (CertificateGuardClosure.config k (TotalIngressClosure.config k (IngressAllocation.extendConfig h c))).state.val=87+c.state.val:=by
  rw [guardedState,totalState,extendState]
  omega
private theorem normal_price (k R g t : Nat) (gp:g ≤ 128*(R+1)^2)
    (tp:t ≤ 2147483648*(k+1)*(R+1)^3) : g+t ≤ CertificateGuardClosure.deadline k R:=by
  have p2 : (R+1)^2 ≤ (R+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  have p3 : (R+1)^3 ≤ (R+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  have g0:=gp.trans (Nat.mul_le_mul_left 128 p2)
  have g1:g ≤ 128*(k+1)*(R+1)^6:=g0.trans (Nat.mul_le_mul_right _ (by omega))
  have t0:=tp.trans (Nat.mul_le_mul_left _ p3)
  change g+t ≤ 137438953472*(k+1)*(R+1)^6
  nlinarith only [g1,t0,Nat.zero_le ((k+1)*(R+1)^6)]
/-- Original exact guarded family, ALL physical normal cases without rho.
The reused complete BODY installer is transported by its actual head interval,
then prefixed by the literal exact-length guard/parsers at their actual time. -/
private theorem raw_normal (k : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical:m=a+1) (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z)
    (rows:2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical:min (9+2*z+2^n) (a+m) < a+m)
    (ellFits:bitLength n ≤ a+m-min (9+2*z+2^n) (a+m))
    (wFits:Cursor.Target.W k n ≤ a+m-min (9+2*z+2^n) (a+m)) :
    let S:=a+m;let R:=pairLength a m;let B0:=FixedRawLengthFence.allocation R
    let C:=CertificateGuardClosure.allocation k R;let O:=CertificateGuardClosure.machine k
    let L:=S+z+2;let F:=3*R+2;let p:=min (9+2*z+2^n) S;let r:=S-p;let W:=Cursor.Target.W k n;let g:=n^k+k
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B0 x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r;let Z:=AllArityBitLength.Target.seedImage Y F r n
    let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 g W 0 0) F r n g (bitLength W) 0 0 W
    let mode:=SerializedBody.sourceMode (Fin.append x w) (Cursor.Target.M k n z)
    let c:=initialConfig O C (encodePair x w)
    ∃ (t:Nat) (hH:S+z+n+3 < tapeLength R C),t ≤ CertificateGuardClosure.deadline k R ∧
      SerializedBody.delimiter F r n 12 < tapeLength R B0 ∧
      (∀ i,Cursor.Target.M k n z ≤ i → ∀ hi:i < S,I i=some ((Fin.append x w) ⟨i,hi⟩)) ∧
      O.run t c=⟨bodyControl k mode,⟨S+z+n+3,hH⟩,
        fun i=>SerializedBody.prepared I S (Cursor.Target.M k n z) F r n g W i.val⟩ ∧
      (∀ u,u < t → (O.run u c).state≠O.accept ∧ (O.run u c).state≠O.reject ∧
        ∀ mode:Fin 3,(O.run u c).state≠bodyControl k mode) ∧
      (∀ u,u ≤ t → (O.run u c).head.val ≤ 12*(R+1)^2):=by
  intro S R B0 C O L F p r W g U V X Y Z I mode c
  let y:=encodePair x w
  let small:=initialConfig (BodyIngress.machine k) B0 y
  obtain ⟨t,hH,tp,heads,atBody,source,bodyEntryFirst⟩:=bodyNormal k x w header tag gamma firstPhysical cap rows physical ellFits wFits
  have eventSafe:=bodyFirst small mode (congrArg (fun q=>q.state) atBody) bodyEntryFirst
  have budget : B0 ≤ C:=bodyBudget k R
  have trace:=traceRoom (BodyIngress.machine k) budget y t (by
    intro u hu
    exact lt_of_le_of_lt (Nat.add_le_add_right (heads u hu.le) 1) (smallRoom R))
  have bodyExt (u:Nat)(hu:u ≤ t) :
      (BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k) C y)=
        IngressAllocation.extendConfig budget ((BodyIngress.machine k).run u small):=uniqueExtension budget (trace u hu)
  obtain ⟨cells,_short,_fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨arena,_src,_end,_reg,_sep,_assn,_last,_marks,_gap,_fence⟩:=cells
  change S+z+n+3+2^n < F at arena
  have pair:S ≤ R:=by dsimp only [S,R,pairLength];omega
  have nr:n ≤ R:=tableWidth R S z n (by dsimp only [R,pairLength];omega) arena
  have rr:r ≤ R:=(Nat.sub_le _ _).trans pair
  have D12 : SerializedBody.delimiter F r n 12 < tapeLength R B0:=
    (twelveBound R r n rr nr (by dsimp only [R,pairLength];omega)).trans_lt (by have h:=smallRoom R;change 12*(R+1)^2+1 < tapeLength R B0 at h;omega)
  have blank:=imageHigh k x w gamma cap rows D12
  have room : 2*R+3 < tapeLength R C:=by
    have h:=oldRoom k R
    have low:2*R+3 ≤ 12*(R+1)^2+1:=by nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
    exact low.trans_lt h
  have parserRoom : FixedPairParser.clock R ≤ C:=by
    have old : FixedPairParser.clock R ≤ B0:=by
      change 2*R+1 ≤ 16*(R+1)^2
      nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
    exact old.trans budget
  obtain ⟨a0,ap,earlyLow,earlyHeads,suffix⟩:=pairPrefix k C x w canonical room parserRoom
  have hHC : S+z+n+3 < tapeLength R C:=by
    change S+z+n+3 < tapeLength R B0 at hH
    dsimp only [tapeLength] at hH ⊢
    omega
  have endBody : (BodyIngress.machine k).run t (initialConfig (BodyIngress.machine k) C y)=
      ⟨BodyIngress.body k (SerializedBody.entry mode),⟨S+z+n+3,hHC⟩,
        fun i=>SerializedBody.prepared I S (Cursor.Target.M k n z) F r n g W i.val⟩:=by
    refine (bodyExt t le_rfl).trans ?_
    rw [atBody]
    exact extendTape budget _ _ _ blank
  have finished : O.run (a0+t) c=⟨bodyControl k mode,⟨S+z+n+3,hHC⟩,
      fun i=>SerializedBody.prepared I S (Cursor.Target.M k n z) F r n g W i.val⟩:=by
    rw [suffix t,endBody]
    rfl
  refine ⟨a0+t,hHC,normal_price k R a0 t ap tp,D12,source,finished,?_,?_⟩
  · intro u hu
    by_cases early:u < a0
    · have low:=earlyLow u early
      change (O.run u c).state.val < 87 at low
      have noBody(j:Fin 3):(O.run u c).state≠bodyControl k j:=by
        intro eq;have value:=congrArg Fin.val eq
        rw [body_value] at value
        omega
      refine ⟨?_,?_,noBody⟩
      · intro eq;have value:=congrArg Fin.val eq
        change (O.run u c).state.val=414 at value
        omega
      · intro eq;have value:=congrArg Fin.val eq
        change (O.run u c).state.val=415 at value
        omega
    · have tail:u-a0 < t:=by omega
      have atTime:=suffix (u-a0)
      rw [show a0+(u-a0)=u by omega] at atTime
      have value : (O.run u c).state.val=87+((BodyIngress.machine k).run (u-a0) small).state.val:=by
        exact (congrArg (fun q=>q.state.val) atTime).trans
          ((congrArg (fun q=>(CertificateGuardClosure.config k (TotalIngressClosure.config k q)).state.val) (bodyExt _ tail.le)).trans
            (state_value k budget ((BodyIngress.machine k).run (u-a0) small)))
      refine ⟨?_,?_,?_⟩
      · intro eq
        apply eventSafe.2 (u-a0) tail.le
        apply Fin.ext
        have v:=congrArg Fin.val eq
        change (O.run u c).state.val=414 at v
        change ((BodyIngress.machine k).run (u-a0) small).state.val=327
        omega
      · intro eq
        apply (eventSafe.1 (u-a0) tail).1
        apply Fin.ext
        have v:=congrArg Fin.val eq
        change (O.run u c).state.val=415 at v
        change ((BodyIngress.machine k).run (u-a0) small).state.val=328
        omega
      · intro j eq
        apply (eventSafe.1 (u-a0) tail).2.2 j
        apply Fin.ext
        have v:=congrArg Fin.val eq
        rw [body_value] at v
        omega
  · intro u hu
    by_cases early:u ≤ a0
    · exact earlyHeads u early
    · rw [show u=a0+(u-a0) by omega,suffix,bodyExt (u-a0) (by omega),guardedHead,totalHead,extendHead]
      exact heads _ (by omega)
#print axioms body_value
#print axioms state_value
#print axioms normal_price
#print axioms raw_normal
end VirtualFinalClosure.OldNormal
