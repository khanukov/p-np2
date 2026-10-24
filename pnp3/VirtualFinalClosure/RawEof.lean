import VirtualFinalClosure.RawPaidStream
import VirtualFinalClosure.EofPrepared
import VirtualFinalClosure.LeafFirst
import VirtualFinalClosure.LeafZero
import VirtualFinalClosure.RawPaidLength
import VirtualFinalClosure.ZeroMeaning
namespace VirtualFinalClosure.RawEof
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.RawPaidStream","VirtualFinalClosure.RawPaidStream","raw_paid","rawPaid",(1:Nat)),
      ("VirtualFinalClosure.EofPrepared","VirtualFinalClosure.EofPrepared","prepared","eofPath",1),
      ("VirtualFinalClosure.LeafFirst","VirtualFinalClosure.LeafFirst","after_prefix","positiveLeaf",1),
      ("VirtualFinalClosure.LeafZero","VirtualFinalClosure.LeafZero","after_prefix","zeroLeaf",1),
      ("VirtualFinalClosure.LeafNativeRows","VirtualFinalClosure.LeafNativeRows","ready","ready",0),
      ("VirtualFinalClosure.RawPaidLength","VirtualFinalClosure.RawPaidLength","assn_false","assnFalse",1),
      ("VirtualFinalClosure.ZeroMeaning","VirtualFinalClosure.ZeroMeaning","mode_test","modeTest",1),
      ("VirtualFinalClosure.GuardZeroSemantics","VirtualFinalClosure.GuardZeroSemantics","zero_suffix","zeroSuffix",1),
      ("VirtualFinalClosure.GuardAddresses","VirtualFinalClosure.GuardAddresses","address","address",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_room","smallRoom",1),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","q","q",0),
      ("VirtualFinalClosure.StreamActiveOrbit","VirtualFinalClosure.StreamActiveOrbit","bits","bits",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","folded","folded",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong plain-V raw EOF FINAL term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique plain-V raw EOF FINAL term {mod}/{key}"
private theorem price (R S z n Q g t u : Nat) (arena : S+z+n+3+Q < 3*R+2)
    (gp : g ≤ 128*(R+1)^2) (tp : t ≤ 144*(R+1)^2) (up : u ≤ 4096*(R+1)^2) :
    g+t+u+(z+n+5)+6 ≤ 8192*(R+1)^2:=by
  nlinarith only [arena,gp,tp,up,Nat.zero_le S,Nat.zero_le Q,Nat.zero_le R,Nat.zero_le (R^2)]
private theorem large_room (k R : Nat) : 12*(R+1)^2 < tapeLength R (allocation k R):=by
  have old:=smallRoom R
  have mono:=smallBudget k R
  dsimp only [tapeLength] at old ⊢
  omega
private theorem eof_image (V : Nat → Option Bool) (S z n F : Nat) (positive : 0 < n) :
    put V (S+z+n+3) (some false)=Target.virtualImage V S z n F S 0:=by
  funext i
  change (if i=S+z+n+3 then some false else V i)=
    (if i=S+z+n+3 then (if n=0 then none else some false)
      else if S=S then V i else Cursor.Target.scratch V F 0 n i)
  rw [if_neg (Nat.ne_of_gt positive),if_pos rfl]
private theorem zero_image (V : Nat → Option Bool) (S z F : Nat) (blank : V (S+z+3)=none) :
    V=Target.virtualImage V S z 0 F S 0:=by
  funext i
  change V i=if i=S+z+0+3 then none else if S=S then V i else Cursor.Target.scratch V F 0 0 i
  rw [if_pos rfl]
  by_cases hit : i=S+z+0+3
  · rw [if_pos hit,hit];exact blank
  · rw [if_neg hit]
/-- Real raw EOF branch, including partial-gamma/source clipping. All Q rows
are physically paid and observed first. The native EOF path has plain V and no
six-bank workspace. Positive n executes canonical5 plus literal flag FINAL;
n0 executes its genuine fifth-row OOB reject. No rho premise is supplied. -/
private theorem raw_eof (k : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,2*z+1))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (eof : min (9+2*z+2^n) (a+m)=a+m) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let L:=S+z+2;let F:=3*R+2;let A:=9+2*z;let Q:=2^n
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n A Q Q false
    let c:=initialConfig (machine k) B (encodePair x w)
    ∃ (T : Nat) (hH : S+z+n+3 < tapeLength R B),T ≤ 8192*(R+1)^2 ∧
      (machine k).run T c=
        ⟨if PartAEndpoint.thresholdContentWitnessRelation k a m x w then (machine k).accept else (machine k).reject,
          ⟨S+z+n+3,hH⟩,fun i=>Target.virtualImage V S z n F S 0 i.val⟩ ∧
      (∀ u,u < T → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (mode : Fin 3) (md : Fin 144),((machine k).run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k
            (BodyIngress.body k (SerializedBody.entry mode)))) md) ∧
      (∀ u,u ≤ T → ((machine k).run u c).head.val ≤ 12*(R+1)^2):=by
  intro S R C B L F A Q U V c
  obtain ⟨g,t,u,hp,gp,tp,up,atStream,oldHeads,table⟩:=rawPaid k x w canonical header tag gamma firstPhysical cap rows
  let f:=folded (bits U (min A S) S) Q
  let md : Fin 144:=⟨8+f.val,by have h:=f.isLt;omega⟩
  have atEOF : Stream.Target.cursor A S Q=S:=eof
  change Stream.Target.cursor A S Q < tapeLength R B at hp
  have hS : S < tapeLength R B:=atEOF ▸ hp
  have start : (machine k).run (g+t+u) c=⟨q k f 57,⟨S,hS⟩,fun i=>V i.val⟩:=by
    have selected : (if Stream.Target.cursor A S Q=S then 57 else 58)=57:=if_pos atEOF
    change (machine k).run (g+t+u) c=
      ⟨q k f (if Stream.Target.cursor A S Q=S then 57 else 58),
        ⟨Stream.Target.cursor A S Q,hp⟩,fun i=>V i.val⟩ at atStream
    refine atStream.trans ?_
    apply Config.ext_parts
    · exact congrArg (q k f) selected
    · exact Fin.ext atEOF
    · rfl
  obtain ⟨cells,_short,_fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨arena,_source,sourceEnd,reg,sep,assn,last,_marks,_gap,_fence⟩:=cells
  change S+z+n+3+Q < F at arena
  have envelope : S+z+n+3 ≤ 12*(R+1)^2:=by
    have low : 3*R+2 ≤ 12*(R+1)^2:=by nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
    exact (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right (S+z+n+3) Q) arena)).trans low
  have finite : 12*(R+1)^2 < tapeLength R B:=large_room k R
  have fullH : L+n+1 < tapeLength R B:=by
    have same : L+n+1=S+z+n+3:=by dsimp only [L];omega
    rw [same];exact envelope.trans_lt finite
  have path:=eofPath k (12*(R+1)^2) S z n f V envelope sourceEnd sep last reg assn
  have atReady : (machine k).run (g+t+u+(z+n+5)) c=
      ⟨ready k md,⟨L+n+1,fullH⟩,fun i=>V i.val⟩:=by
    rw [UniformTM.run_add,start]
    have head : L+n+1=S+z+n+3:=by dsimp only [L];omega
    simpa only [head] using execute path finite
  have heads (v : Nat) (hv : v ≤ g+t+u+(z+n+5)) : ((machine k).run v c).head.val ≤ 12*(R+1)^2:=by
    by_cases early : v ≤ g+t+u
    · exact oldHeads v early
    · rw [show v=g+t+u+(v-(g+t+u)) by omega,UniformTM.run_add,start]
      exact through path finite (v-(g+t+u)) (by omega)
  have beyond : S ≤ A+Q:=by dsimp only [A,Q,S] at eof ⊢;omega
  have virtual : S ≤ treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n:=by
    rw [address k _ header]
    change S ≤ 9+2*z+2^n+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n
    change S ≤ 9+2*z+2^n at beyond
    omega
  have semantics:=zeroSuffix k x w canonical header tag virtual (by
    intro i lo hi
    have same : tagLen+(2*z+1)+Pnp3.Models.Partial.tableLen n=A+Q:=by
      change 8+(2*z+1)+2^n=(9+2*z)+2^n
      omega
    rw [same] at lo
    omega)
  have base : tagLen+(2*z+1)=A:=by change 8+(2*z+1)=9+2*z;omega
  have sameH : L+n+1=S+z+n+3:=by dsimp only [L];omega
  by_cases positive : 0 < n
  · obtain ⟨done,first,allHeads⟩:=positiveLeaf k R B (12*(R+1)^2) L n (g+t+u+(z+n+5)) md V (fun _=>false) c
      positive (by rw [sameH];exact envelope) finite sep (by rw [sameH];exact last)
      (by intro j;exact assnFalse U S z n A (L+n-j.val) (by dsimp only [L];have h:=j.isLt;omega) (by dsimp only [L];omega))
      heads atReady
    have test : (flag md.val%2=1 ∧ bad md.val=0) ↔ PartAEndpoint.thresholdContentWitnessRelation k a m x w=true:=by
      have flagTest:=modeTest f (fun _=>false) 0
      change (flag (8+f.val)%2=1 ∧ bad (8+f.val)=0) ↔ f.val%2=1 at flagTest
      refine flagTest.trans ?_
      constructor
      · intro matched
        apply semantics.mpr
        refine ⟨positive,?_⟩
        intro j
        simpa only [base] using (table.mp matched) j
      · intro accepted
        apply table.mpr
        intro j
        simpa only [base] using (semantics.mp accepted).2 j
    have image : put V (L+n+1) (some false)=Target.virtualImage V S z n F S 0:=by
      rw [sameH];exact eof_image V S z n F positive
    refine ⟨g+t+u+(z+n+5)+6,envelope.trans_lt finite,price R S z n Q g t u arena gp tp up,?_,first,allHeads⟩
    have actual : (machine k).run (g+t+u+(z+n+5)+6) c=
        ⟨if PartAEndpoint.thresholdContentWitnessRelation k a m x w then (machine k).accept else (machine k).reject,
          ⟨L+n+1,fullH⟩,fun i=>put V (L+n+1) (some false) i.val⟩:=by
      simpa only [test] using done
    refine actual.trans ?_
    apply Config.ext_parts
    · rfl
    · exact Fin.ext sameH
    · exact congrArg (fun T=>fun i : Fin (tapeLength R B)=>T i.val) image

  · have zero : n=0:=by omega
    subst n
    have rejecting : PartAEndpoint.thresholdContentWitnessRelation k a m x w=false:=by
      cases h : PartAEndpoint.thresholdContentWitnessRelation k a m x w
      · rfl
      · have impossible:=(semantics.mp h).1
        omega
    obtain ⟨done,first,allHeads⟩:=zeroLeaf k R B (12*(R+1)^2) L (g+t+u+(z+0+5)) md V c
      (by simpa only [Nat.add_zero] using envelope) finite sep (by simpa only [Nat.add_zero] using last) heads atReady
    have image : V=Target.virtualImage V S z 0 F S 0:=zero_image V S z F last
    refine ⟨g+t+u+(z+0+5)+5,envelope.trans_lt finite,?_,?_,first,allHeads⟩
    · have bound:=price R S z 0 Q g t u arena gp tp up
      omega
    · refine done.trans ?_
      apply Config.ext_parts
      · rw [rejecting];rfl
      · apply Fin.ext
        dsimp only [L]
      · exact congrArg (fun T=>fun i : Fin (tapeLength R B)=>T i.val) image

#print axioms large_room
#print axioms eof_image
#print axioms zero_image
#print axioms price
#print axioms raw_eof
end VirtualFinalClosure.RawEof
