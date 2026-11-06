import TotalIngressClosure.CanonicalSpec
import TotalIngressClosure.VirtualFrame
import TotalIngressClosure.VirtualEntry
import TotalIngressClosure.ControlEvents
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("CanonicalSpec","Outcome","Outcome"),("CanonicalSpec","CanonicalResult","CanonicalResult"),
      ("VirtualFrame","virtual_frame","sourceFrame"),("VirtualFrame","clear_frame","clearFrame"),
      ("VirtualEntry","virtual_entry","virtualEntry"),("ControlEvents","virtual_cuts","virtualCuts"),
      ("FirstEvents","leaf_first","leafFirst"),("FirstEvents","reject_first","rejectFirst"),
      ("FirstEvents","leaf_terminal","leafTerminal"),("EventSafety","leaf_stays","leafStays")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private.TotalIngressClosure."++mod++".") && n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique complete virtual branch {mod}/{key}: {found.map Prod.fst}"
private theorem virtual_price (k R t:Nat)(price:t ≤ 536870912*(k+1)*(R+1)^3):
    t+5 ≤ 4294967296*(k+1)*(R+1)^3:=by
  have positive:0 < (k+1)*(R+1)^3:=Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have pos:1 ≤ (k+1)*(R+1)^3:=positive
  nlinarith only [price,pos]
set_option maxRecDepth 4000 in
private theorem virtual_result (k:Nat){a m z n:Nat}(x:Bitstring a)(w:Bitstring m)
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (firstPhysical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z)
    (rows:2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (clean:Bool)
    (branch: (clean=false ∧ min (9+2*z+2^n) (a+m)=a+m) ∨
      (clean=true ∧ min (9+2*z+2^n) (a+m)<a+m ∧
       ((a+m-min (9+2*z+2^n) (a+m) < bitLength n) ∨
        (bitLength n ≤ a+m-min (9+2*z+2^n) (a+m) ∧ ∃ v2 v3 v4 v5 d,CappedWeight.Target.Cap k n
          (a+m-min (9+2*z+2^n) (a+m)) v2 v3 v4 v5 d))))
    (T:Nat)(hH:a+m+z+n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)))
    (price:T ≤ 536870912*(k+1)*(pairLength a m+1)^3)
    (beyond:a+m ≤ Cursor.Target.M k n z)
    (over:min (9+2*z+2^n) (a+m)=a+m ∨
      (min (9+2*z+2^n) (a+m)<a+m ∧ a+m-min (9+2*z+2^n) (a+m) < Cursor.Target.W k n))
    (handoff:
      let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos (pairLength a m)
      let B:=FixedRawLengthFence.allocation (pairLength a m)
      let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
      let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
      (AllArityCursor.machine k).run T (initialConfig (AllArityCursor.machine k) B (encodePair x w))=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,
            fun i=>(if clean then Cursor.Target.image V k S n z F else V) i.val⟩)
    (heads:∀ u,u ≤ T → ((AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val ≤ 12*(pairLength a m+1)^2) :
    CanonicalResult k x w:=by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos R
  let p:=min (9+2*z+2^n) S;let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let tape:=if clean then Cursor.Target.image V k S n z F else V
  let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
  obtain ⟨arena,sep,last,digits⟩:=sourceFrame x w gamma cap rows
  have room:S+z+n+3 < F:=lt_of_le_of_lt (Nat.le_add_right _ _) arena
  have frame:tape L=none ∧ tape (S+z+n+3)=none ∧ ∀ j:Fin n,tape (S+z+n+3-1-j.val)=some false:=by
    cases clean
    · exact ⟨sep,last,digits⟩
    · obtain ⟨sepEq,lastEq,digitEq⟩:=clearFrame V k S n z F beyond room
      exact ⟨sepEq.trans sep,lastEq.trans last,fun j=>(digitEq j).trans (digits j)⟩
  have cuts:=virtualCuts k x w header tag gamma firstPhysical cap rows over
  obtain ⟨s,st,done,foot,firstBody⟩:=virtualEntry k x w tag gamma firstPhysical T (12*(R+1)^2) hH tape handoff heads cuts frame.1 frame.2.1 frame.2.2
  have bound:s+5 ≤ 4294967296*(k+1)*(R+1)^3:=(Nat.add_le_add_right st 5).trans (virtual_price k R T price)
  by_cases zero:n=0
  · have reject:((BodyIngress.machine k).run (s+5) c).state=(BodyIngress.machine k).reject:=by
      rw [done];simp only [if_pos zero]
    have other(u:Nat)(hu:u < s+5):
        (∀ b,((BodyIngress.machine k).run u c).state≠BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))) ∧
        (∀ mode:Fin 3,((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.entry mode)):=by
      refine ⟨?_,firstBody u hu⟩
      intro b bad
      have keep:=leafStays b ((BodyIngress.machine k).run u c) bad (s+5-u)
      rw [←UniformTM.run_add,show u+(s+5-u)=s+5 by omega,reject] at keep
      exact (leafTerminal b).2 keep.symm
    obtain ⟨d,dt,hit,_whole,first,safe,negative⟩:=rejectFirst k x w (s+5) reject other
    exact ⟨d,dt.trans bound,fun u hu=>foot u (hu.trans dt),first,safe,Or.inl ⟨hit,negative⟩⟩
  · have positive:0 < n:=by omega
    have leaf:((BodyIngress.machine k).run (s+5) c).state=
        BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)):=by rw [done];simp only [if_neg zero]
    obtain ⟨d,dt,whole,first,safe⟩:=leafFirst c leaf firstBody
    refine ⟨d,dt.trans bound,fun u hu=>foot u (hu.trans dt),first,safe,Or.inr ?_⟩
    refine ⟨n,z,hH,tag,gamma,header,cap,arena,Or.inr ?_⟩
    refine ⟨positive,beyond,?_,((VirtualLeaf.decode_leaf k n (fun _=>false)).2.2 positive).1,?_⟩
    · intro j;exact padRead_ge _ (by omega)
    · have atEnd:=whole.trans done
      simp only [if_neg zero] at atEnd
      rcases branch with ⟨cl,eof⟩|⟨cl,phys,reason⟩
      · exact Or.inl ⟨eof,by simpa only [tape,cl,Bool.false_eq_true,if_false] using atEnd⟩
      · exact Or.inr ⟨phys,reason,by simpa only [tape,cl,if_true] using atEnd⟩
end TotalIngressClosure
