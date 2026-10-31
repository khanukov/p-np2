import TotalIngressClosure.VirtualCuts
import TotalIngressClosure.EventSafety
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualLeaf.Transport","VirtualLeaf","first_ready","firstReady"),
      ("VirtualLeaf.Transport","VirtualLeaf","transport","virtualTransport"),
      ("CanonicalLeaf.Rows","CanonicalLeaf","transport","canonicalTransport"),
      ("CarryWindow.Transport","CarryWindow","transport","carryTransport"),
      ("TotalIngressClosure.EventSafety","TotalIngressClosure","old_entry_disjoint","oldDisjoint")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique actual first virtual consumer interface {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem virtual_entry (k : Nat) {a m z n : Nat} (x:Bitstring a) (w:Bitstring m)
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (T P : Nat)
    (hH:a+m+z+n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)))
    (V:Nat → Option Bool)
    (handoff:(AllArityCursor.machine k).run T (initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k)
        ⟨Cursor.mReady k ⟨2,by decide⟩,⟨a+m+z+n+3,hH⟩,fun i=>V i.val⟩)
    (heads:∀ u,u ≤ T → ((AllArityCursor.machine k).run u (initialConfig (AllArityCursor.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val ≤ P)
    (cuts:∀ u,∀ j,j=430 ∨ j=613 → ((CanonicalLeaf.machine k).run u (initialConfig (CanonicalLeaf.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state≠
        VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (j+93*k))))
    (separator:V (a+m+z+2)=none) (last:V (a+m+z+n+3)=none)
    (digits:∀ j:Fin n,V (a+m+z+n+3-1-j.val)=some false) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let H:Fin (tapeLength R B):=⟨a+m+z+n+3,hH⟩
    let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
    ∃ s,s ≤ T ∧
      (BodyIngress.machine k).run (s+5) c=
        ⟨if n=0 then (BodyIngress.machine k).reject else
            BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
          if n=0 then (fun i=>V i.val) else Function.update (fun i=>V i.val) H (some false)⟩ ∧
      (∀ u,u ≤ s+5 → ((BodyIngress.machine k).run u c).head.val ≤ P) ∧
      (∀ u,u < s+5 → ∀ mode:Fin 3,((BodyIngress.machine k).run u c).state≠
        BodyIngress.body k (SerializedBody.entry mode)) := by
  intro R B H c
  let old:=initialConfig (IngressRepair.machine k) B (encodePair x w)
  let can:=initialConfig (CanonicalLeaf.machine k) B (encodePair x w)
  let carry:=initialConfig (CarryWindow.machine k) B (encodePair x w)
  have repair(u : Nat):(IngressRepair.machine k).run u old=(AllArityCursor.machine k).run u
      (initialConfig (AllArityCursor.machine k) B (encodePair x w)):=
    IngressRepair.supported_transport k x w z tag gamma physical u
  have oldAt:(IngressRepair.machine k).run T old=⟨VirtualLeaf.entry k,H,fun i=>V i.val⟩:=by
    rw [repair,handoff]
    rfl
  obtain ⟨s,st,same,first⟩:=firstReady old (t:=T) (by rw [oldAt])
  have oldFirst:(IngressRepair.machine k).run s old=⟨VirtualLeaf.entry k,H,fun i=>V i.val⟩:=same.trans oldAt
  have vt:=virtualTransport old (t:=s) first
  have ct:=canonicalTransport (VirtualLeaf.config k old) (t:=s) (by
    intro u hu
    rw [vt u (Nat.le_of_lt hu)]
    exact ((IngressRepair.machine k).run u old).state.isLt)
  have prefixRun(u : Nat)(hu:u ≤ s):(CanonicalLeaf.machine k).run u can=
      VirtualLeaf.config k ((IngressRepair.machine k).run u old):=(ct u hu).trans (vt u hu)
  have atEntry:(CanonicalLeaf.machine k).run s can=⟨CanonicalLeaf.entry k,H,fun i=>V i.val⟩:=by
    rw [prefixRun s le_rfl,oldFirst]
    rfl
  have fit:(a+m+z+2)+n+1 < tapeLength R B:=by
    have bound:a+m+z+n+3 < tapeLength R B:=hH
    omega
  obtain ⟨leaf,foot,_noVerdict,_firstLeaf,_tape,_decode,_window,_tail⟩:=CanonicalLeaf.prepared k
    (N:=R) (B:=B) (a+m+z+2) n (fun _=>false) (fun i=>V i.val) fit separator (by
      change V (a+m+z+2+n+1)=none
      convert last using 1;congr 1;omega) (by
      intro j
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using digits j)
  have headEq:(⟨a+m+z+2+n+1,fit⟩:Fin (tapeLength R B))=H:=Fin.ext (by dsimp only [H];omega)
  rw [headEq] at leaf foot
  have carried:=carryTransport can (t:=s+5) (by
    intro u _hu
    exact ⟨cuts u 430 (Or.inl rfl),cuts u 613 (Or.inr rfl)⟩)
  have carriedRun(u:Nat)(hu:u ≤ s+5):(CarryWindow.machine k).run u carry=
      CarryWindow.config k ((CanonicalLeaf.machine k).run u can):=carried u hu
  have body:=BodyIngress.transport carry (t:=s+5) (by
    intro u hu bad
    rw [carriedRun u (Nat.le_of_lt hu)] at bad
    have equal:=congrArg Fin.val bad
    change ((CanonicalLeaf.machine k).run u can).state.val=(CanonicalLeaf.machine k).stateCount+24 at equal
    have bound:=((CanonicalLeaf.machine k).run u can).state.isLt
    omega)
  have lift(u : Nat)(hu:u ≤ s+5):(BodyIngress.machine k).run u c=
      BodyIngress.config k (CarryWindow.config k ((CanonicalLeaf.machine k).run u can)):=
    (body u hu).trans (congrArg (BodyIngress.config k) (carried u hu))
  have finalCan:(CanonicalLeaf.machine k).run (s+5) can=
      ⟨if n=0 then (CanonicalLeaf.machine k).reject else CanonicalLeaf.result k false,H,
        if n=0 then (fun i=>V i.val) else Function.update (fun i=>V i.val) H (some false)⟩:=by
    rw [UniformTM.run_add,atEntry]
    have bzero:(if h:0 < n then (fun _ : Fin n=>false) ⟨0,h⟩ else false)=false:=by split <;> rfl
    simpa only [bzero] using leaf
  have hP:H.val ≤ P:=by
    have h:=heads T le_rfl
    rw [handoff] at h
    exact h
  refine ⟨s,st,?_,?_,?_⟩
  · rw [lift (s+5) le_rfl,finalCan]
    by_cases zero:n=0
    · simp only [if_pos zero];rfl
    · simp only [if_neg zero];rfl
  · intro u hu
    rw [lift u hu]
    change ((CanonicalLeaf.machine k).run u can).head.val ≤ P
    by_cases early:u ≤ s
    · rw [prefixRun u early,repair]
      exact heads u (early.trans st)
    · rw [show u=s+(u-s) by omega,UniformTM.run_add,atEntry]
      exact (foot (u-s) (by omega)).2.trans (by dsimp only [H] at hP;omega)
  · intro u hu mode
    rw [lift u (Nat.le_of_lt hu)]
    exact oldDisjoint k _ mode
end TotalIngressClosure
