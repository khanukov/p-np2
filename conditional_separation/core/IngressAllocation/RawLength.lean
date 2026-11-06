import IngressAllocation.WorkspaceRaw
import IngressAllocation.LengthTrace
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  let specs := [("IngressAllocation.WorkspaceRaw","IngressAllocation","physical_workspace_heads","workspaceRaw"),
    ("IngressAllocation.LengthTrace","IngressAllocation","length_heads","lengthHeads"),
    ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells"),
    ("VirtualLeaf.Raw","VirtualLeaf","width","acceptedWidth")]
  let fields := ["arena","source","eof","reg","sep","assn","right","marks","gap","fence"]
  let specs := specs ++ fields.map fun f => ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells."++f,"cell_"++f)
  for (mod,ns,key,aliasName) in specs do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique exact workspace raw interface {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem physical_length_heads (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical : min (9+2*z+2^pr.2.n) (a+m) < a+m) :
    let S:=a+m;let n:=pr.2.n;let L:=S+z+2;let F:=3*pairLength a m+2
    let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared (FixedRawLengthFence.allocation (pairLength a m)) x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    ∃ (t : Nat) (hF : (if bitLength n ≤ r then L else F+r+n+3) < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      (AllArityCursor.machine k).run t
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k) ⟨Cursor.q k (if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304),
          ⟨if bitLength n ≤ r then L else F+r+n+3,hF⟩,fun i=>Y i.val⟩ ∧
      Footprint (AllArityCursor.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w) t (12*(pairLength a m+1)^2) ∧
      (∀ u,u ≤ t → ((AllArityCursor.machine k).run u
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val ≤ 617) := by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let S:=a+m;let n:=pr.2.n;let L:=S+z+2;let F:=3*R+2
  let p:=min (9+2*z+2^n) S;let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let C:=SuffixCap.Target.image V F r
  let X:=CappedWorkspace.Target.image C L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  obtain ⟨t,hF,atWork,workHeads,workControl⟩:=workspaceRaw k x w accepted parsed z gamma physical
  have width:=acceptedWidth x w accepted parsed
  have cap:=AcceptedBody.strict_capacity x w gamma width
  have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
  obtain ⟨fr,_shortFit,fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨_legacy,fit⟩:=Cursor.raw_tail_blank x w gamma cap rows
  change F+5*r+n+7 < tapeLength R B at fit
  change ∀ i : Fin (tapeLength R B), F < i.val → V i.val=none at fresh
  have geom : L+n+1+2^n < F:=by have h:=cell_arena fr;change S+z+n+3+2^n < F at h;dsimp only [L];omega
  have geo : L+n+1 < F:=lt_of_le_of_lt (Nat.le_add_right _ _) geom
  have rp : 0 < r:=by change p < S at physical;dsimp only [r];omega
  have oldC (i : Nat) (hi : i ≤ F+1) : C i=V i:=by
    dsimp only [C,SuffixCap.Target.image];rw [if_neg (by omega)]
  have cf : C F=some false:=by rw [oldC _ (by omega)];exact cell_fence fr
  have cd0 : C (F+1)=none:=by rw [oldC _ (by omega)];exact fresh ⟨F+1,by omega⟩ (by change F < F+1;omega)
  have cb0 (i : Nat) (lo : F+1 < i) (hi : i < F+r+2) : C i=some true:=by
    dsimp only [C,SuffixCap.Target.image];rw [if_pos (by omega)]
  have blank (i : Nat) (lo : F+r+2 ≤ i) (hi : i ≤ F+5*r+n+7) : C i=none:=by
    dsimp only [C,SuffixCap.Target.image];rw [if_neg (by omega)]
    exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ (by change F < i;omega)
  obtain ⟨xa,xf,xb0,xzero,xd,xold⟩:=AllArityWorkspace.six_bank_image C L n F r geo cf cd0 cb0 blank
  change ∀ i,i ≤ L ∨ (L+n+1 ≤ i ∧ i ≤ F+1) ∨ F+5*r+n+7 ≤ i → X i=C i at xold
  have xsep : X L=none:=by rw [xold L (Or.inl le_rfl),oldC L (by omega)];exact cell_sep fr
  have xright : X (L+n+1)=none:=by
    rw [xold _ (Or.inr (Or.inl ⟨le_rfl,by omega⟩)),oldC _ (by omega)]
    rw [show L+n+1=S+z+n+3 by dsimp only [L];omega]
    exact cell_right fr
  have xmarks (i : Nat) (lo : L+n+1 < i) (hi : i ≤ L+n+1+2^n) : X i=some true:=by
    rw [xold i (Or.inr (Or.inl ⟨by omega,by omega⟩)),oldC _ (by omega)]
    exact cell_marks fr i (by change S+z+n+3 < i;dsimp only [L] at lo;omega)
      (by change i ≤ S+z+n+3+2^n;dsimp only [L] at hi;omega)
  have xgap (i : Nat) (lo : L+n+1+2^n < i) (hi : i < F) : X i=none:=by
    have above : L+n+1 ≤ i:=(Nat.le_add_right (L+n+1) (2^n)).trans (Nat.le_of_lt lo)
    rw [xold i (Or.inr (Or.inl ⟨above,by omega⟩)),oldC _ (by omega)]
    exact cell_gap fr i (by change S+z+n+3+2^n < i;dsimp only [L] at lo;omega) hi
  obtain ⟨b,hb,runLength,lengthFoot,lengthBefore⟩:=lengthHeads k R B L n (2^n) F r X rp (by positivity)
    geom xsep xa xright xmarks xgap xf (xd _ (Or.inl rfl)) xb0 (xd _ (Or.inr (Or.inl rfl)))
    (fun i lo hi=>xzero i (Or.inl ⟨lo,hi⟩)) (xd _ (Or.inr (Or.inr (Or.inl rfl))))
    (fun i lo hi=>xzero i (Or.inr (Or.inl ⟨lo,hi⟩))) (xd _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) fit
  have replay (s : Nat) (config : Config (Cursor.machine k).stateCount R B) :
      (AllArityCursor.machine k).run s (SmallIngress.producer.seqEmbedRight (Cursor.machine k) config)=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ((Cursor.machine k).run s config):=by
    change (SmallIngress.producer.seq (Cursor.machine k)).run s _=_
    rw [UniformTM.seq_run_right]
  have done : (AllArityCursor.machine k).run (t+b) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k (if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304),
        ⟨if bitLength n ≤ r then L else F+r+n+3,hb⟩,fun i=>Y i.val⟩:=by
    rw [UniformTM.run_add,atWork,replay,runLength]
  have pair : S ≤ R:=by dsimp only [S,R,pairLength];omega
  have nr : n ≤ R:=width.trans pair
  have rr : r ≤ R:=(Nat.sub_le _ _).trans pair
  have envelope : F+5*r+n+7 ≤ 12*(R+1)^2:=by
    dsimp only [F];nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
  refine ⟨t+b,hb,done,?_,?_⟩
  · intro u hu
    by_cases early : u ≤ t
    · exact workHeads u early
    · rw [show u=t+(u-t) by omega,UniformTM.run_add,atWork,replay]
      exact (lengthFoot (u-t) (by omega)).trans envelope
  · intro u hu
    by_cases early : u ≤ t
    · exact (workControl u early).trans (by decide)
    · by_cases last : u < t+b
      · rw [show u=t+(u-t) by omega,UniformTM.run_add,atWork,replay]
        exact (Nat.add_lt_add_left (lengthBefore (u-t) (by omega)) 288).le
      · have eq : u=t+b:=by omega
        rw [eq,done]
        change 288+(if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304)%Cursor.stateCount k ≤ 617
        split_ifs <;> rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)] <;> omega
end IngressAllocation
