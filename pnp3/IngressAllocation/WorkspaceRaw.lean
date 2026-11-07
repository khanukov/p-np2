import IngressAllocation.CursorPrefix
import IngressAllocation.CountTrace
import IngressAllocation.WorkspaceTrace
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  let specs := [("IngressAllocation.CursorPrefix","IngressAllocation","cursor_prefix_heads","cursorHeads"),
    ("IngressAllocation.CountTrace","IngressAllocation","counted_heads","countHeads"),
    ("IngressAllocation.WorkspaceTrace","IngressAllocation","workspace_heads","workspaceHeads"),
    ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells"),
    ("AllArityWorkspace.Runtime","AllArityWorkspace","suffix_bound","suffixBound"),
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
private theorem physical_workspace_heads (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
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
    ∃ (t : Nat) (hF : F+1 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      (AllArityCursor.machine k).run t
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k) ⟨Cursor.q k 201,⟨F+1,hF⟩,fun i=>X i.val⟩ ∧
      Footprint (AllArityCursor.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w) t (12*(pairLength a m+1)^2) ∧
      (∀ u,u ≤ t → ((AllArityCursor.machine k).run u
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val ≤ 489) := by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let S:=a+m;let n:=pr.2.n;let L:=S+z+2;let F:=3*R+2
  let p:=min (9+2*z+2^n) S;let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let C:=SuffixCap.Target.image V F r
  let X:=CappedWorkspace.Target.image C L n F r
  let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  obtain ⟨otherZ,t,_hH,otherGamma,_price,hp,pre,_first,prefixBound,prefixHeads⟩:=cursorHeads k x w accepted parsed
  have same : otherZ=z:=Option.some.inj (otherGamma.symm.trans gamma)
  subst otherZ
  change (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
    ⟨Cursor.q k (if p=S then 57 else 58),⟨p,hp⟩,fun i=>V i.val⟩ at pre
  rw [if_neg (Nat.ne_of_lt physical)] at pre
  have width:=acceptedWidth x w accepted parsed
  have cap:=AcceptedBody.strict_capacity x w gamma width
  have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
  obtain ⟨fr,shortFit,fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨_legacy,fit⟩:=Cursor.raw_tail_blank x w gamma cap rows
  change F+5*r+n+7 < tapeLength R B at fit
  change F+r+2 < tapeLength R B at shortFit
  change ∀ i : Fin (tapeLength R B), F < i.val → V i.val=none at fresh
  have geom : S+z+n+3+2^n < F:=cell_arena fr
  have geo : S+z+n+3 < F:=lt_of_le_of_lt (Nat.le_add_right _ _) geom
  have pe : p=9+2*z+2^n:=Nat.min_eq_left (by change min (9+2*z+2^n) S < S at physical;omega)
  have pos : 0 < p:=by rw [pe];positivity
  have above : 9+2*z ≤ p:=by rw [pe];exact Nat.le_add_right _ _
  have source (i : Nat) (lo : p ≤ i) (hi : i < S) : ∃ b,V i=some b:=cell_source fr i (above.trans lo) hi
  have blank (i : Nat) (lo : F < i) (hi : i ≤ F+r+2) : V i=none:=fresh ⟨i,lt_of_le_of_lt hi shortFit⟩ lo
  let d:=2+r*(2*(F-p)+6)
  have hS : S < tapeLength R B:=by omega
  obtain ⟨counted,_firstCount⟩:=SuffixCap.counted k R B p S z n (2^n) F V pos physical
    (by positivity) geom source (cell_eof fr) (cell_reg fr) (cell_sep fr) (cell_assn fr)
    (cell_right fr) (cell_marks fr) (cell_gap fr) (cell_fence fr) blank shortFit
  have countFoot:=countHeads k R B p S z n (2^n) F V pos physical (by positivity) geom source
    (cell_eof fr) (cell_reg fr) (cell_sep fr) (cell_assn fr) (cell_right fr)
    (cell_marks fr) (cell_gap fr) (cell_fence fr) blank shortFit
  have countControl:=suffixBound k R B p S z n (2^n) F V pos physical (by positivity) geom source
    (cell_eof fr) (cell_reg fr) (cell_sep fr) (cell_assn fr) (cell_right fr)
    (cell_marks fr) (cell_gap fr) (cell_fence fr) blank shortFit
  have oldC (i : Nat) (hi : i ≤ F+1) : C i=V i:=by
    dsimp only [C,SuffixCap.Target.image];rw [if_neg (by omega)]
  have cEof : C S=none:=by rw [oldC _ (by omega)];exact cell_eof fr
  have cReg (i : Nat) (lo : S < i) (hi : i < L) : C i=some false:=by
    rw [oldC _ (by dsimp only [L] at hi;omega)];exact cell_reg fr i lo hi
  have cSep : C L=none:=by rw [oldC _ (by dsimp only [L];omega)];exact cell_sep fr
  have cAssn (i : Nat) (lo : L < i) (hi : i < L+n+1) : C i=some false:=by
    rw [oldC _ (by dsimp only [L] at hi;omega)]
    dsimp only [V,Stream.Target.image]
    rw [if_pos (by dsimp only [L] at lo hi;constructor <;> omega),CappedWorkspace.overflow_bits]
    simp [List.getElem!_eq_getElem?_getD,List.getElem?_replicate]
    split_ifs <;> rfl
  have cRight : C (L+n+1)=none:=by
    rw [oldC _ (by dsimp only [L];omega)]
    rw [show L+n+1=S+z+n+3 by dsimp only [L];omega]
    exact cell_right fr
  have cMarks (i : Nat) (lo : L+n+1 < i) (hi : i ≤ L+n+1+2^n) : C i=some true:=by
    rw [oldC _ (by dsimp only [L] at hi;omega)]
    exact cell_marks fr i (by change S+z+n+3 < i; dsimp only [L] at lo;omega) (by change i ≤ S+z+n+3+2^n;dsimp only [L] at hi;omega)
  have cGap (i : Nat) (lo : L+n+1+2^n < i) (hi : i < F) : C i=none:=by
    rw [oldC _ (by omega)]
    exact cell_gap fr i (by change S+z+n+3+2^n < i;dsimp only [L] at lo;omega) hi
  have cFence : C F=some false:=by rw [oldC _ (by omega)];exact cell_fence fr
  have cD0 : C (F+1)=none:=by rw [oldC _ (by omega)];exact fresh ⟨F+1,by omega⟩ (by change F < F+1;omega)
  have cBank0 (i : Nat) (lo : F+1 < i) (hi : i < F+r+2) : C i=some true:=by
    dsimp only [C,SuffixCap.Target.image];rw [if_pos (by omega)]
  have cFresh (i : Nat) (lo : F+r+2 ≤ i) (hi : i ≤ F+5*r+n+7) : C i=none:=by
    dsimp only [C,SuffixCap.Target.image];rw [if_neg (by omega)]
    exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ (by change F < i;omega)
  obtain ⟨v,_vPrice,setup,setupBefore,setupHeads⟩:=workspaceHeads k R B S L n (2^n) F r C
    (by dsimp only [L];omega) (by positivity) (by dsimp only [L];omega)
    cEof cReg cSep cAssn cRight cMarks cGap cFence cD0 cBank0 cFresh fit
  have replay (s : Nat) (config : Config (Cursor.machine k).stateCount R B) :
      (AllArityCursor.machine k).run s (SmallIngress.producer.seqEmbedRight (Cursor.machine k) config)=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ((Cursor.machine k).run s config):=by
    change (SmallIngress.producer.seq (Cursor.machine k)).run s _=_
    rw [UniformTM.seq_run_right]
  have countAt : (AllArityCursor.machine k).run (t+d) c=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ⟨Cursor.rReady k,⟨S,hS⟩,fun i=>C i.val⟩:=by
    rw [UniformTM.run_add,pre,replay,counted]
  have done : (AllArityCursor.machine k).run (t+d+v) c=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ⟨Cursor.q k 201,⟨F+1,by change F+1 < tapeLength R B;omega⟩,fun i=>X i.val⟩:=by
    rw [UniformTM.run_add,countAt,replay,setup]
  have pair : S ≤ R:=by dsimp only [S,R,pairLength];omega
  have nr : n ≤ R:=width.trans pair
  have rr : r ≤ R:=(Nat.sub_le _ _).trans pair
  have envelope : F+5*r+n+7 ≤ 12*(R+1)^2:=by
    dsimp only [F];nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
  refine ⟨t+d+v,by change F+1 < tapeLength R B;omega,done,?_,?_⟩
  · intro u hu
    by_cases early : u ≤ t
    · exact prefixHeads u early
    · by_cases middle : u ≤ t+d
      · rw [show u=t+(u-t) by omega,UniformTM.run_add,pre,replay]
        exact (countFoot (u-t) (by change u-t ≤ d;omega)).trans (by change F+r+2 ≤ 12*(R+1)^2;omega)
      · rw [show u=(t+d)+(u-(t+d)) by omega,UniformTM.run_add,countAt,replay]
        exact (setupHeads (u-(t+d)) (by omega)).trans envelope
  · intro u hu
    by_cases early : u ≤ t
    · exact (prefixBound u early).le.trans (by decide)
    · by_cases middle : u < t+d
      · rw [show u=t+(u-t) by omega,UniformTM.run_add,pre,replay]
        exact (Nat.add_lt_add_left (countControl (u-t) (by change u-t < d;omega)) 288).le.trans (by decide)
      · by_cases last : u < t+d+v
        · rw [show u=(t+d)+(u-(t+d)) by omega,UniformTM.run_add,countAt,replay]
          exact (Nat.add_lt_add_left (setupBefore (u-(t+d)) (by omega)) 288).le
        · have eq : u=t+d+v:=by omega
          rw [eq,done]
          change 288+201%Cursor.stateCount k ≤ 489
          rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)]
end IngressAllocation
