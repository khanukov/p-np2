import IngressAllocation.CursorPrefix
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  let specs := [("IngressAllocation.CursorPrefix","IngressAllocation","cursor_prefix_heads","cursorHeads"),
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
private theorem eof_raw_heads (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (eof : min (9+2*z+2^pr.2.n) (a+m)=a+m) :
    let S:=a+m;let n:=pr.2.n;let L:=S+z+2
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared (FixedRawLengthFence.allocation (pairLength a m)) x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    ∃ (t : Nat) (hH : S+z+n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      (AllArityCursor.machine k).run t
        (initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i=>V i.val⟩ ∧
      Footprint (AllArityCursor.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w) t (12*(pairLength a m+1)^2) := by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let S:=a+m;let n:=pr.2.n;let L:=S+z+2
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  obtain ⟨otherZ,t,hH,otherGamma,_price,hp,pre,_first,_prefixBound,prefixHeads⟩:=cursorHeads k x w accepted parsed
  have same : otherZ=z:=Option.some.inj (otherGamma.symm.trans gamma)
  subst otherZ
  change S+z+n+3 < tapeLength R B at hH
  change (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
    ⟨Cursor.q k (if min (9+2*z+2^n) S=S then 57 else 58),⟨min (9+2*z+2^n) S,hp⟩,fun i=>V i.val⟩ at pre
  have endEq : min (9+2*z+2^n) S=S:=eof
  simp only [endEq,if_pos] at pre
  have width:=acceptedWidth x w accepted parsed
  have cap:=AcceptedBody.strict_capacity x w gamma width
  have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
  obtain ⟨fr,_short,_fresh⟩:=actualCells x w gamma cap rows
  have tail:=AllArityCounted.eof_body k (N:=R) (B:=B) V S z n hH
    (cell_eof fr) (cell_reg fr) (cell_sep fr) (cell_assn fr) (cell_right fr)
  have replay (s : Nat) (config : Config (Cursor.machine k).stateCount R B) :
      (AllArityCursor.machine k).run s (SmallIngress.producer.seqEmbedRight (Cursor.machine k) config)=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ((Cursor.machine k).run s config):=by
    change (SmallIngress.producer.seq (Cursor.machine k)).run s _=_
    rw [UniformTM.seq_run_right]
  have pair : S ≤ R:=by dsimp only [S,R,pairLength];omega
  have nr : n ≤ R:=width.trans pair
  have gammaBound:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  have zr : z ≤ R:=by change 8+z < S at gammaBound;omega
  have shortBound : S+(z+n+5) ≤ 12*(R+1)^2:=by
    nlinarith only [pair,nr,zr,Nat.zero_le R,Nat.zero_le (R^2)]
  refine ⟨t+(z+n+5),hH,?_,?_⟩
  · rw [UniformTM.run_add,pre,replay,tail]
  · intro u hu
    by_cases early : u ≤ t
    · exact prefixHeads u early
    · rw [show u=t+(u-t) by omega,UniformTM.run_add,pre,replay]
      have speed:=(Cursor.machine k).run_head_le (steps:=u-t)
        (⟨Cursor.q k 57,⟨S,by omega⟩,fun i=>V i.val⟩ : Config (Cursor.machine k).stateCount R B)
      exact speed.trans (by change S+(u-t) ≤ 12*(R+1)^2;omega)
end IngressAllocation
