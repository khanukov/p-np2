import IngressAllocation.Bootstrap
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("bootstrap_price","bootstrapPrice"),("small_modes_trace","smallModes")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith "_private.IngressAllocation.Bootstrap." && n.toString.endsWith (".IngressAllocation."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique bootstrap theorem {key}: {found.map Prod.fst}"
private theorem small_producer_first {a m : Nat} (x : Bitstring a) (w : Bitstring m) (n : Fin 3)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (full : (if n.val=0 then 9 else 11) ≤ a+m)
    (h8 : FixedContentTagGate.physicalSymbol (Fin.append x w) 8=some (n.val==0))
    (h9 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 9=some true)
    (h10 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 10=some (n.val==2)) :
    let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R; let S:=a+m
    let T:=Body.extend (FixedRawLengthFence.fencedContentTape B x w)
    let L:=S+(if n.val=0 then 0 else 1)+2
    let c:=initialConfig SmallIngress.producer B (encodePair x w)
    ∃ (t : Nat) (hL : L < tapeLength R B),t ≤ 64*(R+1)^2 ∧
      SmallIngress.producer.run t c=
        ⟨SmallIngress.producer.accept,⟨L,hL⟩,fun i=>SmallIngress.seeded T S n.val i.val⟩ ∧
      (∀ u,u < t → (SmallIngress.producer.run u c).state ≠ SmallIngress.producer.accept) ∧
      ∀ u,u ≤ t → (SmallIngress.producer.run u c).head.val ≤ 12*(R+1)^2 := by
  intro R B S T L c
  have hS : 9 ≤ S := by dsimp only [S];split_ifs at full <;> omega
  have hSR : S ≤ R := by dsimp only [S,R,pairLength];omega
  have resource:=(FixedRawLengthFence.resource_bounds R).1
  have fit : S+6 < tapeLength R B := by simp only [tapeLength];dsimp only [B] at *;omega
  have hF : S+6 < FixedRawLengthFence.fencePos R := by dsimp only [FixedRawLengthFence.fencePos];omega
  have read (i : Nat) (hi : i < tapeLength R B) :
      T i=FixedRawLengthFence.fencedContentTape B x w ⟨i,hi⟩ := by
    have hj : i < tapeLength (pairLength a m) B:=hi
    simp only [T,Body.extend,dif_pos hj]
  have low (i : Nat) (hi : i < S) : T i=FixedContentTagGate.physicalSymbol (Fin.append x w) i := by
    rw [read i (by omega)]
    simp [FixedRawLengthFence.fencedContentTape,FixedContentTagGate.physicalSymbol,show i<a+m from hi]
  have source (i : Nat) (hi : i < S) : ∃ b,T i=some b := by
    rw [low i hi]
    exact ⟨Fin.append x w ⟨i,hi⟩,by simp [FixedContentTagGate.physicalSymbol,show i<a+m from hi]⟩
  have clear (i : Nat) (lo : S ≤ i) (hi : i ≤ S+6) : T i=none := by
    rw [read i (by omega)]
    simp [FixedRawLengthFence.fencedContentTape,show ¬i<a+m by omega,
      show i≠FixedRawLengthFence.fencePos (pairLength a m) by change i≠FixedRawLengthFence.fencePos R;omega]
  obtain ⟨_,_,_,_,_,_,bit6,bit7,iff,_⟩:=FixedContentTagGate.tag_contract (Fin.append x w)
  have h6 : T 6=some true := by rw [low 6 (by omega)];simpa only [bit6] using iff.mp tag ⟨6,by decide⟩
  have h7 : T 7=some false := by rw [low 7 (by omega)];simpa only [bit7] using iff.mp tag ⟨7,by decide⟩
  obtain ⟨u,hu,he,hh⟩:=smallModes R B S n T full fit h6 h7
    (by rw [low 8 (by omega)];exact h8)
    (by intro hn;rw [low 9 (by dsimp only [S];split_ifs at full <;> omega)];exact h9 hn)
    (by intro hn;rw [low 10 (by dsimp only [S];split_ifs at full <;> omega)];exact h10 hn) source clear
  let g:=FixedRawLengthFence.installClock R+FixedRawLengthFence.contentClock a m+3*S+7
  have gamma : SmallIngress.producer.run g c=
      ⟨SmallIngress.q 124,⟨8,by change 8 < tapeLength R B;omega⟩,fun i=>T i.val⟩ := by
    have actual:=SmallIngress.raw_gamma_start x w tag
    change SmallIngress.producer.run g c=_ at actual
    rw [actual]
    apply Config.ext_parts
    · rfl
    · rfl
    · funext i;exact (Body.extend_read _ i).symm
  have combined : SmallIngress.producer.run (g+u) c=
      ⟨SmallIngress.producer.accept,⟨L,by change L < tapeLength R B;dsimp only [L];split_ifs <;> omega⟩,
        fun i=>SmallIngress.seeded T S n.val i.val⟩ := by
    rw [UniformTM.run_add,gamma];exact he
  have clock : g+u ≤ 64*(R+1)^2 := by
    have pre:=(FixedRawLengthFence.content_prefix_resources a m).2
    change FixedRawLengthFence.installClock R+FixedRawLengthFence.contentClock a m ≤ B at pre
    have sq : R+1 ≤ (R+1)^2 := by
      simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (R+1) (show 1≤R+1 by omega)
    dsimp only [g,B,FixedRawLengthFence.allocation] at *
    nlinarith
  have heads : ∀ v,v ≤ g+u → (SmallIngress.producer.run v c).head.val ≤ 12*(R+1)^2 := by
    intro v hv
    by_cases early : v ≤ g
    · exact (SmallIngress.producer.run_initialConfig_head_le (encodePair x w)).trans
        (early.trans (bootstrapPrice a m))
    · rw [show v=g+(v-g) by omega,UniformTM.run_add,gamma]
      have localBound:=hh (v-g) (by omega)
      have sq : R+1 ≤ (R+1)^2 := by
        simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (R+1) (show 1≤R+1 by omega)
      exact localBound.trans (by omega)
  obtain ⟨t,ht,first,arrived⟩:=Body.first_accept_whole SmallIngress.producer c _ _ combined rfl
  exact ⟨t,by dsimp only [L];split_ifs <;> omega,ht.trans clock,arrived,first,
    fun v hv=>heads v (hv.trans ht)⟩
private theorem small_seq_first (suffix : UniformTM) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (n : Fin 3)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (full : (if n.val=0 then 9 else 11) ≤ a+m)
    (h8 : FixedContentTagGate.physicalSymbol (Fin.append x w) 8=some (n.val==0))
    (h9 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 9=some true)
    (h10 : n.val≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 10=some (n.val==2)) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R;let S:=a+m
    let T:=Body.extend (FixedRawLengthFence.fencedContentTape B x w)
    let L:=S+(if n.val=0 then 0 else 1)+2
    let M:=SmallIngress.producer.seq suffix
    let c:=initialConfig M B (encodePair x w)
    ∃ (t : Nat) (hL : L < tapeLength R B),t ≤ 64*(R+1)^2 ∧
      M.run t c=SmallIngress.producer.seqEmbedRight suffix
        ⟨suffix.start,⟨L,hL⟩,fun i=>SmallIngress.seeded T S n.val i.val⟩ ∧
      (∀ u,u ≤ t → (M.run u c).head.val ≤ 12*(R+1)^2) ∧
      ∀ u,u < t → ∀ s,(M.run u c).state ≠ SmallIngress.producer.seqRight suffix s := by
  intro R B S T L M c
  obtain ⟨t,hL,price,done,first,heads⟩:=small_producer_first x w n tag full h8 h9 h10
  let old:=initialConfig SmallIngress.producer B (encodePair x w)
  have tx (u : Nat) (hu : u ≤ t) : M.run u c=
      SmallIngress.producer.seqEmbedRouted suffix (SmallIngress.producer.run u old) :=
    SmallIngress.producer.seq_run_left suffix old first u hu
  refine ⟨t,hL,price,?_,?_,?_⟩
  · rw [tx t le_rfl,done]
    simp only [UniformTM.seqEmbedRouted,UniformTM.seqRoute,↓reduceIte]
    rfl
  · intro u hu;rw [tx u hu];exact heads u hu
  · intro u hu s
    rw [tx u (Nat.le_of_lt hu)]
    change SmallIngress.producer.seqRoute suffix _ ≠ _
    rw [UniformTM.seqRoute,if_neg (first u hu)]
    split_ifs with rejected
    · exfalso
      have rawReject : (SmallIngress.producer.run t old).state=SmallIngress.producer.reject :=
        (congrArg Config.state (SmallIngress.producer.run_reject_of_le old rejected (by omega))).trans rejected
      exact SmallIngress.producer.accept_ne_reject ((congrArg Config.state done).symm.trans rawReject)
    · exact SmallIngress.producer.seqLeft_ne_seqRight suffix _ s
end IngressAllocation
