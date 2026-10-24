import FullBodyClosure.Evaluate
namespace FullBodyClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Lean Elab Tactic in
private def checkedOwn (owner : Name) (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name:=(leaf.splitOn ".").foldl Name.str
    (Name.str (Name.num (Name.append `_private owner) 0) "FullBodyClosure")
  let some ci:=env.find? name | throwError "Missing exact root declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing root owner: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == owner do throwError "Wrong root owner: {name}"
  logInfo m!"root-adapter|{owner}|{name}|{ci.type}"
  closeMainGoal `checkedOwn (mkConst name (ci.levelParams.map Level.param))
private abbrev Rep : (Nat → Option Bool) → (Nat → Nat) → (Nat → Option Bool) →
    (S L H Q F r M W n g u v : Nat) → (Fin S → Bool) → (Fin n → Bool) → List (Fin 7) → Prop := by
  run_tac checkedOwn `FullBodyClosure.State "Rep"
private abbrev memory : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Nat → Nat → Option Bool := by
  run_tac checkedOwn `FullBodyClosure.State "memory"
private abbrev returnState : Fin 3 → Bool → Fin 7500 := by run_tac checkedOwn `FullBodyClosure.State "returnState"
private abbrev evalSpec : {n : Nat} → (Fin n → Bool) → Nat → Nat → Nat → List Bool → Option ((Nat × Bool) × List Bool) := by
  run_tac checkedOwn `FullBodyClosure.Semantics "evalSpec"
private def NodeResult (base T : Nat → Option Bool) (S L H Q F r M W n g u v : Nat)
    (source : Fin S → Bool) (beta : Fin n → Bool) (K : List (Fin 7)) (N B P fuel : Nat)
    (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B) : Prop :=
  let D:=SerializedBody.delimiter F r n
  let bits:=SerializedBody.window source (M+u) (W-u)
  let C:=16384*(r+1)*(n+1)*(P+1)
  let initial : Config 7500 N B:=⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),
    ⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩
  ∃ t,match evalSpec beta (bitLength n) fuel (g-v) bits with
  | none=>t ≤ C*(g-v+1) ∧ Native t initial
      ⟨SerializedBody.machine.reject,⟨H,hH⟩,
        fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩
  | some ((size,b),tail)=>t ≤ C*size ∧ ∃ U u',u ≤ u' ∧ u' ≤ W ∧ tail=bits.drop (u'-u) ∧
      Rep base D U S L H Q F r M W n g u' (v+size) source beta K ∧ Native t initial
        ⟨returnState (SerializedBody.sourceMode source (M+u')) b,⟨D 0,h0⟩,
          fun i=>memory U D S M W u' i.val⟩
private theorem initial_rep : ∀ (T : Nat → Option Bool) (S L H Q F r M W n g : Nat)
    (source : Fin S → Bool) (beta : Fin n → Bool),S < L → H=L+n+1 → 0 < Q → H+Q < F → g ≤ r → W ≤ r → bitLength n ≤ r →
    (∀ i,M ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) → T S=none →
    (∀ i,S < i → i < L → T i=some false) → T L=none →
    (∀ j : Fin n,T (H-1-j.val)=some (beta j)) → T H=none →
    (∀ i,H < i → i ≤ H+Q → T i=some true) → (∀ i,H+Q < i → i < F → T i=none) → T F=some false →
    Rep T (SerializedBody.delimiter F r n) (SerializedBody.image T F r n g W (S-min M S) 0 0 W g)
      S L H Q F r M W n g 0 0 source beta [] := by run_tac checkedOwn `FullBodyClosure.State "initial_rep"
private theorem node_run : ∀ q : Nat,
    ∀ (base T : Nat → Option Bool) (S L H Q F r M W n g u v : Nat)
      (source : Fin S → Bool) (beta : Fin n → Bool) (K : List (Fin 7)),
    Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K → g-v=q →
    ∀ (N B P fuel : Nat),W-u ≤ fuel → SerializedBody.delimiter F r n 12 ≤ P → P < tapeLength N B →
    ∀ (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B),
    NodeResult base T S L H Q F r M W n g u v source beta K N B P fuel h0 hH := by
  run_tac checkedOwn `FullBodyClosure.Evaluate "node_run"
private theorem seen : ∀ {base D T S L H Q F r M W n g u v source beta K},
    Rep base D T S L H Q F r M W n g u v source beta K → v ≤ g := by run_tac checkedOwn `FullBodyClosure.State "Rep.seen"
private theorem native_finish : ∀ {base T S L H Q F r M W n g u v source beta},
    Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta [] →
    ∀ b N B P,SerializedBody.delimiter F r n 12 ≤ P → P < tapeLength N B →
    ∀ (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B),
    ∃ t,t ≤ 512*(P+1) ∧ Native t
      (⟨returnState (SerializedBody.sourceMode source (M+u)) b,⟨SerializedBody.delimiter F r n 0,h0⟩,
        fun i=>memory T (SerializedBody.delimiter F r n) S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBody.done b,⟨H,hH⟩,
        fun i=>SerializedBody.image base F r n g W (S-min M S) v u (W-u) 0 i.val⟩ : Config 7500 N B) := by
  run_tac checkedOwn `FullBodyClosure.State "Rep.finish"
private theorem image_outside : ∀ T F r n g W a v u rem quota i,
    i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i →
    SerializedBody.image T F r n g W a v u rem quota i=T i := by
  run_tac checkedOwn `FullBodyClosure.Initial "image_outside"
private theorem prepared_memory : ∀ T S M F r n g W,S < SerializedBody.delimiter F r n 0 →
    memory (SerializedBody.image T F r n g W (S-min M S) 0 0 W g)
      (SerializedBody.delimiter F r n) S M W 0=SerializedBody.prepared T S M F r n g W := by
  run_tac checkedOwn `FullBodyClosure.Initial "prepared_memory"
private theorem evalSpec_full : ∀ {n : Nat} (beta : Fin n → Bool) bits g,
    evalSpec beta (bitLength n) bits.length g bits=
      (decodeCircuitFull n (bitLength n) bits).bind (fun p=>
        if p.1.size ≤ g then some ((p.1.size,Pnp3.Models.Circuit.eval p.1 beta),p.2) else none) := by
  run_tac checkedOwn `FullBodyClosure.Semantics "evalSpec_full"
private theorem extent_bound : ∀ R S z n r Q,r ≤ S → S ≤ R → 0 < Q →
    S+z+n+3+Q < FixedRawLengthFence.fencePos R →
    SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+1 ≤ 22*(R+1) ∧ n+1 ≤ 3*(R+1) := by
  run_tac checkedOwn `FullBodyClosure.Frame "extent_bound"
private theorem root_clock (R P n r g t : Nat) (hp : P+1 ≤ 22*(R+1)) (hn : n+1 ≤ 3*(R+1))
    (hr : r ≤ R) (hg : g ≤ r) (price : t ≤ 32768*(P+1)*(n+1)*(r+1)*(g+1)) :
    t ≤ 1073741824*(R+1)^6 := by
  have a:=Nat.mul_le_mul_left 32768 hp
  have b:=Nat.mul_le_mul a hn
  have c:=Nat.mul_le_mul b (show r+1 ≤ R+1 by omega)
  have d:=Nat.mul_le_mul c (show g+1 ≤ R+1 by omega)
  have p4 : 32768*(22*(R+1))*(3*(R+1))*(R+1)*(R+1)=2162688*(R+1)^4 := by ring
  rw [p4] at d
  have powers : (R+1)^4 ≤ (R+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith
private theorem small_ne (q r : Fin 7500) (large : 4 ≤ q.val) (small : r.val < 4) : q≠r := by
  intro eq;subst q;omega
private theorem native_terminal {N B t : Nat} {initial final : Config 7500 N B}
    (execution : Native t initial final) (last : final.state≠SerializedBody.machine.accept) :
    (∀ u,u ≤ t → (SerializedBody.machine.run u initial).state≠SerializedBody.machine.accept) ∧
    (∀ u,u < t → (SerializedBody.machine.run u initial).state≠SerializedBody.machine.reject ∧
      (SerializedBody.machine.run u initial).state≠SerializedBody.done false ∧
      (SerializedBody.machine.run u initial).state≠SerializedBody.done true) := by
  constructor
  · intro u hu
    by_cases early : u < t
    · exact small_ne _ _ (execution.2 u early) (by decide)
    · have eq : u=t := by omega
      rw [eq,execution.1];exact last
  · intro u hu
    exact ⟨small_ne _ _ (execution.2 u hu) (by decide),
      small_ne _ _ (execution.2 u hu) (by decide),small_ne _ _ (execution.2 u hu) (by decide)⟩
private theorem root_price (P n r g entry node cleanup size : Nat)
    (entryPrice : entry ≤ P+1) (nodePrice : node ≤ 16384*(r+1)*(n+1)*(P+1)*(size+1))
    (cleanupPrice : cleanup ≤ 512*(P+1)) (sizeBound : size ≤ g) :
    entry+node+cleanup ≤ 32768*(P+1)*(n+1)*(r+1)*(g+1) := by
  let C:=16384*(r+1)*(n+1)*(P+1)
  have factor : P+1 ≤ (r+1)*(n+1)*(P+1) := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  have overhead : entry+cleanup ≤ C := by dsimp only [C];nlinarith
  have nodeBound : node ≤ C*(g+1) := le_trans nodePrice (Nat.mul_le_mul_left C (by omega))
  have result : entry+node+cleanup ≤ C*(g+2) := by
    calc
      entry+node+cleanup ≤ C+node := by omega
      _ ≤ C+C*(g+1) := Nat.add_le_add_left nodeBound C
      _ = C*(g+2) := by ring
  have stretch : g+2 ≤ 2*(g+1) := by omega
  have bound:=le_trans result (Nat.mul_le_mul_left C stretch)
  have coefficient : C*(2*(g+1))=32768*(P+1)*(n+1)*(r+1)*(g+1) := by dsimp only [C];ring
  rw [coefficient] at bound
  exact bound
/-- The unchanged original prepared BODY on the immutable physical table. -/
theorem full_body : SerializedBody.Target.Body := by
  unfold SerializedBody.Target.Body
  intro R S z n r g W M Q source beta T
  by_cases zeroQuota : g=0
  · subst g
    exact SerializedBodyCompletion.zero_quota_body R S z n r W M Q source beta T
  by_cases zeroWindow : W=0
  · subst W
    exact SerializedBodyCompletion.zero_window_body R S z n r g M Q source beta T
  intro hr hs hg hw he ha
  dsimp only
  intro positive arena src eof reg left betaCells right marks gap fence fit hH
  let F:=FixedRawLengthFence.fencePos R
  let L:=S+z+2
  let H:=L+n+1
  let D:=SerializedBody.delimiter F r n
  let P:=D 12
  let B:=FixedRawLengthFence.allocation R
  let V:=SerializedBody.image T F r n g W (S-min M S) 0 0 W g
  have rep0:=initial_rep T S L H Q F r M W n g source beta (by dsimp only [L];omega) rfl
    positive arena hg hw he src eof reg left betaCells right marks gap fence
  have sourceBefore : S < D 0 := by change S < F+1;change H+Q < F at arena;dsimp only [H,L] at arena;omega
  have rootRoom : F+1 ≤ P := by change F+1 ≤ F+13*r+2*n+16;omega
  have h0 : D 0 < tapeLength R B := lt_of_le_of_lt rootRoom fit
  have header (i : Nat) (lo : S ≤ i) (hi : i < D 0) : SerializedBody.prepared T S M F r n g W i=T i := by
    change (if i=M ∧ i < S then none else SerializedBody.image T F r n g W (S-min M S) 0 0 W g i)=T i
    rw [if_neg (by omega : ¬(i=M ∧ i < S)),image_outside T F r n g W (S-min M S) 0 0 W g i (Or.inl hi)]
  have sourceH : S < H := by dsimp only [H,L];omega
  have beforeH : H < D 0 := by change H+Q < F at arena;change H < F+1;omega
  obtain ⟨entryRun,entryPrefix⟩:=SerializedBodyCompletion.entry_need (SerializedBody.sourceMode source M)
    (SerializedBody.prepared T S M F r n g W) H Q F R B P positive arena rootRoom fit hH h0
    (by rw [header H (by omega) beforeH];exact right)
    (by rw [header F (by change H+Q < F at arena;omega) (by change F < F+1;omega)];exact fence)
    (by intro i lo hi;rw [header i (by omega) (by change H+Q < F at arena;change i < F+1;omega)];exact marks i lo hi)
    (by intro i lo hi;rw [header i (by omega) (by change i < F+1;omega)];exact gap i lo hi)
  let initial : Config 7500 R B:=⟨SerializedBody.entry (SerializedBody.sourceMode source M),⟨H,hH⟩,
    fun i=>SerializedBody.prepared T S M F r n g W i.val⟩
  have entrance : Native (F+2-H) initial
      ⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source M),⟨D 0,h0⟩,
        fun i=>SerializedBody.prepared T S M F r n g W i.val⟩ :=
    ⟨entryRun,fun u hu=>entryPrefix u (by omega)⟩
  have entryPrice : F+2-H ≤ P+1 := by omega
  have call:=node_run g T V S L H Q F r M W n g 0 0 source beta [] rep0 (by omega) R B P W
    (by omega) le_rfl fit h0 hH
  unfold NodeResult at call
  dsimp only at call
  simp only [Nat.add_zero,Nat.zero_add,Nat.sub_zero] at call
  dsimp only [V] at call
  rw [prepared_memory T S M F r n g W sourceBefore] at call
  let bits:=SerializedBody.window source M W
  let semantics:=(decodeCircuitFull n (bitLength n) bits).bind (fun p=>
    if p.1.size ≤ g then some ((p.1.size,Pnp3.Models.Circuit.eval p.1 beta),p.2) else none)
  have length : bits.length=W := by simp only [bits,SerializedBody.window,List.length_ofFn]
  have exactSpec : evalSpec beta (bitLength n) W g bits=semantics := by
    simpa only [length] using evalSpec_full beta bits g
  rw [exactSpec] at call
  have extents:=extent_bound R S z n r Q hr hs positive (by
    change H+Q < F at arena
    dsimp only [H,L,F] at arena
    omega)
  change ∃ t,t ≤ 1073741824*(R+1)^6 ∧
    (∀ u,u ≤ t → (SerializedBody.machine.run u initial).state≠SerializedBody.machine.accept) ∧
    (∀ u,u < t → (SerializedBody.machine.run u initial).state≠SerializedBody.machine.reject ∧
      (SerializedBody.machine.run u initial).state≠SerializedBody.done false ∧
      (SerializedBody.machine.run u initial).state≠SerializedBody.done true) ∧
    match (generalizing := false) semantics with
    | none=>SerializedBody.machine.run t initial=
        ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>SerializedBody.image T F r n g W (S-min M S) 0 0 0 0 i.val⟩
    | some ((size,b),tail)=>∃ consumed,consumed ≤ W ∧ tail=bits.drop consumed ∧
        SerializedBody.machine.run t initial=
          ⟨SerializedBody.done b,⟨H,hH⟩,fun i=>SerializedBody.image T F r n g W (S-min M S) size consumed (W-consumed) 0 i.val⟩
  cases result : semantics with
  | none =>
    rw [result] at call
    obtain ⟨t,price,run⟩:=call
    have execution:=native_trans entrance run
    have terminal:=native_terminal execution (by change SerializedBody.machine.reject≠SerializedBody.machine.accept;decide)
    refine ⟨F+2-H+t,?_,terminal.1,terminal.2,execution.1⟩
    apply root_clock R P n r g _ extents.1 extents.2 (by omega) hg
    have bound:=root_price P n r g (F+2-H) t 0 g entryPrice price (by omega) le_rfl
    simpa only [Nat.add_zero] using bound
  | some pair =>
    rcases pair with ⟨⟨size,b⟩,tail⟩
    rw [result] at call
    obtain ⟨t,price,U,u,_lo,hw',tailLaw,frame,run⟩:=call
    obtain ⟨cleanup,cleanupPrice,last⟩:=native_finish frame b R B P le_rfl fit h0 hH
    have execution:=native_trans (native_trans entrance run) last
    have terminal:=native_terminal execution (by change SerializedBody.done b≠SerializedBody.machine.accept;cases b <;> decide)
    refine ⟨F+2-H+t+cleanup,?_,terminal.1,terminal.2,u,hw',tailLaw,execution.1⟩
    apply root_clock R P n r g _ extents.1 extents.2 (by omega) hg
    apply root_price P n r g (F+2-H) t cleanup size entryPrice _ cleanupPrice (seen frame)
    exact le_trans price (Nat.mul_le_mul_left _ (by omega : size ≤ size+1))
end FullBodyClosure
