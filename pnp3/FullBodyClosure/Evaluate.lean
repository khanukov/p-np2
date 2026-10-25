import FullBodyClosure.State
import FullBodyClosure.Window
namespace FullBodyClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
open Lean Elab Tactic in
private def checkedState (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name:=(leaf.splitOn ".").foldl Name.str
    (Name.str (Name.num `_private.FullBodyClosure.State 0) "FullBodyClosure")
  let some ci:=env.find? name | throwError "Missing exact declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing owner: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == `FullBodyClosure.State do throwError "Wrong owner: {name}"
  logInfo m!"driver-state-adapter|{name}|{ci.type}"
  closeMainGoal `checkedState (mkConst name (ci.levelParams.map Level.param))
private abbrev Rep : (Nat → Option Bool) → (Nat → Nat) → (Nat → Option Bool) →
    (S L H Q F r M W n g u v : Nat) → (Fin S → Bool) → (Fin n → Bool) → List (Fin 7) → Prop := by
  run_tac checkedState "Rep"
private theorem initial_rep : ∀ (T : Nat → Option Bool) (S L H Q F r M W n g : Nat)
    (source : Fin S → Bool) (beta : Fin n → Bool),S < L → H=L+n+1 → 0 < Q → H+Q < F → g ≤ r → W ≤ r → bitLength n ≤ r →
    (∀ i,M ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) → T S=none →
    (∀ i,S < i → i < L → T i=some false) → T L=none →
    (∀ j : Fin n,T (H-1-j.val)=some (beta j)) → T H=none →
    (∀ i,H < i → i ≤ H+Q → T i=some true) → (∀ i,H+Q < i → i < F → T i=none) → T F=some false →
    Rep T (SerializedBody.delimiter F r n) (SerializedBody.image T F r n g W (S-min M S) 0 0 W g)
      S L H Q F r M W n g 0 0 source beta [] := by run_tac checkedState "initial_rep"
private abbrev memory : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Nat → Nat → Option Bool := by
  run_tac checkedState "memory"
private abbrev returnState : Fin 3 → Bool → Fin 7500 := by run_tac checkedState "returnState"
open Lean Elab Tactic in
private def checkedSemantics (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name:=(leaf.splitOn ".").foldl Name.str
    (Name.str (Name.num `_private.FullBodyClosure.Semantics 0) "FullBodyClosure")
  let some ci:=env.find? name | throwError "Missing exact semantic declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing semantic owner: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == `FullBodyClosure.Semantics do throwError "Wrong semantic owner: {name}"
  logInfo m!"node-specification|{name}|{ci.type}"
  closeMainGoal `checkedSemantics (mkConst name (ci.levelParams.map Level.param))
private abbrev evalSpec : {n : Nat} → (Fin n → Bool) → Nat → Nat → Nat → List Bool → Option ((Nat × Bool) × List Bool) := by
  run_tac checkedSemantics "evalSpec"
/-- Full internal CALL contract for the shared native recurrence. A successful
call stops at Return BEFORE the caller's saved record is popped. A failing call
performs literal reject cleanup exactly once, including any dirty operands.
This is a proof proposition, not a machine field or executable oracle. -/
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
private theorem seen : ∀ {base D T S L H Q F r M W n g u v source beta K},
    Rep base D T S L H Q F r M W n g u v source beta K → v ≤ g := by run_tac checkedState "Rep.seen"
private theorem cursor_bound : ∀ {base D T S L H Q F r M W n g u v source beta K},
    Rep base D T S L H Q F r M W n g u v source beta K → u ≤ W := by run_tac checkedState "Rep.cursor"
private theorem emptyQuota : ∀ {base T S L H Q F r M W n g u v source beta K},
    Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K → g=v →
    ∀ N B P,SerializedBody.delimiter F r n 12 ≤ P → P < tapeLength N B →
    ∀ (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B),
    ∃ t,t ≤ 576*(P+1) ∧ Native t
      (⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),⟨SerializedBody.delimiter F r n 0,h0⟩,
        fun i=>memory T (SerializedBody.delimiter F r n) S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBody.machine.reject,⟨H,hH⟩,
        fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩ : Config 7500 N B) := by
  run_tac checkedState "Rep.emptyQuota"
private theorem shortTag : ∀ {base T S L H Q F r M W n g u v source beta K},
    Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K → v < g → W < u+3 →
    ∀ N B P,SerializedBody.delimiter F r n 12 ≤ P → P < tapeLength N B →
    ∀ (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B),
    ∃ t,t ≤ 896*(P+1) ∧ Native t
      (⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),⟨SerializedBody.delimiter F r n 0,h0⟩,
        fun i=>memory T (SerializedBody.delimiter F r n) S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBody.machine.reject,⟨H,hH⟩,
        fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩ : Config 7500 N B) := by
  run_tac checkedState "Rep.shortTag"
private theorem evalSpec_zero {n : Nat} (beta : Fin n → Bool) (width fuel : Nat) (bits : List Bool) :
    evalSpec beta width fuel 0 bits=none := by cases fuel <;> rfl
private theorem evalSpec_short {n : Nat} (beta : Fin n → Bool) (width fuel q : Nat) (bits : List Bool)
    (short : bits.length < 3) : evalSpec beta width fuel q bits=none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases q with
    | zero => rfl
    | succ q =>
      cases bits with
      | nil => rfl
      | cons b0 bits =>
        cases bits with
        | nil => cases b0 <;> rfl
        | cons b1 bits =>
          cases bits with
          | nil => cases b0 <;> cases b1 <;> rfl
          | cons b2 bits => simp only [List.length_cons] at short;omega
private theorem small_cost (r n P t : Nat) (price : t ≤ 896*(P+1)) :
    t ≤ 16384*(r+1)*(n+1)*(P+1) := by
  have a : 1 ≤ (r+1)*(n+1) := Nat.mul_pos (by omega) (by omega)
  have h:=Nat.mul_le_mul_right (16384*(P+1)) a
  have eq : (r+1)*(n+1)*(16384*(P+1))=16384*(r+1)*(n+1)*(P+1) := by ring
  rw [eq] at h
  omega
private abbrev tagDestination : Fin 3 → Bool → Bool → Bool → Fin 7500 := by run_tac checkedState "tagDestination"
private abbrev pushState : Fin 3 → Fin 7 → Fin 7500 := by run_tac checkedState "pushState"
private abbrev constState : Fin 3 → Fin 7500 := by run_tac checkedState "constState"
private abbrev inputState : Fin 3 → Fin 7500 := by run_tac checkedState "inputState"
private abbrev numeral : List Bool → Nat := by run_tac checkedState "numeral"
private abbrev recordWrite : (Nat → Option Bool) → Nat → Bool → Bool → Bool → Nat → Option Bool := by
  run_tac checkedState "recordWrite"
private abbrev recordBit : Fin 7 → Nat → Bool := by run_tac checkedState "recordBit"
private abbrev returnNext : Fin 7 → Bool → Sum (Fin 7) Bool := by run_tac checkedState "returnNext"
private theorem depth_bound : ∀ {base D T S L H Q F r M W n g u v source beta K},
    Rep base D T S L H Q F r M W n g u v source beta K → K.length ≤ v := by run_tac checkedState "Rep.depth"
open Lean Elab Tactic in
private def checkedWindow (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name:=(leaf.splitOn ".").foldl Name.str
    (Name.str (Name.num `_private.FullBodyClosure.Window 0) "FullBodyClosure")
  let some ci:=env.find? name | throwError "Missing exact window declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing window owner: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == `FullBodyClosure.Window do throwError "Wrong window owner: {name}"
  logInfo m!"node-window-specification|{name}|{ci.type}"
  closeMainGoal `checkedWindow (mkConst name (ci.levelParams.map Level.param))
private theorem eval_input_window : ∀ {S n : Nat} (source : Fin S → Bool) (beta : Fin n → Bool) width fuel q c w,
    evalSpec beta width (fuel+1) (q+1) (false::false::false::SerializedBody.window source c w)=
      if width ≤ w then
        if inside : numeral (SerializedBody.window source c width) < n then
          some ((1,beta ⟨numeral (SerializedBody.window source c width),inside⟩),SerializedBody.window source (c+width) (w-width))
        else none
      else none := by run_tac checkedWindow "eval_input_window"
private theorem window_succ : ∀ {S : Nat} (source : Fin S → Bool) c w,
    SerializedBody.window source c (w+1)=padRead source c::SerializedBody.window source (c+1) w := by
  run_tac checkedWindow "window_succ"
private theorem window_tag : ∀ {S : Nat} (source : Fin S → Bool) M u W,u+3 ≤ W →
    SerializedBody.window source (M+u) (W-u)=
      padRead source (M+u)::padRead source (M+(u+1))::padRead source (M+(u+2))::
        SerializedBody.window source (M+(u+3)) (W-(u+3)) := by run_tac checkedWindow "window_tag"
private theorem window_drop_cursor : ∀ {S : Nat} (source : Fin S → Bool) M W u u',u ≤ u' → u' ≤ W →
    (SerializedBody.window source (M+u) (W-u)).drop (u'-u)=SerializedBody.window source (M+u') (W-u') := by
  run_tac checkedWindow "window_drop_cursor"
private theorem native_needStep : ∀ {base T S L H Q F r M W n g u v source beta K}
    (_rep : Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K)
    (N B P : Nat) (_room : SerializedBody.delimiter F r n 12 ≤ P) (_fit : P < tapeLength N B)
    (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B),
    let D:=SerializedBody.delimiter F r n
    let initial : Config 7500 N B:=⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),
      ⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩
    ∃ t,t ≤ 896*(P+1) ∧
      if g=v then Native t initial
        ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩
      else if u+3 ≤ W then ∃ U,
        Native t initial
          ⟨tagDestination (SerializedBody.sourceMode source (M+(u+3)))
            (padRead source (M+u)) (padRead source (M+(u+1))) (padRead source (M+(u+2))),⟨D 0,h0⟩,
            fun i=>memory U D S M W (u+3) i.val⟩ ∧
        Rep base D U S L H Q F r M W n g (u+3) (v+1) source beta K
      else Native t initial
        ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩ := by
  run_tac checkedState "Rep.needStep"
private theorem native_push : ∀ {base D T S L H Q F r M W n g u v source beta K}
    (_rep : Rep base D T S L H Q F r M W n g u v source beta K)
    (c : Fin 7) (_depth : K.length+1 ≤ v) (_len10 : D 11=D 10+3*r+4)
    (N B P : Nat) (_room : D 12 ≤ P) (_fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B),
    let U:=recordWrite T (D 10+3*K.length+1) (recordBit c 0) (recordBit c 1) (recordBit c 2)
    ∃ t,t ≤ 128*(P+1) ∧ Native t
      (⟨pushState (SerializedBody.sourceMode source (M+u)) c,⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
        fun i=>memory U D S M W u i.val⟩ : Config 7500 N B) ∧
      Rep base D U S L H Q F r M W n g u v source beta (K++[c]) := by
  run_tac checkedState "Rep.push"
private theorem native_returnStep : ∀ {base D T S L H Q F r M W n g u v source beta K}
    (c : Fin 7) (_rep : Rep base D T S L H Q F r M W n g u v source beta (K++[c]))
    (b : Bool) (_len10 : D 11=D 10+3*r+4)
    (N B P : Nat) (_room : D 12 ≤ P) (_fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B),
    ∃ t,t ≤ 256*(P+1) ∧ ∃ U,
      match returnNext c b with
      | .inl saved=>Native t
          (⟨returnState (SerializedBody.sourceMode source (M+u)) b,⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
          (⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,
            fun i=>memory U D S M W u i.val⟩ : Config 7500 N B) ∧
          Rep base D U S L H Q F r M W n g u v source beta (K++[saved])
      | .inr value=>Native t
          (⟨returnState (SerializedBody.sourceMode source (M+u)) b,⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩ : Config 7500 N B)
          (⟨returnState (SerializedBody.sourceMode source (M+u)) value,⟨D 0,h0⟩,
            fun i=>memory U D S M W u i.val⟩ : Config 7500 N B) ∧
          Rep base D U S L H Q F r M W n g u v source beta K := by
  run_tac checkedState "Rep.returnStep"
private theorem native_constant : ∀ {base T S L H Q F r M W n g u v source beta K}
    (_rep : Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K)
    (N B P : Nat) (_room : SerializedBody.delimiter F r n 12 ≤ P) (_fit : P < tapeLength N B)
    (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B),
    let D:=SerializedBody.delimiter F r n
    let initial : Config 7500 N B:=⟨constState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩
    ∃ t,t ≤ 640*(P+1) ∧
      if u < W then Native t initial
        ⟨returnState (SerializedBody.sourceMode source (M+(u+1))) (padRead source (M+u)),⟨D 0,h0⟩,
          fun i=>memory T D S M W (u+1) i.val⟩ ∧
        Rep base D T S L H Q F r M W n g (u+1) v source beta K
      else Native t initial
        ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩ := by
  run_tac checkedState "Rep.constant"
private theorem native_inputStep : ∀ {base T S L H Q F r M W n g u v source beta K}
    (_rep : Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K)
    (N B P : Nat) (_room : SerializedBody.delimiter F r n 12 ≤ P) (_fit : P < tapeLength N B)
    (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B),
    let D:=SerializedBody.delimiter F r n
    let ell:=bitLength n
    let payload:=SerializedBody.window source (M+u) ell
    let initial : Config 7500 N B:=⟨inputState (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,fun i=>memory T D S M W u i.val⟩
    let rejected : Config 7500 N B:=⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩
    ∃ t,t ≤ 9216*(r+1)*(n+1)*(P+1) ∧
      if n=0 then Native t initial rejected
      else if ell ≤ W-u then
        if inside : numeral payload < n then Native t initial
          ⟨returnState (SerializedBody.sourceMode source (M+(u+ell))) (beta ⟨numeral payload,inside⟩),⟨D 0,h0⟩,
            fun i=>memory T D S M W (u+ell) i.val⟩ ∧
          Rep base D T S L H Q F r M W n g (u+ell) v source beta K
        else Native t initial rejected
      else Native t initial rejected := by
  run_tac checkedState "Rep.inputStep"
private theorem overhead_cost (r n P t : Nat) (price : t ≤ 2048*(P+1)) :
    t ≤ 16384*(r+1)*(n+1)*(P+1) := by
  have a : 1 ≤ (r+1)*(n+1) := Nat.mul_pos (by omega) (by omega)
  have h:=Nat.mul_le_mul_right (16384*(P+1)) a
  have eq : (r+1)*(n+1)*(16384*(P+1))=16384*(r+1)*(n+1)*(P+1) := by ring
  rw [eq] at h
  omega
private theorem input_parent_cost (r n P a b : Nat) (pa : a ≤ 896*(P+1))
    (pb : b ≤ 9216*(r+1)*(n+1)*(P+1)) : a+b ≤ 16384*(r+1)*(n+1)*(P+1) := by
  have factor : 1 ≤ (r+1)*(n+1) := Nat.mul_pos (by omega) (by omega)
  have h:=Nat.mul_le_mul_right (896*(P+1)) factor
  have eq : (r+1)*(n+1)*(896*(P+1))=896*(r+1)*(n+1)*(P+1) := by ring
  rw [eq] at h
  nlinarith
private abbrev AbortFrame : (Nat → Option Bool) → (Nat → Nat) → (Nat → Option Bool) →
    (S L H Q F r M W n g u : Nat) → (Fin S → Bool) → (Fin n → Bool) → Prop := by
  run_tac checkedState "AbortFrame"
private theorem abortFrame : ∀ {base D T S L H Q F r M W n g u v source beta K},
    Rep base D T S L H Q F r M W n g u v source beta K → AbortFrame base D T S L H Q F r M W n g u source beta := by
  run_tac checkedState "Rep.abortFrame"
private theorem native_abort : ∀ {base T S L H Q F r M W n g u source beta},
    AbortFrame base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u source beta →
    ∀ N B P,SerializedBody.delimiter F r n 12 ≤ P → P < tapeLength N B →
    ∀ (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B),
    ∃ t,t ≤ 512*(P+1) ∧ Native t
      (⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source (M+u)),⟨SerializedBody.delimiter F r n 0,h0⟩,
        fun i=>memory T (SerializedBody.delimiter F r n) S M W u i.val⟩ : Config 7500 N B)
      (⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>SerializedBody.image base F r n g W (S-min M S) 0 0 0 0 i.val⟩ : Config 7500 N B) := by
  run_tac checkedState "AbortFrame.cleanup"
private theorem invalid_bits (a b c : Bool)
    (hn : ¬(a=false ∧ b=true ∧ c=false)) (hc : ¬(a=false ∧ b=false ∧ c=true))
    (hi : ¬(a=false ∧ b=false ∧ c=false))
    (hb : ¬((a=false ∧ b=true ∧ c=true) ∨ (a=true ∧ b=false ∧ c=false))) :
    a=true ∧ (b=true ∨ c=true) := by
  cases a <;> cases b <;> cases c <;> simp_all
private theorem tag_abort (m : Fin 3) (a b c : Bool) (bad : a=true ∧ (b=true ∨ c=true)) :
    tagDestination m a b c=SerializedBodyRefinement.getAbort m := by
  rcases bad with ⟨rfl,other⟩
  cases b <;> cases c <;> simp_all [tagDestination]
  all_goals rfl
private theorem evalSpec_invalid {n : Nat} (beta : Fin n → Bool) (width fuel q : Nat)
    (a b c : Bool) (tail : List Bool) (bad : a=true ∧ (b=true ∨ c=true)) :
    evalSpec beta width fuel q (a::b::c::tail)=none := by
  rcases bad with ⟨rfl,other⟩
  cases fuel <;> cases q <;> cases b <;> cases c <;> simp_all [evalSpec]
  all_goals rfl
private def combine (isOr a b : Bool) : Bool := if isOr then a || b else a && b
private def leftCode (isOr : Bool) : Fin 7 := if isOr then 4 else 1
private def rightCode (isOr a : Bool) : Fin 7 := if isOr then (if a then 6 else 5) else (if a then 3 else 2)
private theorem left_route (isOr b : Bool) : returnNext (leftCode isOr) b=Sum.inl (rightCode isOr b) := by
  cases isOr <;> cases b <;> rfl
private theorem right_route (isOr a b : Bool) : returnNext (rightCode isOr a) b=Sum.inr (combine isOr a b) := by
  cases isOr <;> cases a <;> cases b <;> rfl
private theorem evalSpec_binary {n : Nat} (beta : Fin n → Bool) (width fuel q : Nat) (isOr : Bool) (rest : List Bool) :
    evalSpec beta width (fuel+1) (q+1) (if isOr then true::false::false::rest else false::true::true::rest)=
      (evalSpec beta width fuel q rest).bind (fun p=>
        (evalSpec beta width fuel (q-p.1.1) p.2).bind (fun p'=>
          some ((p.1.1+p'.1.1+1,combine isOr p.1.2 p'.1.2),p'.2))) := by cases isOr <;> rfl
/-- The two real child calls of either binary constructor, parameterized only
by the well-founded induction hypothesis. No such hypothesis is runtime data. -/
private theorem binary_case {base T U S L H Q F r M W n g u v source beta K}
    (rep : Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K)
    (opened : Rep base (SerializedBody.delimiter F r n) U S L H Q F r M W n g (u+3) (v+1) source beta K)
    (paid : v < g) (isOr : Bool) (N B P fuel : Nat)
    (room : SerializedBody.delimiter F r n 12 ≤ P) (fit : P < tapeLength N B)
    (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B)
    (enough : W-(u+3) ≤ fuel)
    (shape : SerializedBody.window source (M+u) (W-u)=if isOr then
      true::false::false::SerializedBody.window source (M+(u+3)) (W-(u+3)) else
      false::true::true::SerializedBody.window source (M+(u+3)) (W-(u+3)))
    (openedTime : Nat) (openedPrice : openedTime ≤ 896*(P+1))
    (openedRun : Native openedTime
      (⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),⟨SerializedBody.delimiter F r n 0,h0⟩,
        fun i=>memory T (SerializedBody.delimiter F r n) S M W u i.val⟩ : Config 7500 N B)
      (⟨pushState (SerializedBody.sourceMode source (M+(u+3))) (leftCode isOr),⟨SerializedBody.delimiter F r n 0,h0⟩,
        fun i=>memory U (SerializedBody.delimiter F r n) S M W (u+3) i.val⟩ : Config 7500 N B))
    (IH : ∀ T' u' v' K',v < v' →
      Rep base (SerializedBody.delimiter F r n) T' S L H Q F r M W n g u' v' source beta K' → W-u' ≤ fuel →
      NodeResult base T' S L H Q F r M W n g u' v' source beta K' N B P fuel h0 hH) :
    NodeResult base T S L H Q F r M W n g u v source beta K N B P (fuel+1) h0 hH := by
  let C:=16384*(r+1)*(n+1)*(P+1)
  have parentQuota : g-v=(g-(v+1))+1 := by omega
  have len10 : SerializedBody.delimiter F r n 11=SerializedBody.delimiter F r n 10+3*r+4 := by
    change F+12*r+2*n+15=F+9*r+2*n+11+3*r+4;omega
  obtain ⟨pushTime,pushPrice,pushRun,pushedRep⟩:=native_push opened (leftCode isOr)
    (by have h:=depth_bound rep;omega) len10 N B P room fit h0
  have nativePrefix:=native_trans openedRun pushRun
  have first:=IH _ (u+3) (v+1) (K++[leftCode isOr]) (by omega) pushedRep enough
  unfold NodeResult at first
  dsimp only at first
  cases leftSpec : evalSpec beta (bitLength n) fuel (g-(v+1))
      (SerializedBody.window source (M+(u+3)) (W-(u+3))) with
  | none =>
    rw [leftSpec] at first
    obtain ⟨t,price,run⟩:=first
    have parentSem : evalSpec beta (bitLength n) (fuel+1) (g-v)
        (SerializedBody.window source (M+u) (W-u))=none := by
      rw [shape,parentQuota,evalSpec_binary,leftSpec];rfl
    unfold NodeResult
    dsimp only
    rw [parentSem]
    refine ⟨openedTime+pushTime+t,?_,native_trans nativePrefix run⟩
    have over:=overhead_cost r n P (openedTime+pushTime) (by omega)
    change openedTime+pushTime+t ≤ C*(g-v+1)
    calc
      openedTime+pushTime+t ≤ C+t := by omega
      _ ≤ C+C*(g-(v+1)+1) := Nat.add_le_add_left price C
      _ = C*(g-v+1) := by rw [parentQuota];ring
  | some pair =>
    rcases pair with ⟨⟨sL,bL⟩,tailL⟩
    rw [leftSpec] at first
    obtain ⟨tL,pL,V,uL,huL,hwL,tailLawL,leftRep,leftRun⟩:=first
    change tL ≤ C*sL at pL
    have leftTail : tailL=SerializedBody.window source (M+uL) (W-uL) := by
      rw [window_drop_cursor source M W (u+3) uL huL hwL] at tailLawL
      exact tailLawL
    obtain ⟨retL,retLp,V',leftReturned⟩:=native_returnStep (leftCode isOr) leftRep bL len10 N B P room fit h0
    rw [left_route] at leftReturned
    obtain ⟨leftReturnRun,rightReady⟩:=leftReturned
    have throughLeft:=native_trans (native_trans nativePrefix leftRun) leftReturnRun
    have second:=IH _ uL (v+1+sL) (K++[rightCode isOr bL]) (by omega) rightReady (by omega)
    unfold NodeResult at second
    dsimp only at second
    have quotaSub : g-(v+1)-sL=g-(v+1+sL) := by omega
    cases rightSpec : evalSpec beta (bitLength n) fuel (g-(v+1+sL))
        (SerializedBody.window source (M+uL) (W-uL)) with
    | none =>
      rw [rightSpec] at second
      obtain ⟨tR,pR,rightRun⟩:=second
      change tR ≤ C*(g-(v+1+sL)+1) at pR
      have parentSem : evalSpec beta (bitLength n) (fuel+1) (g-v)
          (SerializedBody.window source (M+u) (W-u))=none := by
        rw [shape,parentQuota,evalSpec_binary,leftSpec,Option.bind_some]
        dsimp only
        rw [leftTail,quotaSub,rightSpec];rfl
      unfold NodeResult
      dsimp only
      rw [parentSem]
      refine ⟨openedTime+pushTime+tL+retL+tR,?_,native_trans throughLeft rightRun⟩
      have over:=overhead_cost r n P (openedTime+pushTime+retL) (by omega)
      have budget : g-v+1=1+sL+(g-(v+1+sL)+1) := by have h:=seen rightReady;omega
      change openedTime+pushTime+tL+retL+tR ≤ C*(g-v+1)
      calc
        openedTime+pushTime+tL+retL+tR ≤ C+C*sL+C*(g-(v+1+sL)+1) := by omega
        _ = C*(g-v+1) := by rw [budget];ring
    | some pair =>
      rcases pair with ⟨⟨sR,bR⟩,tailR⟩
      rw [rightSpec] at second
      obtain ⟨tR,pR,Y,uR,huR,hwR,tailLawR,rightRep,rightRun⟩:=second
      change tR ≤ C*sR at pR
      obtain ⟨retR,retRp,Y',rightReturned⟩:=native_returnStep (rightCode isOr bL) rightRep bR len10 N B P room fit h0
      rw [right_route] at rightReturned
      obtain ⟨rightReturnRun,finalRep⟩:=rightReturned
      have parentSem : evalSpec beta (bitLength n) (fuel+1) (g-v)
          (SerializedBody.window source (M+u) (W-u))=some ((sL+sR+1,combine isOr bL bR),tailR) := by
        rw [shape,parentQuota,evalSpec_binary,leftSpec,Option.bind_some]
        dsimp only
        rw [leftTail,quotaSub,rightSpec];rfl
      have parentTail : tailR=(SerializedBody.window source (M+u) (W-u)).drop (uR-u) := by
        rw [window_drop_cursor source M W u uR (by omega) hwR,
          ←window_drop_cursor source M W uL uR huR hwR]
        exact tailLawR
      have nodeSum : v+1+sL+sR=v+(sL+sR+1) := by omega
      rw [nodeSum] at finalRep
      unfold NodeResult
      dsimp only
      rw [parentSem]
      refine ⟨openedTime+pushTime+tL+retL+tR+retR,?_,Y',uR,by omega,hwR,parentTail,finalRep,
        native_trans (native_trans throughLeft rightRun) rightReturnRun⟩
      have over:=overhead_cost r n P (openedTime+pushTime+retL+retR) (by omega)
      change openedTime+pushTime+tL+retL+tR+retR ≤ C*(sL+sR+1)
      calc
        openedTime+pushTime+tL+retL+tR+retR ≤ C+C*sL+C*sR := by omega
        _ = C*(sL+sR+1) := by ring
-- Ordinary intended RED for the COMPLETE recurrence. No semantic/run hypothesis
-- is supplied to this theorem; q is the physically stored remaining node quota.
private theorem node_run (q : Nat) :
    ∀ (base T : Nat → Option Bool) (S L H Q F r M W n g u v : Nat)
      (source : Fin S → Bool) (beta : Fin n → Bool) (K : List (Fin 7)),
    Rep base (SerializedBody.delimiter F r n) T S L H Q F r M W n g u v source beta K → g-v=q →
    ∀ (N B P fuel : Nat),W-u ≤ fuel → SerializedBody.delimiter F r n 12 ≤ P → P < tapeLength N B →
    ∀ (h0 : SerializedBody.delimiter F r n 0 < tapeLength N B) (hH : H < tapeLength N B),
    NodeResult base T S L H Q F r M W n g u v source beta K N B P fuel h0 hH := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro base T S L H Q F r M W n g u v source beta K rep quota N B P fuel enough room fit h0 hH
    by_cases exhausted : g=v
    · obtain ⟨t,price,run⟩:=emptyQuota rep exhausted N B P room fit h0 hH
      unfold NodeResult
      dsimp only
      rw [show g-v=0 by omega,evalSpec_zero,Nat.zero_add,Nat.mul_one]
      exact ⟨t,small_cost r n P t (by omega),run⟩
    have paid : v < g := by have h:=seen rep;omega
    by_cases short : W < u+3
    · obtain ⟨t,price,run⟩:=shortTag rep paid short N B P room fit h0 hH
      have spec:=evalSpec_short beta (bitLength n) fuel (g-v)
        (SerializedBody.window source (M+u) (W-u))
        (by simp only [SerializedBody.window,List.length_ofFn];have h:=cursor_bound rep;omega)
      unfold NodeResult
      dsimp only
      rw [spec]
      refine ⟨t,?_,run⟩
      have c:=small_cost r n P t price
      exact le_trans c (Nat.le_mul_of_pos_right _ (by omega))
    have complete : u+3 ≤ W := by omega
    obtain ⟨openedTime,openedPrice,openedResult⟩:=native_needStep rep N B P room fit h0 hH
    simp only [if_neg exhausted,if_pos complete] at openedResult
    obtain ⟨U,openedRun,openedRep⟩:=openedResult
    have sourceShape:=window_tag source M u W complete
    have parentQuota : g-v=(g-(v+1))+1 := by omega
    by_cases isNot : padRead source (M+u)=false ∧ padRead source (M+(u+1))=true ∧ padRead source (M+(u+2))=false
    · rcases isNot with ⟨b0,b1,b2⟩
      simp only [b0,b1,b2] at openedRun sourceShape
      have len10 : SerializedBody.delimiter F r n 11=SerializedBody.delimiter F r n 10+3*r+4 := by
        change F+12*r+2*n+15=F+9*r+2*n+11+3*r+4;omega
      obtain ⟨pushTime,pushPrice,pushRun,pushedRep⟩:=native_push openedRep 0
        (by have h:=depth_bound rep;omega) len10 N B P room fit h0
      have nativePrefix:=native_trans openedRun pushRun
      cases fuel with
      | zero => omega
      | succ childFuel =>
        have child:=ih (g-(v+1)) (by omega) base _ S L H Q F r M W n g (u+3) (v+1)
          source beta (K++[0]) pushedRep rfl N B P childFuel (by omega) room fit h0 hH
        unfold NodeResult at child
        dsimp only at child
        let C:=16384*(r+1)*(n+1)*(P+1)
        cases decoded : evalSpec beta (bitLength n) childFuel (g-(v+1))
            (SerializedBody.window source (M+(u+3)) (W-(u+3))) with
        | none =>
          rw [decoded] at child
          obtain ⟨childTime,childPrice,childRun⟩:=child
          have parentSem : evalSpec beta (bitLength n) (childFuel+1) (g-v)
              (SerializedBody.window source (M+u) (W-u))=none := by
            rw [sourceShape,parentQuota]
            change (evalSpec beta (bitLength n) childFuel (g-(v+1))
              (SerializedBody.window source (M+(u+3)) (W-(u+3)))).bind (fun p=>some ((p.1.1+1,!p.1.2),p.2))=none
            rw [decoded];rfl
          unfold NodeResult
          dsimp only
          rw [parentSem]
          refine ⟨openedTime+pushTime+childTime,?_,native_trans nativePrefix childRun⟩
          have over:=overhead_cost r n P (openedTime+pushTime) (by omega)
          change openedTime+pushTime+childTime ≤ C*(g-v+1)
          calc
            openedTime+pushTime+childTime ≤ C+childTime := by omega
            _ ≤ C+C*(g-(v+1)+1) := Nat.add_le_add_left childPrice C
            _ = C*(g-v+1) := by rw [parentQuota];ring
        | some pair =>
          rcases pair with ⟨⟨size,b⟩,tail⟩
          rw [decoded] at child
          obtain ⟨childTime,childPrice,V,uc,huStart,huW,tailLaw,childRep,childRun⟩:=child
          obtain ⟨returnTime,returnPrice,V',returned⟩:=native_returnStep 0 childRep b len10 N B P room fit h0
          simp only [returnNext] at returned
          obtain ⟨returnRun,returnRep⟩:=returned
          have parentSem : evalSpec beta (bitLength n) (childFuel+1) (g-v)
              (SerializedBody.window source (M+u) (W-u))=some ((size+1,!b),tail) := by
            rw [sourceShape,parentQuota]
            change (evalSpec beta (bitLength n) childFuel (g-(v+1))
              (SerializedBody.window source (M+(u+3)) (W-(u+3)))).bind (fun p=>some ((p.1.1+1,!p.1.2),p.2))=some ((size+1,!b),tail)
            rw [decoded];rfl
          have parentTail : tail=(SerializedBody.window source (M+u) (W-u)).drop (uc-u) := by
            rw [window_drop_cursor source M W u uc (by omega) huW,
              ←window_drop_cursor source M W (u+3) uc huStart huW]
            exact tailLaw
          have nodeSum : v+1+size=v+(size+1) := by omega
          rw [nodeSum] at returnRep
          unfold NodeResult
          dsimp only
          rw [parentSem]
          refine ⟨openedTime+pushTime+childTime+returnTime,?_,V',uc,by omega,huW,parentTail,returnRep,
            native_trans (native_trans nativePrefix childRun) returnRun⟩
          have over:=overhead_cost r n P (openedTime+pushTime+returnTime) (by omega)
          change openedTime+pushTime+childTime+returnTime ≤ C*(size+1)
          calc
            openedTime+pushTime+childTime+returnTime ≤ C+childTime := by omega
            _ ≤ C+C*size := Nat.add_le_add_left childPrice C
            _ = C*(size+1) := by ring
    by_cases isConst : padRead source (M+u)=false ∧ padRead source (M+(u+1))=false ∧ padRead source (M+(u+2))=true
    · rcases isConst with ⟨b0,b1,b2⟩
      simp only [b0,b1,b2] at openedRun sourceShape
      obtain ⟨constantTime,constantPrice,constantResult⟩:=native_constant openedRep N B P room fit h0 hH
      cases fuel with
      | zero => omega
      | succ childFuel =>
        by_cases payloadPresent : u+3 < W
        · simp only [if_pos payloadPresent] at constantResult
          obtain ⟨constantRun,constantRep⟩:=constantResult
          have suffix : SerializedBody.window source (M+(u+3)) (W-(u+3))=
              padRead source (M+(u+3))::SerializedBody.window source (M+(u+3+1)) (W-(u+3+1)) := by
            rw [show W-(u+3)=(W-(u+3+1))+1 by omega,window_succ]
            simp only [Nat.add_assoc]
          have parentSem : evalSpec beta (bitLength n) (childFuel+1) (g-v)
              (SerializedBody.window source (M+u) (W-u))=
                some ((1,padRead source (M+(u+3))),SerializedBody.window source (M+(u+3+1)) (W-(u+3+1))) := by
            rw [sourceShape,parentQuota,suffix];rfl
          unfold NodeResult
          dsimp only
          rw [parentSem]
          refine ⟨openedTime+constantTime,?_,U,u+3+1,by omega,by omega,?_,constantRep,native_trans openedRun constantRun⟩
          · simpa only [Nat.mul_one] using overhead_cost r n P (openedTime+constantTime) (by omega)
          · exact (window_drop_cursor source M W u (u+3+1) (by omega) (by omega)).symm
        · simp only [if_neg payloadPresent] at constantResult
          have emptyChild : SerializedBody.window source (M+(u+3)) (W-(u+3))=[] := by
            rw [show W-(u+3)=0 by omega];rfl
          have parentSem : evalSpec beta (bitLength n) (childFuel+1) (g-v)
              (SerializedBody.window source (M+u) (W-u))=none := by
            rw [sourceShape,parentQuota,emptyChild];rfl
          unfold NodeResult
          dsimp only
          rw [parentSem]
          refine ⟨openedTime+constantTime,?_,native_trans openedRun constantResult⟩
          have over:=overhead_cost r n P (openedTime+constantTime) (by omega)
          exact le_trans over (Nat.le_mul_of_pos_right _ (by omega))
    by_cases isInput : padRead source (M+u)=false ∧ padRead source (M+(u+1))=false ∧ padRead source (M+(u+2))=false
    · rcases isInput with ⟨b0,b1,b2⟩
      simp only [b0,b1,b2] at openedRun sourceShape
      obtain ⟨inputTime,inputPrice,inputResult⟩:=native_inputStep openedRep N B P room fit h0 hH
      cases fuel with
      | zero => omega
      | succ childFuel =>
        by_cases zero : n=0
        · simp only [if_pos zero] at inputResult
          have noIndex : ¬numeral (SerializedBody.window source (M+(u+3)) (bitLength n)) < n := by omega
          have parentSem : evalSpec beta (bitLength n) (childFuel+1) (g-v)
              (SerializedBody.window source (M+u) (W-u))=none := by
            rw [sourceShape,parentQuota,eval_input_window]
            simp only [dif_neg noIndex,ite_self]
          unfold NodeResult
          dsimp only
          rw [parentSem]
          refine ⟨openedTime+inputTime,?_,native_trans openedRun inputResult⟩
          have over:=input_parent_cost r n P openedTime inputTime openedPrice inputPrice
          exact le_trans over (Nat.le_mul_of_pos_right _ (by omega))
        by_cases available : bitLength n ≤ W-(u+3)
        · simp only [if_neg zero,if_pos available] at inputResult
          by_cases inside : numeral (SerializedBody.window source (M+(u+3)) (bitLength n)) < n
          · simp only [dif_pos inside] at inputResult
            obtain ⟨inputRun,inputRep⟩:=inputResult
            have parentSem : evalSpec beta (bitLength n) (childFuel+1) (g-v)
                (SerializedBody.window source (M+u) (W-u))=
                  some ((1,beta ⟨numeral (SerializedBody.window source (M+(u+3)) (bitLength n)),inside⟩),
                    SerializedBody.window source (M+(u+3+bitLength n)) (W-(u+3+bitLength n))) := by
              rw [sourceShape,parentQuota,eval_input_window,if_pos available,dif_pos inside]
              simp only [Nat.add_assoc,Nat.sub_sub]
            unfold NodeResult
            dsimp only
            rw [parentSem]
            refine ⟨openedTime+inputTime,?_,U,u+3+bitLength n,by omega,by omega,?_,inputRep,
              native_trans openedRun inputRun⟩
            · simpa only [Nat.mul_one] using input_parent_cost r n P openedTime inputTime openedPrice inputPrice
            · exact (window_drop_cursor source M W u (u+3+bitLength n) (by omega) (by omega)).symm
          · simp only [dif_neg inside] at inputResult
            have parentSem : evalSpec beta (bitLength n) (childFuel+1) (g-v)
                (SerializedBody.window source (M+u) (W-u))=none := by
              rw [sourceShape,parentQuota,eval_input_window,if_pos available,dif_neg inside]
            unfold NodeResult
            dsimp only
            rw [parentSem]
            refine ⟨openedTime+inputTime,?_,native_trans openedRun inputResult⟩
            have over:=input_parent_cost r n P openedTime inputTime openedPrice inputPrice
            exact le_trans over (Nat.le_mul_of_pos_right _ (by omega))
        · simp only [if_neg zero,if_neg available] at inputResult
          have parentSem : evalSpec beta (bitLength n) (childFuel+1) (g-v)
              (SerializedBody.window source (M+u) (W-u))=none := by
            rw [sourceShape,parentQuota,eval_input_window,if_neg available]
          unfold NodeResult
          dsimp only
          rw [parentSem]
          refine ⟨openedTime+inputTime,?_,native_trans openedRun inputResult⟩
          have over:=input_parent_cost r n P openedTime inputTime openedPrice inputPrice
          exact le_trans over (Nat.le_mul_of_pos_right _ (by omega))
    by_cases binary : (padRead source (M+u)=false ∧ padRead source (M+(u+1))=true ∧ padRead source (M+(u+2))=true) ∨
      (padRead source (M+u)=true ∧ padRead source (M+(u+1))=false ∧ padRead source (M+(u+2))=false)
    · cases fuel with
      | zero => omega
      | succ childFuel =>
        have childIH : ∀ T' u' v' K',v < v' →
            Rep base (SerializedBody.delimiter F r n) T' S L H Q F r M W n g u' v' source beta K' → W-u' ≤ childFuel →
            NodeResult base T' S L H Q F r M W n g u' v' source beta K' N B P childFuel h0 hH := by
          intro T' u' v' K' grown frame hFuel
          exact ih (g-v') (by have h:=seen frame;omega) base T' S L H Q F r M W n g u' v' source beta K' frame rfl
            N B P childFuel hFuel room fit h0 hH
        rcases binary with bits | bits
        · rcases bits with ⟨b0,b1,b2⟩
          simp only [b0,b1,b2] at openedRun sourceShape
          exact binary_case rep openedRep paid false N B P childFuel room fit h0 hH (by omega)
            sourceShape openedTime openedPrice openedRun childIH
        · rcases bits with ⟨b0,b1,b2⟩
          simp only [b0,b1,b2] at openedRun sourceShape
          exact binary_case rep openedRep paid true N B P childFuel room fit h0 hH (by omega)
            sourceShape openedTime openedPrice openedRun childIH
    · have bad:=invalid_bits _ _ _ isNot isConst isInput binary
      have parentSem : evalSpec beta (bitLength n) fuel (g-v) (SerializedBody.window source (M+u) (W-u))=none := by
        rw [sourceShape]
        exact evalSpec_invalid beta _ _ _ _ _ _ _ bad
      rw [tag_abort _ _ _ _ bad] at openedRun
      obtain ⟨abortTime,abortPrice,abortRun⟩:=native_abort (abortFrame openedRep) N B P room fit h0 hH
      unfold NodeResult
      dsimp only
      rw [parentSem]
      refine ⟨openedTime+abortTime,?_,native_trans openedRun abortRun⟩
      have over:=overhead_cost r n P (openedTime+abortTime) (by omega)
      exact le_trans over (Nat.le_mul_of_pos_right _ (by omega))
end FullBodyClosure
