import FullBodyClosure.State
namespace FullBodyClosure
open Pnp4.Frontier.ContractExpansion
/-- Proof-only decomposition of the ORIGINAL finite logical window. -/
private theorem window_succ {S : Nat} (source : Fin S → Bool) (c w : Nat) :
    SerializedBody.window source c (w+1)=padRead source c::SerializedBody.window source (c+1) w := by
  unfold SerializedBody.window
  rw [List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext i
  change padRead source (c+(i.val+1))=padRead source (c+1+i.val)
  congr 1
  omega
private theorem window_add {S : Nat} (source : Fin S → Bool) (a b c : Nat) :
    SerializedBody.window source c (a+b)=SerializedBody.window source c a++SerializedBody.window source (c+a) b := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add,Nat.add_zero,SerializedBody.window,List.ofFn_zero,List.nil_append];rfl
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega,window_succ,window_succ,ih]
    simp [Nat.add_comm,Nat.add_left_comm]
private theorem window_drop {S : Nat} (source : Fin S → Bool) (c w d : Nat) (bound : d ≤ w) :
    (SerializedBody.window source c w).drop d=SerializedBody.window source (c+d) (w-d) := by
  have split:=window_add source d (w-d) c
  rw [show d+(w-d)=w by omega] at split
  rw [split]
  have length : (SerializedBody.window source c d).length=d := by simp only [SerializedBody.window,List.length_ofFn]
  have dropping : (SerializedBody.window source c d++SerializedBody.window source (c+d) (w-d)).drop
      (SerializedBody.window source c d).length=SerializedBody.window source (c+d) (w-d) := by rw [List.drop_left]
  simpa only [length] using dropping
private theorem window_tag {S : Nat} (source : Fin S → Bool) (M u W : Nat) (enough : u+3 ≤ W) :
    SerializedBody.window source (M+u) (W-u)=
      padRead source (M+u)::padRead source (M+(u+1))::padRead source (M+(u+2))::
        SerializedBody.window source (M+(u+3)) (W-(u+3)) := by
  rw [show W-u=(W-(u+3)+2)+1 by omega,window_succ,window_succ,window_succ]
  simp only [Nat.add_assoc]
private theorem window_drop_cursor {S : Nat} (source : Fin S → Bool) (M W u u' : Nat)
    (lo : u ≤ u') (hi : u' ≤ W) :
    (SerializedBody.window source (M+u) (W-u)).drop (u'-u)=SerializedBody.window source (M+u') (W-u') := by
  rw [window_drop source (M+u) (W-u) (u'-u) (by omega)]
  congr 1 <;> omega
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Lean Elab Tactic in
private def checkedOwn (owner : Name) (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name:=(leaf.splitOn ".").foldl Name.str
    (Name.str (Name.num (Name.append `_private owner) 0) "FullBodyClosure")
  let some ci:=env.find? name | throwError "Missing exact semantic declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing semantic owner: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == owner do throwError "Wrong semantic owner: {name}"
  logInfo m!"window-input-specification|{name}|{ci.type}"
  closeMainGoal `checkedOwn (mkConst name (ci.levelParams.map Level.param))
private abbrev numeral : List Bool → Nat := by run_tac checkedOwn `FullBodyClosure.IndexSemantics "numeral"
private theorem numeral_lt : ∀ bits,numeral bits < 2^bits.length := by run_tac checkedOwn `FullBodyClosure.IndexSemantics "numeral_lt"
private theorem decodeFin_numeral : ∀ width bits (len : bits.length=width),
    decodeFin width bits=some ⟨numeral bits,by rw [←len];exact numeral_lt bits⟩ := by
  run_tac checkedOwn `FullBodyClosure.IndexSemantics "decodeFin_numeral"
private abbrev evalSpec : {n : Nat} → (Fin n → Bool) → Nat → Nat → Nat → List Bool → Option ((Nat × Bool) × List Bool) := by
  run_tac checkedOwn `FullBodyClosure.Semantics "evalSpec"
private theorem eval_input_payload {n width : Nat} (beta : Fin n → Bool) (fuel q : Nat) (payload tail : List Bool)
    (len : payload.length=width) :
    evalSpec beta width (fuel+1) (q+1) (false::false::false::(payload++tail))=
      if inside : numeral payload < n then some ((1,beta ⟨numeral payload,inside⟩),tail) else none := by
  change (if (payload++tail).length < width then none else
    (decodeFin width ((payload++tail).take width)).bind (fun i=>if h : i.val < n then
      some ((1,beta ⟨i.val,h⟩),(payload++tail).drop width) else none))=_
  have enough : ¬(payload++tail).length < width := by simp only [List.length_append];omega
  rw [if_neg enough,List.take_append_of_le_length (by omega),←len,List.take_length]
  rw [decodeFin_numeral payload.length payload rfl,List.drop_left]
  rfl
/-- Exact semantic input operand on the same original finite window, including
logical truncation, arbitrary little-endian index and every ignored tail. -/
private theorem eval_input_window {S n : Nat} (source : Fin S → Bool) (beta : Fin n → Bool)
    (width fuel q c w : Nat) :
    evalSpec beta width (fuel+1) (q+1) (false::false::false::SerializedBody.window source c w)=
      if width ≤ w then
        if inside : numeral (SerializedBody.window source c width) < n then
          some ((1,beta ⟨numeral (SerializedBody.window source c width),inside⟩),
            SerializedBody.window source (c+width) (w-width))
        else none
      else none := by
  by_cases enough : width ≤ w
  · rw [if_pos enough]
    have split:=window_add source width (w-width) c
    rw [show width+(w-width)=w by omega] at split
    rw [split]
    exact eval_input_payload beta fuel q _ _ (by simp only [SerializedBody.window,List.length_ofFn])
  · rw [if_neg enough]
    change (if (SerializedBody.window source c w).length < width then none else _)=none
    rw [if_pos (by simp only [SerializedBody.window,List.length_ofFn];omega)]
end FullBodyClosure
