import PhysicalCallerClosure.Bootstrap
import PhysicalCallerClosure.CallerInvalid
import PhysicalCallerClosure.CallerValid
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact paid-row support {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .ctorInfo _=>"constructor" | .inductInfo _=>"inductive" | _=>"other"
  unless actual==kind do throwError "Wrong paid-row support kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row support owner"
  logInfo m!"paid-row-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.AllRows,["Layout"]),
      (`PhysicalCallerClosure.Bootstrap,["bootstrap"]),(`PhysicalCallerClosure.CallerInvalid,["invalid_caller"]),
      (`PhysicalCallerClosure.CallerValid,["valid_caller"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev layoutMk : {B R S z n r g W M A Q : Nat} → {source : Fin S → Bool} → {T : Nat → Option Bool} →
    (1 ≤ R) →
    (r ≤ S) →
    (S ≤ R) →
    (g ≤ r) →
    (0 < W) →
    (W ≤ r) →
    (bitLength n ≤ r) →
    (S-min M S ≤ r) →
    (2 ≤ A) →
    (A ≤ S) →
    (A+2^n+1 ≤ M) →
    (0 < Q) →
    (S+z+n+3+Q < FixedRawLengthFence.fencePos R) →
    (T (A-2)=none) →
    (T (A-1)=some true) →
    (∀ i,A ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩)) →
    (T S=none) →
    (∀ i,S < i → i < S+z+2 → T i=some false) →
    (T (S+z+2)=none) →
    (T (S+z+n+3)=none) →
    (∀ j:Fin n,T (S+z+n+2-j.val)=some false) →
    (∀ i,S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true) →
    (∀ i,S+z+n+3+Q < i → i < FixedRawLengthFence.fencePos R → T i=none) →
    (T (FixedRawLengthFence.fencePos R)=some false) →
    (∀ i,SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12 < i →
      i ≤ SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 → T i=none) →
    (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 < tapeLength R B) →
    (S+z+n+3 < tapeLength R B) →
    Layout B R S z n r g W M A Q source T := by
  run_tac select `PhysicalCallerClosure.AllRows "Layout.mk" "constructor"
theorem caller_rows (k : Nat) : CallerRows k := by
  unfold CallerRows
  intro B R S z n r g W M A Q source T rpos rS sR gates wp windowRoom widthRoom anchorRoom aPos aS margin
  dsimp only
  intro positive arena gamma marker src eof reg left right beta marks gap fence metadata fit hH
  have eqH:S+z+2+n+1=S+z+n+3:=by omega
  simp only [eqH] at arena right marks gap hH ⊢
  have zeroAssignment:∀ j:Fin n,T (S+z+n+2-j.val)=some false:=by
    intro j
    have pos:S+z+2+n+1-1-j.val=S+z+n+2-j.val:=by omega
    simpa only [pos] using beta j
  let layout:Layout B R S z n r g W M A Q source T:=layoutMk rpos rS sR gates wp windowRoom widthRoom anchorRoom
    aPos aS margin positive arena gamma marker src eof reg left right zeroAssignment marks gap fence metadata fit hH
  have power:0 < 2^n:=Nat.pow_pos (by decide)
  obtain ⟨initial,E,initialBound,frame,initialEnd⟩:=bootstrap k B R S z n r g W M A Q source T (by omega)
    aPos aS (by omega) positive arena gamma marker src eof reg left right zeroAssignment marks gap fence
    (metadata _ (by omega) le_rfl) fit hH
  generalize parsed:decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)=decoded
  cases decoded with
  | none =>
    have failed:(do
        let (circuit,tail) ← decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)
        if circuit.size ≤ g then some ((circuit.size,Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n 0)),tail) else none)=none:=by
      rw [parsed];rfl
    obtain ⟨t,bound,safe,first,eq⟩:=invalid_caller k B R S z n r g W M A Q source T E layout frame failed hH initial initialBound initialEnd
    exact ⟨t,bound,safe,first,eq⟩
  | some pair =>
    rcases pair with ⟨circuit,tail⟩
    by_cases cap:circuit.size ≤ g
    · obtain ⟨t,bound,safe,first,usedBound,tailEq,paid,ending⟩:=valid_caller k B R S z n r g W M A Q source T E layout rpos arena positive frame
        circuit tail parsed cap hH initial initialBound initialEnd
      exact ⟨t,bound,safe,first,Or.inr ⟨cap,usedBound,tailEq,paid,ending⟩⟩
    · have failed:(do
          let (circuit,tail) ← decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)
          if circuit.size ≤ g then some ((circuit.size,Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n 0)),tail) else none)=none:=by
        rw [parsed]
        change (if circuit.size ≤ g then some ((circuit.size,Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n 0)),tail) else none)=none
        rw [if_neg cap]
      obtain ⟨t,bound,safe,first,eq⟩:=invalid_caller k B R S z n r g W M A Q source T E layout frame failed hH initial initialBound initialEnd
      exact ⟨t,bound,safe,first,Or.inl ⟨cap,eq⟩⟩
#print axioms caller_rows
end PhysicalCallerClosure
