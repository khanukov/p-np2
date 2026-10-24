import PhysicalCallerClosure.RoundGrid
import PhysicalCallerClosure.WriteReset
import PhysicalCallerClosure.PaymentIncrement
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
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","Grid","NativeSafe"]),
      (`PhysicalCallerClosure.RoundFrame,["Exterior"]),
      (`PhysicalCallerClosure.CallerMemory,["written_image"]),
      (`PhysicalCallerClosure.Compare,["flags"]),(`PhysicalCallerClosure.WriteBits,["written"]),
      (`PhysicalCallerClosure.RoundGrid,["image_facts"]),(`PhysicalCallerClosure.ResetImage,["extD"]),
      (`PhysicalCallerClosure.PaymentIncrement,["front_grid"]),
      (`PhysicalCallerClosure.WriteMeta,["FrontGrid","write_metadata"]),
      (`PhysicalCallerClosure.WriteReset,["writerEntry","writer_code"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac select `PhysicalCallerClosure.Engine "Node.mk" "constructor"
private theorem frame_write : ∀ {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta : Fin n → Bool} {old : Fin 5 → Bool} {th ah : Bool},
    Exterior T E S z n F r M p q beta old th ah → S+z+n+3 < F → ∀ bits : Fin 5 → Bool,
    Exterior T (written E (SerializedBody.delimiter F r n 12) bits 5) S z n F r M p q beta bits th ah := by
  run_tac select `PhysicalCallerClosure.RoundFrame "Exterior.write" "theorem"
private theorem write_frame (k : Nat) (a t : Fin 3) (T E : Nat → Option Bool)
    (S z n F r g W M p q nodes used rem quota : Nat) (beta : Fin n → Bool)
    (bits : Fin 5 → Bool) (th ah : Bool)
    (frame:Exterior T E S z n F r M p q beta bits th ah)
    (positive:0 < q) (arena:S+z+n+3+q < F)
    (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false)
    (left:T (S+z+2)=none) (right:T (S+z+n+3)=none) (fence:T F=some false)
    (endBlank:T (SerializedBody.delimiter F r n 12+6)=none) :
    Exterior T (written E (SerializedBody.delimiter F r n 12) (flags a t false) 5)
      S z n F r M p q beta (flags a t false) th ah ∧
    Path (callerMachine k) (NativeSafe k) (SerializedBody.delimiter F r n 12+6)
      (2*(SerializedBody.delimiter F r n 12-(S+z+n+3))+38)
      (node (writerEntry k a t) (S+z+n+3)
        (SerializedBody.image E F r n g W (S-min M S) nodes used rem quota))
      (node (resetEntry k a) (S+z+n+3)
        (SerializedBody.image (written E (SerializedBody.delimiter F r n 12) (flags a t false) 5)
          F r n g W (S-min M S) nodes used rem quota)) := by
  obtain ⟨grid,_ts,_registers,_tl,th,_beta,marks,gap,tf,_metadata,last⟩:=image_facts T E S z n F r g W M p q nodes used rem quota
    beta bits th ah frame arena eof reg left right fence endBlank
  obtain ⟨code⟩:=writer_code k a t
  have path:=write_metadata (front_grid grid) rfl rfl last (show extD F r n 13 ≤ SerializedBody.delimiter F r n 12+6 from le_rfl)
    positive arena th tf marks gap code
  have d12:extD F r n 12=SerializedBody.delimiter F r n 12:=rfl
  rw [d12,written_image] at path
  exact ⟨frame_write frame (by omega) _,path⟩
end PhysicalCallerClosure
