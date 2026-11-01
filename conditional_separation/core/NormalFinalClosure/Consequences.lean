import NormalFinalClosure.Semantics
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Lean Elab Command Tactic
private theorem accepted_rows_end (k B R S z n r : Nat) (source : Fin S → Bool)
    (T : Nat → Option Bool) (hH:S+z+2+n+1 < tapeLength R B)
    (c : Config (RawCallerClosure.machine k).stateCount R B) (t : Nat)
    (rows:RawCallerClosure.Target.RowsResult k B R S z n r (n^k+k) (Cursor.Target.W k n)
      (Cursor.Target.M k n z) (9+2*z) (2^n) source T hH c t)
    (header:contentHeader? source=some (n,2*z+1))
    (accepted:contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) source=true) :
    ((RawCallerClosure.machine k).run t c).state=RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k) := by
  obtain ⟨circuit,tail,decoded,cap,good⟩:=accepted_content_rows k n z source header accepted
  rcases rows with ⟨_safe,_first,result⟩
  dsimp only at result
  rw [decoded] at result
  rcases result with ⟨bad,_⟩|⟨_size,_used,_tail,_starts,outcome⟩
  · exact (bad cap).elim
  · rcases outcome with ⟨_paid,_all,finish⟩|⟨row,small,_prior,bad,_finish⟩|⟨bad,_all,_finish⟩
    · exact congrArg Config.state finish
    · exact (bad (good row (lt_of_lt_of_le small (Nat.min_le_left _ _)))).elim
    · omega
private def oldRawProof (owner : Name) (leaf : String) : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "RawCallerClosure") leaf
  let some (.thmInfo ci):=e.find? n | throwError "Missing exact old raw theorem"
  let some i:=e.getModuleIdxFor? n | throwError "Missing raw theorem owner"
  unless i.toNat < e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong raw theorem owner"
  logInfo m!"normal-reject-support|{n}|{ci.type}"
  closeMainGoal `oldRawProof (mkConst n (ci.levelParams.map Level.param))
private theorem oldReject : ∀ k,
    RawCallerClosure.old k (CertificateGuardClosure.machine k).reject=(RawCallerClosure.machine k).reject := by
  run_tac oldRawProof `RawCallerClosure.Rows "old_reject"
private theorem oldNotDone : ∀ (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount),
    RawCallerClosure.old k s≠RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k) := by
  run_tac oldRawProof `RawCallerClosure.Work "old_not_done"
/-- Internal semantic soundness for ALL early normal caller reject domains:
decoder none, size overflow, table mismatch and physical payment exhaustion.
The proof uses the existing actual RowsResult, never a new runtime oracle. -/
private theorem normal_reject_false (k B R a m z n r : Nat) (x : Bitstring a) (w : Bitstring m)
    (T : Nat → Option Bool) (hH:a+m+z+2+n+1 < tapeLength R B)
    (c : Config (RawCallerClosure.machine k).stateCount R B) (t : Nat)
    (length:m=a+1) (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (rows:RawCallerClosure.Target.RowsResult k B R (a+m) z n r (n^k+k) (Cursor.Target.W k n)
      (Cursor.Target.M k n z) (9+2*z) (2^n) (Fin.append x w) T hH c t)
    (rejected:((RawCallerClosure.machine k).run t c).state=(RawCallerClosure.machine k).reject) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  cases accept:PartAEndpoint.thresholdContentWitnessRelation k a m x w with
  | false=>rfl
  | true=>
    have sourceAccepted:contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=true :=
      (rho_append k a m x w length).symm.trans accept
    have done:=accepted_rows_end k B R (a+m) z n r (Fin.append x w) T hH c t rows header sourceAccepted
    have different:(RawCallerClosure.machine k).reject≠RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k) := by
      rw [←oldReject]
      exact oldNotDone k _
    exact (different (rejected.symm.trans done)).elim
end NormalFinalClosure
