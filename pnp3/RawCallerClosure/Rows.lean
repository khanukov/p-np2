import RawCallerClosure.SeqMap
import PhysicalCallerClosure.Rows
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let e←getEnv
  for leaf in ["seqMap","seqMap_left","seqMap_right","seqMap_route","seqMap_rows","seqMap_val"] do
    let n:=Name.str (Name.str (Name.num `_private.RawCallerClosure.SeqMap 0) "RawCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing exact seq support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == `RawCallerClosure.SeqMap do throwError "Wrong seq owner"
    let kind:=match ci with|.thmInfo _=>"theorem"|.defnInfo _=>"definition"|_=>"other"
    unless (if leaf=="seqMap" then kind=="definition" else kind=="theorem") do throwError "Wrong seq kind"
    logInfo m!"ordinary-seq|{n}|{kind}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
run_cmd do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Controller 0) "PhysicalCallerClosure") "liftOld"
  let some (.defnInfo ci):=e.find? n | throwError "Missing liftOld"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == `PhysicalCallerClosure.Controller do throwError "Wrong owner"
  logInfo m!"ordinary-lift|{n}|{ci.type}"
  modifyScope fun st=>{st with openDecls:=.explicit `actualOld n::st.openDecls}
private def cut (k : Nat) (mode : Fin 3) : Fin (CertificateGuardClosure.machine k).stateCount :=
  CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))
private theorem push_rows (L A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount)
    (start:f A.start=B.start) (reject:f A.reject=B.reject)
    (ends:Fin 3 → Fin A.stateCount)
    (rows:∀ s,(∀ j,s≠ends j) → ∀ b,B.step (f s) b=(f (A.step s b).1,(A.step s b).2)) :
    ∀ s,(∀ j,s≠L.seqRight A (ends j)) → ∀ b,
    (L.seq B).step (seqMap L A B f s) b=
      (seqMap L A B f ((L.seq A).step s b).1,((L.seq A).step s b).2) := by
  intro s no b
  apply seqMap_rows L A B f start reject (fun q=>∃ j,q=ends j)
  · intro q ne b
    exact rows q (fun j h=>ne ⟨j,h⟩) b
  · intro q eq bad
    obtain ⟨j,hj⟩:=bad
    exact no j (eq.trans (congrArg (L.seqRight A) hj))
private theorem push_start (L A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount)
    (start:f A.start=B.start) (reject:f A.reject=B.reject) :
    seqMap L A B f (L.seq A).start=(L.seq B).start :=
  seqMap_route L A B f start reject L.start
private theorem push_reject (L A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount)
    (reject:f A.reject=B.reject) :
    seqMap L A B f (L.seq A).reject=(L.seq B).reject := by
  change seqMap L A B f (L.seqRight A A.reject)=L.seqRight B B.reject
  rw [seqMap_right,reject]
private def f0 (k : Nat) := PhysicalCallerClosure.oldState k
private def f1 (k : Nat) := seqMap FixedPairParser.machine (BodyIngress.machine k) (PhysicalCallerClosure.callerMachine k) (f0 k)
private def f2 (k : Nat) := seqMap CertificateGuardClosure.guard (TotalIngressClosure.machine k)
  (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k)) (f1 k)
private def f3 (k : Nat) := seqMap FixedPairParser.machine
  (CertificateGuardClosure.guard.seq (TotalIngressClosure.machine k))
  (CertificateGuardClosure.guard.seq (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k))) (f2 k)
private theorem f0_value (k : Nat) (s : Fin (BodyIngress.machine k).stateCount) : (f0 k s).val=s.val := by
  dsimp only [f0,PhysicalCallerClosure.oldState,actualOld]
private theorem f1_value (k : Nat) (s : Fin (TotalIngressClosure.machine k).stateCount) : (f1 k s).val=s.val :=
  seqMap_val FixedPairParser.machine (BodyIngress.machine k) (PhysicalCallerClosure.callerMachine k) (f0 k) (f0_value k) s
private theorem f2_value (k : Nat) (s : Fin (CertificateGuardClosure.guard.seq (TotalIngressClosure.machine k)).stateCount) : (f2 k s).val=s.val :=
  seqMap_val CertificateGuardClosure.guard (TotalIngressClosure.machine k)
    (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k)) (f1 k) (f1_value k) s
private theorem f3_value (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) : (f3 k s).val=s.val :=
  seqMap_val FixedPairParser.machine (CertificateGuardClosure.guard.seq (TotalIngressClosure.machine k))
    (CertificateGuardClosure.guard.seq (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k))) (f2 k) (f2_value k) s
private theorem old_map (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) : f3 k s=old k s := by
  apply Fin.ext
  dsimp only [old]
  exact f3_value k s
private theorem old_start (k : Nat) : old k (CertificateGuardClosure.machine k).start=(machine k).start := by
  have s0:f0 k (BodyIngress.machine k).start=(PhysicalCallerClosure.callerMachine k).start:=rfl
  have r0:f0 k (BodyIngress.machine k).reject=(PhysicalCallerClosure.callerMachine k).reject:=rfl
  have s1:=push_start FixedPairParser.machine (BodyIngress.machine k) (PhysicalCallerClosure.callerMachine k) (f0 k) s0 r0
  have r1:=push_reject FixedPairParser.machine (BodyIngress.machine k) (PhysicalCallerClosure.callerMachine k) (f0 k) r0
  have s2:=push_start CertificateGuardClosure.guard (TotalIngressClosure.machine k)
    (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k)) (f1 k) s1 r1
  have r2:=push_reject CertificateGuardClosure.guard (TotalIngressClosure.machine k)
    (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k)) (f1 k) r1
  exact (old_map k _).symm.trans (push_start FixedPairParser.machine
    (CertificateGuardClosure.guard.seq (TotalIngressClosure.machine k))
    (CertificateGuardClosure.guard.seq (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k))) (f2 k) s2 r2)
private theorem old_reject (k : Nat) : old k (CertificateGuardClosure.machine k).reject=(machine k).reject := by
  have r0:f0 k (BodyIngress.machine k).reject=(PhysicalCallerClosure.callerMachine k).reject:=rfl
  have r1:=push_reject FixedPairParser.machine (BodyIngress.machine k) (PhysicalCallerClosure.callerMachine k) (f0 k) r0
  have r2:=push_reject CertificateGuardClosure.guard (TotalIngressClosure.machine k)
    (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k)) (f1 k) r1
  exact (old_map k _).symm.trans (push_reject FixedPairParser.machine
    (CertificateGuardClosure.guard.seq (TotalIngressClosure.machine k))
    (CertificateGuardClosure.guard.seq (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k))) (f2 k) r2)
private theorem push_accept (L A B : UniformTM) (f : Fin A.stateCount → Fin B.stateCount)
    (accept:f A.accept=B.accept) : seqMap L A B f (L.seq A).accept=(L.seq B).accept := by
  change seqMap L A B f (L.seqRight A A.accept)=L.seqRight B B.accept
  rw [seqMap_right,accept]
private theorem old_accept (k : Nat) : old k (CertificateGuardClosure.machine k).accept=(machine k).accept := by
  have a0:f0 k (BodyIngress.machine k).accept=(PhysicalCallerClosure.callerMachine k).accept:=rfl
  have a1:=push_accept FixedPairParser.machine (BodyIngress.machine k) (PhysicalCallerClosure.callerMachine k) (f0 k) a0
  have a2:=push_accept CertificateGuardClosure.guard (TotalIngressClosure.machine k)
    (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k)) (f1 k) a1
  exact (old_map k _).symm.trans (push_accept FixedPairParser.machine
    (CertificateGuardClosure.guard.seq (TotalIngressClosure.machine k))
    (CertificateGuardClosure.guard.seq (FixedPairParser.machine.seq (PhysicalCallerClosure.callerMachine k))) (f2 k) a2)
private theorem value_injective (A B : Nat) (f : Fin A → Fin B) (value:∀ s,(f s).val=s.val) : Function.Injective f := by
  intro s t eq
  have vals:=congrArg Fin.val eq
  rw [value,value] at vals
  exact Fin.ext vals
private theorem old_injective (k : Nat) : Function.Injective (old k) := by
  apply value_injective (CertificateGuardClosure.machine k).stateCount (machine k).stateCount (old k)
  intro s
  dsimp only [old]
private theorem old_rows (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (uncut:∀ mode,s≠cut k mode) (b : Option Bool) :
    (machine k).step (old k s) b=
      (old k ((CertificateGuardClosure.machine k).step s b).1,((CertificateGuardClosure.machine k).step s b).2) := by
  have base:∀ q,(∀ j,q≠BodyIngress.body k (SerializedBody.entry j)) → ∀ v,
      (PhysicalCallerClosure.callerMachine k).step (f0 k q) v=
        (f0 k ((BodyIngress.machine k).step q v).1,((BodyIngress.machine k).step q v).2):=
    fun q h v=>PhysicalCallerClosure.old_rows k q v h
  have r1:=push_rows FixedPairParser.machine _ _ (f0 k) rfl rfl _ base
  have s1:=push_start FixedPairParser.machine _ _ (f0 k) rfl rfl
  have t1:=push_reject FixedPairParser.machine _ _ (f0 k) rfl
  have r2:=push_rows CertificateGuardClosure.guard _ _ (f1 k) s1 t1 _ r1
  have s2:=push_start CertificateGuardClosure.guard _ _ (f1 k) s1 t1
  have t2:=push_reject CertificateGuardClosure.guard _ _ (f1 k) t1
  have r3:=push_rows FixedPairParser.machine _ _ (f2 k) s2 t2 _ r2
  have result:=r3 s uncut b
  change (machine k).step (f3 k s) b=(f3 k ((CertificateGuardClosure.machine k).step s b).1,_ ) at result
  simpa only [old_map] using result
private theorem chain_run (A L G : UniformTM) {N B : Nat} (c : Config A.stateCount N B) (t : Nat) :
    (L.seq (G.seq (L.seq A))).run t (L.seqEmbedRight _ (G.seqEmbedRight _ (L.seqEmbedRight A c)))=
      L.seqEmbedRight _ (G.seqEmbedRight _ (L.seqEmbedRight A (A.run t c))) := by
  rw [UniformTM.seq_run_right,UniformTM.seq_run_right,UniformTM.seq_run_right]
private theorem caller_run (k : Nat) {N B : Nat}
    (c : Config (PhysicalCallerClosure.callerMachine k).stateCount N B) (t : Nat) :
    (machine k).run t (callerConfig k c)=callerConfig k ((PhysicalCallerClosure.callerMachine k).run t c) := by
  have h:=chain_run (PhysicalCallerClosure.callerMachine k) FixedPairParser.machine CertificateGuardClosure.guard c t
  simpa only [machine,callerConfig,callerState,UniformTM.seqEmbedRight] using h
private theorem old_body (k : Nat) (s : Fin (BodyIngress.machine k).stateCount) :
    old k (CertificateGuardClosure.old k (TotalIngressClosure.old k s))=
      callerState k (PhysicalCallerClosure.oldState k s) := by
  dsimp only [old,CertificateGuardClosure.old,TotalIngressClosure.old,callerState,
    UniformTM.seqRight,PhysicalCallerClosure.oldState,actualOld]
end RawCallerClosure
