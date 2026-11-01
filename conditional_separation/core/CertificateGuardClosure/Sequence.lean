import CertificateGuardClosure.GuardRun
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  let pool:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.TotalIngressClosure.SeqTrace."
  for (key,aliasName) in [("seq_prefix","parserPrefix"),("seq_suffix","parserSuffix")] do
    let found:=pool.filter fun (n,_)=>n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique source-restoring parser interface {key}: {found.map Prod.fst}"
private def includeConfig (O : UniformTM) {N B : Nat} (c : Config O.stateCount N B) :
    Config (FixedPairParser.machine.seq (guard.seq O)).stateCount N B :=
  FixedPairParser.machine.seqEmbedRight (guard.seq O) (guard.seqEmbedRight O c)
private def includeState (O : UniformTM) (q : Fin O.stateCount) :
    Fin (FixedPairParser.machine.seq (guard.seq O)).stateCount :=
  FixedPairParser.machine.seqRight (guard.seq O) (guard.seqRight O q)
private theorem include_injective (O : UniformTM) : Function.Injective (includeState O) := by
  intro a b h
  exact guard.seqRight_injective O (FixedPairParser.machine.seqRight_injective (guard.seq O) h)
private theorem include_suffix (O : UniformTM) {N B : Nat} (c : Config O.stateCount N B) (u : Nat) :
    (FixedPairParser.machine.seq (guard.seq O)).run u (includeConfig O c)=includeConfig O (O.run u c) := by
  simp only [includeConfig,UniformTM.seq_run_right]
private theorem parser_low (O : UniformTM) {N B : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (u:Nat) (hu:u < FixedPairParser.clock N) :
    ((FixedPairParser.machine.seq O).run u (initialConfig (FixedPairParser.machine.seq O) B y)).state.val < 10 := by
  rw [parserPrefix O y room u hu.le]
  have safe:=FixedPairParser.ambient_no_public_terminal_before_clock y room u hu
  change (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).state≠FixedPairParser.machine.accept ∧
    (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).state≠FixedPairParser.machine.reject at safe
  change (FixedPairParser.machine.seqRoute O _).val < 10
  rw [UniformTM.seqRoute,if_neg safe.1,if_neg safe.2]
  exact (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).state.isLt
private theorem parser_heads (O : UniformTM) {N B : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (u:Nat) (hu:u ≤ FixedPairParser.clock N) :
    ((FixedPairParser.machine.seq O).run u (initialConfig (FixedPairParser.machine.seq O) B y)).head.val ≤ N := by
  rw [parserPrefix O y room u hu]
  have e:=FixedPairParser.ambient_run_extension y room u hu
  change (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).head.val ≤ N
  rw [e.2.1]
  exact FixedPairParser.exact_head_le_input_through_clock y u hu
private theorem gate_run (O : UniformTM) {N B h : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (p:DecodedPair) (parsed:decodePair y=some p)
    (safe:∀ u,u < h → (guard.run u (initialConfig guard B y)).state≠guard.accept)
    (u:Nat) (hu:u ≤ h) :
    (FixedPairParser.machine.seq (guard.seq O)).run (FixedPairParser.clock N+u)
      (initialConfig (FixedPairParser.machine.seq (guard.seq O)) B y)=
      FixedPairParser.machine.seqEmbedRight (guard.seq O)
        (guard.seqEmbedRouted O (guard.run u (initialConfig guard B y))) := by
  rw [parserSuffix (guard.seq O) y room p parsed u]
  have e:=guard.seq_run_left O (initialConfig guard B y) safe u hu
  rw [←UniformTM.seq_initialConfig] at e
  rw [e]
private theorem gate_low (O : UniformTM) {N B h : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (p:DecodedPair) (parsed:decodePair y=some p)
    (safe:∀ u,u < h → (guard.run u (initialConfig guard B y)).state≠guard.accept ∧
      (guard.run u (initialConfig guard B y)).state≠guard.reject)
    (u:Nat) (hu:u < FixedPairParser.clock N+h) :
    ((FixedPairParser.machine.seq (guard.seq O)).run u
      (initialConfig (FixedPairParser.machine.seq (guard.seq O)) B y)).state.val < 77 := by
  by_cases early:u < FixedPairParser.clock N
  · exact (parser_low (guard.seq O) y room u early).trans (by decide)
  · rw [show u=FixedPairParser.clock N+(u-FixedPairParser.clock N) by omega,
      gate_run O y room p parsed (fun v hv=>(safe v hv).1) _ (by omega)]
    change 10+(guard.seqRoute O (guard.run (u-FixedPairParser.clock N) (initialConfig guard B y)).state).val < 77
    rw [UniformTM.seqRoute,if_neg (safe _ (by omega)).1,if_neg (safe _ (by omega)).2]
    have bound: (guard.run (u-FixedPairParser.clock N) (initialConfig guard B y)).state.val < 67 :=
      (guard.run (u-FixedPairParser.clock N) (initialConfig guard B y)).state.isLt
    change 10+(guard.run (u-FixedPairParser.clock N) (initialConfig guard B y)).state.val < 77
    omega
private theorem gate_heads (O : UniformTM) {N B h P : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (p:DecodedPair) (parsed:decodePair y=some p)
    (safe:∀ u,u < h → (guard.run u (initialConfig guard B y)).state≠guard.accept)
    (heads:∀ u,u ≤ h → (guard.run u (initialConfig guard B y)).head.val ≤ P) (nBound:N ≤ P)
    (u:Nat) (hu:u ≤ FixedPairParser.clock N+h) :
    ((FixedPairParser.machine.seq (guard.seq O)).run u
      (initialConfig (FixedPairParser.machine.seq (guard.seq O)) B y)).head.val ≤ P := by
  by_cases early:u < FixedPairParser.clock N
  · exact (parser_heads (guard.seq O) y room u early.le).trans nBound
  · rw [show u=FixedPairParser.clock N+(u-FixedPairParser.clock N) by omega,
      gate_run O y room p parsed safe _ (by omega)]
    exact heads _ (by omega)
private theorem gate_entry (O : UniformTM) {N B h : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (p:DecodedPair) (parsed:decodePair y=some p)
    (safe:∀ u,u < h → (guard.run u (initialConfig guard B y)).state≠guard.accept)
    (done:guard.run h (initialConfig guard B y)=⟨guard.accept,⟨0,by simp [tapeLength]⟩,(initialConfig guard B y).tape⟩) :
    (FixedPairParser.machine.seq (guard.seq O)).run (FixedPairParser.clock N+h)
      (initialConfig (FixedPairParser.machine.seq (guard.seq O)) B y)=includeConfig O (initialConfig O B y) := by
  rw [gate_run O y room p parsed safe h le_rfl,done]
  apply Config.ext_parts
  · change FixedPairParser.machine.seqRight (guard.seq O) (guard.seqRoute O guard.accept)=
      FixedPairParser.machine.seqRight (guard.seq O) (guard.seqRight O O.start)
    rw [UniformTM.seqRoute,if_pos rfl]
  · rfl
  · rfl
private theorem gate_reject (O : UniformTM) {N B h : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (p:DecodedPair) (parsed:decodePair y=some p)
    (safe:∀ u,u < h → (guard.run u (initialConfig guard B y)).state≠guard.accept)
    (done:guard.run h (initialConfig guard B y)=⟨guard.reject,⟨0,by simp [tapeLength]⟩,(initialConfig guard B y).tape⟩) :
    (FixedPairParser.machine.seq (guard.seq O)).run (FixedPairParser.clock N+h)
      (initialConfig (FixedPairParser.machine.seq (guard.seq O)) B y)=
      ⟨(FixedPairParser.machine.seq (guard.seq O)).reject,⟨0,by simp [tapeLength]⟩,
        (initialConfig (FixedPairParser.machine.seq (guard.seq O)) B y).tape⟩ := by
  rw [gate_run O y room p parsed safe h le_rfl,done]
  apply Config.ext_parts
  · change FixedPairParser.machine.seqRight (guard.seq O) (guard.seqRoute O guard.reject)=
      FixedPairParser.machine.seqRight (guard.seq O) (guard.seqRight O O.reject)
    rw [UniformTM.seqRoute,if_neg guard.accept_ne_reject.symm,if_pos rfl]
  · rfl
  · rfl
private theorem parser_reject (O : UniformTM) {N B : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (bad:decodePair y=none) :
    (FixedPairParser.machine.seq O).run (FixedPairParser.clock N) (initialConfig (FixedPairParser.machine.seq O) B y)=
      ⟨(FixedPairParser.machine.seq O).reject,⟨0,by simp [tapeLength]⟩,(initialConfig (FixedPairParser.machine.seq O) B y).tape⟩ := by
  rw [parserPrefix O y room _ le_rfl,FixedPairParser.ambient_run_initialConfig_reject y room bad]
  apply Config.ext_parts
  · change FixedPairParser.machine.seqRoute O FixedPairParser.qReject=FixedPairParser.machine.seqRight O O.reject
    rw [UniformTM.seqRoute,if_neg (by decide),if_pos (show FixedPairParser.qReject=FixedPairParser.machine.reject from rfl)]
  · rfl
  · rfl
end CertificateGuardClosure
