import CertificateGuardClosure.Sequence
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Pnp4.Frontier.ContractExpansion Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  let pool:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.CertificateGuardClosure."
  for (mod,key,aliasName) in [("GuardRun","guard_run","guardRun"),("Sequence","parser_low","parserLow"),("Sequence","parser_heads","parserHeads"),("Sequence","gate_low","gateLow"),("Sequence","gate_heads","gateHeads"),("Sequence","gate_entry","gateEntry"),("Sequence","gate_reject","gateReject"),("Sequence","parser_reject","parserReject"),("Sequence","include_suffix","includeSuffix"),("Sequence","include_injective","includeInjective")] do
    let found:=pool.filter fun (n,_)=>n.toString.startsWith ("_private.CertificateGuardClosure."++mod++".") && n.toString.endsWith (".CertificateGuardClosure."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique concrete raw bridge {mod}/{key}: {found.map Prod.fst}"
private theorem room (k N : Nat) : 2*N+3 < tapeLength N (allocation k N) := by
  have power:N+1 ≤ (N+1)^8 := by simpa using Nat.pow_le_pow_right (by omega:1 ≤ N+1) (by decide:1 ≤ 8)
  have scale:4*(N+1) ≤ allocation k N := by
    change 4*(N+1) ≤ 1099511627776*(k+1)*(N+1)^8
    exact Nat.mul_le_mul (by omega) power
  simp only [tapeLength]
  omega
private theorem parser_room (k N : Nat) : FixedPairParser.clock N ≤ allocation k N := by
  have bound:=room k N
  change 2*N+1 ≤ allocation k N
  simp only [tapeLength] at bound
  have power:N+1 ≤ (N+1)^8 := by simpa using Nat.pow_le_pow_right (by omega:1 ≤ N+1) (by decide:1 ≤ 8)
  have scale:4*(N+1) ≤ allocation k N := by
    change 4*(N+1) ≤ 1099511627776*(k+1)*(N+1)^8
    exact Nat.mul_le_mul (by omega) power
  omega
private theorem prefix_price (k N : Nat) : FixedPairParser.clock N+64*(N+1)^2 ≤ TotalIngressClosure.deadline k N := by
  have power:(N+1)^2 ≤ (N+1)^6:=Nat.pow_le_pow_right (by omega) (by decide)
  have small:FixedPairParser.clock N+64*(N+1)^2 ≤ 128*(N+1)^2 := by
    change 2*N+1+64*(N+1)^2 ≤ 128*(N+1)^2
    nlinarith only [Nat.zero_le N,Nat.zero_le (N^2)]
  exact small.trans (Nat.mul_le_mul (by omega:128 ≤ 68719476736*(k+1)) power)
private theorem total_price (k N g d : Nat) (hg:g ≤ FixedPairParser.clock N+64*(N+1)^2)
    (hd:d ≤ TotalIngressClosure.deadline k N) : g+d ≤ deadline k N := by
  have price:=prefix_price k N
  have doubled:deadline k N=2*TotalIngressClosure.deadline k N := by
    dsimp [deadline,TotalIngressClosure.deadline];ring
  rw [doubled]
  omega
private theorem head_envelope (N : Nat) : 2*N+3 ≤ 12*(N+1)^2 := by
  nlinarith only [Nat.zero_le N,Nat.zero_le (N^2)]
private theorem early_absent (k N B u : Nat) (y : Bitstring N)
    (low:((machine k).run u (initialConfig (machine k) B y)).state.val < 77)
    (q:Fin (TotalIngressClosure.machine k).stateCount) :
    ((machine k).run u (initialConfig (machine k) B y)).state≠old k q := by
  intro hit
  have value:=congrArg Fin.val hit
  change ((machine k).run u (initialConfig (machine k) B y)).state.val=10+(67+q.val) at value
  omega
private theorem no_accept_of_reject (M:UniformTM) {N B t:Nat} (c:Config M.stateCount N B)
    (last:(M.run t c).state=M.reject) : ∀ u,u ≤ t → (M.run u c).state≠M.accept := by
  intro u hu hit
  have same:=M.run_accept_of_le c hit hu
  have states:=congrArg Config.state same
  rw [last,hit] at states
  exact M.accept_ne_reject states.symm
private theorem malformed (k N:Nat) (y:Bitstring N) (bad:decodePair y=none) :
    let M:=machine k;let c:=initialConfig M (allocation k N) y
    ∃ T,T ≤ deadline k N ∧
      (∀ u,u ≤ T → (M.run u c).head.val ≤ 12*(N+1)^2) ∧
      (∀ u,u ≤ T → (M.run u c).state≠M.accept) ∧
      (∀ u,u < T → (M.run u c).state≠M.reject ∧
        (∀ b,(M.run u c).state≠old k (TotalIngressClosure.old k (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))) ∧
        (∀ mode:Fin 3,(M.run u c).state≠old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode))))) ∧
      T=FixedPairParser.clock N ∧ M.run T c=⟨M.reject,⟨0,by simp [tapeLength]⟩,c.tape⟩ := by
  intro M c
  have done:=parserReject (guard.seq (TotalIngressClosure.machine k)) y (parser_room k N) bad
  have first(u:Nat)(hu:u < FixedPairParser.clock N): (M.run u c).state.val < 77 :=
    (parserLow (guard.seq (TotalIngressClosure.machine k)) y (parser_room k N) u hu).trans (by decide)
  refine ⟨FixedPairParser.clock N,?_,?_,no_accept_of_reject M c (congrArg Config.state done),?_,rfl,done⟩
  · exact total_price k N (FixedPairParser.clock N) 0 (by omega) (by omega)
  · intro u hu
    exact (parserHeads (guard.seq (TotalIngressClosure.machine k)) y (parser_room k N) u hu).trans (by have h:=head_envelope N;omega)
  · intro u hu
    exact ⟨early_absent k N _ u y (first u hu) (TotalIngressClosure.machine k).reject,
      fun b=>early_absent k N _ u y (first u hu) _,fun mode=>early_absent k N _ u y (first u hu) _⟩
/-- Every raw input physically passes the exact original certificate guard or
literally rejects; successful guards restore the whole original configuration
before the SAME complete all-input ingress and its strict first consumer. -/
theorem raw (k : Nat) : Target.Raw k := by
  intro N y
  cases parsed:decodePair y with
  | none =>
    obtain ⟨T,price,heads,safe,first,clock,done⟩:=malformed k N y parsed
    exact ⟨T,price,heads,safe,first,Or.inl ⟨rfl,clock,done,encodedRelationLanguage_malformed _ y parsed⟩⟩
  | some p =>
    rcases p with ⟨⟨a,x⟩,⟨m,w⟩⟩
    have packed:(⟨N,y⟩:EncodedWord)=⟨pairLength a m,encodePair x w⟩:=(decodePair_eq_some_iff y _).1 parsed
    have length:N=pairLength a m:=congrArg Sigma.fst packed
    subst N
    have word:y=encodePair x w:=by cases packed;rfl
    subst y
    let N:=pairLength a m;let y:=encodePair x w;let B:=allocation k N
    let M:=machine k;let O:=TotalIngressClosure.machine k;let c:=initialConfig M B y;let c0:=initialConfig O B y
    have parsed:decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair):=decodePair_roundtrip x w
    obtain ⟨h,hprice,hheads,hfirst,hdone⟩:=guardRun (B:=B) x w (room k N)
    let g:=FixedPairParser.clock N+h
    have hprice':h ≤ 64*(N+1)^2 := hprice
    have gprice:g ≤ FixedPairParser.clock N+64*(N+1)^2 := by
      change FixedPairParser.clock N+h ≤ FixedPairParser.clock N+64*(N+1)^2
      omega
    have low(u:Nat)(hu:u < g):(M.run u c).state.val < 77 :=
      gateLow O y (parser_room k N) _ parsed hfirst u hu
    have gh(u:Nat)(hu:u ≤ g):(M.run u c).head.val ≤ 12*(N+1)^2 :=
      (gateHeads O y (parser_room k N) _ parsed (fun v hv=>(hfirst v hv).1) hheads (by omega) u hu).trans (head_envelope N)
    by_cases canonical:m=a+1
    · rw [if_pos canonical] at hdone
      have entry:M.run g c=config k c0:=gateEntry O y (parser_room k N) _ parsed (fun v hv=>(hfirst v hv).1) hdone
      have suffixRun(u:Nat):M.run (g+u) c=config k (O.run u c0):=by
        rw [UniformTM.run_add,entry]
        exact includeSuffix O c0 u
      have inject:Function.Injective (old k):=includeInjective O
      have pred:∃ d,Target.Frontier k N y d:=TotalIngressClosure.raw k N y
      obtain ⟨d,front⟩:=pred
      have fullFront:=front
      rcases front with ⟨dprice,dheads,dsafe,dfirst,outcome⟩
      refine ⟨g+d,total_price k N g d gprice dprice,?_,?_,?_,Or.inr (Or.inr ?_)⟩
      · intro u hu
        by_cases before:u < g
        · exact gh u before.le
        · rw [show u=g+(u-g) by omega,suffixRun]
          exact dheads (u-g) (by omega)
      · intro u hu hit
        by_cases before:u < g
        · exact early_absent k N B u y (low u before) O.accept hit
        · have runeq:=suffixRun (u-g)
          rw [show g+(u-g)=u by omega] at runeq
          have stateeq:=congrArg Config.state runeq
          have hitOld:(O.run (u-g) c0).state=O.accept:=inject (stateeq.symm.trans hit)
          exact dsafe (u-g) (by omega) hitOld
      · intro u hu
        by_cases before:u < g
        · exact ⟨early_absent k N B u y (low u before) O.reject,
            fun b=>early_absent k N B u y (low u before) _,fun mode=>early_absent k N B u y (low u before) _⟩
        · have runeq:=suffixRun (u-g)
          rw [show g+(u-g)=u by omega] at runeq
          have stateeq:=congrArg Config.state runeq
          have oldFirst:=dfirst (u-g) (by omega)
          refine ⟨?_,?_,?_⟩
          · intro hit
            exact oldFirst.1 (inject (stateeq.symm.trans hit))
          · intro b hit
            exact oldFirst.2.1 b (inject (stateeq.symm.trans hit))
          · intro mode hit
            exact oldFirst.2.2 mode (inject (stateeq.symm.trans hit))
      · exact ⟨a,m,x,w,rfl,rfl,rfl,canonical,g,d,rfl,gprice,low,entry,suffixRun,fullFront,suffixRun d⟩
    · rw [if_neg canonical] at hdone
      have done:M.run g c=⟨M.reject,⟨0,by simp [tapeLength]⟩,c.tape⟩:=
        gateReject O y (parser_room k N) _ parsed (fun v hv=>(hfirst v hv).1) hdone
      refine ⟨g,total_price k N g 0 gprice (by omega),gh,no_accept_of_reject M c (congrArg Config.state done),?_,Or.inr (Or.inl ?_)⟩
      · intro u hu
        exact ⟨early_absent k N B u y (low u hu) O.reject,
          fun b=>early_absent k N B u y (low u hu) _,fun mode=>early_absent k N B u y (low u hu) _⟩
      · exact ⟨a,m,x,w,rfl,rfl,rfl,canonical,gprice,done,wrong_length k x w canonical⟩
end CertificateGuardClosure
