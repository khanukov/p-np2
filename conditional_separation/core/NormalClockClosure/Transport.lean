import NormalClockClosure.Arithmetic
namespace NormalClockClosure
open Pnp3.Complexity.Uniform.V1
/-- Real initial-config room after the executed sharp price has been proved;
this is not an assumption that the public NORMAL deadline fits its source tape. -/
private theorem actual_room (M : UniformTM) (N C t : Nat) (y : Bitstring N)
    (small:t+1 ≤ C) : ∀ u,u ≤ t → (M.run u (initialConfig M C y)).head.val+1 < tapeLength N C := by
  intro u hu
  have speed:=M.run_initialConfig_head_le (budget:=C) (steps:=u) y
  simp only [tapeLength]
  omega
private theorem lift_actual (M : UniformTM) (N C t : Nat) (y : Bitstring N)
    (small:t+1 ≤ C) (virtual:Bool → Fin M.stateCount)
    (first:∀ u,u < t → (M.run u (initialConfig M C y)).state≠M.accept ∧
      (M.run u (initialConfig M C y)).state≠M.reject ∧
      ∀ b,(M.run u (initialConfig M C y)).state≠virtual b) :
    ∀ (B : Nat) (hCB:C ≤ B),
      (∀ u,u ≤ t →
        (M.run u (initialConfig M C y)).state=(M.run u (initialConfig M B y)).state ∧
        (M.run u (initialConfig M B y)).head=FixedPairParser.tapeEmbed hCB (M.run u (initialConfig M C y)).head ∧
        (∀ i:Fin (tapeLength N C),(M.run u (initialConfig M B y)).tape (FixedPairParser.tapeEmbed hCB i)=(M.run u (initialConfig M C y)).tape i) ∧
        (∀ j:Fin (tapeLength N B),tapeLength N C ≤ j.val → (M.run u (initialConfig M B y)).tape j=none) ∧
        (M.run u (initialConfig M C y)).head.val ≤ t ∧ (M.run u (initialConfig M B y)).head.val ≤ t) ∧
      (∀ u,u < t → (M.run u (initialConfig M B y)).state≠M.accept ∧
        (M.run u (initialConfig M B y)).state≠M.reject ∧
        ∀ b,(M.run u (initialConfig M B y)).state≠virtual b) ∧
      (∀ T,t ≤ T → (M.run t (initialConfig M C y)).state=M.accept ∨
        (M.run t (initialConfig M C y)).state=M.reject →
        M.run T (initialConfig M B y)=M.run t (initialConfig M B y)) := by
  intro B hCB
  have extension (u : Nat) (hu:u ≤ t) : FixedPairParser.ConfigExtension hCB
      (M.run u (initialConfig M C y)) (M.run u (initialConfig M B y)):=
    FixedPairParser.run_extension M hCB (FixedPairParser.initialConfig_extension M hCB y) u
      (fun v hv=>actual_room M N C t y small v (by omega))
  refine ⟨?_,?_,?_⟩
  · intro u hu
    have e:=extension u hu
    have hs:(M.run u (initialConfig M C y)).head.val ≤ t:=
      (M.run_initialConfig_head_le y).trans hu
    have hl:(M.run u (initialConfig M B y)).head.val ≤ t:=by
      rw [e.2.1];exact hs
    exact ⟨e.1,e.2.1,e.2.2.1,e.2.2.2,hs,hl⟩
  · intro u hu
    have e:=extension u hu.le
    rw [←e.1]
    exact first u hu
  · intro T tT terminal
    have e:=extension t le_rfl
    rcases terminal with accept|reject
    · have hit:(M.run t (initialConfig M B y)).state=M.accept:=e.1.symm.trans accept
      rw [show T=t+(T-t) by omega,M.run_add]
      exact M.run_accept _ hit _
    · have hit:(M.run t (initialConfig M B y)).state=M.reject:=e.1.symm.trans reject
      rw [show T=t+(T-t) by omega,M.run_add]
      exact M.run_reject _ hit _
private theorem deadline_decision (M : UniformTM) (N C P t : Nat) (y : Bitstring N)
    (small:t+1 ≤ C) (growth:C ≤ P) (time:t ≤ P) :
    ∀ answer : Bool,(M.run t (initialConfig M C y)).state=(if answer then M.accept else M.reject) →
      M.run P (initialConfig M P y)=M.run t (initialConfig M P y) ∧
      DecidesAt M P P y answer ∧ DecidesWithin M P y answer := by
  intro answer hit
  have e:=FixedPairParser.run_extension M growth (FixedPairParser.initialConfig_extension M growth y) t
    (fun v hv=>actual_room M N C t y small v hv.le)
  have eh:(M.run t (initialConfig M P y)).state=(if answer then M.accept else M.reject):=e.1.symm.trans hit
  have stable:M.run P (initialConfig M P y)=M.run t (initialConfig M P y):=by
    calc M.run P (initialConfig M P y)=M.run (t+(P-t)) (initialConfig M P y):=
           congrArg (fun steps=>M.run steps (initialConfig M P y)) (by omega)
         _ = M.run (P-t) (M.run t (initialConfig M P y)):=M.run_add _ _ _
         _ = M.run t (initialConfig M P y):=by
           cases answer with
           | false=>exact M.run_reject _ eh _
           | true=>exact M.run_accept _ eh _
  have decided:DecidesAt M P P y answer:=by
    cases answer with
    | false=>change (M.run P (initialConfig M P y)).state=M.reject;rw [stable];exact eh
    | true=>change (M.run P (initialConfig M P y)).state=M.accept;rw [stable];exact eh
  exact ⟨stable,decided,(decidesAt_budget_iff_decidesWithin M y answer).mp decided⟩
end NormalClockClosure
