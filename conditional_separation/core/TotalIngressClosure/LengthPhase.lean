import IngressAllocation.AncillaryPaths
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("RuntimeBitLength.Kernel","RuntimeBitLength","Frame.mk","firstFrame"),
      ("RuntimeBitLength.Kernel","RuntimeBitLength","entry","entryPath"),
      ("RuntimeBitLength.Kernel","RuntimeBitLength","Path.execute","entryRun"),
      ("RuntimeBitLength.Kernel","RuntimeBitLength","Path.first","entryFirst"),
      ("BitLengthDriver.Kernel","BitLengthDriver","Frame.mk","lengthFrame"),
      ("BitLengthDriver.Kernel","BitLengthDriver","loop","lengthLoop"),
      ("BitLengthDriver.Kernel","BitLengthDriver","initial_image","initialImage"),
      ("BitLengthDriver.Kernel","BitLengthDriver","Path.execute","loopRun"),
      ("BitLengthDriver.Kernel","BitLengthDriver","Path.first","loopFirst"),
      ("BitLengthDriver.Kernel","BitLengthDriver","early_bound","earlyBound"),
      ("IngressAllocation.AncillaryPaths","IngressAllocation.FirstLengthStage","every_head","entryHeads"),
      ("IngressAllocation.ArithmeticPaths","IngressAllocation.LengthStage","every_head","loopHeads")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique actual all-width length path {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem length_phase (k N B L n Q F r : Nat) (X : Nat → Option Bool)
    (hr : 0 < r) (paid : 0 < Q) (room : L+n+1+Q < F)
    (sep : X L=none) (assn : ∀ i,L < i → i < L+n+1 → X i=some true)
    (right : X (L+n+1)=none)
    (marks : ∀ i,L+n+1 < i → i ≤ L+n+1+Q → X i=some true)
    (gap : ∀ i,L+n+1+Q < i → i < F → X i=none)
    (fence : X F=some false) (d0 : X (F+1)=none)
    (b0 : ∀ i,F+1 < i → i < F+r+2 → X i=some true) (d1 : X (F+r+2)=none)
    (b1 : ∀ i,F+r+2 < i → i < F+r+n+3 → X i=some false) (d2 : X (F+r+n+3)=none)
    (b2 : ∀ i,F+r+n+3 < i → i < F+2*r+n+4 → X i=some false) (d3 : X (F+2*r+n+4)=none)
    (fit : F+5*r+n+7 < tapeLength N B) :
    ∃ (t : Nat) (h : (if bitLength n ≤ r then L else F+r+n+3) < tapeLength N B),
      t ≤ 2048*(n+1)*(F+5*r+n+8) ∧
      (Cursor.machine k).run t
        (⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i=>X i.val⟩ : Config (Cursor.machine k).stateCount N B)=
        ⟨Cursor.q k (if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304),
          ⟨if bitLength n ≤ r then L else F+r+n+3,h⟩,fun i=>RuntimeBitLength.Target.fullImage X L n F r i.val⟩ ∧
      (∀ u,u ≤ t → ((Cursor.machine k).run u
        (⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i=>X i.val⟩ : Config (Cursor.machine k).stateCount N B)).head.val ≤ F+5*r+n+7) ∧
      (∀ u,u < t → ((Cursor.machine k).run u
        (⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i=>X i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val < 329) := by
  let C : Config (Cursor.machine k).stateCount N B:=⟨Cursor.q k 201,⟨F+1,by omega⟩,fun i=>X i.val⟩
  have fr:=lengthFrame paid room sep assn right marks gap fence d0 b0 d1 b1 d2 b2 d3
  have ff:=firstFrame paid room sep assn right marks gap fence d0 b0 d1 b1 d2 (b2 _ (by omega) (by omega))
  obtain ⟨a,_exact,entryPrice,entry⟩:=entryPath k L n Q F r X ff
  have enter:=entryRun (N:=N) (B:=B) entry fit
  change (Cursor.machine k).run a C=⟨Cursor.q k 209,⟨L,by omega⟩,fun i=>X i.val⟩ at enter
  have entryBefore:=entryFirst (N:=N) (B:=B) entry fit
  have entryLow:=earlyBound C (Or.inl (by rw [enter];change 209 < 250;omega)) entryBefore
  have entryFoot:=entryHeads entry fit (by change F+1 < tapeLength N B;omega)
  obtain ⟨b,loopPrice,path⟩:=lengthLoop k L n Q F r X fr n 0 true le_rfl (by omega) (by simp) (by simp) rfl
  rw [initialImage fr] at path
  have finish:=loopRun (N:=N) (B:=B) path fit
  change (Cursor.machine k).run b
    (⟨Cursor.q k 209,⟨L,by omega⟩,fun i=>X i.val⟩ : Config (Cursor.machine k).stateCount N B)=
    ⟨Cursor.q k (if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304),
      ⟨if bitLength n ≤ r then L else F+r+n+3,by split <;> omega⟩,
      fun i=>RuntimeBitLength.Target.fullImage X L n F r i.val⟩ at finish
  have loopFoot:=loopHeads path fit (by change L < tapeLength N B;omega)
  have loopBefore:=loopFirst (N:=N) (B:=B) path fit
  have avoid : ∀ u,u < a+b → ((Cursor.machine k).run u C).state.val ≠ 250 ∧
      ((Cursor.machine k).run u C).state.val ≠ 304 ∧ ((Cursor.machine k).run u C).state.val ≠ 308:=by
    intro u hu
    by_cases early : u < a
    · have bound:=entryLow u early
      exact ⟨by omega,by omega,by omega⟩
    · rw [show u=a+(u-a) by omega,UniformTM.run_add,enter]
      exact loopBefore (u-a) (by omega)
  have price:a+b ≤ 2048*(n+1)*(F+5*r+n+8):=by
    nlinarith only [entryPrice,loopPrice,Nat.zero_le (n*(F+5*r+n+8))]
  refine ⟨a+b,by split <;> omega,price,?_,?_,?_⟩
  · rw [UniformTM.run_add,enter,finish]
  · intro u hu
    by_cases early : u ≤ a
    · exact entryFoot u early
    · rw [show u=a+(u-a) by omega,UniformTM.run_add,enter]
      exact loopFoot (u-a) (by omega)
  · apply AllArityBitLength.control_before C (Or.inr ⟨rfl,rfl⟩)
      (Or.inr (by change 201 ≤ 201 ∧ 201 ≤ 308 ∧ (201 ≤ 250 ∨ 254 ≤ 201) ∧ (201 ≤ 304 ∨ 308 ≤ 201);omega))
    intro u hu
    have h:=avoid u hu
    exact ⟨h.2.2,fun _=>⟨h.1,h.2.1⟩⟩
end TotalIngressClosure
