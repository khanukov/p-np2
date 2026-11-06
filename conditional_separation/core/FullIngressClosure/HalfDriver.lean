import Complexity.PrivateInterfaceLookupResolvedHalving
import FullIngressClosure.HalfDriverCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateHalving.bindings `FullIngressClosure.HalfDriver
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated halving identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private def halfPhase (T : Nat → Option Bool) (D : Nat → Nat) (side : Bool) (v u : Nat) : Nat → Option Bool :=
  image3 T D 1 8 2 (if side then v else 0) (if side then 0 else v) u
private theorem phase_grid {D T} (grid : Grid D T) (side : Bool) (v u : Nat) : Grid D (halfPhase T D side v u) :=
  bankGrid (bankGrid (bankGrid grid 1 _ (by decide)) 8 _ (by decide)) 2 u (by decide)
private theorem phase_unary {D T} (grid : Grid D T) (side : Bool) (v u : Nat) :
    BankUnary D (halfPhase T D side v u) 1 (if side then v else 0) ∧
    BankUnary D (halfPhase T D side v u) 8 (if side then 0 else v) ∧
    BankUnary D (halfPhase T D side v u) 2 u := by
  have grid1:=bankGrid grid 1 (if side then v else 0) (by decide)
  have grid8:=bankGrid grid1 8 (if side then 0 else v) (by decide)
  refine ⟨?_,?_,bankUnary _ D 2 u⟩
  · exact bankOther grid8 1 2 _ u (by decide) (by decide) (by decide)
      (bankOther grid1 1 8 _ _ (by decide) (by decide) (by decide) (bankUnary T D 1 _))
  · exact bankOther grid8 8 2 _ u (by decide) (by decide) (by decide) (bankUnary _ D 8 _)
private theorem phase_zero (T : Nat → Option Bool) (D : Nat → Nat) (side : Bool) (u : Nat) :
    halfPhase T D side 0 u=halfPhase T D true 0 u := by cases side <;> rfl
private theorem phase_left (T : Nat → Option Bool) (D : Nat → Nat) (v u : Nat) :
    image3 (halfPhase T D true v u) D 1 8 2 0 (v/2) (u+1)=halfPhase T D false (v/2) (u+1) := by
  change image3 (image3 T D 1 8 2 v 0 u) D 1 8 2 0 (v/2) (u+1)=_
  exact shadow3 _ _ _ _ _ _ _ _ _ _ _
private theorem phase_right {T : Nat → Option Bool} {D : Nat → Nat} (grid : Grid D T) (v u : Nat) :
    image3 (halfPhase T D false v u) D 8 1 2 0 (v/2) (u+1)=halfPhase T D true (v/2) (u+1) := by
  have grid0:=phase_grid grid false v u
  dsimp only [image3]
  rw [bankCommute grid0 8 1 0 (v/2) (by decide) (by decide) (by decide)]
  change image3 (halfPhase T D false v u) D 1 8 2 (v/2) 0 (u+1)=_
  change image3 (image3 T D 1 8 2 0 v u) D 1 8 2 (v/2) 0 (u+1)=_
  exact shadow3 _ _ _ _ _ _ _ _ _ _ _
private theorem length_step (v : Nat) (hv : 0 < v) : bitLength v=bitLength (v/2)+1 := by
  by_cases two : 2 ≤ v
  · have hp : v/2 ≠ 0 := by omega
    simp only [bitLength,if_neg (by omega : v ≠ 0),if_neg hp]
    conv_lhs => rw [Nat.log2]
    rw [if_pos two]
  · have eq : v=1 := by omega
    subst v
    simp [bitLength,Nat.log2]
private theorem alternating_halving {k lo P D} (n r : Nat)
    (lenA : D 2=D 1+n+1) (lenB : D 9=D 8+n+1) (lenC : D 3=D 2+r+1)
    (lower : lo ≤ D 0) (upper : D 12 ≤ P) (T : Nat → Option Bool) (grid : Grid D T)
    (v : Nat) : ∀ (side : Bool) (u : Nat), v ≤ n → u+bitLength v ≤ r →
    ∃ t,t ≤ (512*v+8)*(P+16) ∧ PPath k lo P t
      (pNode (st k (if side then 1180 else 1239)) (D (if side then 1 else 8)) (halfPhase T D side v u))
      (pNode (st k 1311) (D 1) (halfPhase T D true 0 (u+bitLength v))) := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    intro side u vf fits
    have grid0:=phase_grid grid side v u
    have unary:=phase_unary grid side v u
    by_cases zero : v=0
    · subst v
      have result : ∃ t,t ≤ 8*(P+16) ∧ PPath k lo P t
          (pNode (st k (if side then 1180 else 1239)) (D (if side then 1 else 8)) (halfPhase T D side 0 u))
          (pNode (st k 1311) (D 1) (halfPhase T D side 0 u)) := by
        cases side
        · exact emptyHalf (rightEmpty k) _ grid0 (by decide) n lenB lower upper unary.2.1
        · exact emptyHalf (leftEmpty k) _ grid0 (by decide) n lenA lower upper unary.1
      obtain ⟨t,price,path⟩:=result
      rw [phase_zero T D side u] at path
      rw [phase_zero T D side u]
      exact ⟨t,by omega,path⟩
    · have positive : 0 < v:=by omega
      have stepLength:=length_step v positive
      have room : u < r:=by omega
      have body : ∃ t,t ≤ 128*(v+1)*(P+16) ∧ PPath k lo P t
          (pNode (st k (if side then 1180 else 1239)) (D (if side then 1 else 8)) (halfPhase T D side v u))
          (pNode (st k (if !side then 1180 else 1239)) (D (if !side then 1 else 8)) (halfPhase T D (!side) (v/2) (u+1))) := by
        cases side
        · obtain ⟨t,price,path⟩:=positiveHalf (rightHalf k) _ grid0 (by decide) (by decide)
            (by decide) (by decide) (by decide) n r v u lenB lenA lenC lower upper
            unary.2.1 unary.1 unary.2.2 positive vf room
          change PPath k lo P t _ (pNode (st k 1180) (D 1) (image3 (halfPhase T D false v u) D 8 1 2 0 (v/2) (u+1))) at path
          rw [phase_right grid v u] at path
          exact ⟨t,price,path⟩
        · obtain ⟨t,price,path⟩:=positiveHalf (leftHalf k) _ grid0 (by decide) (by decide)
            (by decide) (by decide) (by decide) n r v u lenA lenB lenC lower upper
            unary.1 unary.2.1 unary.2.2 positive vf room
          change PPath k lo P t _ (pNode (st k 1239) (D 8) (image3 (halfPhase T D true v u) D 1 8 2 0 (v/2) (u+1))) at path
          rw [phase_left T D v u] at path
          exact ⟨t,price,path⟩
      obtain ⟨t0,h0,path0⟩:=body
      have small : v/2 < v:=Nat.div_lt_self positive (by decide)
      obtain ⟨t1,h1,path1⟩:=ih (v/2) small (!side) (u+1) (by omega) (by omega)
      have eq : u+1+bitLength (v/2)=u+bitLength v:=by omega
      rw [eq] at path1
      refine ⟨_,?_,pAppend path0 path1⟩
      have halfBound : 2*(v/2) ≤ v:=by omega
      nlinarith only [h0,h1,halfBound,positive]
end FullIngressClosure
