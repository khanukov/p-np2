import VirtualFinalClosure.LengthConnected
import VirtualFinalClosure.GrowDispatch
namespace VirtualFinalClosure.LengthGrowFrame
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked",(0:Nat)),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","unary","unary",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","lifted","lifted",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.defnInfo ci)]=>
      unless kind=0 do throwError "Wrong physical length-growth image kind {name}"
      logInfo m!"private-term|{name}|kind=definition|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique physical length-growth image {mod}/{key}"
private theorem banks (V : Nat → Option Bool) (L n F r : Nat) (room : L+n+1 < F)
    (fresh : ∀ i,F < i → i ≤ F+5*r+n+7 → V i=none) :
    let Y:=RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    (∀ j,j ≤ 6 → Y (SerializedBody.delimiter F r n j)=none) ∧
    (∀ j,j < 6 → ∀ i,SerializedBody.delimiter F r n j < i →
      i < SerializedBody.delimiter F r n (j+1) → ∃ b,Y i=some b) := by
  intro Y
  have tally : min (bitLength n) r ≤ r := Nat.min_le_right _ _
  constructor
  · intro j hj
    interval_cases j <;>
      dsimp only [Y,SerializedBody.delimiter,RuntimeBitLength.Target.fullImage,
        CappedWorkspace.Target.image,SuffixCap.Target.image] <;>
      rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
        if_neg (by omega),if_neg (by omega)] <;>
      exact fresh _ (by omega) (by omega)
  · intro j hj i lo hi
    interval_cases j <;>
      dsimp only [SerializedBody.delimiter] at lo hi <;>
      dsimp only [Y,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image] <;>
      split_ifs <;> first | exact ⟨_,rfl⟩ | omega
/-- Marker writes preserve all six observed delimiters and occupied fields.
The only extra source edit is below S, strictly below the workspace. -/
private theorem marked_banks (T : Nat → Option Bool) (F r S n : Nat) (source : S ≤ F)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F r n j)=none)
    (occupied : ∀ j,j < 6 → ∀ i,SerializedBody.delimiter F r n j < i →
      i < SerializedBody.delimiter F r n (j+1) → ∃ b,T i=some b) :
    (∀ j,j ≤ 6 → marked T F r S r (SerializedBody.delimiter F r n j)=none) ∧
    (∀ j,j < 6 → ∀ i,SerializedBody.delimiter F r n j < i →
      i < SerializedBody.delimiter F r n (j+1) → ∃ b,marked T F r S r i=some b) := by
  have lower (j : Nat) (hj : j ≤ 6) : F < SerializedBody.delimiter F r n j := by
    interval_cases j <;> dsimp only [SerializedBody.delimiter] <;> omega
  have before (j : Nat) (hj : j < 6) : F+1 ≤ SerializedBody.delimiter F r n j := by
    have h:=lower j (by omega)
    omega
  constructor
  · intro j hj
    have lo:=lower j hj
    have outside : ¬(F+1 < SerializedBody.delimiter F r n j ∧
        SerializedBody.delimiter F r n j < F+1+r+1) := by
      interval_cases j <;> dsimp only [SerializedBody.delimiter] <;> omega
    dsimp only [marked,unary,lifted]
    rw [if_neg outside,if_neg (by omega)]
    exact blank j hj
  · intro j hj i lo hi
    have start:=before j hj
    dsimp only [marked,unary,lifted]
    by_cases bank : F+1 < i ∧ i < F+1+r+1
    · rw [if_pos bank]
      exact ⟨_,rfl⟩
    · rw [if_neg bank,if_neg (by omega)]
      exact occupied j hj i lo hi
#print axioms banks
#print axioms marked_banks
end VirtualFinalClosure.LengthGrowFrame
