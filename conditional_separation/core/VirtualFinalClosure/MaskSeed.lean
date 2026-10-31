import VirtualFinalClosure.SeedAndWeight
namespace VirtualFinalClosure.MaskSeed
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (key,aliasName,kind) in [("masked","masked",(0:Nat)),("masked_low","maskedLow",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.LengthBanks." && name.toString.endsWith (".VirtualFinalClosure.LengthBanks."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong exact mask/seed image interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique exact mask/seed interface {key}"
/-- Actual blank extension commutes with these bounded physical writes;
this is whole-tape equality, not a transported execution from endpoint alone. -/
private theorem full (V : Nat → Option Bool) (L n F r bound : Nat)
    (room : L+n+1 < F) (fit : F+5*r+n+7 < bound) :
    masked (RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r) bound=
      RuntimeBitLength.Target.fullImage
        (CappedWorkspace.Target.image (SuffixCap.Target.image (masked V bound) F r) L n F r) L n F r := by
  funext i
  by_cases low : i < bound
  · rw [maskedLow _ bound i low]
    dsimp only [RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
    rw [maskedLow V bound i low]
  · have count:=Nat.min_le_right (bitLength n) r
    dsimp only [masked,RuntimeBitLength.Target.fullImage,CappedWorkspace.Target.image,SuffixCap.Target.image]
    rw [if_neg low,if_neg (by omega),if_neg (by omega),if_neg (by omega),
      if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg low]
private theorem seed (Y : Nat → Option Bool) (F r n bound : Nat)
    (fit : F+5*r+n+7 < bound) :
    AllArityBitLength.Target.seedImage (masked Y bound) F r n=
      masked (AllArityBitLength.Target.seedImage Y F r n) bound := by
  funext i
  by_cases hit : i=F+2*r+n+5
  · subst i
    have low : F+2*r+n+5 < bound:=by omega
    dsimp only [AllArityBitLength.Target.seedImage,masked]
    rw [if_pos rfl,if_pos low,if_pos rfl]
  · dsimp only [AllArityBitLength.Target.seedImage,masked]
    rw [if_neg hit]
    split_ifs <;> rfl
#print axioms full
#print axioms seed
end VirtualFinalClosure.MaskSeed
