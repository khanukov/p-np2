import VirtualFinalClosure.CapImageFrame
import VirtualFinalClosure.GrowDouble
namespace VirtualFinalClosure.CapGrowImage
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","marked"),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","unary","unary"),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","lifted","lifted"),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled"),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.defnInfo ci)]=>
      logInfo m!"private-term|{name}|kind=definition|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual cap-reset image term {mod}/{key}"
/-- The real reset/double/assignment-paint sequence erases ALL four cap
residual layouts, including a dirty assignment. The fixed base T and original
source hole remain identical to the shared elln-growth path, pointwise. This
is a tape equality used AFTER actual execution, not a proof-side installer. -/
private theorem erase (T : Nat → Option Bool) (S L n F r a b c d e : Nat)
    (room : L+n+1 < F) :
    block (doubled (marked (CappedWeight.Target.image (AllArityBitLength.Target.seedImage T F r n)
      L n F r a b c d e) F r S r) F r n) (L+1) n (some false)=
    block (doubled (marked T F r S r) F r n) (L+1) n (some false):=by
  funext i
  by_cases assignment : L+1 ≤ i ∧ i < L+1+n
  · dsimp only [block]
    rw [if_pos assignment,if_pos assignment]
  · dsimp only [block]
    rw [if_neg assignment,if_neg assignment]
    by_cases grow : F+1 < i ∧ i < F+2*r+2
    · dsimp only [doubled]
      rw [if_pos grow,if_pos grow]
    · dsimp only [doubled]
      rw [if_neg grow,if_neg grow]
      by_cases cleared : F+2*r+2 ≤ i ∧ i ≤ F+5*r+n+7
      · rw [if_pos cleared,if_pos cleared]
      · rw [if_neg cleared,if_neg cleared]
        dsimp only [marked,unary]
        rw [if_neg (by omega),if_neg (by omega)]
        dsimp only [lifted]
        split_ifs
        · rfl
        · dsimp only [CappedWeight.Target.image,AllArityBitLength.Target.seedImage]
          rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
#print axioms erase
end VirtualFinalClosure.CapGrowImage
