import VirtualFinalClosure.Finite
namespace VirtualFinalClosure.ConfigStay
open Pnp3.Complexity.Uniform.V1
set_option autoImplicit false
/-- Ordinary generic one-edge execution, with a SYMBOLIC machine. Keeping this
term separate avoids normalizing a large concrete ROM inside Config extensionality. -/
private theorem one {M : UniformTM} {N B : Nat} (q q' : Fin M.stateCount)
    (h : Fin (tapeLength N B)) (T : Fin (tapeLength N B) → Option Bool)
    (row : M.step q (T h)=(q',T h,.stay)) :
    M.run 1 ⟨q,h,T⟩=⟨q',h,T⟩:=by
  change M.stepConfig _=_
  apply Config.ext_parts
  · exact congrArg Prod.fst row
  · change moveHead h (M.step q (T h)).2.2=h
    rw [row]
    rfl
  · funext j
    change (if j=h then (M.step q (T h)).2.1 else T j)=T j
    rw [row]
    by_cases same : j=h
    · rw [if_pos same,same]
    · rw [if_neg same]
#print axioms one
end VirtualFinalClosure.ConfigStay
