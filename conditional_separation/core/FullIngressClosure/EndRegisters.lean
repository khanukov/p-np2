import Complexity.PrivateInterfaceLookupResolvedFinish
import FullIngressClosure.SourceSkipDriver
import FullIngressClosure.CounterFront
import FullIngressClosure.FinishPrepared
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateFinish.bindings `FullIngressClosure.EndRegisters
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated finish-frame identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private theorem skip_original {D T a v u} (av : BankUnary D T a v) (au : BankUnary D T 7 u) :
    skipTape T D a v u=T := by
  dsimp only [skipTape]
  rw [bankOriginal av,bankOriginal au]
private theorem end9_registers {D T g ell W n r residue}
    (frame : Registers D T (counterValues g ell W n r)) :
    Registers D (skipTape (setBank T D 10 0) D 9 residue 0) (endValues n g W 0 residue W) := by
  have done:=registersSet (registersSet (registersSet frame 10 0 (by decide)) 9 residue (by decide)) 7 0 (by decide)
  refine registersMk (registerGrid done) ?_
  intro j hj
  have h:=registerUnary done j hj
  have eq : Function.update (Function.update (Function.update (counterValues g ell W n r) 10 0) 9 residue) 7 0 j=endValues n g W 0 residue W j:=by
    interval_cases j <;> rfl
  rwa [eq] at h
private theorem end11_registers {D T g ell W n r anchor1 anchor2 residue}
    (frame : Registers D T (counterValues g ell W n r)) :
    Registers D (skipTape (skipTape (setBank T D 10 0) D 9 0 anchor1) D 11 residue anchor2)
      (endValues n g W anchor2 0 residue) := by
  have done:=registersSet (registersSet (registersSet (registersSet (registersSet frame 10 0 (by decide)) 9 0 (by decide)) 7 anchor1 (by decide)) 11 residue (by decide)) 7 anchor2 (by decide)
  refine registersMk (registerGrid done) ?_
  intro j hj
  have h:=registerUnary done j hj
  have eq : Function.update (Function.update (Function.update (Function.update (Function.update (counterValues g ell W n r) 10 0) 9 0) 7 anchor1) 11 residue) 7 anchor2 j=endValues n g W anchor2 0 residue j:=by
    interval_cases j <;> rfl
  rwa [eq] at h
end FullIngressClosure
