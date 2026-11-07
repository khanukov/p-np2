import VirtualFinalClosure.ElasticMachine
namespace VirtualFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("candidateMachine","elasticCandidate"),("pack","elasticPack")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith "_private.VirtualFinalClosure.ElasticMachine." &&
      n.toString.endsWith (".VirtualFinalClosure.Elastic."++key)
    match found with
    | [(n,.defnInfo ci)]=>
      logInfo m!"private-term|{n}|kind=definition|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique fixed native candidate {key}"
/-- Fixed once for k. No input-dependent operand or proof is passed to the ROM. -/
def machine (k : Nat) : UniformTM := elasticCandidate k
/-- Finite-control embedding with an explicit varying runtime flag/mode. -/
def control (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) (m : Fin 144) :
    Fin (machine k).stateCount := elasticPack k s.val m.val
/-- Mathematical whole-Config map at a specified finite mode, not an execution. -/
def config (k : Nat) {N B : Nat} (m : Fin 144)
    (c : Config (CertificateGuardClosure.machine k).stateCount N B) :
    Config (machine k).stateCount N B := ⟨control k c.state m,c.head,c.tape⟩
/-- The additional unary arithmetic has polynomial size at each fixed k. -/
def allocation (k N : Nat) : Nat := 281474976710656*(k+1)^4*(N+1)^(k+12)
def deadline (k N : Nat) : Nat := 18446744073709551616*(k+1)^8*(N+1)^(4*k+24)
def spaceBound (k N : Nat) : Nat := 1048576*(k+1)^2*(N+1)^(k+3)
private def machine_type : Nat → UniformTM := machine
private def control_type : ∀ k,Fin (CertificateGuardClosure.machine k).stateCount → Fin 144 →
    Fin (machine k).stateCount := control
private def config_type : ∀ k,{N B : Nat} → Fin 144 →
    Config (CertificateGuardClosure.machine k).stateCount N B → Config (machine k).stateCount N B := config
private def allocation_type : Nat → Nat → Nat := allocation
private def deadline_type : Nat → Nat → Nat := deadline
private def spaceBound_type : Nat → Nat → Nat := spaceBound
#print axioms machine
#print axioms control
#print axioms config
#print axioms allocation
#print axioms deadline
#print axioms spaceBound
#print axioms machine_type
#print axioms control_type
#print axioms config_type
#print axioms allocation_type
#print axioms deadline_type
#print axioms spaceBound_type
end VirtualFinalClosure
