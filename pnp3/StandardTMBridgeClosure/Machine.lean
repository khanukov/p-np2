import StandardTMBridgeClosure.Joint
namespace StandardTMBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing
/-- Fixed pointwise, length-preserving encoding; the origin track is initialized
by the actual boot row, including empty input. -/
def encode (x : List Bool) : List (Bool × Option Bool) :=
  x.map (fun b=>(false,some b))
private def phase : Move → Fin 4
  | .left=>1 | .stay=>2 | .right=>3
/-- One boot row, then write/move pairs. Only finite symbols and finite labels
occur in the table. No input length, allocation, head coordinate or proof is data. -/
def compile (M : UniformTM) :
    TM0.Machine (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)) :=
  fun q a=>match q with
  | none=>some (some (M.start,0),TM0.Stmt.write (true,a.2))
  | some (s,p)=>
    if p=0 then
      if s=M.accept ∨ s=M.reject then none
      else
        let action:=M.step s a.2
        some (some (action.1,phase action.2.2),TM0.Stmt.write (a.1,action.2.1))
    else if p=1 then
      some (some (s,0),if a.1 then TM0.Stmt.write a else TM0.Stmt.move .left)
    else if p=2 then some (some (s,0),TM0.Stmt.write a)
    else some (some (s,0),TM0.Stmt.move .right)
/-- Exact finite iteration of real library steps. A halted configuration has no
positive-length execution; this iterator does not pad a halted trace. -/
def steps (M : UniformTM) : Nat →
    TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)) →
    Option (TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)))
  | 0,c=>some c
  | n+1,c=>(TM0.step (compile M) c).bind (steps M n)
/-- Whole unbounded tape, relative to its real head. This is proof-only ghost
correspondence; no such coordinate or finite tape is supplied to `compile`. -/
def Represents (M : UniformTM) {N B : Nat} (c : Config M.stateCount N B)
    (d : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4))) : Prop :=
  d.q=some (c.state,0) ∧ ∀ i : Int,
    d.Tape.nth i=
      if h:0 ≤ (c.head.val : Int)+i ∧ (c.head.val : Int)+i < (tapeLength N B : Int)
      then (decide ((c.head.val : Int)+i=0),
        c.tape ⟨((c.head.val : Int)+i).toNat,by omega⟩)
      else (false,none)
end StandardTMBridgeClosure
