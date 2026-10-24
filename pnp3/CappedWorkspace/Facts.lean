import CappedWorkspace.Rows
namespace CappedWorkspace
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
private theorem zero_list (bs : List Bool) (hz : Body.value bs=0) : bs=List.replicate bs.length false := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · have hv : Body.value bs=0 := by simpa [Body.value] using hz
      simp only [List.length_cons,List.replicate_succ]
      exact congrArg (List.cons false) (ih hv)
    · have pos : 0 < 2^bs.length := by positivity
      simp only [Body.value,Bool.toNat_true] at hz
      omega
/-- Semantic fact used only to identify the assignment left by the executed Stream overflow. -/
theorem overflow_bits (n : Nat) : Body.iterBits (List.replicate n false) (2^n)=List.replicate n false := by
  run_tac do
    let names := (← getEnv).constants.toList.map Prod.fst
    let get (s : String) := mkIdent ((names.find? fun name =>
      name.toString.startsWith "_private.Stream.Kernel." && name.toString.endsWith (".Stream."++s)).get!)
    let current := get "current_value"; let over := get "last_overflow"; let succ := get "iter_succ"
    let nv := mkIdent `n
    evalTactic (← `(tactic| (
      let r := 2^$nv:ident-1
      have pos : 0 < 2^$nv:ident := by positivity
      have hlt : r < 2^$nv:ident := by dsimp only [r]; omega
      have last : r+1=2^$nv:ident := by dsimp only [r]; omega
      have ov := $over:ident $nv:ident r hlt last
      have val := Body.inc_value (Body.iterBits (List.replicate $nv:ident false) r)
      rw [$current:ident $nv:ident r hlt,Body.iter_length,List.length_replicate,ov] at val
      simp only [↓reduceIte] at val
      have step := $succ:ident (List.replicate $nv:ident false) r
      rw [last] at step
      have zero : Body.value (Body.iterBits (List.replicate $nv:ident false) (2^$nv:ident))=0 := by
        rw [step]
        simpa only [↓reduceIte] using (show Body.value (Body.inc (Body.iterBits (List.replicate $nv:ident false) r)).1=0 by omega)
      simpa only [Body.iter_length,List.length_replicate] using zero_list _ zero)))
end CappedWorkspace
