import VirtualReady.Raw
import CappedWeight.Target
open Pnp3.Complexity.Uniform.V1
#check (Cursor.machine : Nat → UniformTM)
#check (CappedWeight.Target.image : (Nat → Option Bool) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option Bool)
open Lean in
run_cmd do
  logInfo m!"registered-option|maxHeartbeats|{Lean.maxHeartbeats.get (← getOptions)}"
  logInfo m!"registered-option|maxRecDepth|{Lean.maxRecDepth.get (← getOptions)}"
