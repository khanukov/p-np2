/-
  mistral_test/SourceTheorems/ConcreteFamily.lean
  
  Concrete gap slice family for the P≠NP proof.
  
  Uses minimal circuit size bounds (sYES = 1, sNO = 2) to satisfy
  circuit_bound_ok: circuitCountBound n (sNO-1) = circuitCountBound n 1 < 2^(2^n/2)
-/
import MistralTestLib.SourceTheorems.CircuitBound
import Pnp3.LowerBounds.MCSPGapLocality

namespace MistralTestLib

open Pnp3.Models Pnp3.LowerBounds Pnp3.Core

/-!
Minimal parameters for concrete family.
- sYES = 1: smallest non-degenerate YES threshold (Circuit.const has size 1)
- sNO = 2: so sYES + 1 = 2 ≤ sNO ✓
- circuit_bound_ok: circuitCountBound n 1 < 2^(2^n/2) by circuit_bound_ok_minimal
- n_ge = 8: starting index
-/
def baseParams (n : Nat) (hn : n ≥ 8) : GapPartialMCSPParams where
  n := n
  sYES := 1
  sNO := 2
  gap_ok := by omega
  n_ge := hn
  sYES_pos := by norm_num
  circuit_bound_ok := CircuitBound.circuit_bound_ok_minimal n hn

def concreteFamily : GapSliceFamilyEventually where
  N0 := 8
  paramsOf n β := baseParams n (by omega)
  Tof n β := 1  -- = sNO - 1 = 2 - 1
  Mof n s := circuitCountBound n s
  hIndex n hn β := by simp [baseParams]
  hT n hn β := by simp [baseParams]; omega
  hM n hn T := by simp [circuitCountBound]

end MistralTestLib
