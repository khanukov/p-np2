import Complexity.Uniform.V1.FixedRawLengthFence
import Complexity.Uniform.V1.FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown

/-!
# Raw fence installation followed by the existing G3q machine (G3r)

Infrastructure only. Sequential composition consumes the actual full initializer
configuration at its first acceptance. The suffix is the unchanged G3q table on
the fenced tape; this is not a preservation theorem for that tape through G3q.
No overflow rejection, parser identification, whole-verifier clock, acceptance
comparison or P-vs-NP source obligation is discharged here.
-/
namespace Pnp3.Complexity.Uniform.V1.FixedRawLengthFence

abbrev G : UniformTM := FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.machine
def prefixed : UniformTM := machine.seq G
def g3qEntry {R : Nat} (B : Nat) (input : Bitstring R) : Config G.stateCount R B :=
  ⟨G.start, ⟨0, by simp [tapeLength]⟩, fenceTape B input⟩

set_option maxRecDepth 40000 in
/-- The composed table and literal G3q entry. Reaching entry is neither verdict. -/
theorem prefixed_pins :
    prefixed.stateCount = 256 ∧ Fintype.card (Fin prefixed.stateCount × Option Bool) = 768 ∧
    prefixed.start.val = 0 ∧ prefixed.accept.val = 254 ∧ prefixed.reject.val = 255 ∧
    (machine.seqRight G G.start).val = 48 := by
  repeat' apply And.intro
  all_goals rfl

/-- Real sequential execution from raw input, at any sufficient physical allocation. -/
theorem fence_handoff_exact {R B : Nat} (input : Bitstring R)
    (hroom : 2*R+2 ≤ B) (s : Nat) :
    prefixed.run (installClock R+s) (initialConfig prefixed B input) =
      machine.seqEmbedRight G (G.run s (g3qEntry B input)) := by
  have h := machine.seq_handoff G (initialConfig machine B input) (T := installClock R)
    (fun t ht => ((install_trace input hroom).1 t ht).1)
    (by rw [install_exact input hroom]; rfl) s
  rw [install_exact input hroom] at h
  exact h

/-- Hypothesis-free raw capstone: full configuration equality at every suffix time. -/
theorem raw_fence_handoff_exact {R : Nat} (input : Bitstring R) (s : Nat) :
    prefixed.run (installClock R+s) (initialConfig prefixed (allocation R) input) =
      machine.seqEmbedRight G (G.run s (g3qEntry (allocation R) input)) :=
  fence_handoff_exact input (resource_bounds R).1 s

end Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
