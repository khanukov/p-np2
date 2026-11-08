import Stream.Kernel
import Tests.PartACanonicalSupport

/-! Infrastructure private-owner usability prototype. These transparent typed
links retain the original Stream.Kernel owners and private numbering. A private
Path is constructed and consumed to prove the entire Config execution equation.
This does not copy the private proof graph or establish a new raw verifier. -/
namespace PartACanonical.PrivateMini
open Pnp3.Complexity.Uniform.V1
set_option autoImplicit false

abbrev StreamNode : Type :=
  partA_private% "_private.Stream.Kernel.0.Stream.Node" owner% "Stream.Kernel"
abbrev streamHead : StreamNode → Nat :=
  partA_private% "_private.Stream.Kernel.0.Stream.Node.head" owner% "Stream.Kernel"
abbrev StreamPath : Nat → Nat → StreamNode → StreamNode → Prop :=
  partA_private% "_private.Stream.Kernel.0.Stream.Path" owner% "Stream.Kernel"
abbrev StreamArena : (Nat → Option Bool) → Nat → Nat → Nat → Nat → Nat → Prop :=
  partA_private% "_private.Stream.Kernel.0.Stream.Arena" owner% "Stream.Kernel"
abbrev streamEmbed {N B : Nat} (c : StreamNode)
    (room : streamHead c < tapeLength N B) : Config 64 N B :=
  (partA_private% "_private.Stream.Kernel.0.Stream.embed" owner% "Stream.Kernel") c room
abbrev streamBounds {P t : Nat} {c d : StreamNode} (h : StreamPath P t c d) :
    streamHead c ≤ P ∧ streamHead d ≤ P :=
  (partA_private% "_private.Stream.Kernel.0.Stream.Path.bounds" owner% "Stream.Kernel") h
abbrev streamNil : ∀ (P : Nat) (c : StreamNode), streamHead c ≤ P → StreamPath P 0 c c :=
  partA_private% "_private.Stream.Kernel.0.Stream.Path.nil" owner% "Stream.Kernel"

abbrev streamExecute {N B P t c d} (h : StreamPath P t c d) (hp : P < tapeLength N B) :
    Stream.machine.run t (streamEmbed c (lt_of_le_of_lt (streamBounds h).1 hp)) =
      streamEmbed d (lt_of_le_of_lt (streamBounds h).2 hp) :=
  (partA_private% "_private.Stream.Kernel.0.Stream.Path.execute" owner% "Stream.Kernel") h hp

theorem stream_execute_use {N B P t c d} (h : StreamPath P t c d) (hp : P < tapeLength N B) :
    Stream.machine.run t (streamEmbed c (lt_of_le_of_lt (streamBounds h).1 hp)) =
      streamEmbed d (lt_of_le_of_lt (streamBounds h).2 hp) := by
  exact streamExecute h hp

theorem stream_zero_path (P : Nat) (c : StreamNode) (hc : streamHead c ≤ P) :
    StreamPath P 0 c c := streamNil P c hc

theorem stream_zero_execute {N B P : Nat} (c : StreamNode)
    (hc : streamHead c ≤ P) (hp : P < tapeLength N B) :
    Stream.machine.run 0 (streamEmbed c (lt_of_le_of_lt hc hp)) =
      streamEmbed c (lt_of_le_of_lt hc hp) := by
  exact streamExecute (streamNil P c hc) hp

#check (StreamNode : Type)
#check (StreamPath : Nat → Nat → StreamNode → StreamNode → Prop)
#check (StreamArena : (Nat → Option Bool) → Nat → Nat → Nat → Nat → Nat → Prop)
#print axioms StreamNode
#print axioms StreamPath
#print axioms StreamArena
#print axioms stream_execute_use
#print axioms stream_zero_path
#print axioms stream_zero_execute
end PartACanonical.PrivateMini
