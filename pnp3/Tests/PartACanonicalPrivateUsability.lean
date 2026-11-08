import Tests.PartACanonicalABI
import Tests.PartACanonicalPrivateFamilies
import Tests.PartACanonicalPrivateSmoke
import Tests.PartACanonicalCursorABI

/-! Infrastructure: construct a one-edge private path from its original Edge
value, then apply the full private execute interface. This tests usable typed
constructors and preserves every safety premise carried by the original Edge. -/
open Pnp3.Complexity.Uniform.V1
set_option autoImplicit false
namespace PartACanonical.PrivateUsability

namespace SmallIngress
open PartACanonical.PrivateFamilies.SmallIngress
noncomputable abbrev before {M : UniformTM} {P : Nat} {c d : Node M}
    (edge : Edge P c d) : head c ≤ P := (partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Edge.before" owner% "SmallIngress.Runtime") edge
noncomputable abbrev after {M : UniformTM} {P : Nat} {c d : Node M}
    (edge : Edge P c d) : head d ≤ P := (partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Edge.after" owner% "SmallIngress.Runtime") edge
theorem onePath {M : UniformTM} {P : Nat} {c d : Node M} (edge : Edge P c d) : Path P 1 c d := by
  exact (partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Path.cons" owner% "SmallIngress.Runtime") edge (nil P d (after edge))
theorem oneExecute {M : UniformTM} {N B P : Nat} {c d : Node M}
    (edge : Edge P c d) (room : P < tapeLength N B) :
    M.run 1 (embed c (lt_of_le_of_lt (before edge) room)) =
      embed d (lt_of_le_of_lt (after edge) room) := by
  exact execute (onePath edge) room
end SmallIngress

namespace SmallOrbit
open PartACanonical.PrivateFamilies.SmallOrbit
noncomputable abbrev before {M : UniformTM} {P : Nat} {c d : Node M}
    (edge : Edge P c d) : head c ≤ P := (partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Edge.before" owner% "SmallOrbit.Runtime") edge
noncomputable abbrev after {M : UniformTM} {P : Nat} {c d : Node M}
    (edge : Edge P c d) : head d ≤ P := (partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Edge.after" owner% "SmallOrbit.Runtime") edge
theorem onePath {M : UniformTM} {P : Nat} {c d : Node M} (edge : Edge P c d) : Path P 1 c d := by
  exact (partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Path.cons" owner% "SmallOrbit.Runtime") edge (nil P d (after edge))
theorem oneExecute {M : UniformTM} {N B P : Nat} {c d : Node M}
    (edge : Edge P c d) (room : P < tapeLength N B) :
    M.run 1 (embed c (lt_of_le_of_lt (before edge) room)) =
      embed d (lt_of_le_of_lt (after edge) room) := by
  exact execute (onePath edge) room
end SmallOrbit

namespace SuffixCap
open PartACanonical.PrivateFamilies.SuffixCap
noncomputable abbrev before {k P : Nat} {c d : Node k}
    (edge : Edge k P c d) : head c ≤ P := (partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Edge.before" owner% "SuffixCap.Kernel") edge
noncomputable abbrev after {k P : Nat} {c d : Node k}
    (edge : Edge k P c d) : head d ≤ P := (partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Edge.after" owner% "SuffixCap.Kernel") edge
theorem onePath {k P : Nat} {c d : Node k} (edge : Edge k P c d) : Path k P 1 c d := by
  exact (partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Path.cons" owner% "SuffixCap.Kernel") edge (nil k P d (after edge))
theorem oneExecute {k N B P : Nat} {c d : Node k}
    (edge : Edge k P c d) (room : P < tapeLength N B) :
    (Cursor.machine k).run 1 (embed c (lt_of_le_of_lt (before edge) room)) =
      embed d (lt_of_le_of_lt (after edge) room) := by
  exact execute (onePath edge) room
end SuffixCap

namespace CappedWorkspace
open PartACanonical.PrivateFamilies.CappedWorkspace
noncomputable abbrev before {k P : Nat} {c d : Node k}
    (edge : Edge k P c d) : head c ≤ P := (partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Edge.before" owner% "CappedWorkspace.Kernel") edge
noncomputable abbrev after {k P : Nat} {c d : Node k}
    (edge : Edge k P c d) : head d ≤ P := (partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Edge.after" owner% "CappedWorkspace.Kernel") edge
theorem onePath {k P : Nat} {c d : Node k} (edge : Edge k P c d) : Path k P 1 c d := by
  exact (partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.cons" owner% "CappedWorkspace.Kernel") edge (nil k P d (after edge))
theorem oneExecute {k N B P : Nat} {c d : Node k}
    (edge : Edge k P c d) (room : P < tapeLength N B) :
    (Cursor.machine k).run 1 (embed c (lt_of_le_of_lt (before edge) room)) =
      embed d (lt_of_le_of_lt (after edge) room) := by
  exact execute (onePath edge) room
end CappedWorkspace

end PartACanonical.PrivateUsability

#print axioms PartACanonical.PrivateUsability.SmallIngress.oneExecute
#print axioms PartACanonical.PrivateUsability.SmallOrbit.oneExecute
#print axioms PartACanonical.PrivateUsability.SuffixCap.oneExecute
#print axioms PartACanonical.PrivateUsability.CappedWorkspace.oneExecute


/-! Internal named usability assertions, not a new public API. They consume the
unchanged private Stream ABI, including a nonzero path and a concrete entry node.
Original public dependencies retain their visibility and full literal contracts. -/
namespace PartACanonical.PrivateUsability.Stream
open PartACanonical.PrivateMini

private noncomputable abbrev Edge : Nat → StreamNode → StreamNode → Prop :=
  partA_private% "_private.Stream.Kernel.0.Stream.Edge" owner% "Stream.Kernel"
private noncomputable abbrev before {P : Nat} {c d : StreamNode}
    (edge : Edge P c d) : streamHead c ≤ P :=
  (partA_private% "_private.Stream.Kernel.0.Stream.Edge.before" owner% "Stream.Kernel") edge
private noncomputable abbrev after {P : Nat} {c d : StreamNode}
    (edge : Edge P c d) : streamHead d ≤ P :=
  (partA_private% "_private.Stream.Kernel.0.Stream.Edge.after" owner% "Stream.Kernel") edge
private theorem onePath {P : Nat} {c d : StreamNode} (edge : Edge P c d) :
    StreamPath P 1 c d := by
  exact (partA_private% "_private.Stream.Kernel.0.Stream.Path.cons" owner% "Stream.Kernel")
    edge (streamNil P d (after edge))
private theorem oneExecute {N B P : Nat} {c d : StreamNode}
    (edge : Edge P c d) (room : P < tapeLength N B) :
    Stream.machine.run 1 (streamEmbed c (lt_of_le_of_lt (before edge) room)) =
      streamEmbed d (lt_of_le_of_lt (after edge) room) := by
  exact streamExecute (onePath edge) room

private noncomputable def sampleNode : StreamNode :=
  PartACanonical.PrivateABI.a0061 (fun _ => none) 0 0 0 0 0
private theorem samplePath :
    StreamPath (streamHead sampleNode) 0 sampleNode sampleNode := by
  exact streamNil (streamHead sampleNode) sampleNode le_rfl
private theorem sampleExecute {N B : Nat}
    (room : streamHead sampleNode < tapeLength N B) :
    Stream.machine.run 0 (streamEmbed sampleNode room) = streamEmbed sampleNode room := by
  exact streamExecute samplePath room

end PartACanonical.PrivateUsability.Stream
