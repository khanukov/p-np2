import Tests.PartACanonicalSupport
import SmallOrbit.Runtime
import SuffixCap.Kernel
import CappedWorkspace.Kernel

/-! Infrastructure: usable consumers of the exact private path ABI. Every link
has a literal expected type; executeUse and zeroExecute apply it to entire Config
equalities. No original private owner, numeric component or proof is renamed. -/
open Pnp3.Complexity.Uniform.V1
set_option autoImplicit false
namespace PartACanonical.PrivateFamilies

namespace SmallIngress
noncomputable abbrev Node : UniformTM → Type := @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Node" owner% "SmallIngress.Runtime")
noncomputable abbrev head : {M : UniformTM} → Node M → Nat := @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Node.head" owner% "SmallIngress.Runtime")
noncomputable abbrev Edge : {M : UniformTM} → Nat → Node M → Node M → Prop := @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Edge" owner% "SmallIngress.Runtime")
noncomputable abbrev Path : {M : UniformTM} → Nat → Nat → Node M → Node M → Prop := @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Path" owner% "SmallIngress.Runtime")
noncomputable abbrev embed {M : UniformTM} {N B : Nat} (c : Node M)
    (room : head c < tapeLength N B) : Config M.stateCount N B :=
  (partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.embed" owner% "SmallIngress.Runtime") c room
noncomputable abbrev bounds {M : UniformTM} {P t : Nat} {c d : Node M}
    (h : Path P t c d) : head c ≤ P ∧ head d ≤ P := (partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Path.bounds" owner% "SmallIngress.Runtime") h
noncomputable abbrev nil {M : UniformTM} (P : Nat) (c : Node M) (h : head c ≤ P) : Path P 0 c c :=
  (partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Path.nil" owner% "SmallIngress.Runtime") c h
noncomputable abbrev execute {M : UniformTM} {N B P t : Nat} {c d : Node M}
    (h : Path P t c d) (hp : P < tapeLength N B) :
    M.run t (embed c (lt_of_le_of_lt (bounds h).1 hp)) =
      embed d (lt_of_le_of_lt (bounds h).2 hp) := (partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Path.execute" owner% "SmallIngress.Runtime") h hp
theorem executeUse {M : UniformTM} {N B P t : Nat} {c d : Node M}
    (h : Path P t c d) (hp : P < tapeLength N B) :
    M.run t (embed c (lt_of_le_of_lt (bounds h).1 hp)) =
      embed d (lt_of_le_of_lt (bounds h).2 hp) := execute h hp
theorem zeroPath {M : UniformTM} (P : Nat) (c : Node M) (h : head c ≤ P) : Path P 0 c c := nil P c h
theorem zeroExecute {M : UniformTM} {N B : Nat} (c : Node M) (room : head c < tapeLength N B) :
    M.run 0 (embed c room) = embed c room := by
  exact execute (zeroPath (head c) c (Nat.le_refl _)) room
end SmallIngress

namespace SmallOrbit
noncomputable abbrev Node : UniformTM → Type := @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Node" owner% "SmallOrbit.Runtime")
noncomputable abbrev head : {M : UniformTM} → Node M → Nat := @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Node.head" owner% "SmallOrbit.Runtime")
noncomputable abbrev Edge : {M : UniformTM} → Nat → Node M → Node M → Prop := @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Edge" owner% "SmallOrbit.Runtime")
noncomputable abbrev Path : {M : UniformTM} → Nat → Nat → Node M → Node M → Prop := @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Path" owner% "SmallOrbit.Runtime")
noncomputable abbrev embed {M : UniformTM} {N B : Nat} (c : Node M)
    (room : head c < tapeLength N B) : Config M.stateCount N B :=
  (partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.embed" owner% "SmallOrbit.Runtime") c room
noncomputable abbrev bounds {M : UniformTM} {P t : Nat} {c d : Node M}
    (h : Path P t c d) : head c ≤ P ∧ head d ≤ P := (partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Path.bounds" owner% "SmallOrbit.Runtime") h
noncomputable abbrev nil {M : UniformTM} (P : Nat) (c : Node M) (h : head c ≤ P) : Path P 0 c c :=
  (partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Path.nil" owner% "SmallOrbit.Runtime") c h
noncomputable abbrev execute {M : UniformTM} {N B P t : Nat} {c d : Node M}
    (h : Path P t c d) (hp : P < tapeLength N B) :
    M.run t (embed c (lt_of_le_of_lt (bounds h).1 hp)) =
      embed d (lt_of_le_of_lt (bounds h).2 hp) := (partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Path.execute" owner% "SmallOrbit.Runtime") h hp
theorem executeUse {M : UniformTM} {N B P t : Nat} {c d : Node M}
    (h : Path P t c d) (hp : P < tapeLength N B) :
    M.run t (embed c (lt_of_le_of_lt (bounds h).1 hp)) =
      embed d (lt_of_le_of_lt (bounds h).2 hp) := execute h hp
theorem zeroPath {M : UniformTM} (P : Nat) (c : Node M) (h : head c ≤ P) : Path P 0 c c := nil P c h
theorem zeroExecute {M : UniformTM} {N B : Nat} (c : Node M) (room : head c < tapeLength N B) :
    M.run 0 (embed c room) = embed c room := by
  exact execute (zeroPath (head c) c (Nat.le_refl _)) room
end SmallOrbit

namespace SuffixCap
noncomputable abbrev Node : Nat → Type := @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Node" owner% "SuffixCap.Kernel")
noncomputable abbrev head : {k : Nat} → Node k → Nat := @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Node.head" owner% "SuffixCap.Kernel")
noncomputable abbrev Edge : (k P : Nat) → Node k → Node k → Prop := @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Edge" owner% "SuffixCap.Kernel")
noncomputable abbrev Path : (k P : Nat) → Nat → Node k → Node k → Prop := @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Path" owner% "SuffixCap.Kernel")
noncomputable abbrev embed {k N B : Nat} (c : Node k)
    (room : head c < tapeLength N B) : Config (Cursor.stateCount k) N B :=
  (partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.embed" owner% "SuffixCap.Kernel") c room
noncomputable abbrev bounds {k P t : Nat} {c d : Node k}
    (h : Path k P t c d) : head c ≤ P ∧ head d ≤ P := (partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Path.bounds" owner% "SuffixCap.Kernel") h
noncomputable abbrev nil (k P : Nat) (c : Node k) (h : head c ≤ P) : Path k P 0 c c :=
  (partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Path.nil" owner% "SuffixCap.Kernel") c h
noncomputable abbrev execute {k N B P t : Nat} {c d : Node k}
    (h : Path k P t c d) (hp : P < tapeLength N B) :
    (Cursor.machine k).run t (embed c (lt_of_le_of_lt (bounds h).1 hp)) =
      embed d (lt_of_le_of_lt (bounds h).2 hp) := (partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Path.execute" owner% "SuffixCap.Kernel") h hp
theorem executeUse {k N B P t : Nat} {c d : Node k}
    (h : Path k P t c d) (hp : P < tapeLength N B) :
    (Cursor.machine k).run t (embed c (lt_of_le_of_lt (bounds h).1 hp)) =
      embed d (lt_of_le_of_lt (bounds h).2 hp) := execute h hp
theorem zeroPath (k P : Nat) (c : Node k) (h : head c ≤ P) : Path k P 0 c c := nil k P c h
theorem zeroExecute {k N B : Nat} (c : Node k) (room : head c < tapeLength N B) :
    (Cursor.machine k).run 0 (embed c room) = embed c room := by
  exact execute (zeroPath k (head c) c (Nat.le_refl _)) room
end SuffixCap

namespace CappedWorkspace
noncomputable abbrev Node : Nat → Type := @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Node" owner% "CappedWorkspace.Kernel")
noncomputable abbrev head : {k : Nat} → Node k → Nat := @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Node.head" owner% "CappedWorkspace.Kernel")
noncomputable abbrev Edge : (k P : Nat) → Node k → Node k → Prop := @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Edge" owner% "CappedWorkspace.Kernel")
noncomputable abbrev Path : (k P : Nat) → Nat → Node k → Node k → Prop := @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Path" owner% "CappedWorkspace.Kernel")
noncomputable abbrev embed {k N B : Nat} (c : Node k)
    (room : head c < tapeLength N B) : Config (Cursor.stateCount k) N B :=
  (partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.embed" owner% "CappedWorkspace.Kernel") c room
noncomputable abbrev bounds {k P t : Nat} {c d : Node k}
    (h : Path k P t c d) : head c ≤ P ∧ head d ≤ P := (partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.bounds" owner% "CappedWorkspace.Kernel") h
noncomputable abbrev nil (k P : Nat) (c : Node k) (h : head c ≤ P) : Path k P 0 c c :=
  (partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.nil" owner% "CappedWorkspace.Kernel") c h
noncomputable abbrev execute {k N B P t : Nat} {c d : Node k}
    (h : Path k P t c d) (hp : P < tapeLength N B) :
    (Cursor.machine k).run t (embed c (lt_of_le_of_lt (bounds h).1 hp)) =
      embed d (lt_of_le_of_lt (bounds h).2 hp) := (partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.execute" owner% "CappedWorkspace.Kernel") h hp
theorem executeUse {k N B P t : Nat} {c d : Node k}
    (h : Path k P t c d) (hp : P < tapeLength N B) :
    (Cursor.machine k).run t (embed c (lt_of_le_of_lt (bounds h).1 hp)) =
      embed d (lt_of_le_of_lt (bounds h).2 hp) := execute h hp
theorem zeroPath (k P : Nat) (c : Node k) (h : head c ≤ P) : Path k P 0 c c := nil k P c h
theorem zeroExecute {k N B : Nat} (c : Node k) (room : head c < tapeLength N B) :
    (Cursor.machine k).run 0 (embed c room) = embed c room := by
  exact execute (zeroPath k (head c) c (Nat.le_refl _)) room
end CappedWorkspace

end PartACanonical.PrivateFamilies

#print axioms PartACanonical.PrivateFamilies.SmallIngress.Node
#print axioms PartACanonical.PrivateFamilies.SmallIngress.Edge
#print axioms PartACanonical.PrivateFamilies.SmallIngress.Path
#print axioms PartACanonical.PrivateFamilies.SmallIngress.executeUse
#print axioms PartACanonical.PrivateFamilies.SmallIngress.zeroPath
#print axioms PartACanonical.PrivateFamilies.SmallIngress.zeroExecute
#print axioms PartACanonical.PrivateFamilies.SmallOrbit.Node
#print axioms PartACanonical.PrivateFamilies.SmallOrbit.Edge
#print axioms PartACanonical.PrivateFamilies.SmallOrbit.Path
#print axioms PartACanonical.PrivateFamilies.SmallOrbit.executeUse
#print axioms PartACanonical.PrivateFamilies.SmallOrbit.zeroPath
#print axioms PartACanonical.PrivateFamilies.SmallOrbit.zeroExecute
#print axioms PartACanonical.PrivateFamilies.SuffixCap.Node
#print axioms PartACanonical.PrivateFamilies.SuffixCap.Edge
#print axioms PartACanonical.PrivateFamilies.SuffixCap.Path
#print axioms PartACanonical.PrivateFamilies.SuffixCap.executeUse
#print axioms PartACanonical.PrivateFamilies.SuffixCap.zeroPath
#print axioms PartACanonical.PrivateFamilies.SuffixCap.zeroExecute
#print axioms PartACanonical.PrivateFamilies.CappedWorkspace.Node
#print axioms PartACanonical.PrivateFamilies.CappedWorkspace.Edge
#print axioms PartACanonical.PrivateFamilies.CappedWorkspace.Path
#print axioms PartACanonical.PrivateFamilies.CappedWorkspace.executeUse
#print axioms PartACanonical.PrivateFamilies.CappedWorkspace.zeroPath
#print axioms PartACanonical.PrivateFamilies.CappedWorkspace.zeroExecute
