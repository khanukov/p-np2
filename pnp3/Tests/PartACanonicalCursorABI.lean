import Cursor.Proof
import Tests.PartACanonicalAuditSupport

/-! Infrastructure: six exact Cursor.Proof private-owner contracts. The guard
¬exits is retained by rawRow; this gives no global statement about WORK-false.
All proof applications reuse the original private theorem terms. -/
open Pnp3.Complexity.Uniform.V1
namespace PartACanonical.CursorABI
set_option autoImplicit false

noncomputable abbrev er : (k : Nat) → Fin Stream.rawMachine.stateCount → Fin (Cursor.rawMachine k).stateCount :=
  partA_private% "_private.Cursor.Proof.0.Cursor.er" owner% "Cursor.Proof"
noncomputable abbrev exits : Fin Stream.rawMachine.stateCount → Prop :=
  partA_private% "_private.Cursor.Proof.0.Cursor.exits" owner% "Cursor.Proof"

theorem exits_body (s : Fin Stream.rawMachine.stateCount) :
    exits s ↔ s.val = 313 ∨ s.val = 314 := by rfl

theorem rawRow (k : Nat) (s : Fin Stream.rawMachine.stateCount)
    (he : ¬exits s) (b : Option Bool) :
    (Cursor.rawMachine k).step (er k s) b =
      (er k (Stream.rawMachine.step s b).1, (Stream.rawMachine.step s b).2) := by
  exact (partA_private% "_private.Cursor.Proof.0.Cursor.raw_row" owner% "Cursor.Proof") k s he b

theorem oldInert {N B : Nat} (c : Config Stream.rawMachine.stateCount N B)
    (he : exits c.state) : Stream.rawMachine.stepConfig c = c := by
  exact (partA_private% "_private.Cursor.Proof.0.Cursor.old_inert" owner% "Cursor.Proof") c he

theorem erVal (k : Nat) (s : Fin Stream.rawMachine.stateCount) : (er k s).val = s.val := by
  exact (partA_private% "_private.Cursor.Proof.0.Cursor.er_val" owner% "Cursor.Proof") k s

theorem erInitial (k : Nat) {N B : Nat} (y : Bitstring N) :
    (⟨er k (initialConfig Stream.rawMachine B y).state,
      (initialConfig Stream.rawMachine B y).head,
      (initialConfig Stream.rawMachine B y).tape⟩ : Config (Cursor.rawMachine k).stateCount N B) =
      initialConfig (Cursor.rawMachine k) B y := by
  exact (partA_private% "_private.Cursor.Proof.0.Cursor.er_initial" owner% "Cursor.Proof") k y

end PartACanonical.CursorABI

#partA_axioms "_private.Cursor.Proof.0.Cursor.er"
#partA_axioms "_private.Cursor.Proof.0.Cursor.exits"
#partA_axioms "_private.Cursor.Proof.0.Cursor.old_inert"
#partA_axioms "_private.Cursor.Proof.0.Cursor.raw_row"
#partA_axioms "_private.Cursor.Proof.0.Cursor.er_initial"
#partA_axioms "_private.Cursor.Proof.0.Cursor.er_val"
#partA_axioms "PartACanonical.CursorABI.er"
#partA_axioms "PartACanonical.CursorABI.exits"
#partA_axioms "PartACanonical.CursorABI.exits_body"
#partA_axioms "PartACanonical.CursorABI.rawRow"
#partA_axioms "PartACanonical.CursorABI.oldInert"
#partA_axioms "PartACanonical.CursorABI.erVal"
#partA_axioms "PartACanonical.CursorABI.erInitial"
