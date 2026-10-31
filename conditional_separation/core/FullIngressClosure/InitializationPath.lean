import Complexity.PrivateInterfaceLookupResolvedInstallerPath
import FullIngressClosure.Initialization
import FullIngressClosure.Move
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateInstallerPath.bindings `FullIngressClosure.InitializationPath
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated installer-path identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private theorem partial_travel {k lo P F r n b f a c e out}
    (code : Travel k a c e out) (T : Nat → Option Bool) (frame : Six T F r n)
    (six : 6 ≤ b) (b12 : b ≤ 12) (ha : a ≤ b) (hc : c ≤ b)
    (lower : lo ≤ SerializedBody.delimiter F r n 0) (upper : SerializedBody.delimiter F r n 12 ≤ P) :
    ∃ t,t ≤ 2*(P+16) ∧ PPath k lo P t
      (pNode e (SerializedBody.delimiter F r n a) (stageTape T F r n b f))
      (pNode out (SerializedBody.delimiter F r n c) (stageTape T F r n b f)) := by
  let D:=SerializedBody.delimiter F r n
  let E:=stageTape T F r n b f
  have low (u) (hu : u ≤ b) : lo ≤ D u:=lower.trans (delimiterMono F r n 0 u (Nat.zero_le u) (by omega))
  have high (u) (hu : u ≤ b) : D u ≤ P:=(delimiterMono F r n u 12 (by omega) le_rfl).trans upper
  cases code with
  | right code =>
    have order:=spanR code
    have path:=routeR (lo:=lo) (hi:=P) code D E (low a ha) (high c hc)
      (by intro j _ jb; exact delimiterRise F r n j (by omega))
      (by intro u v _ uv vb; exact delimiterMono F r n u v uv (by omega))
      (by intro j _ jb; exact partialBlank frame b f j six b12 (by omega))
      (by intro j i _ jb il iu; exact partialCells frame b f j i six b12 (by omega) il iu)
    refine ⟨_,?_,path⟩
    have h:=high c hc
    have bound : c ≤ 12:=by omega
    omega
  | left code =>
    have order:=spanL code
    have path:=routeL (lo:=lo) (hi:=P) code D E (low c hc) (high a ha)
      (by intro j _ jb; exact delimiterRise F r n j (by omega))
      (by intro u v _ uv vb; exact delimiterMono F r n u v uv (by omega))
      (by intro j _ jb; exact partialBlank frame b f j six b12 (by omega))
      (by intro j i _ jb il iu; exact partialCells frame b f j i six b12 (by omega) il iu)
    refine ⟨_,?_,path⟩
    have h:=high a ha
    have bound : a ≤ 12:=by omega
    omega
  | stay safe row =>
    have path:=pKeep (k:=k) (lo:=lo) (hi:=P) e out (D a) (D a) E .stay
      ⟨safe.1,safe.2.1⟩ safe.2.2 ⟨low a ha,high a ha⟩ ⟨low a ha,high a ha⟩
      (by
        have blank : E (D a)=none:=partialBlank frame b f a six b12 ha
        rw [blank]; exact row) rfl
    exact ⟨1,by omega,path⟩
private def join0 (k : Nat) : Travel k 0 0 (st k 57) (st k 58) :=
  (trStay (safeNative k 57 (by decide)) (by rw [stSmall k 57 (by decide),nativeRow]; rfl))
private def join1 (k : Nat) : Travel k 0 1 (st k 123) (st k 125) :=
  (trRight (rrNext (safeNative k 123 (by decide)) (safeNative k 124 (by decide))
      (by rw [stSmall k 123 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 124 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 124 (by decide),nativeRow]; rfl) (rrNil 1 (st k 125))))
private def join2 (k : Nat) : Travel k 1 0 (st k 190) (st k 192) :=
  (trLeft (rlNext (safeNative k 190 (by decide)) (safeNative k 191 (by decide))
      (by rw [stSmall k 190 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 191 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 191 (by decide),nativeRow]; rfl) (rlNil 0 (st k 192))))
private def join3 (k : Nat) : Travel k 0 0 (st k 273) (st k 274) :=
  (trStay (safeNative k 273 (by decide)) (by rw [stSmall k 273 (by decide),nativeRow]; rfl))
private def join4 (k : Nat) : Travel k 0 0 (st k 355) (st k 356) :=
  (trStay (safeNative k 355 (by decide)) (by rw [stSmall k 355 (by decide),nativeRow]; rfl))
private def join5 (k : Nat) : Travel k 0 0 (st k 445) (st k 446) :=
  (trStay (safeNative k 445 (by decide)) (by rw [stSmall k 445 (by decide),nativeRow]; rfl))
private def join6 (k : Nat) : Travel k 0 0 (st k 535) (st k 536) :=
  (trStay (safeNative k 535 (by decide)) (by rw [stSmall k 535 (by decide),nativeRow]; rfl))
private def toPad (k : Nat) : Travel k 0 10 (st k 625) (st k 645) :=
  (trRight (rrNext (safeNative k 625 (by decide)) (safeNative k 626 (by decide))
      (by rw [stSmall k 625 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 626 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 626 (by decide),nativeRow]; rfl) (rrNext (safeNative k 627 (by decide)) (safeNative k 628 (by decide))
      (by rw [stSmall k 627 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 628 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 628 (by decide),nativeRow]; rfl) (rrNext (safeNative k 629 (by decide)) (safeNative k 630 (by decide))
      (by rw [stSmall k 629 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 630 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 630 (by decide),nativeRow]; rfl) (rrNext (safeNative k 631 (by decide)) (safeNative k 632 (by decide))
      (by rw [stSmall k 631 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 632 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 632 (by decide),nativeRow]; rfl) (rrNext (safeNative k 633 (by decide)) (safeNative k 634 (by decide))
      (by rw [stSmall k 633 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 634 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 634 (by decide),nativeRow]; rfl) (rrNext (safeNative k 635 (by decide)) (safeNative k 636 (by decide))
      (by rw [stSmall k 635 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 636 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 636 (by decide),nativeRow]; rfl) (rrNext (safeNative k 637 (by decide)) (safeNative k 638 (by decide))
      (by rw [stSmall k 637 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 638 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 638 (by decide),nativeRow]; rfl) (rrNext (safeNative k 639 (by decide)) (safeNative k 640 (by decide))
      (by rw [stSmall k 639 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 640 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 640 (by decide),nativeRow]; rfl) (rrNext (safeNative k 641 (by decide)) (safeNative k 642 (by decide))
      (by rw [stSmall k 641 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 642 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 642 (by decide),nativeRow]; rfl) (rrNext (safeNative k 643 (by decide)) (safeNative k 644 (by decide))
      (by rw [stSmall k 643 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 644 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 644 (by decide),nativeRow]; rfl) (rrNil 10 (st k 645)))))))))))))
private def fromPad (k : Nat) : Travel k 10 0 (st k 652) (st k 672) :=
  (trLeft (rlNext (safeNative k 652 (by decide)) (safeNative k 653 (by decide))
      (by rw [stSmall k 652 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 653 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 653 (by decide),nativeRow]; rfl) (rlNext (safeNative k 654 (by decide)) (safeNative k 655 (by decide))
      (by rw [stSmall k 654 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 655 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 655 (by decide),nativeRow]; rfl) (rlNext (safeNative k 656 (by decide)) (safeNative k 657 (by decide))
      (by rw [stSmall k 656 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 657 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 657 (by decide),nativeRow]; rfl) (rlNext (safeNative k 658 (by decide)) (safeNative k 659 (by decide))
      (by rw [stSmall k 658 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 659 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 659 (by decide),nativeRow]; rfl) (rlNext (safeNative k 660 (by decide)) (safeNative k 661 (by decide))
      (by rw [stSmall k 660 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 661 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 661 (by decide),nativeRow]; rfl) (rlNext (safeNative k 662 (by decide)) (safeNative k 663 (by decide))
      (by rw [stSmall k 662 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 663 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 663 (by decide),nativeRow]; rfl) (rlNext (safeNative k 664 (by decide)) (safeNative k 665 (by decide))
      (by rw [stSmall k 664 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 665 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 665 (by decide),nativeRow]; rfl) (rlNext (safeNative k 666 (by decide)) (safeNative k 667 (by decide))
      (by rw [stSmall k 666 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 667 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 667 (by decide),nativeRow]; rfl) (rlNext (safeNative k 668 (by decide)) (safeNative k 669 (by decide))
      (by rw [stSmall k 668 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 669 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 669 (by decide),nativeRow]; rfl) (rlNext (safeNative k 670 (by decide)) (safeNative k 671 (by decide))
      (by rw [stSmall k 670 (by decide),nativeRow]; rfl)
      (by intro value; cases value <;> (rw [stSmall k 671 (by decide),nativeRow]; rfl))
      (by rw [stSmall k 671 (by decide),nativeRow]; rfl) (rlNil 0 (st k 672)))))))))))))
private def join8 (k : Nat) : Travel k 0 0 (st k 672) (st k 673) :=
  (trStay (safeNative k 672 (by decide)) (by rw [stSmall k 672 (by decide),nativeRow]; rfl))
end FullIngressClosure
