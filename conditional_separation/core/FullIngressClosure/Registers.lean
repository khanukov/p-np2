import Complexity.PrivateInterfaceLookupResolvedInstallerPath
import FullIngressClosure.ArithmeticCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateInstallerPath.bindings `FullIngressClosure.Registers
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated installer-path identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private structure Registers (D : Nat → Nat) (T : Nat → Option Bool) (values : Nat → Nat) : Prop where
  grid : Grid D T
  unary : ∀ j,j < 12 → BankUnary D T j (values j)
private theorem registers_set {D T values} (frame : Registers D T values) (j v : Nat) (hj : j < 12) :
    Registers D (setBank T D j v) (Function.update values j v) := by
  refine ⟨bankGrid frame.grid j v hj,?_⟩
  intro i hi
  by_cases same : i=j
  · subst i
    simp only [Function.update_self]
    exact bankUnary T D j v
  · rw [Function.update_of_ne same]
    exact bankOther frame.grid i j (values i) v hi hj same (frame.unary i hi)
private theorem transfer_registers {k lo P D a b entry out} (code : TransferCode k a b entry out)
    (ha : a < 12) (hb : b < 12) (ne : a ≠ b)
    (wa wb : Nat) (lenA : D (a+1)=D a+wa+1) (lenB : D (b+1)=D b+wb+1)
    (lower : lo ≤ D 0) (upper : D 12 ≤ P)
    (T : Nat → Option Bool) (values : Nat → Nat) (frame : Registers D T values)
    (va : values a ≤ wa) (vb : values b+values a ≤ wb) :
    ∃ t,t ≤ 32*(values a+1)*(P+16) ∧ PPath k lo P t (pNode entry (D a) T)
      (pNode out (D a) (setBank (setBank T D a 0) D b (values b+values a))) ∧
      Registers D (setBank (setBank T D a 0) D b (values b+values a))
        (Function.update (Function.update values a 0) b (values b+values a)) := by
  obtain ⟨t,price,path⟩:=transfer code ha hb ne wa wb lenA lenB lower upper (values a) (values b) va vb
    T frame.grid (frame.unary a ha) (frame.unary b hb)
  exact ⟨t,price,path,registers_set (registers_set frame a 0 ha) b (values b+values a) hb⟩
private theorem copy_registers {k lo P D a b c entry out} (code : CopyCode k a b c entry out)
    (ha : a < 12) (hb : b < 12) (hc : c < 12) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (wa wb wc : Nat) (lenA : D (a+1)=D a+wa+1) (lenB : D (b+1)=D b+wb+1) (lenC : D (c+1)=D c+wc+1)
    (lower : lo ≤ D 0) (upper : D 12 ≤ P)
    (T : Nat → Option Bool) (values : Nat → Nat) (frame : Registers D T values)
    (va : values a ≤ wa) (vb : values a ≤ wb) (vc : values a ≤ wc) (b0 : values b=0) (c0 : values c=0) :
    ∃ t,t ≤ 128*(values a+1)*(P+16) ∧ PPath k lo P t (pNode entry (D a) T)
      (pNode out (D a) (setBank (setBank T D b (values a)) D c 0)) ∧
      Registers D (setBank (setBank T D b (values a)) D c 0)
        (Function.update (Function.update values b (values a)) c 0) := by
  have target : BankUnary D T b 0:=by rw [← b0]; exact frame.unary b hb
  have scratch : BankUnary D T c 0:=by rw [← c0]; exact frame.unary c hc
  obtain ⟨t,price,path⟩:=copyValue code ha hb hc ab ac bc wa wb wc lenA lenB lenC lower upper
    (values a) va vb vc T frame.grid (frame.unary a ha) target scratch
  exact ⟨t,price,path,registers_set (registers_set frame b (values a) hb) c 0 hc⟩
end FullIngressClosure
