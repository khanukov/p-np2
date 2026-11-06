import Complexity.PrivateInterfaceLookupResolvedInstallerPath
import FullIngressClosure.FrontSection
import FullIngressClosure.AnchorSetup
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateInstallerPath.bindings `FullIngressClosure.CounterFront
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated installer-path identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private theorem counter_front_price (R r n a b c : Nat) (rn : r ≤ R) (nn : n ≤ R)
    (ha : a ≤ 262144*(R+1)^2)
    (hb : b ≤ 1024*(n+1)*(SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+16))
    (hc : c ≤ 256*(r+1)*(SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+16)) :
    a+b+c ≤ 524288*(R+1)^2 := by
  have span:=workspaceSpan R r n rn nn
  have left:=Nat.mul_le_mul (Nat.mul_le_mul_left 1024 (show n+1 ≤ R+1 by omega)) span
  have right:=Nat.mul_le_mul (Nat.mul_le_mul_left 256 (show r+1 ≤ R+1 by omega)) span
  nlinarith only [ha,hb,hc,left,right]
private def counterTape (T : Nat → Option Bool) (F r n g ell W : Nat) : Nat → Option Bool :=
  let D:=SerializedBody.delimiter F r n
  let A:=arithmeticTape (stageTape T F r n 12 0) D g ell W
  setBank (setBank (setBank (halfPhase A D true 0 (bitLength n)) D 7 r) D 10 r) D 5 0
private def counterValues (g ell W n r : Nat) : Nat → Nat :=
  Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (finalValues g ell W) 1 0) 8 0) 2 (bitLength n))
    7 r) 10 r) 5 0
private theorem installer_counter_front (k R r n lo g ell W : Nat) (T : Nat → Option Bool)
    (hr : r ≤ R) (hn : n ≤ R) (hg : g ≤ r) (he : ell ≤ r) (hw : W ≤ r) (fitEllN : bitLength n ≤ r)
    (frame : Six T (FixedRawLengthFence.fencePos R) r n)
    (old : ∀ j,j < 6 → BankUnary (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n)
      T j (initialValues g ell W j))
    (lower : lo ≤ SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 0) :
    ∃ t,t ≤ 524288*(R+1)^2 ∧ PPath k lo
      (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12) t
      (pNode (BodyIngress.old k (CarryWindow.ready k)) (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 0) T)
      (pNode (st k 1461) (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 10)
        (counterTape T (FixedRawLengthFence.fencePos R) r n g ell W)) ∧
      Registers (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n)
        (counterTape T (FixedRawLengthFence.fencePos R) r n g ell W) (counterValues g ell W n r) := by
  let F:=FixedRawLengthFence.fencePos R
  let D:=SerializedBody.delimiter F r n
  let P:=D 12
  let A:=arithmeticTape (stageTape T F r n 12 0) D g ell W
  have upper : D 12 ≤ P:=le_rfl
  obtain ⟨t0,h0,front,regs⟩:=frontSection k R r n lo g ell W T hr hn hg he hw frame old lower
  change Registers D A (finalValues g ell W) at regs
  have unary8 : BankUnary D A 8 0:=by
    have h:=registerUnary regs 8 (by decide)
    change BankUnary D A 8 0 at h
    exact h
  have unary2 : BankUnary D A 2 0:=by
    have h:=registerUnary regs 2 (by decide)
    change BankUnary D A 2 0 at h
    exact h
  have lenA : D 2=D 1+n+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have lenB : D 9=D 8+n+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have lenC : D 3=D 2+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  obtain ⟨t1,h1,halfPath⟩:=fullBitLength (k:=k) (lo:=lo) (P:=P) n r A (registerGrid regs)
    lenA lenB lenC lower upper fitEllN unary8 unary2
  have regsHalf:=registersSet (registersSet (registersSet regs 1 0 (by decide)) 8 0 (by decide)) 2 (bitLength n) (by decide)
  change Registers D (halfPhase A D true 0 (bitLength n)) _ at regsHalf
  have empty10 : BankUnary D (halfPhase A D true 0 (bitLength n)) 10 0:=by
    have h:=registerUnary regsHalf 10 (by decide)
    change BankUnary D (halfPhase A D true 0 (bitLength n)) 10 0 at h
    exact h
  have empty5 : BankUnary D (halfPhase A D true 0 (bitLength n)) 5 0:=by
    have h:=registerUnary regsHalf 5 (by decide)
    change BankUnary D (halfPhase A D true 0 (bitLength n)) 5 0 at h
    exact h
  have len7 : D 8=D 7+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have len10 : D 11=D 10+(3*r+3)+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have len5 : D 6=D 5+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  obtain ⟨t2,h2,anchor⟩:=anchorSetup (k:=k) (lo:=lo) (P:=P) r _ (registerGrid regsHalf)
    len7 len10 len5 lower upper empty10 empty5
  have finalRegs:=registersSet (registersSet (registersSet regsHalf 7 r (by decide)) 10 r (by decide)) 5 0 (by decide)
  have path:=pAppend front (pAppend halfPath anchor)
  refine ⟨_,?_,path,finalRegs⟩
  have price:=counter_front_price R r n t0 t1 t2 hr hn h0 h1 h2
  omega
end FullIngressClosure
