import Complexity.PrivateInterfaceLookupResolvedInstallerPath
import FullIngressClosure.SourceBackDriver
import FullIngressClosure.SourceSkipCertificates
import FullIngressClosure.Environment
import FullIngressClosure.EndRegisters
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateInstallerPath.bindings `FullIngressClosure.SelectTail
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated installer-path identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private theorem finish_physical (k : Nat) {S : Nat} (source : Fin S → Bool) (M : Nat) (physical : M < S) :
    finishState k (SerializedBody.sourceMode source M)=finishEntry k (source ⟨M,physical⟩) := by
  dsimp only [SerializedBody.sourceMode]
  rw [dif_pos physical]
  cases source ⟨M,physical⟩ <;> rfl
private theorem finish_virtual (k : Nat) {S : Nat} (source : Fin S → Bool) (M : Nat) (past : S ≤ M) :
    finishState k (SerializedBody.sourceMode source M)=st k 1977 := by
  dsimp only [SerializedBody.sourceMode]
  rw [dif_neg (by omega)]
  rfl
private theorem select_tail {k lo P S L H F Q p r n g ell W}
    (source : Fin S → Bool) (original C : Nat → Option Bool)
    (frame : Registers (SerializedBody.delimiter F r n) C (counterValues g ell W n r))
    (env : Environment (SerializedBody.delimiter F r n) original C S L H F Q p source)
    (phys : p < S) (width : p+r=S) (ellFit : ell ≤ r) (wFit : W ≤ r)
    (lower : lo ≤ p) (upper : SerializedBody.delimiter F r n 12 ≤ P) :
    ∃ b c d e,b ≤ (32*r+4)*(P+16) ∧ c ≤ (64*ell+4)*(P+16) ∧
      d ≤ (64*W+4)*(P+16) ∧ e ≤ 32*(P+16) ∧ PPath k lo P (b+(c+(d+e)))
      (pNode (st k 1461) (SerializedBody.delimiter F r n 10) C)
      (pNode (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source (p+ell+W)))) H
        (SerializedBody.prepared original S (p+ell+W) F r n g W)) := by
  let D:=SerializedBody.delimiter F r n
  let M:=p+ell+W
  let B0:=setBank C D 10 0
  have grid:=registerGrid frame
  have order:=corridorOrder (envCorridor env)
  have len10 : D 11=D 10+(3*r+3)+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have len9 : D 10=D 9+(2*r)+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have len11 : D 12=D 11+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  have len7 : D 8=D 7+r+1:=by dsimp only [D,SerializedBody.delimiter]; omega
  obtain ⟨b,hb,back⟩:=backDriver (k:=k) (lo:=lo) (P:=P) source grid (envCorridor env) (envArena env) (envD0 env)
    lower phys (envCells env) (3*r+3) len10 upper r (by omega) (by omega)
  have self10 : setBank C D 10 r=C:=by
    apply bankOriginal
    have h:=registerUnary frame 10 (by decide)
    change BankUnary D C 10 r at h
    exact h
  have eofState : backState k source S=st k 1461:=by
    dsimp only [backState,savedAt]
    rw [dif_neg (by omega)]
  rw [self10,width,eofState,liftedVirtual C S S le_rfl] at back
  change PPath k lo P b (pNode (st k 1461) (D 10) C)
    (pNode (entry9 k (source ⟨p,phys⟩)) (D 9) (lifted B0 S p)) at back
  have frame0:=registersSet frame 10 0 (by decide)
  have env0:=environmentBank env grid 10 0 (by decide)
  have u9 : BankUnary D B0 9 ell:=by
    have h:=registerUnary frame0 9 (by decide)
    change BankUnary D B0 9 ell at h
    exact h
  have u7 : BankUnary D B0 7 r:=by
    have h:=registerUnary frame0 7 (by decide)
    change BankUnary D B0 7 r at h
    exact h
  have start9 : skipTape B0 D 9 ell (S-p)=B0:=by
    have eq : S-p=r:=by omega
    rw [eq]
    exact skipOriginal u9 u7
  obtain ⟨c,hc,skip9⟩:=skipDriver (k:=k) (lo:=lo) (P:=P) (skip9Codes k) source (registerGrid frame0)
    (envCorridor env0) (envArena env0) (envD0 env0) (by decide) (by decide) (by decide) lower (envCells env0)
    (2*r) r len9 len7 upper ell p le_rfl phys (by omega) (by omega)
  rw [start9] at skip9
  rcases skip9 with ⟨physical1,path9⟩ | ⟨past9,path9⟩
  · let B1:=skipTape B0 D 9 0 (S-(p+ell))
    have frame1:=registersSet (registersSet frame0 9 0 (by decide)) 7 (S-(p+ell)) (by decide)
    have env1:=environmentBank (environmentBank env0 (registerGrid frame0) 9 0 (by decide))
      (registerGrid (registersSet frame0 9 0 (by decide))) 7 (S-(p+ell)) (by decide)
    have u11 : BankUnary D B1 11 W:=by
      have h:=registerUnary frame1 11 (by decide)
      change BankUnary D B1 11 W at h
      exact h
    have u7' : BankUnary D B1 7 (S-(p+ell)):=by
      have h:=registerUnary frame1 7 (by decide)
      change BankUnary D B1 7 (S-(p+ell)) at h
      exact h
    have start11 : skipTape B1 D 11 W (S-(p+ell))=B1:=skipOriginal u11 u7'
    obtain ⟨d,hd,skip11⟩:=skipDriver (k:=k) (lo:=lo) (P:=P) (T:=B1) (skip11Codes k) source (registerGrid frame1)
      (envCorridor env1) (envArena env1) (envD0 env1) (by decide) (by decide) (by decide) lower (envCells env1)
      r r len11 len7 upper W (p+ell) (by omega) physical1 wFit (by omega)
    rw [start11] at skip11
    rcases skip11 with ⟨physical2,path11⟩ | ⟨past11,path11⟩
    · let U:=skipTape B1 D 11 0 (S-M)
      have finalEnv:=environmentBank (environmentBank env1 (registerGrid frame1) 11 0 (by decide))
        (registerGrid (registersSet frame1 11 0 (by decide))) 7 (S-M) (by decide)
      have finalFrame:=end11Registers (anchor1:=S-(p+ell)) (anchor2:=S-M) (residue:=0) frame
      have fitM : M < S:=physical2
      have adjusted : Registers D U (endValues n g W (S-min M S) 0 0) := by
        rw [Nat.min_eq_left (Nat.le_of_lt fitM)]
        exact finalFrame
      obtain ⟨e,he,finish⟩:=finishPrepared (k:=k) (lo:=lo) (P:=P) (M:=M) source original U adjusted
        (envCorridor finalEnv) (envArena finalEnv) (envExterior finalEnv) (by omega) upper
      rw [Nat.min_eq_left (Nat.le_of_lt fitM),finish_physical k source M fitM] at finish
      refine ⟨b,c,d,e,hb,hc,hd,he,pAppend back (pAppend path9 (pAppend path11 finish))⟩
    · let U:=skipTape B1 D 11 (W-(S-(p+ell))) 0
      have past : S ≤ M:=past11
      have finalEnv:=environmentBank (environmentBank env1 (registerGrid frame1) 11 (W-(S-(p+ell))) (by decide))
        (registerGrid (registersSet frame1 11 (W-(S-(p+ell))) (by decide))) 7 0 (by decide)
      have finalFrame:=end11Registers (anchor1:=S-(p+ell)) (anchor2:=0) (residue:=W-(S-(p+ell))) frame
      have adjusted : Registers D U (endValues n g W (S-min M S) 0 (W-(S-(p+ell)))) := by
        rw [Nat.min_eq_right past,Nat.sub_self]
        exact finalFrame
      obtain ⟨e,he,finish⟩:=finishPrepared (k:=k) (lo:=lo) (P:=P) (M:=M) source original U adjusted
        (envCorridor finalEnv) (envArena finalEnv) (envExterior finalEnv) (by omega) upper
      rw [Nat.min_eq_right past,liftedVirtual U S S le_rfl,finish_virtual k source M past] at finish
      exact ⟨b,c,d,e,hb,hc,hd,he,pAppend back (pAppend path9 (pAppend path11 finish))⟩
  · let U:=skipTape B0 D 9 (ell-(S-p)) 0
    have past : S ≤ M:=by dsimp only [M]; omega
    have finalEnv:=environmentBank (environmentBank env0 (registerGrid frame0) 9 (ell-(S-p)) (by decide))
      (registerGrid (registersSet frame0 9 (ell-(S-p)) (by decide))) 7 0 (by decide)
    have finalFrame:=end9Registers (residue:=ell-(S-p)) frame
    have adjusted : Registers D U (endValues n g W (S-min M S) (ell-(S-p)) W) := by
      rw [Nat.min_eq_right past,Nat.sub_self]
      exact finalFrame
    obtain ⟨e,he,finish⟩:=finishPrepared (k:=k) (lo:=lo) (P:=P) (M:=M) source original U adjusted
      (envCorridor finalEnv) (envArena finalEnv) (envExterior finalEnv) (by omega) upper
    rw [Nat.min_eq_right past,liftedVirtual U S S le_rfl,finish_virtual k source M past] at finish
    refine ⟨b,c,0,e,hb,hc,by omega,he,?_⟩
    simpa only [Nat.zero_add] using pAppend back (pAppend path9 finish)
end FullIngressClosure
