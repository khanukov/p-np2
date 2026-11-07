import FullIngressClosure.Clone
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","dest","dest"),
      ("BodyIngress.Native","BodyIngress","Path.nil","pNil"),
      ("BodyIngress.Native","BodyIngress","Path.append","pAppend"),
      ("FullIngressClosure.Clone","FullIngressClosure","fill","fill"),
      ("FullIngressClosure.Clone","FullIngressClosure","fill_old","fillOld"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyRows","CopyRows"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyRows.safeEntry","safeEntry"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyRows.safeRead","safeRead"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyRows.safeFinish","safeFinish"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyRows.enter","enter"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyRows.done","done"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyRows.finishPass","finishPass"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyRows.finishEnd","finishEnd"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyFrame","CopyFrame"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyFrame.lower","frameLower"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyFrame.fit","frameFit"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyFrame.apart","frameApart"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyFrame.monotone","frameMono"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyFrame.sourceRight","frameRight"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyFrame.blank","frameBlank"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyFrame.source","frameSource"),
      ("FullIngressClosure.Clone","FullIngressClosure","CopyFrame.prior","framePrior"),
      ("FullIngressClosure.Clone","FullIngressClosure","keep","keep"),
      ("FullIngressClosure.Clone","FullIngressClosure","sweepL","sweepL"),
      ("FullIngressClosure.Clone","FullIngressClosure","clone_round","cloneRound")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique clone iteration term {mod}/{key}: {found.map Prod.fst}"
private theorem fill_initial {T lo P a b w f D} (frame : CopyFrame T lo P a b w f D) :
    fill T (D b) f=T := by
  funext i
  dsimp only [fill]
  split_ifs with inside
  · exact (framePrior frame i inside.1 inside.2).symm
  · rfl
private theorem clone_iteration {k lo P a b w f entry read finish out}
    (code : CopyRows k a b entry read finish out) (T : Nat → Option Bool) (D : Nat → Nat)
    (frame : CopyFrame T lo P a b w f D) (count j : Nat) (total : j+count=w) :
    ∃ t,t ≤ count*8*(P+16) ∧ PPath k lo P t
      (pNode read (D a+j+1) (fill T (D b) (f+j)))
      (pNode read (D a+w+1) (fill T (D b) (f+w))) := by
  have lower:=frameLower frame
  have upper:=frameFit frame
  have apart:=frameApart frame
  have right:=frameRight frame
  have after : D a+w+1 ≤ D b := by
    rw [← right]
    exact frameMono frame (a+1) b (by omega) apart le_rfl
  induction count generalizing j with
  | zero =>
    have same : j=w := by omega
    subst j
    refine ⟨0,by omega,pNil _ ?_⟩
    change lo ≤ D a+w+1 ∧ D a+w+1 ≤ P
    exact ⟨by omega,by omega⟩
  | succ count ih =>
    obtain ⟨u,hu,one⟩:=cloneRound code T D frame j (by omega)
    obtain ⟨v,hv,rest⟩:=ih (j+1) (by omega)
    rw [show D a+j+2=D a+(j+1)+1 by omega] at one
    refine ⟨_,?_,pAppend one rest⟩
    nlinarith
private theorem clone_stage {k lo P a b w f entry read finish out}
    (code : CopyRows k a b entry read finish out) (T : Nat → Option Bool) (D : Nat → Nat)
    (frame : CopyFrame T lo P a b w f D) :
    ∃ t,t ≤ 16*(w+1)*(P+16) ∧ PPath k lo P t
      (pNode entry (D a) T) (pNode out (D a) (fill T (D b) (f+w))) := by
  let E:=fill T (D b) (f+w)
  have lower:=frameLower frame
  have upper:=frameFit frame
  have apart:=frameApart frame
  have right:=frameRight frame
  have after : D a+w+1 ≤ D b := by
    rw [← right]
    exact frameMono frame (a+1) b (by omega) apart le_rfl
  have old (i : Nat) (hi : i ≤ D b) : E i=T i := fillOld T (D b) (f+w) i (Or.inl hi)
  have first:=keep (k:=k) (lo:=lo) (hi:=P) entry read (D a) (D a+1) T .right (safeEntry code)
    ⟨lower,by omega⟩ ⟨by omega,by omega⟩
    (by rw [frameBlank frame a le_rfl (by omega)]; exact enter code) rfl
  obtain ⟨u,hu,loop⟩:=clone_iteration code T D frame w 0 (by omega)
  simp only [Nat.add_zero] at loop
  rw [fill_initial frame] at loop
  have stop:=keep (k:=k) (lo:=lo) (hi:=P) read finish (D a+w+1) (D a+w) E .left (safeRead code)
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [old _ (by omega),← right,frameBlank frame (a+1) (by omega) apart]; exact done code)
    (by simp [dest])
  have back:=sweepL (k:=k) (lo:=lo) (hi:=P) finish E (D a) w (safeFinish code) lower (by omega) (by
    intro i hl hu
    rw [old i (by omega)]
    obtain ⟨bit,hbit⟩:=frameSource frame i hl (by omega)
    rw [hbit]; exact finishPass code bit)
  have last:=keep (k:=k) (lo:=lo) (hi:=P) finish out (D a) (D a) E .stay (safeFinish code)
    ⟨lower,by omega⟩ ⟨lower,by omega⟩
    (by rw [old _ (by omega),frameBlank frame a le_rfl (by omega)]; exact finishEnd code) rfl
  have path:=pAppend first (pAppend loop (pAppend stop (pAppend back last)))
  refine ⟨_,?_,path⟩
  have width : w ≤ P := by omega
  nlinarith
end FullIngressClosure
