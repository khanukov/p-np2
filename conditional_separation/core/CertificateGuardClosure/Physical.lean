import CertificateGuardClosure.Kernel
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [("SmallIngress.Runtime","SmallIngress","Node","GNode"),("SmallIngress.Runtime","SmallIngress","Node.mk","node"),("SmallIngress.Runtime","SmallIngress","put","put"),("SmallIngress.Runtime","SmallIngress","embed","emb"),("SmallIngress.Runtime","SmallIngress","dest","dest"),("SmallIngress.Runtime","SmallIngress","Path","GPath"),("SmallIngress.Runtime","SmallIngress","Path.nil","nilP"),("SmallIngress.Runtime","SmallIngress","Path.append","appendP"),("SmallIngress.Runtime","SmallIngress","Path.execute","executeP"),("SmallIngress.Runtime","SmallIngress","hop","hop"),("SmallIngress.Runtime","SmallIngress","keep","keep"),("SmallIngress.Runtime","SmallIngress","sweepR","sweepR"),("SmallIngress.Runtime","SmallIngress","sweepL","sweepL"),("CertificateGuardClosure.Machine","CertificateGuardClosure","q","q"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank","bank"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","hole","hole"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_low","bankLow"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_cell","bankCell"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_end","bankEnd"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_spend","bankSpend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_append","bankAppend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_origin","bankOrigin"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","put_restore","putRestore"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedR","occupiedR"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedL","occupiedL")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique physical application {mod}/{key}: {found.map Prod.fst}"
private theorem round_good {N c s p P : Nat} (o b : Bool) (T : Nat → Option Bool)
    (positive : 0 < p) (inside : p < N) (fit : N+c+1 ≤ P) (left : s < c)
    (bit : T p=some b) (eof : T N=none)
    (occupied : ∀ i, p < i → i < N → ∃ v,T i=some v) :
    GPath (M:=guard) P (2*(N-p)+2*s+3)
      (node (q o 10) p (bank T N c s))
      (node (q o 10) (p+1) (bank T N c (s+1))) := by
  let V:=bank T N c s
  let E:=hole V p
  let J:=bank T N c (s+1)
  let E1:=hole J p
  have vp : V p=some b := by dsimp [V];rw [bankLow T N c s p (by omega),bit]
  have vN : V N=none := by dsimp [V];rw [bankLow T N c s N le_rfl,eof]
  have eN : E N=none := by simp only [E,hole,put,if_neg (show N≠p by omega),vN]
  have ep : E p=none := by simp [E,hole,put]
  have e1N : E1 N=none := by
    simp only [E1,hole,put,if_neg (show N≠p by omega),J,bankLow T N c (s+1) N le_rfl,eof]
  have e1p : E1 p=none := by simp [E1,hole,put]
  have source (i : Nat) (hp:p < i) (hi:i < N) : E i=T i := by
    simp only [E,hole,put,if_neg (show i≠p by omega),V,bankLow T N c s i hi.le]
  have source1 (i : Nat) (hp:p < i) (hi:i < N) : E1 i=T i := by
    simp only [E1,hole,put,if_neg (show i≠p by omega),J,bankLow T N c (s+1) i hi.le]
  have bankE (i : Nat) (lo:N < i) (hi:i ≤ N+c) : E i=some (decide (N+s < i)) := by
    simp only [E,hole,put,if_neg (show i≠p by omega),V];exact bankCell T lo hi
  have bankE1 (i : Nat) (lo:N < i) (hi:i ≤ N+c) : E1 i=some (decide (N+(s+1) < i)) := by
    simp only [E1,hole,put,if_neg (show i≠p by omega),J];exact bankCell T lo hi
  have a:=hop (M:=guard) (P:=P) (q o 10) (q o (if b then 13 else 12)) p (p+1) V none .right
    (by omega) (by omega) (by rw [vp];cases o <;> cases b <;> rfl) rfl
  change GPath (M:=guard) P 1 (node (q o 10) p V) (node (q o (if b then 13 else 12)) (p+1) E) at a
  have z:=occupiedR (P:=P) o (if b then 13 else 12) E (show p+1 ≤ N by omega) (by omega)
    (by intro v;cases o <;> cases b <;> rfl) (by
      intro i lo hi;rw [source i (by omega) hi];exact occupied i (by omega) hi)
  have c0:=keep (M:=guard) (P:=P) (q o (if b then 13 else 12)) (q o (if b then 15 else 14)) N (N+1) E .right
    (by omega) (by omega) (by rw [eN];cases o <;> cases b <;> rfl) rfl
  have z1:=sweepR (M:=guard) (P:=P) (q o (if b then 15 else 14)) E (N+1) s (by omega) (by
    intro i lo hi
    have cell:E i=some false := by rw [bankE i (by omega) (by omega)];simp [show ¬ N+s < i by omega]
    rw [cell];cases o <;> cases b <;> rfl)
  have spend : put E (N+s+1) (some false)=E1 := by
    dsimp [E,E1,V,J]
    rw [bankOrigin T N c s p (by omega),bankOrigin T N c (s+1) p (by omega)]
    exact bankSpend (hole T p) left
  have c1:=hop (M:=guard) (P:=P) (q o (if b then 15 else 14)) (q o (if b then 17 else 16))
    (N+s+1) (N+s) E (some false) .left (by omega) (by omega) (by
      have cell:E (N+s+1)=some true := by rw [bankE _ (by omega) (by omega)];simp
      rw [cell];cases o <;> cases b <;> rfl) (by simp [dest])
  rw [spend] at c1
  have z2:=occupiedL (P:=P) o (if b then 17 else 16) E1 (show N ≤ N+s by omega) (by omega)
    (by intro v;cases o <;> cases b <;> rfl) (by
      intro i lo hi;exact ⟨_,bankE1 i lo (by omega)⟩)
  have c2:=keep (M:=guard) (P:=P) (q o (if b then 17 else 16)) (q o (if b then 19 else 18)) N (N-1) E1 .left
    (by omega) (by omega) (by rw [e1N];cases o <;> cases b <;> rfl) rfl
  have z3:=occupiedL (P:=P) o (if b then 19 else 18) E1 (show p ≤ N-1 by omega) (by omega)
    (by intro v;cases o <;> cases b <;> rfl) (by
      intro i lo hi;rw [source1 i lo (by omega)];exact occupied i lo (by omega))
  have restore : put E1 p (some b)=J := by
    have jp:J p=some b := by dsimp [J];rw [bankLow T N c (s+1) p (by omega),bit]
    rw [←jp];exact putRestore J p
  have c3:=hop (M:=guard) (P:=P) (q o (if b then 19 else 18)) (q o 10) p (p+1) E1 (some b) .right
    (by omega) (by omega) (by rw [e1p];cases o <;> cases b <;> rfl) rfl
  rw [restore] at c3
  rw [show N+1+s=N+s+1 by omega] at z1
  have path:=appendP a (appendP z (appendP c0 (appendP z1 (appendP c1 (appendP z2 (appendP c2 (appendP z3 c3)))))))
  convert path using 1; (simp only [Nat.add_sub_cancel_left];omega)
end CertificateGuardClosure
