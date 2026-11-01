import CertificateGuardClosure.Kernel
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  let pool:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.SmallIngress.Runtime." || n.toString.startsWith "_private.CertificateGuardClosure."
  for (mod,ns,key,aliasName) in [("SmallIngress.Runtime","SmallIngress","Node","GNode"),("SmallIngress.Runtime","SmallIngress","Node.mk","node"),("SmallIngress.Runtime","SmallIngress","put","put"),("SmallIngress.Runtime","SmallIngress","embed","emb"),("SmallIngress.Runtime","SmallIngress","dest","dest"),("SmallIngress.Runtime","SmallIngress","Path","GPath"),("SmallIngress.Runtime","SmallIngress","Path.nil","nilP"),("SmallIngress.Runtime","SmallIngress","Path.append","appendP"),("SmallIngress.Runtime","SmallIngress","Path.execute","executeP"),("SmallIngress.Runtime","SmallIngress","hop","hop"),("SmallIngress.Runtime","SmallIngress","keep","keep"),("SmallIngress.Runtime","SmallIngress","sweepR","sweepR"),("SmallIngress.Runtime","SmallIngress","sweepL","sweepL"),("CertificateGuardClosure.Machine","CertificateGuardClosure","q","q"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank","bank"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","hole","hole"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_low","bankLow"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_cell","bankCell"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_end","bankEnd"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_spend","bankSpend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_append","bankAppend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_origin","bankOrigin"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","put_restore","putRestore"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedR","occupiedR"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedL","occupiedL")] do
    let found:=pool.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique physical application {mod}/{key}: {found.map Prod.fst}"
private theorem query_round {N c p P : Nat} (T : Nat → Option Bool)
    (positive : 0 < p) (inside : p < N) (fit : N+c+2 ≤ P)
    (bit : T p=some false) (eof : T N=none) (blank : T (N+c+1)=none)
    (occupied : ∀ i, p < i → i < N → ∃ v,T i=some v) :
    GPath (M:=guard) P (2*(N-p)+2*c+3)
      (node (q false 6) p (bank T N c 0))
      (node (q false 5) (p+1) (bank T N (c+1) 0)) := by
  let V:=bank T N c 0
  let E:=hole V p
  let J:=bank T N (c+1) 0
  let E1:=hole J p
  have vp : V p=some false := by dsimp [V];rw [bankLow T N c 0 p (by omega),bit]
  have eN : E N=none := by simp only [E,hole,put,if_neg (show N≠p by omega),V,bankLow T N c 0 N le_rfl,eof]
  have e1N : E1 N=none := by simp only [E1,hole,put,if_neg (show N≠p by omega),J,bankLow T N (c+1) 0 N le_rfl,eof]
  have source (i : Nat) (hp:p < i) (hi:i < N) : E i=T i := by
    simp only [E,hole,put,if_neg (show i≠p by omega),V,bankLow T N c 0 i hi.le]
  have source1 (i : Nat) (hp:p < i) (hi:i < N) : E1 i=T i := by
    simp only [E1,hole,put,if_neg (show i≠p by omega),J,bankLow T N (c+1) 0 i hi.le]
  have bankE (i : Nat) (lo:N < i) (hi:i ≤ N+c) : E i=some true := by
    simp only [E,hole,put,if_neg (show i≠p by omega),V]
    rw [bankCell T lo hi];simp [lo]
  have bankE1 (i : Nat) (lo:N < i) (hi:i ≤ N+c+1) : E1 i=some true := by
    simp only [E1,hole,put,if_neg (show i≠p by omega),J]
    rw [bankCell T lo (by omega)];simp [lo]
  have a:=hop (M:=guard) (P:=P) (q false 6) (q false 7) p (p+1) V none .right
    (by omega) (by omega) (by rw [vp];rfl) rfl
  change GPath (M:=guard) P 1 (node (q false 6) p V) (node (q false 7) (p+1) E) at a
  have z:=occupiedR (P:=P) false 7 E (show p+1 ≤ N by omega) (by omega) (by intro v;rfl) (by
    intro i lo hi;rw [source i (by omega) hi];exact occupied i (by omega) hi)
  have c0:=keep (M:=guard) (P:=P) (q false 7) (q false 8) N (N+1) E .right
    (by omega) (by omega) (by rw [eN];rfl) rfl
  have z1:=occupiedR (P:=P) false 8 E (show N+1 ≤ N+c+1 by omega) (by omega) (by intro v;rfl) (by
    intro i lo hi;exact ⟨true,bankE i (by omega) (by omega)⟩)
  have append : put E (N+c+1) (some true)=E1 := by
    dsimp [E,E1,V,J]
    rw [bankOrigin T N c 0 p (by omega),bankOrigin T N (c+1) 0 p (by omega)]
    exact bankAppend (hole T p) N c
  have cell:E (N+c+1)=none := by
    simp only [E,hole,put,if_neg (show N+c+1≠p by omega),V,bankEnd,blank]
  have c1:=hop (M:=guard) (P:=P) (q false 8) (q false 9) (N+c+1) (N+c) E (some true) .left
    (by omega) (by omega) (by rw [cell];rfl) (by simp [dest])
  rw [append] at c1
  have z2:=occupiedL (P:=P) false 9 E1 (show N ≤ N+c by omega) (by omega) (by intro v;rfl) (by
    intro i lo hi;exact ⟨true,bankE1 i lo (by omega)⟩)
  have c2:=keep (M:=guard) (P:=P) (q false 9) (q false 11) N (N-1) E1 .left
    (by omega) (by omega) (by rw [e1N];rfl) rfl
  have z3:=occupiedL (P:=P) false 11 E1 (show p ≤ N-1 by omega) (by omega) (by intro v;rfl) (by
    intro i lo hi;rw [source1 i lo (by omega)];exact occupied i lo (by omega))
  have restore : put E1 p (some false)=J := by
    have jp:J p=some false := by dsimp [J];rw [bankLow T N (c+1) 0 p (by omega),bit]
    rw [←jp];exact putRestore J p
  have c3:=hop (M:=guard) (P:=P) (q false 11) (q false 5) p (p+1) E1 (some false) .right
    (by omega) (by omega) (by simp only [E1,hole,put];rfl) rfl
  rw [restore] at c3
  have path:=appendP a (appendP z (appendP c0 (appendP z1 (appendP c1 (appendP z2 (appendP c2 (appendP z3 c3)))))))
  convert path using 1; (simp only [Nat.add_sub_cancel_left];omega)
end CertificateGuardClosure
