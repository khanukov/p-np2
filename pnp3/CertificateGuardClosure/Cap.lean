import CertificateGuardClosure.Physical
import CertificateGuardClosure.Finish
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  let pool:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.SmallIngress.Runtime." || n.toString.startsWith "_private.CertificateGuardClosure."
  for (mod,ns,key,aliasName) in [("SmallIngress.Runtime","SmallIngress","Node","GNode"),("SmallIngress.Runtime","SmallIngress","Node.mk","node"),("SmallIngress.Runtime","SmallIngress","put","put"),("SmallIngress.Runtime","SmallIngress","embed","emb"),("SmallIngress.Runtime","SmallIngress","dest","dest"),("SmallIngress.Runtime","SmallIngress","Path","GPath"),("SmallIngress.Runtime","SmallIngress","Path.nil","nilP"),("SmallIngress.Runtime","SmallIngress","Path.append","appendP"),("SmallIngress.Runtime","SmallIngress","Path.execute","executeP"),("SmallIngress.Runtime","SmallIngress","hop","hop"),("SmallIngress.Runtime","SmallIngress","keep","keep"),("SmallIngress.Runtime","SmallIngress","sweepR","sweepR"),("SmallIngress.Runtime","SmallIngress","sweepL","sweepL"),("CertificateGuardClosure.Machine","CertificateGuardClosure","q","q"),("CertificateGuardClosure.Machine","CertificateGuardClosure","qa","qa"),("CertificateGuardClosure.Machine","CertificateGuardClosure","qr","qr"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank","bank"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","hole","hole"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_low","bankLow"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_cell","bankCell"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_end","bankEnd"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_spend","bankSpend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_append","bankAppend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_origin","bankOrigin"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","put_restore","putRestore"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedR","occupiedR"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedL","occupiedL"),("CertificateGuardClosure.Finish","CertificateGuardClosure","bad_finish","badFinish")] do
    let found:=pool.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique physical application {mod}/{key}: {found.map Prod.fst}"
private theorem round_cap {N c p P : Nat} (o b : Bool) (T : Nat → Option Bool)
    (positive : 0 < p) (inside : p < N) (fit : N+c+1 ≤ P)
    (bit : T p=some b) (origin:T 0=none)
    (blank:∀ i,N ≤ i → T i=none)
    (occupied : ∀ i, 0 < i → i < N → ∃ v,T i=some v) :
    GPath (M:=guard) P (3*(N-p)+N+4*c+5)
      (node (q o 10) p (bank T N c c)) (node qr 0 (put T 0 (some o))) := by
  let V:=bank T N c c
  let E:=hole V p
  have vp : V p=some b := by dsimp [V];rw [bankLow T N c c p (by omega),bit]
  have vN : V N=none := by dsimp [V];rw [bankLow T N c c N le_rfl,blank N le_rfl]
  have eN : E N=none := by simp only [E,hole,put,if_neg (show N≠p by omega),vN]
  have ep : E p=none := by simp [E,hole,put]
  have source (i : Nat) (hp:p < i) (hi:i < N) : E i=T i := by
    simp only [E,hole,put,if_neg (show i≠p by omega),V,bankLow T N c c i hi.le]
  have bankE (i : Nat) (lo:N < i) (hi:i ≤ N+c) : E i=some false := by
    simp only [E,hole,put,if_neg (show i≠p by omega),V]
    rw [bankCell T lo hi];simp [show ¬ N+c < i by omega]
  have a:=hop (M:=guard) (P:=P) (q o 10) (q o (if b then 13 else 12)) p (p+1) V none .right
    (by omega) (by omega) (by rw [vp];cases o <;> cases b <;> rfl) rfl
  change GPath (M:=guard) P 1 (node (q o 10) p V) (node (q o (if b then 13 else 12)) (p+1) E) at a
  have z:=occupiedR (P:=P) o (if b then 13 else 12) E (show p+1 ≤ N by omega) (by omega)
    (by intro v;cases o <;> cases b <;> rfl) (by intro i lo hi;rw [source i (by omega) hi];exact occupied i (by omega) hi)
  have c0:=keep (M:=guard) (P:=P) (q o (if b then 13 else 12)) (q o (if b then 15 else 14)) N (N+1) E .right
    (by omega) (by omega) (by rw [eN];cases o <;> cases b <;> rfl) rfl
  have z1:=sweepR (M:=guard) (P:=P) (q o (if b then 15 else 14)) E (N+1) c (by omega) (by
    intro i lo hi;rw [bankE i (by omega) (by omega)];cases o <;> cases b <;> rfl)
  rw [show N+1+c=N+c+1 by omega] at z1
  have atEnd:E (N+c+1)=none := by
    simp only [E,hole,put,if_neg (show N+c+1≠p by omega),V,bankEnd,blank (N+c+1) (by omega)]
  have c1:=keep (M:=guard) (P:=P) (q o (if b then 15 else 14)) (q o (if b then 21 else 20))
    (N+c+1) (N+c) E .left (by omega) (by omega)
    (by rw [atEnd];cases o <;> cases b <;> rfl) (by simp [dest])
  have z2:=occupiedL (P:=P) o (if b then 21 else 20) E (show N ≤ N+c by omega) (by omega)
    (by intro v;cases o <;> cases b <;> rfl) (by intro i lo hi;exact ⟨false,bankE i lo hi⟩)
  have c2:=keep (M:=guard) (P:=P) (q o (if b then 21 else 20)) (q o (if b then 23 else 22)) N (N-1) E .left
    (by omega) (by omega) (by rw [eN];cases o <;> cases b <;> rfl) rfl
  have z3:=occupiedL (P:=P) o (if b then 23 else 22) E (show p ≤ N-1 by omega) (by omega)
    (by intro v;cases o <;> cases b <;> rfl) (by intro i lo hi;rw [source i lo (by omega)];exact occupied i (by omega) (by omega))
  have restore : put E p (some b)=V := by rw [←vp];exact putRestore V p
  have c3:=hop (M:=guard) (P:=P) (q o (if b then 23 else 22)) (q o 24) p (p+1) E (some b) .right
    (by omega) (by omega) (by rw [ep];cases o <;> cases b <;> rfl) rfl
  rw [restore] at c3
  have again:=occupiedR (P:=P) o 24 V (show p+1 ≤ N by omega) (by omega) (by intro v;cases o <;> rfl)
    (by intro i lo hi;dsimp [V];rw [bankLow T N c c i hi.le];exact occupied i (by omega) hi)
  have c4:=keep (M:=guard) (P:=P) (q o 24) (q o 25) N (N+1) V .right
    (by omega) (by omega) (by rw [vN];cases o <;> rfl) rfl
  have finish:=badFinish (c:=c) (s:=c) o T (by omega) fit origin blank occupied
  convert appendP a (appendP z (appendP c0 (appendP z1 (appendP c1 (appendP z2 (appendP c2 (appendP z3 (appendP c3 (appendP again (appendP c4 finish)))))))))) using 1; omega
end CertificateGuardClosure
