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
private theorem empty_bank (T : Nat → Option Bool) (N : Nat) : bank T N 0 0=T := by
  funext i
  simp only [bank,Nat.add_zero]
  rw [if_neg (by omega)]
private theorem bootstrap {N P : Nat} (o : Bool) (T : Nat → Option Bool)
    (positive:0 < N) (fit:N+3 ≤ P) (first:T 0=some o)
    (blank:∀ i,N ≤ i → T i=none)
    (occupied:∀ i,0 < i → i < N → ∃ v,T i=some v) :
    let c:=if o then 1 else 2
    GPath (M:=guard) P (2*N+2*c+1) (node guard.start 0 T)
      (node (q o (if o then 10 else 5)) 1 (bank (hole T 0) N c 0)) := by
  intro c
  let U:=hole T 0
  have origin:U 0=none := by simp [U,hole,put]
  have source (i:Nat) (pos:0 < i) : U i=T i := by simp only [U,hole,put,if_neg (show i≠0 by omega)]
  have high (i:Nat) (hi:N ≤ i) : U i=none := by rw [source i (by omega),blank i hi]
  have a:=hop (M:=guard) (P:=P) guard.start (q o 0) 0 1 T none .right
    (by omega) (by omega) (by rw [first];cases o <;> rfl) rfl
  change GPath (M:=guard) P 1 (node guard.start 0 T) (node (q o 0) 1 U) at a
  have seek:=occupiedR (P:=P) o 0 U (show 1 ≤ N by omega) (by omega) (by intro v;cases o <;> rfl)
    (by intro i lo hi;rw [source i (by omega)];exact occupied i (by omega) hi)
  have toBank:=keep (M:=guard) (P:=P) (q o 0) (q o 1) N (N+1) U .right
    (by omega) (by omega) (by rw [high N le_rfl];cases o <;> rfl) rfl
  have paint:GPath (M:=guard) P c (node (q o 1) (N+1) U)
      (node (q o 3) (N+c-1) (bank U N c 0)) := by
    have one : put U (N+1) (some true)=bank U N 1 0 := by simpa only [empty_bank,Nat.add_zero] using bankAppend U N 0
    cases o with
    | true =>
      change GPath (M:=guard) P 1 (node (q true 1) (N+1) U) (node (q true 3) N (bank U N 1 0))
      have h:=hop (M:=guard) (P:=P) (q true 1) (q true 3) (N+1) N U (some true) .left
        (by omega) (by omega) (by rw [high _ (by omega)];rfl) (by simp [dest])
      rwa [one] at h
    | false =>
      change GPath (M:=guard) P 2 (node (q false 1) (N+1) U) (node (q false 3) (N+1) (bank U N 2 0))
      have h:=hop (M:=guard) (P:=P) (q false 1) (q false 2) (N+1) (N+2) U (some true) .right
        (by omega) (by omega) (by rw [high _ (by omega)];rfl) rfl
      rw [one] at h
      have h2:=hop (M:=guard) (P:=P) (q false 2) (q false 3) (N+2) (N+1) (bank U N 1 0) (some true) .left
        (by omega) (by omega) (by rw [bankEnd U N 1 0,high _ (by omega)];rfl) (by simp [dest])
      rw [show put (bank U N 1 0) (N+2) (some true)=bank U N 2 0 from bankAppend U N 1] at h2
      exact appendP h h2
  have cs : 1 ≤ c ∧ c ≤ 2 := by dsimp [c];cases o <;> decide
  have back:=occupiedL (P:=P) o 3 (bank U N c 0) (show N ≤ N+c-1 by omega) (by omega)
    (by intro v;cases o <;> rfl) (by intro i lo hi;exact ⟨_,bankCell U lo (by omega)⟩)
  have eof:bank U N c 0 N=none := by rw [bankLow U N c 0 N le_rfl,high N le_rfl]
  have turn:=keep (M:=guard) (P:=P) (q o 3) (q o 4) N (N-1) (bank U N c 0) .left
    (by omega) (by omega) (by rw [eof];cases o <;> rfl) rfl
  have rewind:=occupiedL (P:=P) o 4 (bank U N c 0) (show 0 ≤ N-1 by omega) (by omega)
    (by intro v;cases o <;> rfl) (by
      intro i lo hi;rw [bankLow U N c 0 i (by omega),source i lo];exact occupied i lo (by omega))
  have atOrigin:bank U N c 0 0=none := by rw [bankLow U N c 0 0 (by omega),origin]
  have entry:=keep (M:=guard) (P:=P) (q o 4) (q o (if o then 10 else 5)) 0 1 (bank U N c 0) .right
    (by omega) (by omega) (by rw [atOrigin];cases o <;> rfl) rfl
  convert appendP a (appendP seek (appendP toBank (appendP paint (appendP back (appendP turn (appendP rewind entry)))))) using 1; omega
end CertificateGuardClosure
