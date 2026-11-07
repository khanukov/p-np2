import CertificateGuardClosure.Kernel
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  let pool:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.SmallIngress.Runtime." || n.toString.startsWith "_private.CertificateGuardClosure."
  for (mod,ns,key,aliasName) in [("SmallIngress.Runtime","SmallIngress","Node","GNode"),("SmallIngress.Runtime","SmallIngress","Node.mk","node"),("SmallIngress.Runtime","SmallIngress","put","put"),("SmallIngress.Runtime","SmallIngress","embed","emb"),("SmallIngress.Runtime","SmallIngress","dest","dest"),("SmallIngress.Runtime","SmallIngress","Path","GPath"),("SmallIngress.Runtime","SmallIngress","Path.nil","nilP"),("SmallIngress.Runtime","SmallIngress","Path.append","appendP"),("SmallIngress.Runtime","SmallIngress","Path.execute","executeP"),("SmallIngress.Runtime","SmallIngress","hop","hop"),("SmallIngress.Runtime","SmallIngress","keep","keep"),("SmallIngress.Runtime","SmallIngress","sweepR","sweepR"),("SmallIngress.Runtime","SmallIngress","sweepL","sweepL"),("CertificateGuardClosure.Machine","CertificateGuardClosure","q","q"),("CertificateGuardClosure.Machine","CertificateGuardClosure","qa","qa"),("CertificateGuardClosure.Machine","CertificateGuardClosure","qr","qr"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank","bank"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","hole","hole"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_low","bankLow"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_cell","bankCell"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_end","bankEnd"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_spend","bankSpend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_append","bankAppend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_origin","bankOrigin"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","put_restore","putRestore"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedR","occupiedR"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedL","occupiedL")] do
    let found:=pool.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique physical application {mod}/{key}: {found.map Prod.fst}"
private theorem bank_trim (T : Nat → Option Bool) (N c s : Nat) (blank:T (N+c+1)=none) :
    put (bank T N (c+1) s) (N+c+1) none=bank T N c s := by
  funext i
  by_cases h:i=N+c+1
  · subst i
    calc
      put (bank T N (c+1) s) (N+c+1) none (N+c+1)=none := by
        unfold put
        exact if_pos rfl
      _ = bank T N c s (N+c+1) := by rw [bankEnd,blank]
  · simp only [put,if_neg h,bank]
    have same : (N < i ∧ i ≤ N+(c+1)) ↔ (N < i ∧ i ≤ N+c) := by omega
    simp only [same]
private theorem bank_zero (T : Nat → Option Bool) (N s : Nat) : bank T N 0 s=T := by
  funext i
  simp only [bank,Nat.add_zero]
  rw [if_neg (by omega)]
private theorem clear_bank {N P : Nat} (o good : Bool) (T : Nat → Option Bool) (s : Nat)
    (blank : ∀ i,N ≤ i → T i=none) (c : Nat) (fit:N+c ≤ P) :
    GPath (M:=guard) P c
      (node (q o (if good then 30 else 26)) (N+c) (bank T N c s))
      (node (q o (if good then 30 else 26)) N T) := by
  induction c with
  | zero => simpa only [Nat.add_zero,bank_zero] using nilP (M:=guard) (P:=P) (node (q o (if good then 30 else 26)) N T) fit
  | succ c ih =>
    have cell:bank T N (c+1) s (N+c+1)=some (decide (N+s < N+c+1)) := bankCell T (by omega) (by omega)
    have a:=hop (M:=guard) (P:=P) (q o (if good then 30 else 26)) (q o (if good then 30 else 26))
      (N+c+1) (N+c) (bank T N (c+1) s) none .left (by omega) (by omega)
      (by rw [cell];cases o <;> cases good <;> rfl) (by simp [dest])
    rw [bank_trim T N c s (blank _ (by omega))] at a
    have rest:=ih (by omega)
    simpa only [Nat.add_assoc,Nat.add_comm 1 c] using appendP a rest
private theorem restore_origin {N P : Nat} (o good : Bool) (T : Nat → Option Bool)
    (pos:0 < N) (fit:N ≤ P) (origin:T 0=none)
    (occupied:∀ i,0 < i → i < N → ∃ v,T i=some v) :
    GPath (M:=guard) P N (node (q o (if good then 31 else 27)) (N-1) T)
      (node (if good then qa else qr) 0 (put T 0 (some o))) := by
  have scan:=occupiedL (P:=P) o (if good then 31 else 27) T (show 0 ≤ N-1 by omega) (by omega)
    (by intro v;cases o <;> cases good <;> rfl)
    (by intro i lo hi;exact occupied i lo (by omega))
  have last:=hop (M:=guard) (P:=P) (q o (if good then 31 else 27)) (if good then qa else qr) 0 0 T (some o) .stay
    (by omega) (by omega) (by rw [origin];cases o <;> cases good <;> rfl) rfl
  convert appendP scan last using 1; omega
private theorem clean_return {N c s P : Nat} (o good : Bool) (T : Nat → Option Bool)
    (pos:0 < N) (fit:N+c+1 ≤ P) (origin:T 0=none)
    (blank:∀ i,N ≤ i → T i=none)
    (occupied:∀ i,0 < i → i < N → ∃ v,T i=some v) :
    GPath (M:=guard) P (c+N+1)
      (node (q o (if good then 30 else 26)) (N+c) (bank T N c s))
      (node (if good then qa else qr) 0 (put T 0 (some o))) := by
  have a:=clear_bank (P:=P) o good T s blank c (by omega)
  have b:=keep (M:=guard) (P:=P) (q o (if good then 30 else 26)) (q o (if good then 31 else 27)) N (N-1) T .left
    (by omega) (by omega) (by rw [blank N le_rfl];cases o <;> cases good <;> rfl) rfl
  have z:=restore_origin (P:=P) o good T pos (by omega) origin occupied
  convert appendP a (appendP b z) using 1; omega
private theorem bad_finish {N c s P : Nat} (o : Bool) (T : Nat → Option Bool)
    (pos:0 < N) (fit:N+c+1 ≤ P) (origin:T 0=none)
    (blank:∀ i,N ≤ i → T i=none)
    (occupied:∀ i,0 < i → i < N → ∃ v,T i=some v) :
    GPath (M:=guard) P (N+2*c+2)
      (node (q o 25) (N+1) (bank T N c s)) (node qr 0 (put T 0 (some o))) := by
  have scan:=occupiedR (P:=P) o 25 (bank T N c s) (show N+1 ≤ N+c+1 by omega) (by omega) (by intro v;cases o <;> rfl)
    (by intro i lo hi;exact ⟨_,bankCell T (by omega) (by omega)⟩)
  have atEnd:bank T N c s (N+c+1)=none := by rw [bankEnd,blank _ (by omega)]
  have edge:=keep (M:=guard) (P:=P) (q o 25) (q o 26) (N+c+1) (N+c) (bank T N c s) .left
    (by omega) (by omega) (by rw [atEnd];cases o <;> rfl) (by simp [dest])
  have rest:=clean_return (c:=c) (s:=s) o false T pos fit origin blank occupied
  convert appendP scan (appendP edge rest) using 1; omega
private theorem compare_finish {N c s P : Nat} (o : Bool) (T : Nat → Option Bool)
    (pos:0 < N) (fit:N+c+1 ≤ P) (spent:s ≤ c) (origin:T 0=none)
    (blank:∀ i,N ≤ i → T i=none)
    (occupied:∀ i,0 < i → i < N → ∃ v,T i=some v) :
    GPath (M:=guard) P (N+2*c+3)
      (node (q o 10) N (bank T N c s))
      (node (if s=c then qa else qr) 0 (put T 0 (some o))) := by
  have eof:bank T N c s N=none := by rw [bankLow T N c s N le_rfl,blank N le_rfl]
  have first:=keep (M:=guard) (P:=P) (q o 10) (q o 28) N (N+1) (bank T N c s) .right
    (by omega) (by omega) (by rw [eof];cases o <;> rfl) rfl
  have scan:=sweepR (M:=guard) (P:=P) (q o 28) (bank T N c s) (N+1) s (by omega) (by
    intro i lo hi
    have cell:bank T N c s i=some false := by rw [bankCell T (by omega) (by omega)];simp [show ¬ N+s < i by omega]
    rw [cell];cases o <;> rfl)
  rw [show N+1+s=N+s+1 by omega] at scan
  by_cases full:s=c
  · subst s
    have atEnd:bank T N c c (N+c+1)=none := by rw [bankEnd,blank _ (by omega)]
    have edge:=keep (M:=guard) (P:=P) (q o 28) (q o 30) (N+c+1) (N+c) (bank T N c c) .left
      (by omega) (by omega) (by rw [atEnd];cases o <;> rfl) (by simp [dest])
    have rest:=clean_return (c:=c) (s:=c) o true T pos fit origin blank occupied
    convert appendP first (appendP scan (appendP edge rest)) using 1
    all_goals first | omega | simp
  · have cell:bank T N c s (N+s+1)=some true := by rw [bankCell T (by omega) (by omega)];simp
    have edge:=keep (M:=guard) (P:=P) (q o 28) (q o 25) (N+s+1) (N+s+2) (bank T N c s) .right
      (by omega) (by omega) (by rw [cell];cases o <;> rfl) rfl
    have more:=occupiedR (P:=P) o 25 (bank T N c s) (show N+s+2 ≤ N+c+1 by omega) (by omega)
      (by intro v;cases o <;> rfl) (by intro i lo hi;exact ⟨_,bankCell T (by omega) (by omega)⟩)
    have atEnd:bank T N c s (N+c+1)=none := by rw [bankEnd,blank _ (by omega)]
    have turn:=keep (M:=guard) (P:=P) (q o 25) (q o 26) (N+c+1) (N+c) (bank T N c s) .left
      (by omega) (by omega) (by rw [atEnd];cases o <;> rfl) (by simp [dest])
    have rest:=clean_return (c:=c) (s:=s) o false T pos fit origin blank occupied
    rw [if_neg full]
    convert appendP first (appendP scan (appendP edge (appendP more (appendP turn rest)))) using 1; omega
end CertificateGuardClosure
