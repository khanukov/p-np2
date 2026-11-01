import CertificateGuardClosure.Machine
import SmallIngress.Runtime
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [("SmallIngress.Runtime","SmallIngress","Node","GNode"),("SmallIngress.Runtime","SmallIngress","Node.mk","node"),("SmallIngress.Runtime","SmallIngress","put","put"),("SmallIngress.Runtime","SmallIngress","embed","emb"),("SmallIngress.Runtime","SmallIngress","dest","dest"),("SmallIngress.Runtime","SmallIngress","Path","GPath"),("SmallIngress.Runtime","SmallIngress","Path.nil","nilP"),("SmallIngress.Runtime","SmallIngress","Path.cons","consP"),("SmallIngress.Runtime","SmallIngress","Path.bounds","boundsP"),("SmallIngress.Runtime","SmallIngress","Path.append","appendP"),("SmallIngress.Runtime","SmallIngress","Path.execute","executeP"),("SmallIngress.Runtime","SmallIngress","hop","hop"),("SmallIngress.Runtime","SmallIngress","keep","keep"),("SmallIngress.Runtime","SmallIngress","sweepR","sweepR"),("SmallIngress.Runtime","SmallIngress","sweepL","sweepL"),("CertificateGuardClosure.Machine","CertificateGuardClosure","q","q"),("CertificateGuardClosure.Machine","CertificateGuardClosure","qa","qa"),("CertificateGuardClosure.Machine","CertificateGuardClosure","qr","qr"),("CertificateGuardClosure.Machine","CertificateGuardClosure","raw","raw")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique physical interface {mod}/{key}: {found.map Prod.fst}"
private def bank (T : Nat → Option Bool) (N c s : Nat) : Nat → Option Bool :=
  fun i=>if N < i ∧ i  ≤  N+c then some (decide (N+s < i)) else T i
private def hole (T : Nat → Option Bool) (p : Nat) : Nat → Option Bool := put T p none
private theorem put_at (T : Nat → Option Bool) (p : Nat) (v : Option Bool) : put T p v p=v := by simp [put]
private theorem put_off (T : Nat → Option Bool) (p i : Nat) (v : Option Bool) (h:i ≠ p) : put T p v i=T i := by simp [put,h]
private theorem put_restore (T : Nat → Option Bool) (p : Nat) : put (hole T p) p (T p)=T := by
  funext i;by_cases h:i=p <;> simp [put,hole,h]
private theorem bank_low (T : Nat → Option Bool) (N c s i : Nat) (h:i  ≤  N) : bank T N c s i=T i := by
  simp only [bank];rw [if_neg (by omega)]
private theorem bank_cell (T : Nat → Option Bool) {N c s i : Nat} (hi:N < i) (hc:i ≤ N+c) :
    bank T N c s i=some (decide (N+s < i)) := by simp [bank,hi,hc]
private theorem bank_end (T : Nat → Option Bool) (N c s : Nat) : bank T N c s (N+c+1)=T (N+c+1) := by simp [bank]
private theorem bank_append (T : Nat → Option Bool) (N c : Nat) :
    put (bank T N c 0) (N+c+1) (some true)=bank T N (c+1) 0 := by
  funext i
  by_cases h:i=N+c+1
  · subst i
    have slot : N < N+c+1 ∧ N+c+1  ≤  N+(c+1) := by omega
    simp [put,bank,slot]
  · simp only [put,if_neg h,bank,Nat.add_zero]
    have same : (N < i ∧ i  ≤  N+c) ↔ (N < i ∧ i  ≤  N+(c+1)) := by omega
    simp only [same]
private theorem bank_spend (T : Nat → Option Bool) {N c s : Nat} (h:s < c) :
    put (bank T N c s) (N+s+1) (some false)=bank T N c (s+1) := by
  funext i
  by_cases hi:i=N+s+1
  · subst i
    have slot : N < N+s+1 ∧ N+s+1  ≤  N+c := by omega
    simp only [put,ite_true,bank,if_pos slot]
    simp [Nat.add_assoc]
  · simp only [put,if_neg hi,bank]
    by_cases mem:N < i ∧ i  ≤  N+c
    · rw [if_pos mem,if_pos mem]
      congr 2
      apply propext
      omega
    · rw [if_neg mem,if_neg mem]
private theorem bank_origin (T : Nat → Option Bool) (N c s p : Nat) (h:p ≤ N) :
    hole (bank T N c s) p=bank (hole T p) N c s := by
  funext i
  by_cases hi:i=p
  · subst i
    have outside : ¬ (N < p ∧ p  ≤  N+c) := by omega
    simp [hole,put,bank,outside]
  · simp only [hole,put,if_neg hi,bank]
private theorem rows (o : Bool) (p : Fin 32) (b : Option Bool) :
    guard.step (q o p) b=raw (q o p) b := by
  apply UniformTM.step_of_ne <;> (cases o <;> apply Fin.ne_of_val_ne <;> simp [guard,q,qa,qr] <;> omega)
private theorem occupiedR {P lo hi : Nat} (o : Bool) (p : Fin 32) (T : Nat → Option Bool)
    (le:lo ≤ hi) (fit:hi ≤ P)
    (row:∀ v,guard.step (q o p) (some v)=(q o p,some v,.right))
    (occ:∀ i,lo ≤ i → i < hi → ∃ v,T i=some v) :
    GPath (M:=guard) P (hi-lo) (node (q o p) lo T) (node (q o p) hi T) := by
  have h:=sweepR (M:=guard) (P:=P) (q o p) T lo (hi-lo) (by omega) (by
    intro i hl hu;obtain ⟨v,hv⟩:=occ i hl (by omega);rw [hv];exact row v)
  simpa [Nat.add_sub_of_le le] using h
private theorem occupiedL {P lo hi : Nat} (o : Bool) (p : Fin 32) (T : Nat → Option Bool)
    (le:lo ≤ hi) (fit:hi ≤ P)
    (row:∀ v,guard.step (q o p) (some v)=(q o p,some v,.left))
    (occ:∀ i,lo < i → i ≤ hi → ∃ v,T i=some v) :
    GPath (M:=guard) P (hi-lo) (node (q o p) hi T) (node (q o p) lo T) := by
  have h:=sweepL (M:=guard) (P:=P) (q o p) T lo (hi-lo) (by omega) (by
    intro i hl hu;obtain ⟨v,hv⟩:=occ i hl (by omega);rw [hv];exact row v)
  simpa [Nat.add_sub_of_le le] using h
