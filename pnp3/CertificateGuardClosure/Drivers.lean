import CertificateGuardClosure.Cap
import CertificateGuardClosure.Query
import CertificateGuardClosure.Bootstrap
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  let pool:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.SmallIngress.Runtime." || n.toString.startsWith "_private.CertificateGuardClosure."
  for (mod,ns,key,aliasName) in [("SmallIngress.Runtime","SmallIngress","Node","GNode"),("SmallIngress.Runtime","SmallIngress","Node.mk","node"),("SmallIngress.Runtime","SmallIngress","put","put"),("SmallIngress.Runtime","SmallIngress","embed","emb"),("SmallIngress.Runtime","SmallIngress","dest","dest"),("SmallIngress.Runtime","SmallIngress","Path","GPath"),("SmallIngress.Runtime","SmallIngress","Path.nil","nilP"),("SmallIngress.Runtime","SmallIngress","Path.append","appendP"),("SmallIngress.Runtime","SmallIngress","Path.execute","executeP"),("SmallIngress.Runtime","SmallIngress","hop","hop"),("SmallIngress.Runtime","SmallIngress","keep","keep"),("SmallIngress.Runtime","SmallIngress","sweepR","sweepR"),("SmallIngress.Runtime","SmallIngress","sweepL","sweepL"),("CertificateGuardClosure.Machine","CertificateGuardClosure","q","q"),("CertificateGuardClosure.Machine","CertificateGuardClosure","qa","qa"),("CertificateGuardClosure.Machine","CertificateGuardClosure","qr","qr"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank","bank"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","hole","hole"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_low","bankLow"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_cell","bankCell"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_end","bankEnd"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_spend","bankSpend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_append","bankAppend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_origin","bankOrigin"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","put_restore","putRestore"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedR","occupiedR"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedL","occupiedL"),("CertificateGuardClosure.Finish","CertificateGuardClosure","bad_finish","badFinish"),("CertificateGuardClosure.Finish","CertificateGuardClosure","compare_finish","compareFinish"),("CertificateGuardClosure.Physical","CertificateGuardClosure","round_good","roundGood"),("CertificateGuardClosure.Cap","CertificateGuardClosure","round_cap","roundCap"),("CertificateGuardClosure.Query","CertificateGuardClosure","query_round","queryRound"),("CertificateGuardClosure.Bootstrap","CertificateGuardClosure","bootstrap","bootstrap")] do
    let found:=pool.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique physical application {mod}/{key}: {found.map Prod.fst}"
private theorem query_driver {N a P : Nat} (T : Nat → Option Bool)
    (width:2*a+1 ≤ N) (fit:N+a+3 ≤ P)
    (blank:∀ j,N ≤ j → T j=none)
    (occupied:∀ j,0 < j → j < N → ∃ v,T j=some v)
    (tags:∀ j,0 < j → j < a → T (2*j)=some false) (sep:T (2*a)=some true)
    (i:Nat) (pos:0 < i) (hi:i ≤ a) :
    ∃ t,t ≤ 8*(a-i+1)*(N+a+3) ∧
      GPath (M:=guard) P t (node (q false 5) (2*i-1) (bank T N (i+1) 0))
        (node (q false 10) (2*a+1) (bank T N (a+1) 0)) := by
  let V:=bank T N (i+1) 0
  obtain ⟨b,atData⟩:=occupied (2*i-1) (by omega) (by omega)
  have read:V (2*i-1)=some b := by dsimp [V];rw [bankLow T N (i+1) 0 _ (by omega),atData]
  have one:=keep (M:=guard) (P:=P) (q false 5) (q false 6) (2*i-1) (2*i) V .right
    (by omega) (by omega) (by rw [read];rfl) (by simp [dest];omega)
  by_cases last:i=a
  · subst i
    have atSep:V (2*a)=some true := by dsimp [V];rw [bankLow T N (a+1) 0 _ (by omega),sep]
    have two:=keep (M:=guard) (P:=P) (q false 6) (q false 10) (2*a) (2*a+1) V .right
      (by omega) (by omega) (by rw [atSep];rfl) rfl
    refine ⟨2,by nlinarith,appendP one two⟩
  · have next:i < a := by omega
    have round:=queryRound (P:=P) (c:=i+1) (p:=2*i) T (by omega) (by omega) (by omega)
      (tags i pos next) (blank N le_rfl) (blank _ (by omega))
      (by intro j lo hj;exact occupied j (by omega) hj)
    obtain ⟨t,price,rest⟩:=query_driver T width fit blank occupied tags sep (i+1) (by omega) (by omega)
    rw [show 2*(i+1)-1=2*i+1 by omega] at rest
    refine ⟨1+((2*(N-2*i)+2*(i+1)+3)+t),?_,appendP one (appendP round rest)⟩
    have hopBound : 1+(2*(N-2*i)+2*(i+1)+3) ≤ 8*(N+a+3) := by omega
    have eq:a-i+1=(a-(i+1)+1)+1 := by omega
    rw [eq]
    nlinarith
termination_by a-i
private theorem certificate_driver {N m off c P : Nat} (o : Bool) (T : Nat → Option Bool)
    (shape:N=off+m) (offpos:0 < off) (fit:N+c+2 ≤ P) (origin:T 0=none)
    (blank:∀ i,N ≤ i → T i=none)
    (occupied:∀ i,0 < i → i < N → ∃ v,T i=some v)
    (j:Nat) (hj:j ≤ m) (jc:j ≤ c) :
    ∃ t,t ≤ 8*(m-j+1)*(N+c+3) ∧
      GPath (M:=guard) P t (node (q o 10) (off+j) (bank T N c j))
        (node (if m=c then qa else qr) 0 (put T 0 (some o))) := by
  by_cases done:j=m
  · subst j
    have path:=compareFinish (P:=P) (c:=c) (s:=m) o T (by omega) (by omega) jc origin blank occupied
    rw [show N=off+m from shape] at path
    refine ⟨N+2*c+3,?_,?_⟩
    · nlinarith
    · simpa only [←shape] using path
  · have more:j < m := by omega
    obtain ⟨b,bit⟩:=occupied (off+j) (by omega) (by omega)
    by_cases cap:j=c
    · subst j
      have ne:m≠c := by omega
      rw [if_neg ne]
      have path:=roundCap (P:=P) (c:=c) (p:=off+c) o b T (by omega) (by omega) (by omega) bit origin blank occupied
      refine ⟨3*(N-(off+c))+N+4*c+5,?_,path⟩
      have hopBound : 3*(N-(off+c))+N+4*c+5 ≤ 8*(N+c+3) := by omega
      have factor:1 ≤ m-c+1 := by omega
      nlinarith
    · have left:j < c := by omega
      have one:=roundGood (P:=P) (c:=c) (s:=j) (p:=off+j) o b T (by omega) (by omega) (by omega) left bit
        (blank N le_rfl) (by intro i lo hi;exact occupied i (by omega) hi)
      obtain ⟨t,price,rest⟩:=certificate_driver o T shape offpos fit origin blank occupied (j+1) (by omega) (by omega)
      rw [show off+(j+1)=off+j+1 by omega] at rest
      refine ⟨(2*(N-(off+j))+2*j+3)+t,?_,appendP one rest⟩
      have hopBound : 2*(N-(off+j))+2*j+3 ≤ 8*(N+c+3) := by omega
      have eq:m-j+1=(m-(j+1)+1)+1 := by omega
      rw [eq]
      nlinarith
termination_by m-j
end CertificateGuardClosure
