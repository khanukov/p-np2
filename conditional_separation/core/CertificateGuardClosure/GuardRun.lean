import CertificateGuardClosure.Drivers
import CertificateGuardClosure.Target
import IngressAllocation.SmallPaths
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  let pool:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.SmallIngress.Runtime." || n.toString.startsWith "_private.CertificateGuardClosure." || n.toString.startsWith "_private.IngressAllocation.SmallPaths."
  for (mod,ns,key,aliasName) in [("SmallIngress.Runtime","SmallIngress","Node","GNode"),("SmallIngress.Runtime","SmallIngress","Node.mk","node"),("SmallIngress.Runtime","SmallIngress","put","put"),("SmallIngress.Runtime","SmallIngress","embed","emb"),("SmallIngress.Runtime","SmallIngress","dest","dest"),("SmallIngress.Runtime","SmallIngress","Path","GPath"),("SmallIngress.Runtime","SmallIngress","Path.nil","nilP"),("SmallIngress.Runtime","SmallIngress","Path.append","appendP"),("SmallIngress.Runtime","SmallIngress","Path.execute","executeP"),("SmallIngress.Runtime","SmallIngress","hop","hop"),("SmallIngress.Runtime","SmallIngress","keep","keep"),("SmallIngress.Runtime","SmallIngress","sweepR","sweepR"),("SmallIngress.Runtime","SmallIngress","sweepL","sweepL"),("CertificateGuardClosure.Machine","CertificateGuardClosure","q","q"),("CertificateGuardClosure.Machine","CertificateGuardClosure","qa","qa"),("CertificateGuardClosure.Machine","CertificateGuardClosure","qr","qr"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank","bank"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","hole","hole"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_low","bankLow"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_cell","bankCell"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_end","bankEnd"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_spend","bankSpend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_append","bankAppend"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","bank_origin","bankOrigin"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","put_restore","putRestore"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedR","occupiedR"),("CertificateGuardClosure.Kernel","CertificateGuardClosure","occupiedL","occupiedL"),("CertificateGuardClosure.Finish","CertificateGuardClosure","bad_finish","badFinish"),("CertificateGuardClosure.Finish","CertificateGuardClosure","compare_finish","compareFinish"),("CertificateGuardClosure.Physical","CertificateGuardClosure","round_good","roundGood"),("CertificateGuardClosure.Cap","CertificateGuardClosure","round_cap","roundCap"),("CertificateGuardClosure.Query","CertificateGuardClosure","query_round","queryRound"),("CertificateGuardClosure.Bootstrap","CertificateGuardClosure","bootstrap","bootstrap"),("CertificateGuardClosure.Drivers","CertificateGuardClosure","query_driver","queryDriver"),("CertificateGuardClosure.Drivers","CertificateGuardClosure","certificate_driver","certificateDriver"),("IngressAllocation.SmallPaths","IngressAllocation.SmallPrefix","every_head","everyHead")] do
    let found:=pool.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique physical application {mod}/{key}: {found.map Prod.fst}"
private def rawTape {N : Nat} (y : Bitstring N) (i : Nat) : Option Bool :=
  if h:i < N then some (y ⟨i,h⟩) else none
private theorem path_price (N a m qd cd : Nat) (shape:N=2*a+1+m)
    (qprice:qd ≤ 8*a*(N+a+3)) (cprice:cd ≤ 8*(m+1)*(N+a+4)) :
    2*N+5+qd+cd ≤ 64*(N+1)^2 := by
  have smalla:a ≤ N := by omega
  have sum:a+m+1 ≤ N+1 := by omega
  have column:N+a+4 ≤ 3*(N+1) := by omega
  have sumBound:8*(a+m+1)*(N+a+4) ≤ 24*(N+1)^2 := by
    have mul:=Nat.mul_le_mul sum column
    nlinarith only [mul]
  nlinarith only [qprice,cprice,sumBound]
private theorem canonical_path {a m : Nat} (x : Bitstring a) (w : Bitstring m) :
    let N:=pairLength a m;let T:=rawTape (encodePair x w)
    ∃ t,t ≤ 64*(N+1)^2 ∧ GPath (M:=guard) (2*N+3) t
      (node guard.start 0 T) (node (if m=a+1 then guard.accept else guard.reject) 0 T) := by
  intro N T
  let U:=hole T 0
  have shape:N=2*a+1+m := rfl
  have Npos:0 < N := by omega
  have source (i:Nat) (hi:i < N) : T i=some ((encodePair x w) ⟨i,hi⟩) := by
    change (if h:i < N then some ((encodePair x w) ⟨i,h⟩) else none)=_
    rw [dif_pos hi]
  have high (i:Nat) (hi:N ≤ i) : T i=none := by
    change (if h:i < N then some ((encodePair x w) ⟨i,h⟩) else none)=none
    rw [dif_neg (by omega)]
  have uSource (i:Nat) (hi:0 < i) : U i=T i := by simp only [U,hole,put,if_neg (show i≠0 by omega)]
  have uHigh (i:Nat) (hi:N ≤ i) : U i=none := by rw [uSource i (by omega),high i hi]
  have uOcc (i:Nat) (hi:0 < i) (lo:i < N) : ∃ v,U i=some v := by rw [uSource i hi,source i lo];exact ⟨_,rfl⟩
  have origin:U 0=none := by simp [U,hole,put]
  by_cases zero:a=0
  · subst a
    have first:T 0=some true := by rw [source 0 Npos];exact congrArg some (encodePair_separator x w)
    have init:=bootstrap (P:=2*N+3) true T Npos (by omega) first high (by
      intro i hi lo;rw [source i lo];exact ⟨_,rfl⟩)
    obtain ⟨t,price,path⟩:=certificateDriver (N:=N) (m:=m) (off:=1) (c:=1) (P:=2*N+3) true U (by omega) (by omega) (by omega) origin uHigh uOcc 0 (by omega) (by omega)
    have restore:put U 0 (some true)=T := by rw [←first];exact putRestore T 0
    rw [restore] at path
    refine ⟨2*N+3+t,?_,?_⟩
    · have bound:=path_price N 0 m 0 t shape (by omega) price
      omega
    · simpa only [Bool.true_eq,↓reduceIte,Nat.mul_one,Nat.mul_zero,Nat.zero_add,Nat.add_zero] using appendP init path
  · have positive:0 < a := by omega
    have first:T 0=some false := by
      rw [source 0 Npos]
      exact congrArg some (encodePair_tag x w ⟨0,positive⟩)
    have init:=bootstrap (P:=2*N+3) false T Npos (by omega) first high (by
      intro i hi lo;rw [source i lo];exact ⟨_,rfl⟩)
    have tag(j:Nat)(pos:0 < j)(hj:j < a):U (2*j)=some false := by
      rw [uSource _ (by omega),source _ (by omega)]
      exact congrArg some (encodePair_tag x w ⟨j,hj⟩)
    have sep:U (2*a)=some true := by
      rw [uSource _ (by omega),source _ (by omega)]
      exact congrArg some (encodePair_separator x w)
    obtain ⟨tq,qprice,query⟩:=queryDriver (P:=2*N+3) U (by omega) (by omega) uHigh uOcc tag sep 1 (by omega) (by omega)
    obtain ⟨tc,cprice,cert⟩:=certificateDriver (N:=N) (m:=m) (off:=2*a+1) (c:=a+1) (P:=2*N+3) false U shape (by omega) (by omega) origin uHigh uOcc 0 (by omega) (by omega)
    have restore:put U 0 (some false)=T := by rw [←first];exact putRestore T 0
    rw [restore] at cert
    refine ⟨(2*N+5)+(tq+tc),?_,?_⟩
    · have qprice':tq ≤ 8*a*(N+a+3) := by
        simpa only [Nat.sub_add_cancel (show 1 ≤ a by omega)] using qprice
      have cprice':tc ≤ 8*(m+1)*(N+a+4) := by simpa [Nat.add_assoc] using cprice
      have bound:=path_price N a m tq tc shape qprice' cprice'
      omega
    · simpa only [Bool.false_eq,↓reduceIte,Nat.add_zero] using appendP init (appendP query cert)
private theorem first_terminal (M : UniformTM) {N B : Nat} (c : Config M.stateCount N B)
    (t : Nat) (last:(M.run t c).state=M.accept ∨ (M.run t c).state=M.reject) :
    ∃ s,s ≤ t ∧ ((M.run s c).state=M.accept ∨ (M.run s c).state=M.reject) ∧
      (∀ u,u < s → (M.run u c).state≠M.accept ∧ (M.run u c).state≠M.reject) := by
  classical
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases early:∃ u,u < t ∧ ((M.run u c).state=M.accept ∨ (M.run u c).state=M.reject)
    · obtain ⟨u,hu,event⟩:=early
      obtain ⟨s,hs,terminal,prior⟩:=ih u hu event
      exact ⟨s,hs.trans hu.le,terminal,prior⟩
    · refine ⟨t,le_rfl,last,?_⟩
      intro u hu
      exact ⟨fun h=>early ⟨u,hu,Or.inl h⟩,fun h=>early ⟨u,hu,Or.inr h⟩⟩
private theorem guard_run {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (room:2*pairLength a m+3 < tapeLength (pairLength a m) B) :
    ∃ t,t ≤ 64*(pairLength a m+1)^2 ∧
      (∀ u,u ≤ t → (guard.run u (initialConfig guard B (encodePair x w))).head.val ≤ 2*pairLength a m+3) ∧
      (∀ u,u < t → (guard.run u (initialConfig guard B (encodePair x w))).state≠guard.accept ∧
        (guard.run u (initialConfig guard B (encodePair x w))).state≠guard.reject) ∧
      guard.run t (initialConfig guard B (encodePair x w))=
        ⟨if m=a+1 then guard.accept else guard.reject,⟨0,by simp [tapeLength]⟩,
          (initialConfig guard B (encodePair x w)).tape⟩ := by
  obtain ⟨t,price,path⟩:=canonical_path x w
  have endpoint:=executeP (N:=pairLength a m) (B:=B) path room
  change guard.run t (initialConfig guard B (encodePair x w))=_ at endpoint
  have terminal:(guard.run t (initialConfig guard B (encodePair x w))).state=guard.accept ∨
      (guard.run t (initialConfig guard B (encodePair x w))).state=guard.reject := by
    rw [endpoint]
    change (if m=a+1 then guard.accept else guard.reject)=guard.accept ∨
      (if m=a+1 then guard.accept else guard.reject)=guard.reject
    by_cases h:m=a+1 <;> simp [h]
  obtain ⟨s,hs,event,prior⟩:=first_terminal guard _ t terminal
  have same:guard.run t (initialConfig guard B (encodePair x w))=guard.run s (initialConfig guard B (encodePair x w)) := by
    rcases event with ha|hr
    · exact guard.run_accept_of_le _ ha hs
    · exact guard.run_reject_of_le _ hr hs
  refine ⟨s,hs.trans price,?_,prior,?_⟩
  · intro u hu
    exact everyHead path room (by simp [tapeLength]) u (hu.trans hs)
  · rw [←same,endpoint]
    rfl
end CertificateGuardClosure
