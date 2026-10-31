import FullIngressClosure.Paint
import FullIngressClosure.Certificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","Path.append","pAppend"),
      ("BodyIngress.Native","BodyIngress","put","put"),
      ("BodyIngress.Native","BodyIngress","dest","dest"),
      ("BodyIngress.Native","BodyIngress","keep","pKeep"),
      ("BodyIngress.Native","BodyIngress","sweepR","pSweepR"),
      ("BodyIngress.Native","BodyIngress","sweepL","pSweepL"),
      ("FullIngressClosure.Paths","FullIngressClosure","hop","hop"),
      ("FullIngressClosure.Paths","FullIngressClosure","Safe","Safe"),
      ("FullIngressClosure.Rows","FullIngressClosure","native_row","nativeRow"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st","st"),
      ("FullIngressClosure.Certificates","FullIngressClosure","st_small","stSmall"),
      ("FullIngressClosure.Certificates","FullIngressClosure","safeNative","safeNative")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique three-cell padding term {mod}/{key}: {found.map Prod.fst}"
private def prefixFalse (T : Nat → Option Bool) (a f : Nat) : Nat → Option Bool :=
  fun i=>if a < i ∧ i ≤ a+f then some false else T i
private theorem prefix_put (T : Nat → Option Bool) (a f : Nat) :
    put (prefixFalse T a f) (a+f+1) (some false)=prefixFalse T a (f+1) := by
  funext i
  dsimp only [put,prefixFalse]
  split_ifs <;> first | rfl | (exfalso; omega)
private theorem prefix_old (T : Nat → Option Bool) (a f i : Nat) (outside : i ≤ a ∨ a+f < i) :
    prefixFalse T a f i=T i := by dsimp only [prefixFalse]; rw [if_neg (by omega)]
private theorem prefix_same {T a f} (cells : ∀ i,a < i → i ≤ a+f → T i=some false) :
    prefixFalse T a f=T := by
  funext i
  dsimp only [prefixFalse]
  split_ifs with inside
  · exact (cells i inside.1 inside.2).symm
  · rfl
private theorem stack_padding (k lo P a f : Nat) (T : Nat → Option Bool)
    (lower : lo ≤ a) (upper : a+f+4 ≤ P) (blank : T a=none)
    (cells : ∀ i,a < i → i ≤ a+f → T i=some false)
    (fresh : ∀ j,1 ≤ j → j ≤ 4 → T (a+f+j)=none) :
    PPath k lo P (2*f+10) (pNode (st k 645) a T)
      (pNode (st k 652) a (prefixFalse T a (f+3))) := by
  let E (j : Nat):=prefixFalse T a (f+j)
  have first:=pKeep (k:=k) (lo:=lo) (hi:=P) (st k 645) (st k 646) a (a+1) T .right
    ⟨(safeNative k 645 (by decide)).1,(safeNative k 645 (by decide)).2.1⟩
    (safeNative k 645 (by decide)).2.2 ⟨lower,by omega⟩ ⟨by omega,by omega⟩
    (by rw [blank,stSmall k 645 (by decide),nativeRow]; rfl) rfl
  have scan:=pSweepR (k:=k) (lo:=lo) (hi:=P) (st k 646) T (a+1) f (by omega) (by omega)
    ⟨(safeNative k 646 (by decide)).1,(safeNative k 646 (by decide)).2.1⟩
    (safeNative k 646 (by decide)).2.2 (by
      intro i il iu
      rw [cells i (by omega) (by omega),stSmall k 646 (by decide),nativeRow]; rfl)
  rw [show a+1+f=a+f+1 by omega] at scan
  have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) (st k 646) (st k 647) (a+f+1) (a+f+1) T .stay
    ⟨(safeNative k 646 (by decide)).1,(safeNative k 646 (by decide)).2.1⟩
    (safeNative k 646 (by decide)).2.2 ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [fresh 1 (by decide) (by decide),stSmall k 646 (by decide),nativeRow]; rfl) rfl
  have writes (j : Nat) (h : j < 3) :
      PPath k lo P 1 (pNode (st k (647+j)) (a+f+j+1) (E j))
        (pNode (st k (648+j)) (a+f+j+2) (E (j+1))) := by
    have old : E j (a+f+j+1)=none := by
      change prefixFalse T a (f+j) (a+f+j+1)=none
      rw [prefix_old T a (f+j) _ (by omega)]
      simpa only [Nat.add_assoc] using fresh (j+1) (by omega) (by omega)
    have one:=hop (k:=k) (lo:=lo) (hi:=P) (st k (647+j)) (st k (648+j))
      (a+f+j+1) (a+f+j+2) (E j) (some false) .right
      (safeNative k (647+j) (by omega)) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by
        rw [old]
        interval_cases j <;> rw [stSmall k _ (by decide),nativeRow] <;> rfl) rfl
    have eq : put (E j) (a+f+j+1) (some false)=E (j+1) := by
      dsimp only [E]
      rw [show a+f+j+1=a+(f+j)+1 by omega,prefix_put]
      congr 1
    rwa [eq] at one
  have w0:=writes 0 (by decide)
  have w1:=writes 1 (by decide)
  have w2:=writes 2 (by decide)
  have e0 : E 0=T := by dsimp only [E,Nat.add_zero]; exact prefix_same cells
  rw [e0] at w0
  have endBlank : E 3 (a+f+4)=none := by
    change prefixFalse T a (f+3) (a+f+4)=none
    rw [prefix_old T a (f+3) _ (by omega)]
    exact fresh 4 (by decide) (by decide)
  have backOne:=pKeep (k:=k) (lo:=lo) (hi:=P) (st k 650) (st k 651) (a+f+4) (a+f+3) (E 3) .left
    ⟨(safeNative k 650 (by decide)).1,(safeNative k 650 (by decide)).2.1⟩
    (safeNative k 650 (by decide)).2.2 ⟨by omega,upper⟩ ⟨by omega,by omega⟩
    (by rw [endBlank,stSmall k 650 (by decide),nativeRow]; rfl) (by simp [dest])
  have back:=pSweepL (k:=k) (lo:=lo) (hi:=P) (st k 651) (E 3) a (f+3) lower (by omega)
    ⟨(safeNative k 651 (by decide)).1,(safeNative k 651 (by decide)).2.1⟩
    (safeNative k 651 (by decide)).2.2 (by
      intro i il iu
      have bit : E 3 i=some false := by dsimp only [E,prefixFalse]; rw [if_pos ⟨il,iu⟩]
      rw [bit,stSmall k 651 (by decide),nativeRow]; rfl)
  rw [show a+(f+3)=a+f+3 by omega] at back
  have last:=pKeep (k:=k) (lo:=lo) (hi:=P) (st k 651) (st k 652) a a (E 3) .stay
    ⟨(safeNative k 651 (by decide)).1,(safeNative k 651 (by decide)).2.1⟩
    (safeNative k 651 (by decide)).2.2 ⟨lower,by omega⟩ ⟨lower,by omega⟩
    (by
      have old : E 3 a=T a:=prefix_old T a (f+3) a (Or.inl le_rfl)
      rw [old,blank,stSmall k 651 (by decide),nativeRow]; rfl) rfl
  have path:=pAppend first (pAppend scan (pAppend stop (pAppend w0 (pAppend w1 (pAppend w2 (pAppend backOne (pAppend back last)))))))
  simpa only [Nat.add_zero,show 1+(f+(1+(1+(1+(1+(1+(f+3+1)))))))=2*f+10 by omega,
    show a+f+3=a+(f+3) by omega] using path
end FullIngressClosure
