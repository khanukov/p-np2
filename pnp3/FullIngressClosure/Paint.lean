import FullIngressClosure.Paths
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","Path.nil","pNil"),
      ("BodyIngress.Native","BodyIngress","Path.append","pAppend"),
      ("BodyIngress.Native","BodyIngress","put","put"),
      ("BodyIngress.Native","BodyIngress","dest","dest"),
      ("BodyIngress.Native","BodyIngress","keep","pKeep"),
      ("BodyIngress.Native","BodyIngress","sweepL","pSweepL"),
      ("FullIngressClosure.Paths","FullIngressClosure","Safe","Safe"),
      ("FullIngressClosure.Paths","FullIngressClosure","hop","hop")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique physical paint term {mod}/{key}: {found.map Prod.fst}"
private structure PaintCode (k : Nat) (entry out : Fin (BodyIngress.machine k).stateCount) (value : Bool) where
  scan : Fin (BodyIngress.machine k).stateCount
  back : Fin (BodyIngress.machine k).stateCount
  safeEntry : Safe k entry
  safeScan : Safe k scan
  safeBack : Safe k back
  enter : (BodyIngress.machine k).step entry none=(scan,none,.right)
  write : ∀ old,(BodyIngress.machine k).step scan (some old)=(scan,some value,.right)
  stop : (BodyIngress.machine k).step scan none=(back,none,.left)
  retreat : ∀ old,(BodyIngress.machine k).step back (some old)=(back,some old,.left)
  done : (BodyIngress.machine k).step back none=(out,none,.stay)
private def painted (T : Nat → Option Bool) (a w : Nat) (value : Bool) : Nat → Option Bool :=
  fun i=>if a < i ∧ i ≤ a+w then some value else T i
private theorem painted_zero (T : Nat → Option Bool) (a : Nat) (value : Bool) : painted T a 0 value=T := by
  funext i
  dsimp only [painted]
  rw [if_neg (by omega)]
private theorem painted_step (T : Nat → Option Bool) (a j : Nat) (value : Bool) :
    put (painted T a j value) (a+j+1) (some value)=painted T a (j+1) value := by
  funext i
  dsimp only [put,painted]
  split_ifs <;> first | rfl | (exfalso; omega)
private theorem scan_paint {k lo P entry out value} (code : PaintCode k entry out value)
    (T : Nat → Option Bool) (a w : Nat) (lower : lo ≤ a) (upper : a+w+1 ≤ P)
    (cells : ∀ i,a < i → i < a+w+1 → ∃ bit,T i=some bit) (count j : Nat) (total : j+count=w) :
    PPath k lo P count (pNode code.scan (a+j+1) (painted T a j value))
      (pNode code.scan (a+w+1) (painted T a w value)) := by
  induction count generalizing j with
  | zero =>
    have same : j=w:=by omega
    subst j
    apply pNil
    change lo ≤ a+w+1 ∧ a+w+1 ≤ P
    exact ⟨by omega,upper⟩
  | succ count ih =>
    obtain ⟨bit,hbit⟩:=cells (a+j+1) (by omega) (by omega)
    have row : (BodyIngress.machine k).step code.scan (painted T a j value (a+j+1))=(code.scan,some value,.right) := by
      dsimp only [painted]
      rw [if_neg (by omega),hbit]
      exact code.write bit
    have one:=hop (k:=k) (lo:=lo) (hi:=P) code.scan code.scan (a+j+1) (a+j+2) (painted T a j value) (some value) .right code.safeScan
      ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ row rfl
    rw [painted_step,show a+j+2=a+(j+1)+1 by omega] at one
    have rest:=ih (j+1) (by omega)
    simpa only [show 1+count=count+1 by omega] using pAppend one rest
private theorem paint_price (w : Nat) : 1+(w+(1+(w+1)))=2*w+3 := by omega
private theorem paint {k lo P entry out value} (code : PaintCode k entry out value)
    (T : Nat → Option Bool) (a w : Nat) (lower : lo ≤ a) (upper : a+w+1 ≤ P)
    (left : T a=none) (right : T (a+w+1)=none)
    (cells : ∀ i,a < i → i < a+w+1 → ∃ bit,T i=some bit) :
    PPath k lo P (2*w+3) (pNode entry a T) (pNode out a (painted T a w value)) := by
  let E:=painted T a w value
  have first:=pKeep (k:=k) (lo:=lo) (hi:=P) entry code.scan a (a+1) T .right
    ⟨code.safeEntry.1,code.safeEntry.2.1⟩ code.safeEntry.2.2 ⟨lower,by omega⟩ ⟨by omega,by omega⟩
    (by rw [left]; exact code.enter) rfl
  have scan:=scan_paint code T a w lower upper cells w 0 (by omega)
  simp only [Nat.add_zero,painted_zero] at scan
  have atRight : E (a+w+1)=none := by dsimp only [E,painted]; rw [if_neg (by omega)]; exact right
  have stop:=pKeep (k:=k) (lo:=lo) (hi:=P) code.scan code.back (a+w+1) (a+w) E .left
    ⟨code.safeScan.1,code.safeScan.2.1⟩ code.safeScan.2.2 ⟨by omega,upper⟩ ⟨by omega,by omega⟩
    (by rw [atRight]; exact code.stop) (by simp [dest])
  have back:=pSweepL (k:=k) (lo:=lo) (hi:=P) code.back E a w lower (by omega)
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2 (by
      intro i hl hu
      dsimp only [E,painted]
      rw [if_pos ⟨hl,hu⟩]
      exact code.retreat value)
  have atLeft : E a=none := by dsimp only [E,painted]; rw [if_neg (by omega)]; exact left
  have last:=pKeep (k:=k) (lo:=lo) (hi:=P) code.back out a a E .stay
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2 ⟨lower,by omega⟩ ⟨lower,by omega⟩
    (by rw [atLeft]; exact code.done) rfl
  have path:=pAppend first (pAppend scan (pAppend stop (pAppend back last)))
  rw [paint_price] at path
  exact path
end FullIngressClosure
