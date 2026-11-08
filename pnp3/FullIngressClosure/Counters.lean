import FullIngressClosure.Paths
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","put","put"),
      ("BodyIngress.Native","BodyIngress","dest","dest"),
      ("BodyIngress.Native","BodyIngress","Path.append","pAppend"),
      ("BodyIngress.Native","BodyIngress","keep","pKeep"),
      ("BodyIngress.Native","BodyIngress","sweepR","pSweepR"),
      ("BodyIngress.Native","BodyIngress","sweepL","pSweepL"),
      ("FullIngressClosure.Paths","FullIngressClosure","Safe","Safe"),
      ("FullIngressClosure.Paths","FullIngressClosure","hop","hop")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique counter proof term {mod}/{key}: {found.map Prod.fst}"
private def Unary (T : Nat → Option Bool) (a w v : Nat) : Prop :=
  ∀ i, a < i → i < a+w+1 → T i=some (decide (i ≤ a+v))
private theorem unary_true {T a w v i} (unary : Unary T a w v)
    (lo : a < i) (hi : i ≤ a+v) (fits : v ≤ w) : T i=some true := by
  rw [unary i lo (by omega),decide_eq_true hi]
private theorem unary_false {T a w v i} (unary : Unary T a w v)
    (lo : a+v < i) (hi : i < a+w+1) : T i=some false := by
  rw [unary i (by omega) hi,decide_eq_false (by omega)]
private theorem unary_boundary {T a w v} (unary : Unary T a w v)
    (right : T (a+w+1)=none) (fits : v ≤ w) :
    T (a+v+1)=if v < w then some false else none := by
  split_ifs with short
  · exact unary_false unary (by omega) (by omega)
  · have eq : v=w := by omega
    simpa only [eq] using right
private structure Increment (k : Nat) (entry out : Fin (BodyIngress.machine k).stateCount) where
  scan : Fin (BodyIngress.machine k).stateCount
  back : Fin (BodyIngress.machine k).stateCount
  safeEntry : Safe k entry
  safeScan : Safe k scan
  safeBack : Safe k back
  start : (BodyIngress.machine k).step entry none=(scan,none,.right)
  pass : (BodyIngress.machine k).step scan (some true)=(scan,some true,.right)
  write : (BodyIngress.machine k).step scan (some false)=(back,some true,.left)
  ret : ∀ b, (BodyIngress.machine k).step back (some b)=(back,some b,.left)
  stop : (BodyIngress.machine k).step back none=(out,none,.stay)
private theorem increment {k lo hi entry out} (code : Increment k entry out)
    (T : Nat → Option Bool) (a w v : Nat) (lower : lo ≤ a) (upper : a+w+1 ≤ hi)
    (blank : T a=none) (unary : Unary T a w v) (room : v < w) :
    PPath k lo hi (2*v+3) (pNode entry a T) (pNode out a (put T (a+v+1) (some true))) := by
  let T' := put T (a+v+1) (some true)
  have one:=pKeep (k:=k) (lo:=lo) (hi:=hi) entry code.scan a (a+1) T .right
    ⟨code.safeEntry.1,code.safeEntry.2.1⟩ code.safeEntry.2.2
    ⟨lower,by omega⟩ ⟨by omega,by omega⟩ (by rw [blank]; exact code.start) rfl
  have scan:=pSweepR (k:=k) (lo:=lo) (hi:=hi) code.scan T (a+1) v (by omega) (by omega)
    ⟨code.safeScan.1,code.safeScan.2.1⟩ code.safeScan.2.2 (by
      intro i hl hu
      rw [unary_true unary (by omega) (by omega) (by omega)]
      exact code.pass)
  rw [show a+1+v=a+v+1 by omega] at scan
  have cell : T (a+v+1)=some false := unary_false unary (by omega) (by omega)
  have write:=hop (k:=k) (lo:=lo) (hi:=hi) code.scan code.back (a+v+1) (a+v) T (some true) .left code.safeScan
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by rw [cell]; exact code.write) (by simp [dest])
  have back:=pSweepL (k:=k) (lo:=lo) (hi:=hi) code.back T' a v lower (by omega)
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2 (by
      intro i hl hu
      have old : T' i=T i := by dsimp only [T',put]; rw [if_neg (by omega)]
      rw [old,unary_true unary hl hu (by omega)]
      exact code.ret true)
  have tblank : T' a=none := by dsimp only [T',put]; rw [if_neg (by omega)]; exact blank
  have last:=pKeep (k:=k) (lo:=lo) (hi:=hi) code.back out a a T' .stay
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2
    ⟨lower,by omega⟩ ⟨lower,by omega⟩ (by rw [tblank]; exact code.stop) rfl
  have path:=pAppend one (pAppend scan (pAppend write (pAppend back last)))
  simpa only [show 1+(v+(1+(v+1)))=2*v+3 by omega] using path
private structure Decrement (k : Nat) (entry yes no : Fin (BodyIngress.machine k).stateCount) where
  scan : Fin (BodyIngress.machine k).stateCount
  pick : Fin (BodyIngress.machine k).stateCount
  back : Fin (BodyIngress.machine k).stateCount
  safeEntry : Safe k entry
  safeScan : Safe k scan
  safePick : Safe k pick
  safeBack : Safe k back
  start : (BodyIngress.machine k).step entry none=(scan,none,.right)
  pass : (BodyIngress.machine k).step scan (some true)=(scan,some true,.right)
  boundaryFalse : (BodyIngress.machine k).step scan (some false)=(pick,some false,.left)
  boundaryNone : (BodyIngress.machine k).step scan none=(pick,none,.left)
  write : (BodyIngress.machine k).step pick (some true)=(back,some false,.left)
  zero : (BodyIngress.machine k).step pick none=(no,none,.stay)
  ret : ∀ b, (BodyIngress.machine k).step back (some b)=(back,some b,.left)
  stop : (BodyIngress.machine k).step back none=(yes,none,.stay)
private theorem decrement_positive {k lo hi entry yes no} (code : Decrement k entry yes no)
    (T : Nat → Option Bool) (a w v : Nat) (lower : lo ≤ a) (upper : a+w+1 ≤ hi)
    (left : T a=none) (right : T (a+w+1)=none) (unary : Unary T a w v)
    (positive : 0 < v) (room : v ≤ w) :
    PPath k lo hi (2*v+3) (pNode entry a T) (pNode yes a (put T (a+v) (some false))) := by
  let T' := put T (a+v) (some false)
  have one:=pKeep (k:=k) (lo:=lo) (hi:=hi) entry code.scan a (a+1) T .right
    ⟨code.safeEntry.1,code.safeEntry.2.1⟩ code.safeEntry.2.2
    ⟨lower,by omega⟩ ⟨by omega,by omega⟩ (by rw [left]; exact code.start) rfl
  have scan:=pSweepR (k:=k) (lo:=lo) (hi:=hi) code.scan T (a+1) v (by omega) (by omega)
    ⟨code.safeScan.1,code.safeScan.2.1⟩ code.safeScan.2.2 (by
      intro i hl hu
      rw [unary_true unary (by omega) (by omega) room]
      exact code.pass)
  rw [show a+1+v=a+v+1 by omega] at scan
  have atBoundary : (BodyIngress.machine k).step code.scan (T (a+v+1))=(code.pick,T (a+v+1),.left) := by
    rw [unary_boundary unary right room]
    split_ifs
    · exact code.boundaryFalse
    · exact code.boundaryNone
  have boundary:=pKeep (k:=k) (lo:=lo) (hi:=hi) code.scan code.pick (a+v+1) (a+v) T .left
    ⟨code.safeScan.1,code.safeScan.2.1⟩ code.safeScan.2.2
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ atBoundary (by simp [dest])
  have write:=hop (k:=k) (lo:=lo) (hi:=hi) code.pick code.back (a+v) (a+(v-1)) T (some false) .left code.safePick
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [unary_true unary (by omega) le_rfl room]; exact code.write)
    (by dsimp only [dest]; omega)
  have back:=pSweepL (k:=k) (lo:=lo) (hi:=hi) code.back T' a (v-1) lower (by omega)
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2 (by
      intro i hl hu
      have old : T' i=T i := by dsimp only [T',put]; rw [if_neg (by omega)]
      rw [old,unary_true unary hl (by omega) room]
      exact code.ret true)
  have tblank : T' a=none := by dsimp only [T',put]; rw [if_neg (by omega)]; exact left
  have last:=pKeep (k:=k) (lo:=lo) (hi:=hi) code.back yes a a T' .stay
    ⟨code.safeBack.1,code.safeBack.2.1⟩ code.safeBack.2.2
    ⟨lower,by omega⟩ ⟨lower,by omega⟩ (by rw [tblank]; exact code.stop) rfl
  have path:=pAppend one (pAppend scan (pAppend boundary (pAppend write (pAppend back last))))
  simpa only [show 1+(v+(1+(1+(v-1+1))))=2*v+3 by omega] using path
private theorem decrement_zero {k lo hi entry yes no} (code : Decrement k entry yes no)
    (T : Nat → Option Bool) (a w : Nat) (lower : lo ≤ a) (upper : a+w+1 ≤ hi)
    (left : T a=none) (right : T (a+w+1)=none) (unary : Unary T a w 0) :
    PPath k lo hi 3 (pNode entry a T) (pNode no a T) := by
  have one:=pKeep (k:=k) (lo:=lo) (hi:=hi) entry code.scan a (a+1) T .right
    ⟨code.safeEntry.1,code.safeEntry.2.1⟩ code.safeEntry.2.2
    ⟨lower,by omega⟩ ⟨by omega,by omega⟩ (by rw [left]; exact code.start) rfl
  have atBoundary : (BodyIngress.machine k).step code.scan (T (a+1))=(code.pick,T (a+1),.left) := by
    have cell:=unary_boundary unary right (Nat.zero_le w)
    simp only [Nat.add_zero] at cell
    rw [cell]
    split_ifs
    · exact code.boundaryFalse
    · exact code.boundaryNone
  have boundary:=pKeep (k:=k) (lo:=lo) (hi:=hi) code.scan code.pick (a+1) a T .left
    ⟨code.safeScan.1,code.safeScan.2.1⟩ code.safeScan.2.2
    ⟨by omega,by omega⟩ ⟨lower,by omega⟩ atBoundary (by simp [dest])
  have last:=pKeep (k:=k) (lo:=lo) (hi:=hi) code.pick no a a T .stay
    ⟨code.safePick.1,code.safePick.2.1⟩ code.safePick.2.2
    ⟨lower,by omega⟩ ⟨lower,by omega⟩ (by rw [left]; exact code.zero) rfl
  exact pAppend one (pAppend boundary last)
private theorem unary_after_increment {T a w v} (unary : Unary T a w v) (_room : v < w) :
    Unary (put T (a+v+1) (some true)) a w (v+1) := by
  intro i hl hu
  dsimp only [put]
  split_ifs with eq
  · subst i
    rw [decide_eq_true (by omega)]
  · rw [unary i hl hu]
    congr 1
    exact decide_eq_decide.mpr (by omega)
private theorem unary_after_decrement {T a w v} (unary : Unary T a w v) (positive : 0 < v) :
    Unary (put T (a+v) (some false)) a w (v-1) := by
  intro i hl hu
  dsimp only [put]
  split_ifs with eq
  · subst i
    rw [decide_eq_false (by omega)]
  · rw [unary i hl hu]
    congr 1
    exact decide_eq_decide.mpr (by omega)
end FullIngressClosure
