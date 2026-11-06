import FullIngressClosure.Paths
import FullIngressClosure.Costs
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
      ("BodyIngress.Native","BodyIngress","sweepR","pSweepR"),
      ("BodyIngress.Native","BodyIngress","sweepL","pSweepL"),
      ("FullIngressClosure.Paths","FullIngressClosure","Safe","Safe"),
      ("FullIngressClosure.Paths","FullIngressClosure","hop","hop"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR","RouteR"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL","RouteL"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.execute","routeR"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.execute","routeL")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique clone proof term {mod}/{key}: {found.map Prod.fst}"
private theorem keep {k lo hi : Nat} (s q : Fin (BodyIngress.machine k).stateCount)
    (h h' : Nat) (T : Nat → Option Bool) (mv : Move) (safe : Safe k s)
    (hb : lo ≤ h ∧ h ≤ hi) (ha : lo ≤ h' ∧ h' ≤ hi)
    (row : (BodyIngress.machine k).step s (T h)=(q,T h,mv)) (move : dest h mv=h') :
    PPath k lo hi 1 (pNode s h T) (pNode q h' T) :=
  pKeep s q h h' T mv ⟨safe.1,safe.2.1⟩ safe.2.2 hb ha row move
private theorem sweepR {k lo hi : Nat} (s : Fin (BodyIngress.machine k).stateCount)
    (T : Nat → Option Bool) (h w : Nat) (safe : Safe k s)
    (lower : lo ≤ h) (upper : h+w ≤ hi)
    (rows : ∀ i,h ≤ i → i < h+w → (BodyIngress.machine k).step s (T i)=(s,T i,.right)) :
    PPath k lo hi w (pNode s h T) (pNode s (h+w) T) :=
  pSweepR s T h w lower upper ⟨safe.1,safe.2.1⟩ safe.2.2 rows
private theorem sweepL {k lo hi : Nat} (s : Fin (BodyIngress.machine k).stateCount)
    (T : Nat → Option Bool) (h w : Nat) (safe : Safe k s)
    (lower : lo ≤ h) (upper : h+w ≤ hi)
    (rows : ∀ i,h < i → i ≤ h+w → (BodyIngress.machine k).step s (T i)=(s,T i,.left)) :
    PPath k lo hi w (pNode s (h+w) T) (pNode s h T) :=
  pSweepL s T h w lower upper ⟨safe.1,safe.2.1⟩ safe.2.2 rows
private def fill (T : Nat → Option Bool) (d v : Nat) : Nat → Option Bool :=
  fun i=>if d < i ∧ i ≤ d+v then some false else T i
private theorem fill_old (T : Nat → Option Bool) (d v i : Nat) (outside : i ≤ d ∨ d+v < i) :
    fill T d v i=T i := by rw [fill,if_neg (by omega)]
private structure CopyFrame (T : Nat → Option Bool) (lo P a b w f : Nat) (D : Nat → Nat) : Prop where
  apart : a+1 ≤ b
  lower : lo ≤ D a
  fit : D b+f+w+1 ≤ P
  sourceRight : D (a+1)=D a+w+1
  monotone : ∀ u v,a ≤ u → u ≤ v → v ≤ b → D u ≤ D v
  rise : ∀ u,a ≤ u → u < b → D u < D (u+1)
  blank : ∀ u,a ≤ u → u ≤ b → T (D u)=none
  cells : ∀ u i,a+1 ≤ u → u < b → D u < i → i < D (u+1) → ∃ bit,T i=some bit
  source : ∀ i,D a < i → i < D a+w+1 → ∃ bit,T i=some bit
  prior : ∀ i,D b < i → i ≤ D b+f → T i=some false
  fresh : ∀ i,D b+f < i → i ≤ D b+f+w+1 → T i=none
private structure CopyBranch (k a b : Nat) (read : Fin (BodyIngress.machine k).stateCount) (bit : Bool) where
  tail : Fin (BodyIngress.machine k).stateCount
  finishTail : Fin (BodyIngress.machine k).stateCount
  putAt : Fin (BodyIngress.machine k).stateCount
  seekEnd : Fin (BodyIngress.machine k).stateCount
  append : Fin (BodyIngress.machine k).stateCount
  ret : Fin (BodyIngress.machine k).stateCount
  hole : Fin (BodyIngress.machine k).stateCount
  restore : Fin (BodyIngress.machine k).stateCount
  seek : Fin (BodyIngress.machine k).stateCount
  safeTail : Safe k tail
  safePut : Safe k putAt
  safeFind : Safe k seekEnd
  safeAppend : Safe k append
  safeRet : Safe k ret
  safeRestore : Safe k restore
  safeSeek : Safe k seek
  lift : (BodyIngress.machine k).step read (some bit)=(tail,none,.right)
  tailPass : ∀ v,(BodyIngress.machine k).step tail (some v)=(tail,some v,.right)
  tailEnd : (BodyIngress.machine k).step tail none=(finishTail,none,.stay)
  outward : RouteR k (a+1) b finishTail putAt
  enter : (BodyIngress.machine k).step putAt none=(seekEnd,none,.right)
  findPass : ∀ v,(BodyIngress.machine k).step seekEnd (some v)=(seekEnd,some v,.right)
  findEnd : (BodyIngress.machine k).step seekEnd none=(append,none,.stay)
  write : (BodyIngress.machine k).step append none=(ret,some false,.left)
  retPass : ∀ v,(BodyIngress.machine k).step ret (some v)=(ret,some v,.left)
  retEnd : (BodyIngress.machine k).step ret none=(hole,none,.stay)
  inward : RouteL k b (a+1) hole restore
  seekStart : (BodyIngress.machine k).step restore none=(seek,none,.left)
  seekPass : ∀ v,(BodyIngress.machine k).step seek (some v)=(seek,some v,.left)
  restoreBit : (BodyIngress.machine k).step seek none=(read,some bit,.right)
private structure CopyRows (k a b : Nat) (entry read finish out : Fin (BodyIngress.machine k).stateCount) where
  safeEntry : Safe k entry
  safeRead : Safe k read
  safeFinish : Safe k finish
  enter : (BodyIngress.machine k).step entry none=(read,none,.right)
  branch : ∀ bit,CopyBranch k a b read bit
  done : (BodyIngress.machine k).step read none=(finish,none,.left)
  finishPass : ∀ bit,(BodyIngress.machine k).step finish (some bit)=(finish,some bit,.left)
  finishEnd : (BodyIngress.machine k).step finish none=(out,none,.stay)
private theorem clone_round {k lo P a b w f entry read finish out}
    (code : CopyRows k a b entry read finish out) (T : Nat → Option Bool) (D : Nat → Nat)
    (frame : CopyFrame T lo P a b w f D) (j : Nat) (more : j < w) :
    ∃ t,t ≤ 8*(P+16) ∧ PPath k lo P t
      (pNode read (D a+j+1) (fill T (D b) (f+j)))
      (pNode read (D a+j+2) (fill T (D b) (f+(j+1)))) := by
  let h:=D a+j+1
  let Z:=D b
  let B:=fill T Z (f+j)
  let C:=put B h none
  let E:=fill T Z (f+(j+1))
  let V:=put E h none
  have apart:=frame.apart
  have sourceRight:=frame.sourceRight
  have upper:=frame.fit
  have lower:=frame.lower
  have dBound : D a+w+1 ≤ Z := by
    rw [← sourceRight]
    exact frame.monotone _ _ (by omega) apart le_rfl
  have oldB (i : Nat) (hi : i ≤ Z) : B i=T i := fill_old T Z (f+j) i (Or.inl hi)
  have oldC (i : Nat) (hi : i ≤ Z) (ne : i ≠ h) : C i=T i := by
    dsimp only [C,put]; rw [if_neg ne,oldB i hi]
  have oldV (i : Nat) (hi : i ≤ Z) (ne : i ≠ h) : V i=T i := by
    dsimp only [V,put]; rw [if_neg ne]
    exact fill_old T Z (f+(j+1)) i (Or.inl hi)
  obtain ⟨bit,hbit⟩:=frame.source h (by dsimp only [h]; omega) (by dsimp only [h]; omega)
  let rows:=code.branch bit
  have add : put C (Z+f+j+1) (some false)=V := by
    funext i
    dsimp only [C,B,V,E,fill,put]
    split_ifs <;> first | rfl | (exfalso; omega)
  have restore : put V h (some bit)=E := by
    have eq : E h=some bit := by
      change fill T Z (f+(j+1)) h=some bit
      rw [fill_old T Z (f+(j+1)) h (Or.inl (by dsimp only [h]; omega))]
      exact hbit
    funext i
    by_cases same : i=h
    · subst i; simp only [put,ite_true,eq]
    · dsimp only [V,put]; rw [if_neg same,if_neg same]
  have one:=hop (k:=k) (lo:=lo) (hi:=P) read rows.tail h (h+1) B none .right code.safeRead
    ⟨by dsimp only [h]; omega,by dsimp only [h]; omega⟩
    ⟨by dsimp only [h]; omega,by dsimp only [h]; omega⟩
    (by rw [oldB h (by dsimp only [h]; omega),hbit]; exact rows.lift) rfl
  have tail:=sweepR (k:=k) (lo:=lo) (hi:=P) rows.tail C (h+1) (w-j-1) rows.safeTail
    (by dsimp only [h]; omega) (by dsimp only [h]; omega) (by
      intro i hl hu
      rw [oldC i (by dsimp only [h] at hu; omega) (by omega)]
      obtain ⟨v,hv⟩:=frame.source i (by dsimp only [h] at hl; omega) (by dsimp only [h] at hu; omega)
      rw [hv]; exact rows.tailPass v)
  rw [show h+1+(w-j-1)=D (a+1) by dsimp only [h]; omega] at tail
  have tailEnd:=keep (k:=k) (lo:=lo) (hi:=P) rows.tail rows.finishTail (D (a+1)) (D (a+1)) C .stay rows.safeTail
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [oldC (D (a+1)) (by omega) (by dsimp only [h]; omega),frame.blank _ (by omega) apart]; exact rows.tailEnd) rfl
  have outward:=routeR (lo:=lo) (hi:=P) rows.outward D C (by omega) (by omega)
    (by intro u hl hu; exact frame.rise u (by omega) hu)
    (by intro u v hl uv vb; exact frame.monotone u v (by omega) uv vb)
    (by intro u hl hu
        rw [oldC _ (frame.monotone _ _ (by omega) hu le_rfl) (by
          have d:=frame.monotone (a+1) u (by omega) hl hu
          dsimp only [h]; omega)]
        exact frame.blank u (by omega) hu)
    (by intro u i hl hu il iu
        rw [oldC i (by have d:=frame.monotone (u+1) b (by omega) (by omega) le_rfl; omega) (by
          have d:=frame.monotone (a+1) u (by omega) hl (by omega)
          dsimp only [h]; omega)]
        exact frame.cells u i hl hu il iu)
  have enter:=keep (k:=k) (lo:=lo) (hi:=P) rows.putAt rows.seekEnd Z (Z+1) C .right rows.safePut
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [oldC Z le_rfl (by dsimp only [h]; omega),frame.blank b (by omega) le_rfl]; exact rows.enter) rfl
  have destScan:=sweepR (k:=k) (lo:=lo) (hi:=P) rows.seekEnd C (Z+1) (f+j) rows.safeFind
    (by omega) (by omega) (by
      intro i hl hu
      dsimp only [C,put]
      rw [if_neg (by dsimp only [h]; omega)]
      dsimp only [B,fill]
      rw [if_pos (by omega)]
      exact rows.findPass false)
  rw [show Z+1+(f+j)=Z+f+j+1 by omega] at destScan
  have nextBlank : C (Z+f+j+1)=none := by
    dsimp only [C,put]
    rw [if_neg (by dsimp only [h]; omega)]
    dsimp only [B,fill]
    rw [if_neg (by omega)]
    exact frame.fresh _ (by omega) (by omega)
  have found:=keep (k:=k) (lo:=lo) (hi:=P) rows.seekEnd rows.append (Z+f+j+1) (Z+f+j+1) C .stay rows.safeFind
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by rw [nextBlank]; exact rows.findEnd) rfl
  have write:=hop (k:=k) (lo:=lo) (hi:=P) rows.append rows.ret (Z+f+j+1) (Z+f+j) C (some false) .left rows.safeAppend
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by rw [nextBlank]; exact rows.write) (by simp [dest])
  rw [add] at write
  have back:=sweepL (k:=k) (lo:=lo) (hi:=P) rows.ret V Z (f+j) rows.safeRet
    (by omega) (by omega) (by
      intro i hl hu
      dsimp only [V,put]
      rw [if_neg (by dsimp only [h]; omega)]
      dsimp only [E,fill]
      rw [if_pos (by omega)]
      exact rows.retPass false)
  rw [show Z+(f+j)=Z+f+j by omega] at back
  have retEnd:=keep (k:=k) (lo:=lo) (hi:=P) rows.ret rows.hole Z Z V .stay rows.safeRet
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [oldV Z le_rfl (by dsimp only [h]; omega),frame.blank b (by omega) le_rfl]; exact rows.retEnd) rfl
  have inward:=routeL (lo:=lo) (hi:=P) rows.inward D V (by omega) (by omega)
    (by intro u hl hu; exact frame.rise u (by omega) hu)
    (by intro u v hl uv vb; exact frame.monotone u v (by omega) uv vb)
    (by intro u hl hu
        rw [oldV _ (frame.monotone _ _ (by omega) hu le_rfl) (by
          have d:=frame.monotone (a+1) u (by omega) hl hu
          dsimp only [h]; omega)]
        exact frame.blank u (by omega) hu)
    (by intro u i hl hu il iu
        rw [oldV i (by have d:=frame.monotone (u+1) b (by omega) (by omega) le_rfl; omega) (by
          have d:=frame.monotone (a+1) u (by omega) hl (by omega)
          dsimp only [h]; omega)]
        exact frame.cells u i hl hu il iu)
  have seekStart:=keep (k:=k) (lo:=lo) (hi:=P) rows.restore rows.seek (D (a+1)) (D (a+1)-1) V .left rows.safeRestore
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    (by rw [oldV (D (a+1)) (by omega) (by dsimp only [h]; omega),frame.blank _ (by omega) apart]; exact rows.seekStart) rfl
  have seek:=sweepL (k:=k) (lo:=lo) (hi:=P) rows.seek V h (w-j-1) rows.safeSeek
    (by dsimp only [h]; omega) (by dsimp only [h]; omega) (by
      intro i hl hu
      rw [oldV i (by dsimp only [h] at hu; omega) (by omega)]
      obtain ⟨v,hv⟩:=frame.source i (by dsimp only [h] at hl; omega) (by dsimp only [h] at hu; omega)
      rw [hv]; exact rows.seekPass v)
  rw [show h+(w-j-1)=D (a+1)-1 by dsimp only [h]; omega] at seek
  have restored:=hop (k:=k) (lo:=lo) (hi:=P) rows.seek read h (h+1) V (some bit) .right rows.safeSeek
    ⟨by dsimp only [h]; omega,by dsimp only [h]; omega⟩
    ⟨by dsimp only [h]; omega,by dsimp only [h]; omega⟩
    (by dsimp only [V,put]; rw [if_pos rfl]; exact rows.restoreBit) rfl
  rw [restore] at restored
  have path:=pAppend one (pAppend tail (pAppend tailEnd (pAppend outward (pAppend enter (pAppend destScan
    (pAppend found (pAppend write (pAppend back (pAppend retEnd (pAppend inward (pAppend seekStart (pAppend seek restored))))))))))))
  dsimp only [h,Z,B,E] at path
  rw [clone_sum (w-j-1) (D b-D (a+1)+(b-(a+1))) (f+j)] at path
  rw [show D a+j+1+1=D a+j+2 by omega] at path
  refine ⟨_,?_,path⟩
  have span : b-(a+1) ≤ D b-D (a+1) :=
    discrete_span D (a+1) b apart (by intro u hl hu; exact frame.rise u (by omega) hu)
  have width : w ≤ P := by omega
  have prefixWidth : f+j ≤ P := by omega
  have dist : D b-D (a+1) ≤ P := by omega
  omega
end FullIngressClosure
