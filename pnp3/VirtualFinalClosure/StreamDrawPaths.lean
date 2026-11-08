import VirtualFinalClosure.StreamPhasePaths
namespace VirtualFinalClosure.StreamDrawPaths
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",2),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","Path.cons","consPath",3),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Edge.mk","edgeMk",3),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","q","q",0),
      ("VirtualFinalClosure.StreamPhasePaths","VirtualFinalClosure.StreamPhasePaths","unpaid","unpaid",0),
      ("Stream.Kernel","Stream","draw","draw",0),
      ("Stream.Kernel","Stream","put","streamPut",0),
      ("Stream.Kernel","Stream","modeOf","modeOf",0),
      ("Stream.Kernel","Stream","mode_correct","mode_correct",1),
      ("Stream.Kernel","Stream","draw_low","draw_low",1),
      ("Stream.Kernel","Stream","draw_high","draw_high",1),
      ("Stream.Kernel","Stream","draw_occupied","draw_occupied",1),
      ("Stream.Kernel","Stream","draw_lift","draw_lift",1),
      ("Stream.Kernel","Stream","draw_restore","draw_restore",1),
      ("Stream.Kernel","Stream","draw_unlifted","draw_unlifted",1),
      ("Stream.Kernel","Stream","draw_cells","draw_cells",1),
      ("VirtualFinalClosure.StreamPhasePaths","VirtualFinalClosure.StreamPhasePaths","lift_path","lift_path",1),
      ("VirtualFinalClosure.StreamPhasePaths","VirtualFinalClosure.StreamPhasePaths","advance_path","advance_path",1),
      ("VirtualFinalClosure.StreamPhasePaths","VirtualFinalClosure.StreamPhasePaths","finish_physical","finish_physical",1),
      ("VirtualFinalClosure.StreamPhasePaths","VirtualFinalClosure.StreamPhasePaths","finish_virtual","finish_virtual",1),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","pure_row","pureRow",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong SAME literal paid-orbit interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique SAME literal paid-orbit interface {mod}/{key}"
private theorem put_same (T : Nat → Option Bool) (p : Nat) (b : Option Bool) : put T p b=streamPut T p b:=rfl
private theorem append {M : UniformTM} {P t u : Nat} {c d e}
    (h : GPath (M:=M) P t c d) (g : GPath (M:=M) P u d e) : GPath (M:=M) P (t+u) c e:=joinPath h g
private theorem widen {M : UniformTM} {P Q t : Nat} {c d}
    (h : GPath (M:=M) P t c d) (bound : P ≤ Q) : GPath (M:=M) Q t c d:=by
  induction h with
  | nil c fit=>exact nilPath c (fit.trans bound)
  | cons edge tail ih=>
    obtain ⟨before,after,row,move,tape⟩:=edge
    exact consPath (edgeMk (before.trans bound) (after.trans bound) row move tape) ih
private theorem read_draw (k : Nat) (f : Fin 4) (U : Nat → Option Bool) (S z n p marks : Nat) (bs : List Bool) (hp : p ≤ S) (source : ∀ i, p ≤ i → i < S → ∃ b, U i=some b)
    (eof : U S=none) (reg : ∀ i, S < i → i < S+z+2 → U i=some false) (sep : U (S+z+2)=none) (right : U (S+z+n+3)=none) :
    GPath (S+z+n+3) (n+z+(S-p)+4)
      (node ((q k f) 7) (p) (draw U S z n bs p marks false))
      (node ((unpaid k f) (Stream.Target.mode U p S)) (S+z+n+3) (draw U S z n bs p marks true)) := by
  let T := draw U S z n bs p marks false
  have low (i : Nat) (hi : i ≤ S+z+2) : T i=U i := by
    rw [show T i=draw U S z n bs p marks false i from rfl,draw_low U S z n bs p marks i false hi]
    simp
  obtain ⟨mode,hm,hb,path⟩ := (lift_path k f) T p S z n hp (by intro i hl hu; rw [low i (by omega)]; exact source i hl hu) (by rw [low S (by omega)]; exact eof)
    (by intro i hl hu; rw [low i (by omega)]; exact reg i hl hu) (by rw [low _ le_rfl]; exact sep) (draw_occupied U S z n bs p marks false)
    (by change draw U S z n bs p marks false (S+z+n+3)=none; rw [draw_high,right])
  have same : mode=Stream.Target.mode U p S := by
    by_cases last : p=S
    · apply Fin.ext
      have hv := hm.mpr last
      simpa [Stream.Target.mode,last] using hv
    · obtain ⟨b,hbit⟩ := source p le_rfl (by omega)
      have hread : InputRead.result mode=b := by
        have h := hb (by omega)
        rw [low p (by omega),hbit] at h
        exact (Option.some.inj h).symm
      have nonEOF : mode.val≠2 := by intro he; exact last (hm.mp he)
      rw [mode_correct U p S b (by omega) hbit]
      have unique : ∀ (m : Fin 3) (v : Bool), m.val≠2 → InputRead.result m=v → m=modeOf v := by decide
      exact unique mode b nonEOF hread
  dsimp only [T] at path
  simp only [put_same] at path
  rw [same,draw_lift U S z n bs p marks hp eof] at path
  exact path
private theorem next_draw (k : Nat) (f : Fin 4) (U : Nat → Option Bool) (S z n p marks : Nat) (bs : List Bool) (hp : p  ≤  S) (source : ∀ i, p  ≤  i → i < S → ∃ b, U i=some b)
    (eof : U S=none) (reg : ∀ i, S < i → i < S+z+2 → U i=some false) (sep : U (S+z+2)=none) (right : U (S+z+n+3)=none) :
    ∃ t, t  ≤  2*(S+z+n+3)+8 ∧ GPath (S+z+n+3) t
      (node ((q k f) (13+8*(Stream.Target.mode U p S).val)) (S+z+n+3) (draw U S z n bs p marks true))
      (node ((unpaid k f) (Stream.Target.mode U (min (p+1) S) S)) (S+z+n+3) (draw U S z n bs (min (p+1) S) marks true)) := by
  have cells := draw_cells U S z n p marks bs hp (by intro i hl hu; exact source i (by omega) hu) eof reg sep right
  by_cases last : p=S
  · have one := keep ((q k f) 29) ((unpaid k f) ⟨2,by decide⟩) (S+z+n+3) (S+z+n+3) (draw U S z n bs p marks true) .stay (P := S+z+n+3) le_rfl le_rfl (by rw [cells.2.2.2.2.2.2];apply pureRow <;> decide) rfl
    refine ⟨1,by omega,?_⟩
    simpa [last,Stream.Target.mode,Nat.min_eq_right (by omega : S  ≤  S+1)] using one
  · have hm : (Stream.Target.mode U p S).val < 2 := by
      simp only [Stream.Target.mode,if_neg last]
      split_ifs <;> decide
    obtain ⟨bit,hbit⟩ := source p le_rfl (by omega)
    have bitpin : U p=some (InputRead.result (Stream.Target.mode U p S)) := by
      rw [mode_correct U p S bit (by omega) hbit]
      cases bit <;> simpa [InputRead.result,modeOf] using hbit
    have ad := (advance_path k f) (draw U S z n bs p marks true) p S z n (Stream.Target.mode U p S)
      hm (by omega) cells.1 cells.2.1 cells.2.2.1 cells.2.2.2.1 cells.2.2.2.2.1
      cells.2.2.2.2.2.1 cells.2.2.2.2.2.2
    simp only [put_same] at ad
    rw [draw_restore U S z n bs p marks _ (by omega) bitpin,
      draw_unlifted U S z n bs p (p+1) marks] at ad
    have read := (read_draw k f) U S z n (p+1) marks bs (by omega) (by intro i hl hu; exact source i (by omega) hu) eof reg sep right
    refine ⟨(n+z+(S-p)+4)+(n+z+(S-(p+1))+4),by omega,?_⟩
    rw [Nat.min_eq_left (by omega : p+1  ≤  S)]
    exact ad.append read
private theorem finish_draw (k : Nat) (f : Fin 4) (U : Nat → Option Bool) (S z n p marks : Nat) (bs : List Bool) (hp : p  ≤  S) (source : ∀ i, p  ≤  i → i < S → ∃ b, U i=some b)
    (eof : U S=none) (reg : ∀ i, S < i → i < S+z+2 → U i=some false) (sep : U (S+z+2)=none) (right : U (S+z+n+3)=none) :
    ∃ t, t  ≤  S+z+n+7 ∧ GPath (S+z+n+3) t
      (node ((q k f) (12+8*(Stream.Target.mode U p S).val)) (S+z+2) (draw U S z n bs p marks true))
      (node ((q k f) (if min (p+1) S=S then 57 else 58)) (min (p+1) S) (draw U S z n bs (min (p+1) S) marks false)) := by
  have cells := draw_cells U S z n p marks bs hp (by intro i hl hu; exact source i (by omega) hu) eof reg sep right
  by_cases last : p=S
  · have path := (finish_virtual k f) (draw U S z n bs p marks true) S z n
      cells.2.2.1 cells.2.2.2.1 cells.2.2.2.2.1
    have unlift : draw U S z n bs S marks true=draw U S z n bs S marks false := by
      funext i
      dsimp only [draw]
      split_ifs <;> first | rfl | omega
    refine ⟨z+3,by omega,?_⟩
    simpa [last,Stream.Target.mode,Nat.min_eq_right (by omega : S  ≤  S+1),unlift] using path
  · have hm : (Stream.Target.mode U p S).val < 2 := by
      simp only [Stream.Target.mode,if_neg last]
      split_ifs <;> decide
    obtain ⟨bit,hbit⟩ := source p le_rfl (by omega)
    have bitpin : U p=some (InputRead.result (Stream.Target.mode U p S)) := by
      rw [mode_correct U p S bit (by omega) hbit]
      cases bit <;> simpa [InputRead.result,modeOf] using hbit
    have path := (finish_physical k f) (draw U S z n bs p marks true) p S z n (Stream.Target.mode U p S)
      hm (by omega) cells.1 cells.2.1 cells.2.2.1 cells.2.2.2.1 cells.2.2.2.2.1
    simp only [put_same] at path
    rw [draw_restore U S z n bs p marks _ (by omega) bitpin,
      draw_unlifted U S z n bs p (p+1) marks] at path
    refine ⟨z+(S-p)+4,by omega,?_⟩
    simpa only [Nat.min_eq_left (by omega : p+1  ≤  S)] using path
#print axioms put_same
#print axioms append
#print axioms widen
#print axioms read_draw
#print axioms next_draw
#print axioms finish_draw
end VirtualFinalClosure.StreamDrawPaths
