import VirtualFinalClosure.StreamDrawPaths
namespace VirtualFinalClosure.StreamActiveRound
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
      ("Stream.Kernel","Stream","Arena","Arena",2),
      ("Stream.Kernel","Stream","Arena.room","arenaRoom",1),
      ("Stream.Kernel","Stream","Arena.eof","arenaEOF",1),
      ("Stream.Kernel","Stream","Arena.reg","arenaReg",1),
      ("Stream.Kernel","Stream","Arena.sep","arenaSep",1),
      ("Stream.Kernel","Stream","Arena.right","arenaRight",1),
      ("Stream.Kernel","Stream","Arena.source","arenaSource",1),
      ("Stream.Kernel","Stream","Arena.scratch","arenaScratch",1),
      ("Stream.Kernel","Stream","Arena.start_le","arenaStart",1),
      ("Stream.Kernel","Stream","carryCost","carryCost",0),
      ("Stream.Kernel","Stream","draw_cells","draw_cells",1),
      ("Stream.Kernel","Stream","draw_pay","draw_pay",1),
      ("VirtualFinalClosure.StreamDrawPaths","VirtualFinalClosure.StreamDrawPaths","put_same","putSame",1),
      ("Stream.Kernel","Stream","draw_reads","draw_reads",1),
      ("Stream.Kernel","Stream","draw_high","draw_high",1),
      ("Stream.Kernel","Stream","draw_carry","draw_carry",1),
      ("Stream.Kernel","Stream","carry_cost_le","carry_cost_le",1),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","pay_path","payPath",1),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","paid_row","paidRow",1),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","next","nextFlag",0),
      ("VirtualFinalClosure.StreamPhasePaths","VirtualFinalClosure.StreamPhasePaths","carry_path","carryPath",1),
      ("VirtualFinalClosure.StreamDrawPaths","VirtualFinalClosure.StreamDrawPaths","append","append",1),
      ("VirtualFinalClosure.StreamDrawPaths","VirtualFinalClosure.StreamDrawPaths","widen","widen",1),
      ("VirtualFinalClosure.StreamDrawPaths","VirtualFinalClosure.StreamDrawPaths","next_draw","next_draw",1),
      ("VirtualFinalClosure.StreamDrawPaths","VirtualFinalClosure.StreamDrawPaths","finish_draw","finish_draw",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong SAME literal paid-orbit interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique SAME literal paid-orbit interface {mod}/{key}"
private theorem row_draw (k : Nat) (f : Fin 4) (U : Nat → Option Bool) (S z n A F p r : Nat) (bs : List Bool) (arena : Arena U S z n A F) (hp : A  ≤  p ∧ p  ≤  S) (len : bs.length=n)
    (hr : r < F-(S+z+n+3)-1) :
    ∃ t, t  ≤  8*F+16 ∧ GPath F t
      (node (unpaid k f (Stream.Target.mode U p S)) (S+z+n+3) (draw U S z n bs p r true))
      (if (Body.inc bs).2 then
        (node (q k (nextFlag f (decide ((Stream.Target.mode U p S).val=1))) (if min (p+1) S=S then 57 else 58)) (min (p+1) S) (draw U S z n (Body.inc bs).1 (min (p+1) S) (r+1) false))
       else (node (unpaid k (nextFlag f (decide ((Stream.Target.mode U p S).val=1))) (Stream.Target.mode U (min (p+1) S) S)) (S+z+n+3) (draw U S z n (Body.inc bs).1 (min (p+1) S) (r+1) true))) := by
  let H := S+z+n+3
  let cap := F-H-1
  have geo : H+cap+1=F := by dsimp [cap]; have h := (arenaRoom arena); dsimp [H] at *; omega
  have cells := draw_cells U S z n p r bs hp.2 (by intro i hl hu; exact (arenaSource arena) i (by omega) hu) (arenaEOF arena) (arenaReg arena) (arenaSep arena) (arenaRight arena)
  have pay := payPath k f (draw U S z n bs p r true) H r cap (Stream.Target.mode U p S)
    cells.2.2.2.2.2.2 (by intro i hl hu; dsimp only [draw]; rw [if_neg (by dsimp [H] at *; omega),if_pos (by dsimp [H] at *; omega)])
    (by dsimp only [draw]; rw [if_neg (by dsimp [H] at *; omega),if_neg (by dsimp [H] at *; omega),if_neg (by dsimp [H] at *; omega)]
        exact (arenaScratch arena) _ (by dsimp [H]; omega) (by omega)) hr
  rw [geo] at pay
  simp only [putSame] at pay
  dsimp only [H] at pay
  rw [draw_pay] at pay
  let T := draw U S z n bs p (r+1) true
  have blank : T H=none := (draw_high U S z n bs p (r+1) true).trans (arenaRight arena)
  let f1:=nextFlag f (decide ((Stream.Target.mode U p S).val=1))
  have one:=keep (q k f (43+4*(Stream.Target.mode U p S).val)) (q k f1 (12+8*(Stream.Target.mode U p S).val))
    H (H-1) T .left (P:=F) (by omega) (by omega)
    (by rw [blank];exact paidRow k f (Stream.Target.mode U p S)) rfl
  have carry := carryPath k f1 T (S+z+2) 0 bs (Stream.Target.mode U p S) (draw_reads U S z n bs p (r+1) true len) (by intro i hl hu; omega)
  have bound : S+z+2+bs.length+0+1=H := by dsimp [H]; omega
  rw [bound,draw_carry U S z n bs p (r+1) true len] at carry
  have head : S+z+2+bs.length=H-1 := by dsimp [H]; omega
  rw [head] at carry
  have price := carry_cost_le bs 0
  rw [len] at price
  have source : ∀ i, p  ≤  i → i < S → ∃ b, U i=some b := by
    intro i hl hu; exact (arenaSource arena) i (hp.1.trans hl) hu
  cases over : (Body.inc bs).2 with
  | false =>
    simp only [over,Bool.false_eq_true,↓reduceIte] at carry ⊢
    obtain ⟨t,priceNext,next⟩ := next_draw k f1 U S z n p (r+1) (Body.inc bs).1 hp.2 source
      (arenaEOF arena) (arenaReg arena) (arenaSep arena) (arenaRight arena)
    refine ⟨(2*r+3)+1+carryCost bs 0+t,by have h := (arenaRoom arena); dsimp [H] at *; omega,?_⟩
    exact ((pay.append one).append (widen carry (by omega))).append (widen next (by have h := (arenaRoom arena); omega))
  | true =>
    simp only [over,↓reduceIte] at carry ⊢
    obtain ⟨t,priceNext,next⟩ := finish_draw k f1 U S z n p (r+1) (Body.inc bs).1 hp.2 source
      (arenaEOF arena) (arenaReg arena) (arenaSep arena) (arenaRight arena)
    refine ⟨(2*r+3)+1+carryCost bs 0+t,by have h := (arenaRoom arena); dsimp [H] at *; omega,?_⟩
    exact ((pay.append one).append (widen carry (by omega))).append (widen next (by have h := (arenaRoom arena); omega))
#print axioms row_draw
end VirtualFinalClosure.StreamActiveRound
