import VirtualFinalClosure.StreamActiveRound
namespace VirtualFinalClosure.StreamActiveOrbit
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("Stream.Kernel","Stream","Arena","Arena",(2:Nat)),
      ("Stream.Kernel","Stream","Arena.room","arenaRoom",1),
      ("Stream.Kernel","Stream","Arena.eof","arenaEOF",1),
      ("Stream.Kernel","Stream","Arena.reg","arenaReg",1),
      ("Stream.Kernel","Stream","Arena.sep","arenaSep",1),
      ("Stream.Kernel","Stream","Arena.right","arenaRight",1),
      ("Stream.Kernel","Stream","Arena.source","arenaSource",1),
      ("Stream.Kernel","Stream","Arena.scratch","arenaScratch",1),
      ("Stream.Kernel","Stream","Arena.start_le","arenaStart",1),
      ("Stream.Kernel","Stream","image_draw","imageDraw",1),
      ("Stream.Kernel","Stream","iter_succ","iterSucc",1),
      ("Stream.Kernel","Stream","cursor_succ","cursorSucc",1),
      ("Stream.Kernel","Stream","before_overflow","beforeOverflow",1),
      ("Stream.Kernel","Stream","last_overflow","lastOverflow",1),
      ("VirtualFinalClosure.StreamActiveRound","VirtualFinalClosure.StreamActiveRound","row_draw","round",1),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","q","q",0),
      ("VirtualFinalClosure.StreamPhasePaths","VirtualFinalClosure.StreamPhasePaths","unpaid","unpaid",0),
      ("VirtualFinalClosure.StreamDrawPaths","VirtualFinalClosure.StreamDrawPaths","append","append",1),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","next","nextFlag",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","folded","folded",0),
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",2),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("SmallIngress.Runtime","SmallIngress","embed","embed",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual all-row active flag interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual all-row active flag interface {mod}/{key}"
private def bits (U : Nat → Option Bool) (A S r : Nat) : Bool:=
  decide ((Stream.Target.mode U (Stream.Target.cursor A S r) S).val=1)
private def entry (k : Nat) (U : Nat → Option Bool) (S z n A r : Nat) : GNode (machine k):=
  node (unpaid k (folded (bits U A S) r) (Stream.Target.mode U (Stream.Target.cursor A S r) S))
    (S+z+n+3) (Stream.Target.image U S z n A r r true)
private def ended (k : Nat) (U : Nat → Option Bool) (S z n A r : Nat) : GNode (machine k):=
  node (q k (folded (bits U A S) r) (if Stream.Target.cursor A S r=S then 57 else 58))
    (Stream.Target.cursor A S r) (Stream.Target.image U S z n A r r false)
private def bits_type : (Nat → Option Bool) → Nat → Nat → Nat → Bool:=bits
private def entry_type : ∀ k,(Nat → Option Bool) → Nat → Nat → Nat → Nat → Nat → GNode (machine k):=entry
private def ended_type : ∀ k,(Nat → Option Bool) → Nat → Nat → Nat → Nat → Nat → GNode (machine k):=ended
private theorem step_row (k : Nat) (U : Nat → Option Bool) (S z n A F r : Nat)
    (arena : Arena U S z n A F) (room : r < F-(S+z+n+3)-1) :
    ∃ t,t ≤ 8*F+16 ∧ GPath F t (entry k U S z n A r)
      (if (Body.inc (Body.iterBits (List.replicate n false) r)).2 then ended k U S z n A (r+1)
       else entry k U S z n A (r+1)):=by
  obtain ⟨t,price,path⟩:=round k (folded (bits U A S) r) U S z n A F (Stream.Target.cursor A S r) r
    (Body.iterBits (List.replicate n false) r) arena
    (by have h:=(arenaStart arena);unfold Stream.Target.cursor;omega)
    (by rw [Body.iter_length,List.length_replicate]) room
  refine ⟨t,price,?_⟩
  have next : folded (bits U A S) (r+1)=nextFlag (folded (bits U A S) r) (bits U A S r):=rfl
  simpa only [entry,ended,imageDraw,iterSucc,cursorSucc,next,bits] using path
private theorem unpaid_orbit (k : Nat) (U : Nat → Option Bool) (S z n A F r : Nat)
    (arena : Arena U S z n A F) (hr : r < 2^n) (cap : r ≤ F-(S+z+n+3)-1) :
    ∃ t,t ≤ r*(8*F+16) ∧ GPath F t (entry k U S z n A 0) (entry k U S z n A r):=by
  induction r with
  | zero=>exact ⟨0,by omega,nilPath _ (Nat.le_of_lt (arenaRoom arena))⟩
  | succ r ih=>
    obtain ⟨t,tp,path⟩:=ih (by omega) (by omega)
    obtain ⟨u,up,next⟩:=step_row k U S z n A F r arena (by omega)
    rw [beforeOverflow n r hr] at next
    simp only [Bool.false_eq_true,ite_false] at next
    refine ⟨t+u,?_,append path next⟩
    calc
      t+u ≤ r*(8*F+16)+(8*F+16):=Nat.add_le_add tp up
      _=(r+1)*(8*F+16):=by ring
/-- ALL assignments come from the SAME native Stream carry orbit. Each
completed row passes the actual active paid edge and the next round receives
its finite updated flag; source/tally/canonical counter are the original images.
This prepared orbit is a component, not the unconditional raw FINAL theorem. -/
private theorem complete_orbit (k : Nat) (U : Nat → Option Bool) (S z n A F : Nat)
    (arena : Arena U S z n A F) (cap : 2^n ≤ F-(S+z+n+3)-1) :
    ∃ t,t ≤ (2^n)*(8*F+16) ∧ GPath F t (entry k U S z n A 0) (ended k U S z n A (2^n)):=by
  have positive:=Nat.two_pow_pos n
  obtain ⟨t,tp,orbitPrefix⟩:=unpaid_orbit k U S z n A F (2^n-1) arena (by omega) (by omega)
  obtain ⟨u,up,last⟩:=step_row k U S z n A F (2^n-1) arena (by omega)
  have lastIndex : 2^n-1+1=2^n:=by omega
  rw [lastOverflow n (2^n-1) (by omega) lastIndex] at last
  simp only [ite_true,lastIndex] at last
  refine ⟨t+u,?_,append orbitPrefix last⟩
  calc
    t+u ≤ (2^n-1)*(8*F+16)+(8*F+16):=Nat.add_le_add tp up
    _=(2^n)*(8*F+16):=by rw [←Nat.add_one_mul,lastIndex]
#print axioms bits_type
#print axioms entry_type
#print axioms ended_type
#print axioms step_row
#print axioms unpaid_orbit
#print axioms complete_orbit
end VirtualFinalClosure.StreamActiveOrbit
