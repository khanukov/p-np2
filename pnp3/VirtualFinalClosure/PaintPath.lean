import VirtualFinalClosure.Paths
namespace VirtualFinalClosure.PaintPath
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (key,aliasName,kind) in [("Node.mk","node",(3:Nat)),("Path","GPath",2),
      ("Path.nil","nilPath",3),("Path.append","joinPath",1),("put","put",0),("hop","hop",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.SmallIngress.Runtime." &&
      name.toString.endsWith (".SmallIngress."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong existing painting path term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique existing painting path term {key}"
private def block (T : Nat  →  Option Bool) (h width : Nat) (b : Option Bool) : Nat  →  Option Bool :=
  fun i=>if h ≤ i  ∧  i < h+width then b else T i
private def block_type : (Nat  →  Option Bool)  →  Nat  →  Nat  →  Option Bool  →  Nat  →  Option Bool := block
private theorem outside (T : Nat  →  Option Bool) (h width i : Nat) (b : Option Bool)
    (hi : i < h  ∨  h+width ≤ i) : block T h width b i=T i := by
  dsimp only [block]
  rw [if_neg (by omega)]
private theorem add_front (T : Nat  →  Option Bool) (h width : Nat) (b : Option Bool) :
    block (put T h b) (h+1) width b=block T h (width+1) b := by
  funext i
  dsimp only [block,put]
  by_cases first : i=h
  · subst i
    rw [if_neg (by omega),if_pos rfl,if_pos (by omega)]
  · rw [if_neg first]
    by_cases inside : h+1 ≤ i  ∧  i < h+1+width
    · rw [if_pos inside,if_pos (by omega)]
    · rw [if_neg inside,if_neg (by omega)]
/-- A write-qualified scan on an opaque concrete table, using only the EXISTING
hop/path engine. The caller supplies actual literal SomeBool rows. Width is an
execution/specification index, never a transition argument. -/
private theorem paint_right {M : UniformTM} (q : Fin M.stateCount) (P h width : Nat)
    (T : Nat  →  Option Bool) (b : Option Bool) (fit : h+width ≤ P)
    (occupied : ∀ i,h ≤ i  →  i < h+width  →  ∃ v,T i=some v)
    (row : ∀ v : Bool,M.step q (some v)=(q,b,.right)) :
    GPath (M:=M) P width (node q h T) (node q (h+width) (block T h width b)) := by
  induction width generalizing h T with
  | zero=>
    have image : block T h 0 b=T := by
      funext i
      dsimp only [block]
      rw [if_neg (by omega)]
    rw [image]
    exact nilPath _ (by change h≤P;omega)
  | succ width ih=>
    obtain ⟨v,cell⟩:=occupied h le_rfl (by omega)
    have entry:=hop (M:=M) (P:=P) q q h (h+1) T b .right
      (by omega) (by omega) (by rw [cell];exact row v) rfl
    have tail:=ih (h+1) (put T h b) (by omega) (by
      intro i lo hi
      change ∃ v,(if i=h then b else T i)=some v
      rw [if_neg (by omega)]
      exact occupied i (by omega) (by omega))
    have path:=joinPath entry tail
    rw [add_front,show h+1+width=h+(width+1) by omega] at path
    simpa only [Nat.add_comm 1 width] using path
#print axioms block_type
#print axioms outside
#print axioms add_front
#print axioms paint_right
end VirtualFinalClosure.PaintPath
