import VirtualFinalClosure.SourceRound
import VirtualFinalClosure.MarkerImages
import VirtualFinalClosure.MarkerState
import VirtualFinalClosure.PathTrace
namespace VirtualFinalClosure.SourceLoop
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node","GNode",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protectedFrame",1),
      ("VirtualFinalClosure.SourceRound","VirtualFinalClosure.SourceRound","positive_round","round",1),
      ("VirtualFinalClosure.SourceRound","VirtualFinalClosure.SourceRound","nextTape","nextTape",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","image",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","unary","unary",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","lifted","lifted",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image_zero","zeroImage",1),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","marked_step","imageStep",1),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","round_price","roundPrice",1),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_bound","modeBound",1),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_mode","modeValue",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong physical marker loop interface {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique marker loop declaration {mod}/{key}"
private theorem lower (T : Nat → Option Bool) (F r S j i : Nat)
    (room : S ≤ F+1) (position : i ≤ S) :
    image T F r S j i=(if 0 < j ∧ i=S-j then none else T i) := by
  dsimp only [image,unary,lifted]
  rw [if_neg (by omega)]
private theorem protected_image (T : Nat → Option Bool) (F r S j i : Nat)
    (stage : j < S) (low : S ≤ i) (high : i ≤ F+1) : image T F r S j i=T i := by
  dsimp only [image,unary,lifted]
  rw [if_neg (by omega),if_neg (by omega)]
private theorem delimiter (T : Nat → Option Bool) (F r S j : Nat) (room : S ≤ F+1) :
    image T F r S j (F+r+2)=T (F+r+2) := by
  dsimp only [image,unary,lifted]
  rw [if_neg (by omega),if_neg (by omega)]
private theorem digit (T : Nat → Option Bool) (F r S j i : Nat)
    (lo : F+1 < i) (hi : i < F+r+2) :
    image T F r S j i=some (decide (i ≤ F+1+(r-j))) := by
  dsimp only [image,unary]
  rw [if_pos (by omega)]
private theorem old_source (T : Nat → Option Bool) (S r j : Nat) (bits : Nat → Bool)
    (inside : j < r) (cells : ∀ i,i < r → T (S-1-i)=some (bits i)) :
    0 < j → T (S-j)=some (bits (j-1)) := by
  intro positive
  have actual:=cells (j-1) (by omega)
  simpa only [show S-1-(j-1)=S-j by omega] using actual
private theorem selected (T : Nat → Option Bool) (F r S j : Nat) (bits : Nat → Bool)
    (room : S ≤ F+1) (source : r < S) (inside : j < r)
    (cells : ∀ i,i < r → T (S-1-i)=some (bits i)) :
    image T F r S j (S-j-1)=some (bits j) := by
  rw [lower T F r S j _ room (by omega),if_neg (by omega)]
  simpa only [show S-j-1=S-1-j by omega] using cells j inside
private theorem suffix (T : Nat → Option Bool) (F r S j : Nat) (bits : Nat → Bool)
    (room : S ≤ F+1) (source : r < S) (inside : j < r)
    (cells : ∀ i,i < r → T (S-1-i)=some (bits i)) :
    ∀ i,S-j < i → i < S → ∃ b,image T F r S j i=some b := by
  intro i lo hi
  have index : S-1-i < r := by omega
  have actual:=cells (S-1-i) index
  have eq : S-1-(S-1-i)=i := by omega
  refine ⟨bits (S-1-i),?_⟩
  rw [lower T F r S j i room hi.le,if_neg (by omega)]
  exact (congrArg T eq.symm).trans actual
/-- The ENTIRE real source-marking loop, not a fixed number of sampled rounds.
Each bit is obtained from the physical source. Full images and finite modes are
proof indices only; the frozen runtime never receives them as operands. -/
private theorem mark_loop (k P m S L H Q F r : Nat) (T : Nat → Option Bool) (bits : Nat → Bool)
    (hm : m < 144) (eof : sourceMode m=2) (fr : Frame T S L H Q F)
    (gap : H+Q+1 < F) (source : r < S) (fit : F+r+2 ≤ P)
    (bank : ∀ i,F+1 < i → i < F+r+2 → T i=some true) (last : T (F+r+2)=none)
    (cells : ∀ i,i < r → T (S-1-i)=some (bits i)) :
    ∀ j,j ≤ r → ∃ d,d ≤ j*(2*r+2*(F-S)+14) ∧
      GPath (M:=machine k) P d (C k 6 m (F+1) T)
        (C k 6 (modes m bits j) (F+1) (image T F r S j)) := by
  have copyFrame:=fr
  obtain ⟨sl,lh,_q,arena,_s,_l,_h,_d0,_f,_reg,_assign,_tally,_gap⟩:=copyFrame
  have room : S ≤ F+1 := by omega
  intro j limit
  induction j with
  | zero=>
    refine ⟨0,by omega,?_⟩
    rw [zeroImage T F r S bank]
    exact nilPath (C k 6 m (F+1) T) (by change F+1 ≤ P;omega)
  | succ j ih=>
    have inside : j < r := by omega
    obtain ⟨d,price,history⟩:=ih (by omega)
    have frame : Frame (image T F r S j) S L H Q F := protectedFrame fr (by
      intro i lo hi
      exact protected_image T F r S j i (by omega) lo hi)
    have one:=round k P (modes m bits j) S L H Q F r (r-j) (S-j)
      (image T F r S j) (bits (j-1)) (bits j) (modeBound m bits j hm) frame gap
      (by omega) (by omega) fit (by rw [delimiter T F r S j room];exact last)
      (fun i lo hi=>digit T F r S j i lo hi) (by omega) (by omega)
      (by
        intro eq
        have zero : j=0 := by omega
        subst j
        exact eof)
      (by intro lt;exact modeValue m bits j (by omega))
      (by
        intro lt
        rw [lower T F r S j (S-j) room (by omega),if_pos ⟨by omega,rfl⟩])
      (selected T F r S j bits room source inside cells)
      (suffix T F r S j bits room source inside cells)
    have tapeStep : nextTape (image T F r S j) F (r-j) (S-j) S (bits (j-1))=image T F r S (j+1) :=
      imageStep T F r S j (bits (j-1)) room inside source (old_source T S r j bits inside cells)
    rw [tapeStep] at one
    have stepPrice:=roundPrice F S r j inside source
    let delta:=2*(r-j)+3+(F-S+3)+(if S-j=S then 4 else 2*(S-(S-j))+5)+(F-S+3)
    refine ⟨d+delta,?_,?_⟩
    · change d+delta ≤ (j+1)*(2*r+2*(F-S)+14)
      calc
        d+delta ≤ j*(2*r+2*(F-S)+14)+(2*r+2*(F-S)+14) := Nat.add_le_add price stepPrice
        _ = (j+1)*(2*r+2*(F-S)+14) := by ring
    · exact joinPath history one
#print axioms mark_loop
end VirtualFinalClosure.SourceLoop
