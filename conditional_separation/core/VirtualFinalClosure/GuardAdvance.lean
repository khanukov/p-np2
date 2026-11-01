import VirtualFinalClosure.GuardRoutes
import VirtualFinalClosure.GuardLayout
import VirtualFinalClosure.GuardForward
namespace VirtualFinalClosure.GuardAdvance
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("PostWeight.Kernel","PostWeight","Banks","Banks",2),
      ("PostWeight.Kernel","PostWeight","Banks.room","room",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.SL","sourceLow",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.sourceEnd","sourceEnd",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","image","image",0),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","delimiters","delimiters",1),
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","occupied","occupied",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole","hole",0),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","image_low","low",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","image_frame","imageFrame",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_frame","holeFrame",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_banks","holeBanks",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_bank0","holeBank0",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_bank1","holeBank1",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","next_image","nextImage",1),
      ("VirtualFinalClosure.GuardRoutes","VirtualFinalClosure.GuardRoutes","to_source","toSource",1),
      ("VirtualFinalClosure.GuardRoutes","VirtualFinalClosure.GuardRoutes","to_banks","toBanks",1),
      ("VirtualFinalClosure.GuardForward","VirtualFinalClosure.GuardForward","next","nextCell",1),
      ("VirtualFinalClosure.GuardForward","VirtualFinalClosure.GuardForward","eof","eof",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0) ] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong moving-source term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique moving-source term {mod}/{key}"
/-- Entire physically executed forward source shuttle. The base T and source
bits are specified BEFORE execution; all restored source cells and the new hole
are related pointwise. This consumes the actual arithmetic-round endpoint. -/
private theorem prepared (k P m S L n Q F width ell v out quota h : Nat)
    (T : Nat → Option Bool) (bits : Nat → Bool)
    (hm : m < 144) (fr : Frame T S L (L+n+1) Q F) (banks : Banks T L n F width)
    (gap : L+n+1+Q+1 < F) (fit : F+5*width+n+7 ≤ P) (range : h ≤ S)
    (source : ∀ j,h ≤ j → j < S → T j=some (bits j))
    (carried : sourceMode m=(if h < S then if bits h then 1 else 0 else 2))
    (b0 : ∀ j,F+1 < j → j < F+width+2 → ∃ b,T j=some b)
    (b1 : ∀ j,F+width+2 < j → j < F+width+n+3 → ∃ b,T j=some b) :
    ∃ t m',t ≤ 8*(F+width+n+8) ∧ m' < 144 ∧
      sourceMode m'=(if min (h+1) S < S then if bits (min (h+1) S) then 1 else 0 else 2) ∧
      flag m'=flag m ∧ bad m'=bad m ∧ GPath (M:=machine k) P t
        (C k 152 m (F+2*width+n+4) (image (hole T h S) L n F width ell v out quota))
        (C k 93 m' (F+width+n+3) (image (hole T (min (h+1) S) S) L n F width ell v out quota)) := by
  have rm:=room banks
  have sl:=sourceLow fr
  let A:=image (hole T h S) L n F width ell v out quota
  have atLow (j : Nat) (lo : j ≤ L) : A j=hole T h S j:=low (hole T h S) L n F width ell v out quota j rm lo
  have hb:=holeBanks banks sl h
  have imageFr:=imageFrame (width:=width) (holeFrame fr h) ell v out quota
  have imageBlank:=delimiters hb ell v out quota
  have imageOccupied:=occupied hb (holeBank0 T S L n F width h rm sl b0)
    (holeBank1 T S L n F width h rm sl b1) ell v out quota
  have front:=toSource k P m S L (L+n+1) Q F width n A hm imageFr fit imageBlank imageOccupied
  by_cases atEOF : h=S
  · have same : min (h+1) S=h:=by omega
    have mode : sourceMode m=2:=by simpa only [atEOF,lt_self_iff_false,if_false] using carried
    have middle:=eof k P m S A hm mode (by omega) (sourceEnd imageFr)
    have back:=toBanks k P m S L (L+n+1) Q F width n A hm imageFr gap fit imageBlank imageOccupied
    refine ⟨(((width+2)+(n+2)+(width+2))+(F-S+3))+2+((F-S+3)+((width+2)+(n+2))),m,by omega,hm,?_,rfl,rfl,?_⟩
    · rw [same,atEOF,if_neg (Nat.lt_irrefl S)]
      exact mode
    · simpa only [same,A] using joinPath (joinPath front middle) back
  · have inside : h < S:=by omega
    have oldCell:=source h le_rfl inside
    have selectCell (nextInside : h+1 < S) : A (h+1)=some (bits (h+1)):=by
      rw [atLow (h+1) (by omega)]
      dsimp only [hole]
      rw [if_pos inside]
      change (if h+1=h then none else T (h+1))=some (bits (h+1))
      rw [if_neg (by omega),source (h+1) (by omega) nextInside]
    obtain ⟨m',mb,mc,mflag,mbad,middle⟩:=nextCell k P m S h A (bits h) (bits (h+1)) hm
      (by simpa only [if_pos inside] using carried) inside (by omega) (sourceEnd imageFr)
      (by
        rw [atLow h (by omega)]
        dsimp only [hole]
        rw [if_pos inside]
        change (if h=h then none else T h)=none
        rw [if_pos rfl]) selectCell (by
        intro j lo hi
        refine ⟨bits j,?_⟩
        rw [atLow j (by omega)]
        dsimp only [hole]
        rw [if_pos inside]
        change (if j=h then none else T j)=some (bits j)
        rw [if_neg (by omega),source j (by omega) hi])
    rw [nextImage T S L n F width ell v out quota h (bits h) sl rm inside oldCell] at middle
    have nextH : min (h+1) S=h+1:=Nat.min_eq_left (by omega)
    let B:=image (hole T (h+1) S) L n F width ell v out quota
    have hb':=holeBanks banks sl (h+1)
    have back:=toBanks k P m' S L (L+n+1) Q F width n B mb
      (imageFrame (width:=width) (holeFrame fr (h+1)) ell v out quota) gap fit
      (delimiters hb' ell v out quota)
      (occupied hb' (holeBank0 T S L n F width (h+1) rm sl b0)
        (holeBank1 T S L n F width (h+1) rm sl b1) ell v out quota)
    refine ⟨(((width+2)+(n+2)+(width+2))+(F-S+3))+(2*(S-h)+3)+((F-S+3)+((width+2)+(n+2))),m',by omega,mb,?_,mflag,mbad,?_⟩
    · rw [nextH]
      by_cases last : h+1=S
      · simpa only [if_pos last,last,lt_self_iff_false,if_false] using mc
      · simpa only [if_neg last,if_pos (show h+1 < S by omega)] using mc
    · simpa only [nextH,A,B] using joinPath (joinPath front middle) back
#print axioms prepared
end VirtualFinalClosure.GuardAdvance
