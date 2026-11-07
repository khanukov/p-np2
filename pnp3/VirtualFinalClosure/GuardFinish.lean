import VirtualFinalClosure.GuardRestore
import VirtualFinalClosure.GuardFinishRoutes
import VirtualFinalClosure.GuardLayout
namespace VirtualFinalClosure.GuardFinish
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
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
      ("VirtualFinalClosure.GuardImage","VirtualFinalClosure.GuardImage","source_write","sourceWrite",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole","hole",0),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","image_low","low",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","image_frame","imageFrame",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_frame","holeFrame",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_banks","holeBanks",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_bank0","holeBank0",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","hole_bank1","holeBank1",1),
      ("VirtualFinalClosure.GuardLayout","VirtualFinalClosure.GuardLayout","restore_hole","restoreHole",1),
      ("VirtualFinalClosure.GuardRestore","VirtualFinalClosure.GuardRestore","live","live",1),
      ("VirtualFinalClosure.GuardRestore","VirtualFinalClosure.GuardRestore","eof","eof",1),
      ("VirtualFinalClosure.GuardFinishRoutes","VirtualFinalClosure.GuardFinishRoutes","back","back",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","flag","flag",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","bad","bad",0) ] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong moving-source term {n}"
      logInfo m!"private-term|{n}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique moving-source term {mod}/{key}"
/-- Entire restored-source/padding scan and real return to the observed D0.
The original pre-run U is restored pointwise; no source hole remains.
The bad bit is exactly the prior bad bit OR an actual remaining TRUE source cell. -/
private theorem prepared (k P m S L n Q F width a b c d h : Nat)
    (U : Nat → Option Bool) (bits : Nat → Bool)
    (hm : m < 144) (fr : Frame U S L (L+n+1) Q F) (banks : Banks U L n F width)
    (gap : L+n+1+Q+1 < F) (fit : F+5*width+n+7 ≤ P) (range : h ≤ S)
    (source : ∀ j,h ≤ j → j < S → U j=some (bits j))
    (carried : sourceMode m=(if h < S then if bits h then 1 else 0 else 2))
    (_b0 : ∀ j,F+1 < j → j < F+width+2 → ∃ b,U j=some b)
    (_b1 : ∀ j,F+width+2 < j → j < F+width+n+3 → ∃ b,U j=some b) :
    ∃ t m',t ≤ 2*(S-h)+(F-S)+6 ∧ m' < 144 ∧ flag m'=flag m ∧
      (bad m'=0 ↔ bad m=0 ∧ ∀ j,h ≤ j → j < S → bits j=false) ∧
      GPath (M:=machine k) P t
        (C k 194 m S (image (hole U h S) L n F width a b c d))
        (C k 238 m' (F+1) (image U L n F width a b c d)) := by
  have rm:=room banks
  have sl:=sourceLow fr
  let A:=image (hole U h S) L n F width a b c d
  have atLow (j : Nat) (lo : j ≤ L) : A j=hole U h S j:=low (hole U h S) L n F width a b c d j rm lo
  let B:=image U L n F width a b c d
  have framed:=imageFrame (width:=width) (holeFrame fr h) a b c d
  have imageFr:=imageFrame (width:=width) fr a b c d
  by_cases atEOF : h=S
  · have noHole : hole U h S=U:=by dsimp only [hole];rw [if_neg (by omega)]
    have mid:=eof k P m S A hm (by simpa only [atEOF,lt_self_iff_false,if_false] using carried)
      (by omega) (sourceEnd framed)
    have tail:=back k P m S L (L+n+1) Q F B hm imageFr gap (by omega)
    dsimp only [A] at mid
    rw [noHole] at mid
    refine ⟨1+(F-S+3),m,by omega,hm,rfl,?_,?_⟩
    · constructor
      · intro hbad
        exact ⟨hbad,by intro j lo hi;omega⟩
      · exact fun hbad=>hbad.1
    · simpa only [noHole] using joinPath mid tail
  · have inside : h < S:=by omega
    have blank : A h=none:=by
      rw [atLow h (by omega)]
      dsimp only [hole]
      rw [if_pos inside]
      change (if h=h then none else U h)=none
      rw [if_pos rfl]
    obtain ⟨m',mb,mf,clean,mid⟩:=live k P m S h A bits hm
      (by simpa only [if_pos inside] using carried) inside (by omega) (sourceEnd framed) blank (by
        intro j lo hi
        rw [atLow j (by omega)]
        dsimp only [hole]
        rw [if_pos inside]
        change (if j=h then none else U j)=some (bits j)
        rw [if_neg (by omega),source j (by omega) hi])
    have restored : put A h (some (bits h))=B:=by
      rw [sourceWrite (hole U h S) L n F width a b c d h (some (bits h)) rm (by omega),
        restoreHole U S h (bits h) inside (source h le_rfl inside)]
    rw [restored] at mid
    have tail:=back k P m' S L (L+n+1) Q F B mb imageFr gap (by omega)
    exact ⟨(2*(S-h)+3)+(F-S+3),m',by omega,mb,mf,clean,joinPath mid tail⟩
#print axioms prepared
end VirtualFinalClosure.GuardFinish
