import FullWeight.Kernel
import FullWeight.Checks
namespace FullWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Tactic
set_option maxRecDepth 10000
run_cmd do
  for s in ["Node","put","Path.nil","Path.cons","Path.bounds","Path","Path.append","Path.execute","Path.first","K","crossL","crossR","inc","dec","D","Frame","I","atD","unary","occupied","write"] do
    let ns:=(← getEnv).constants.toList.map Prod.fst |>.filter fun n => n.toString.startsWith "_private.FullWeight.Kernel." && n.toString.endsWith (".FullWeight."++s)
    unless ns.length=1 do throwError "Ambiguous literal path interface {s}: {ns}"
    logInfo m!"private-term|{ns.head!}"
    Lean.Elab.Command.modifyScope fun st => {st with openDecls := .explicit ((s.splitOn ".").foldl Name.str Name.anonymous) ns.head! :: st.openDecls}
private def N {k : Nat} (s : Fin (Cursor.stateCount k)) (h : Nat) (T : Nat → Option Bool) : Node k := by
  fromDonor "FullWeight.Kernel" "FullWeight" "Node.mk" => exact OLD s h T
private def rowTac : TacticM Unit := by
  run_tac do
    let ns:=(← getEnv).constants.toList.map Prod.fst |>.filter fun n => n.toString.startsWith "_private.FullWeight.Checks." && n.toString.endsWith ".FullWeight.rowTac"
    unless ns.length=1 do throwError "Ambiguous row checker {ns}"
    logInfo m!"private-term|{ns.head!}"
    evalTactic (← `(tactic| exact $(mkIdent ns.head!)))
private def V (a b c d : Nat) : Nat → Nat := fun j => if j=2 then a else if j=3 then b else if j=4 then c else if j=5 then d else 0
private abbrev J (T : Nat → Option Bool) (L n F r a b c d : Nat) : Nat → Option Bool := I T L n F r (V a b c d)
private theorem patch {T : Nat → Option Bool} (L n F r a b c d j e : Nat) (lo : 2 ≤ j) (hi : j < 6) :
    I T L n F r (Function.update (V a b c d) j e)=
      J T L n F r (if j=2 then e else a) (if j=3 then e else b) (if j=4 then e else c) (if j=5 then e else d) := by
  interval_cases j <;> dsimp only [I,J,V,Function.update] <;> rfl
private theorem put2true {T L n Q F r} (fr : Frame T L n Q F r) (a b c d : Nat) (h : a < r) :
    put (J T L n F r a b c d) (D F r n 2+a+1) (some true)=J T L n F r (a+1) b c d := by
  exact (write fr (V a b c d) 2 a (by omega) (by omega) h true rfl).trans (patch L n F r a b c d 2 (a+1) (by omega) (by omega))
private theorem put2false {T L n Q F r} (fr : Frame T L n Q F r) (a b c d : Nat) (h : a < r) :
    put (J T L n F r (a+1) b c d) (D F r n 2+a+1) (some false)=J T L n F r a b c d := by
  exact (write fr (V (a+1) b c d) 2 a (by omega) (by omega) h false rfl).trans (patch L n F r (a+1) b c d 2 a (by omega) (by omega))
private theorem put3true {T L n Q F r} (fr : Frame T L n Q F r) (a b c d : Nat) (h : b < r) :
    put (J T L n F r a b c d) (D F r n 3+b+1) (some true)=J T L n F r a (b+1) c d := by
  exact (write fr (V a b c d) 3 b (by omega) (by omega) h true rfl).trans (patch L n F r a b c d 3 (b+1) (by omega) (by omega))
private theorem put3false {T L n Q F r} (fr : Frame T L n Q F r) (a b c d : Nat) (h : b < r) :
    put (J T L n F r a (b+1) c d) (D F r n 3+b+1) (some false)=J T L n F r a b c d := by
  exact (write fr (V a (b+1) c d) 3 b (by omega) (by omega) h false rfl).trans (patch L n F r a (b+1) c d 3 b (by omega) (by omega))
private theorem put4true {T L n Q F r} (fr : Frame T L n Q F r) (a b c d : Nat) (h : c < r) :
    put (J T L n F r a b c d) (D F r n 4+c+1) (some true)=J T L n F r a b (c+1) d := by
  exact (write fr (V a b c d) 4 c (by omega) (by omega) h true rfl).trans (patch L n F r a b c d 4 (c+1) (by omega) (by omega))
private theorem put4false {T L n Q F r} (fr : Frame T L n Q F r) (a b c d : Nat) (h : c < r) :
    put (J T L n F r a b (c+1) d) (D F r n 4+c+1) (some false)=J T L n F r a b c d := by
  exact (write fr (V a b (c+1) d) 4 c (by omega) (by omega) h false rfl).trans (patch L n F r a b (c+1) d 4 c (by omega) (by omega))
private theorem put5true {T L n Q F r} (fr : Frame T L n Q F r) (a b c d : Nat) (h : d < r) :
    put (J T L n F r a b c d) (D F r n 5+d+1) (some true)=J T L n F r a b c (d+1) := by
  exact (write fr (V a b c d) 5 d (by omega) (by omega) h true rfl).trans (patch L n F r a b c d 5 (d+1) (by omega) (by omega))
private theorem put5false {T L n Q F r} (fr : Frame T L n Q F r) (a b c d : Nat) (h : d < r) :
    put (J T L n F r a b c (d+1)) (D F r n 5+d+1) (some false)=J T L n F r a b c d := by
  exact (write fr (V a b c (d+1)) 5 d (by omega) (by omega) h false rfl).trans (patch L n F r a b c (d+1) 5 d (by omega) (by omega))
private def width (n r j : Nat) : Nat := if j=1 then n else r
private def travelTac (ss out fromBank toBank : Nat) (shift : String := "93*k") : TacticM Unit := do
  let right:=fromBank < toBank;let count:=if right then toBank-fromBank else fromBank-toBank
  let mut text:=""
  for z in List.range count do
    let j:=if right then fromBank+z else fromBank-z-1
    let target:=if z+1=count then toString out++"+93*k" else toString (ss+2*(z+1))++"+"++shift
    text:=text++s!"have he{z} : D F r n {j}+width n r {j}+1=D F r n {j+1} := by dsimp [D,width];omega\n"
    text:=text++s!"have tr{z} := cross{if right then "R" else "L"} (k:=k) (P:=P) ({ss+2*z}+{shift}) ({ss+2*z+1}+{shift}) ({target}) (D F r n {j}) (width n r {j}) (J T L n F r a b c d) (by omega) (by omega) (by dsimp [D,width,P];omega) (atD fr (V a b c d) {j} (by omega)) (by rw [he{z}];exact atD fr (V a b c d) {j+1} (by omega)) (by intro i lo hi;exact occupied fr (V a b c d) {j} (by omega) i lo (by rw [← he{z}];exact hi)) (by run_tac rowTac) (by intro bit;cases bit <;> run_tac rowTac) (by run_tac rowTac)\n"
    text:=text++s!"rw [he{z}] at tr{z}\n"
  text:=text++"have path := "++String.intercalate " |>.append " ((List.range count).map fun z => "tr"++toString z)++"\nrefine ⟨_,?_,path⟩\ndsimp only [P,width,D]\nsplit_ifs <;> omega"
  let ast ← ofExcept (Parser.runParserCategory (← getEnv) `tactic ("(\n  "++text.replace "\n" "\n  "++"\n)"))
  evalTactic ast
private def Route (ss fromBank toBank out : Nat) (price : Nat := 8) : Prop :=
  ∀ {k L n Q F r : Nat} (T : Nat → Option Bool), Frame T L n Q F r → ∀ a b c d,
  let P:=F+5*r+n+7
  ∃ t, t  ≤  price*(P+1) ∧ Path k P t (N (Cursor.q k (ss+93*k)) (D F r n fromBank) (J T L n F r a b c d))
    (N (Cursor.q k (out+93*k)) (D F r n toBank) (J T L n F r a b c d))
private theorem route330 : Route 330 3 2 332 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 330 332 3 2
private theorem route336 : Route 336 2 0 798 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 336 798 2 0
private theorem route344 : Route 344 2 0 798 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 344 798 2 0
private theorem route352 : Route 352 2 0 798 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 352 798 2 0
private theorem route360 : Route 360 2 0 798 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 360 798 2 0
private theorem route368 : Route 368 2 3 370 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 368 370 2 3
private theorem route374 : Route 374 3 4 376 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 374 376 3 4
private theorem route380 : Route 380 4 5 382 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 380 382 4 5
private theorem route386 : Route 386 5 3 370 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 386 370 5 3
private theorem route390 : Route 390 3 5 394 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 390 394 3 5
private theorem route398 : Route 398 5 3 402 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 398 402 5 3
private theorem route406 : Route 406 3 5 394 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 406 394 3 5
private theorem route416 : Route 416 5 2 364 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 416 364 5 2
private theorem route422a : Route 422 4 2 426 4 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 422 426 4 2
private theorem route426 : Route 426 2 0 798 4 := by
  intro k L n Q F r T fr a b c d;dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 426 798 2 0
private theorem route422 : Route 422 4 0 798 := by
  intro k L n Q F r T fr a b c d
  obtain ⟨u,pu,p1⟩:=route422a (k:=k) T fr a b c d
  obtain ⟨v,pv,p2⟩:=route426 (k:=k) T fr a b c d
  exact ⟨u+v,by omega,p1.append p2⟩
private theorem addCap {k j L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r) (hk : j < k) (a b c d : Nat) :
    let P:=F+5*r+n+7
    ∃ t, t  ≤  8*(P+1) ∧ Path k P t (N (Cursor.q k (335+82*k+11*j)) (D F r n 3) (J T L n F r a b c d)) (N (Cursor.q k (798+93*k)) (D F r n 0) (J T L n F r a b c d)) := by
  dsimp only;let P:=F+5*r+n+7
  run_tac travelTac 335 798 3 0 "82*k+11*j"
private theorem incAdd {k L n Q F r : Nat} {j : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r) (hk : j < k) (a b c d : Nat) (hv : b  ≤  r) :
    let P:=F+5*r+n+7
    Path k P (2*b+3) (N (Cursor.q k (330+82*k+11*j)) (D F r n 3) (J T L n F r a b c d))
      (N (Cursor.q k (if b < r then 334+82*k+11*j else 335+82*k+11*j)) (D F r n 3) (if b < r then put (J T L n F r a b c d) (D F r n 3+b+1) (some true) else J T L n F r a b c d)) := by
  dsimp only
  apply inc (k:=k) (330+82*k+11*j) (334+82*k+11*j) (335+82*k+11*j) (D F r n 3) r b (J T L n F r a b c d) (by omega) (by dsimp [D];omega) hv
    (atD fr (V a b c d) 3 (by omega)) (by
      have eq : D F r n 3+r+1=D F r n 4 := by dsimp only [D];omega
      rw [eq]
      exact atD fr (V a b c d) 4 (by omega))
    (by intro i lo hi;apply unary fr (V a b c d) 3 (by omega) (by omega) i lo;dsimp only [D] at hi ⊢;omega)
    (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by intro bit;cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
private theorem incFour {k L n Q F r : Nat} {j : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r) (hj : j < 4) (a b c d : Nat) (hv : a  ≤  r) :
    let P:=F+5*r+n+7
    Path k P (2*a+3) (N (Cursor.q k (332+8*j+93*k)) (D F r n 2) (J T L n F r a b c d))
      (N (Cursor.q k (if a < r then 340+8*j+93*k else 336+8*j+93*k)) (D F r n 2) (if a < r then put (J T L n F r a b c d) (D F r n 2+a+1) (some true) else J T L n F r a b c d)) := by
  dsimp only
  fromDonor "FullWeight.Checks" "FullWeight" "four_rows" =>
    obtain ⟨entry,scan,add,full,back,ok,bad,over⟩:=OLD k j hj
  apply inc (k:=k) (332+8*j+93*k) (340+8*j+93*k) (336+8*j+93*k) (D F r n 2) r a (J T L n F r a b c d) (by omega) (by dsimp [D];omega) hv
    (atD fr (V a b c d) 2 (by omega)) (by
      have eq : D F r n 2+r+1=D F r n 3 := by dsimp only [D];omega
      rw [eq]
      exact atD fr (V a b c d) 3 (by omega))
    (by intro i lo hi;apply unary fr (V a b c d) 2 (by omega) (by omega) i lo;dsimp only [D] at hi ⊢;omega)
    entry scan add full back ok bad over
private theorem decOuter {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)  (a b c d : Nat) (hv : a  ≤  r) :
    let P:=F+5*r+n+7
    Path k P (2*a+3) (N (Cursor.q k (364+93*k)) (D F r n 2) (J T L n F r a b c d))
      (N (Cursor.q k (if a=0 then 430+93*k else 368+93*k)) (D F r n 2) (if a=0 then J T L n F r a b c d else put (J T L n F r a b c d) (D F r n 2+a) (some false))) := by
  dsimp only
  apply dec (k:=k) (364+93*k) (368+93*k) (430+93*k) (D F r n 2) r a (J T L n F r a b c d) (by omega) (by dsimp [D];omega) hv
    (atD fr (V a b c d) 2 (by omega)) (by
      have eq : D F r n 2+r+1=D F r n 3 := by dsimp only [D];omega
      rw [eq]
      exact atD fr (V a b c d) 3 (by omega))
    (by intro i lo hi;apply unary fr (V a b c d) 2 (by omega) (by omega) i lo;dsimp only [D] at hi ⊢;omega)
    (by run_tac rowTac) (by run_tac rowTac) (by intro bit hb;cases bit with
      | none => run_tac rowTac
      | some bit => cases bit with
        | false => run_tac rowTac
        | true => exact False.elim (hb rfl)) (by run_tac rowTac) (by intro bit;cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
private theorem decInner {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)  (a b c d : Nat) (hv : b  ≤  r) :
    let P:=F+5*r+n+7
    Path k P (2*b+3) (N (Cursor.q k (370+93*k)) (D F r n 3) (J T L n F r a b c d))
      (N (Cursor.q k (if b=0 then 390+93*k else 374+93*k)) (D F r n 3) (if b=0 then J T L n F r a b c d else put (J T L n F r a b c d) (D F r n 3+b) (some false))) := by
  dsimp only
  apply dec (k:=k) (370+93*k) (374+93*k) (390+93*k) (D F r n 3) r b (J T L n F r a b c d) (by omega) (by dsimp [D];omega) hv
    (atD fr (V a b c d) 3 (by omega)) (by
      have eq : D F r n 3+r+1=D F r n 4 := by dsimp only [D];omega
      rw [eq]
      exact atD fr (V a b c d) 4 (by omega))
    (by intro i lo hi;apply unary fr (V a b c d) 3 (by omega) (by omega) i lo;dsimp only [D] at hi ⊢;omega)
    (by run_tac rowTac) (by run_tac rowTac) (by intro bit hb;cases bit with
      | none => run_tac rowTac
      | some bit => cases bit with
        | false => run_tac rowTac
        | true => exact False.elim (hb rfl)) (by run_tac rowTac) (by intro bit;cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
private theorem incOut {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)  (a b c d : Nat) (hv : c  ≤  r) :
    let P:=F+5*r+n+7
    Path k P (2*c+3) (N (Cursor.q k (376+93*k)) (D F r n 4) (J T L n F r a b c d))
      (N (Cursor.q k (if c < r then 380+93*k else 422+93*k)) (D F r n 4) (if c < r then put (J T L n F r a b c d) (D F r n 4+c+1) (some true) else J T L n F r a b c d)) := by
  dsimp only
  apply inc (k:=k) (376+93*k) (380+93*k) (422+93*k) (D F r n 4) r c (J T L n F r a b c d) (by omega) (by dsimp [D];omega) hv
    (atD fr (V a b c d) 4 (by omega)) (by
      have eq : D F r n 4+r+1=D F r n 5 := by dsimp only [D];omega
      rw [eq]
      exact atD fr (V a b c d) 5 (by omega))
    (by intro i lo hi;apply unary fr (V a b c d) 4 (by omega) (by omega) i lo;dsimp only [D] at hi ⊢;omega)
    (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by intro bit;cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
private theorem incTemp {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)  (a b c d : Nat) (hv : d  ≤  r) :
    let P:=F+5*r+n+7
    Path k P (2*d+3) (N (Cursor.q k (382+93*k)) (D F r n 5) (J T L n F r a b c d))
      (N (Cursor.q k (if d < r then 386+93*k else 422+93*k)) (D F r n 5) (if d < r then put (J T L n F r a b c d) (D F r n 5+d+1) (some true) else J T L n F r a b c d)) := by
  dsimp only
  apply inc (k:=k) (382+93*k) (386+93*k) (422+93*k) (D F r n 5) r d (J T L n F r a b c d) (by omega) (by dsimp [D];omega) hv
    (atD fr (V a b c d) 5 (by omega)) (by
      have eq : D F r n 5+r+1=D F r n 6 := by dsimp only [D];omega
      rw [eq]
      exact atD fr (V a b c d) 6 (by omega))
    (by intro i lo hi;apply unary fr (V a b c d) 5 (by omega) (by omega) i lo;dsimp only [D] at hi ⊢;omega)
    (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by intro bit;cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
private theorem decRest {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)  (a b c d : Nat) (hv : d  ≤  r) :
    let P:=F+5*r+n+7
    Path k P (2*d+3) (N (Cursor.q k (394+93*k)) (D F r n 5) (J T L n F r a b c d))
      (N (Cursor.q k (if d=0 then 416+93*k else 398+93*k)) (D F r n 5) (if d=0 then J T L n F r a b c d else put (J T L n F r a b c d) (D F r n 5+d) (some false))) := by
  dsimp only
  apply dec (k:=k) (394+93*k) (398+93*k) (416+93*k) (D F r n 5) r d (J T L n F r a b c d) (by omega) (by dsimp [D];omega) hv
    (atD fr (V a b c d) 5 (by omega)) (by
      have eq : D F r n 5+r+1=D F r n 6 := by dsimp only [D];omega
      rw [eq]
      exact atD fr (V a b c d) 6 (by omega))
    (by intro i lo hi;apply unary fr (V a b c d) 5 (by omega) (by omega) i lo;dsimp only [D] at hi ⊢;omega)
    (by run_tac rowTac) (by run_tac rowTac) (by intro bit hb;cases bit with
      | none => run_tac rowTac
      | some bit => cases bit with
        | false => run_tac rowTac
        | true => exact False.elim (hb rfl)) (by run_tac rowTac) (by intro bit;cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
private theorem incRest {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)  (a b c d : Nat) (hv : b  ≤  r) :
    let P:=F+5*r+n+7
    Path k P (2*b+3) (N (Cursor.q k (402+93*k)) (D F r n 3) (J T L n F r a b c d))
      (N (Cursor.q k (if b < r then 406+93*k else 410+93*k)) (D F r n 3) (if b < r then put (J T L n F r a b c d) (D F r n 3+b+1) (some true) else J T L n F r a b c d)) := by
  dsimp only
  apply inc (k:=k) (402+93*k) (406+93*k) (410+93*k) (D F r n 3) r b (J T L n F r a b c d) (by omega) (by dsimp [D];omega) hv
    (atD fr (V a b c d) 3 (by omega)) (by
      have eq : D F r n 3+r+1=D F r n 4 := by dsimp only [D];omega
      rw [eq]
      exact atD fr (V a b c d) 4 (by omega))
    (by intro i lo hi;apply unary fr (V a b c d) 3 (by omega) (by omega) i lo;dsimp only [D] at hi ⊢;omega)
    (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by intro bit;cases bit <;> run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac) (by run_tac rowTac)
end FullWeight
