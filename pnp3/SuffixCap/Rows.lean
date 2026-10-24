import SuffixCap.Target
namespace SuffixCap
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
set_option maxRecDepth 10000
-- Proof aliases of immutable data, never a second runtime controller.
private abbrev codes (k : Nat) : Array Nat := by
  run_tac do
    let n := (← getEnv).constants.toList.find? fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.program"
    let id := mkIdent n.get!.1
    let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident))
private abbrev chunk0 (k : Nat) : List Nat := by
  run_tac do
    let n := (← getEnv).constants.toList.find? fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.before0"
    let id := mkIdent n.get!.1
    let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident 0))
private abbrev chunk1 (k : Nat) : List Nat := by
  run_tac do
    let n := (← getEnv).constants.toList.find? fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.before1"
    let id := mkIdent n.get!.1
    let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident 0))
private theorem lookup (k i : Nat) (hi : i < 144) :
    (codes k)[i]?=(chunk0 k++chunk1 k)[i]? := by
  have l0 : (chunk0 k).length=72 := rfl
  have l1 : (chunk1 k).length=72 := rfl
  unfold codes
  run_tac do
    let ns := (← getEnv).constants.toList.filterMap fun (n,_) =>
      if n.toString.startsWith "_private.Cursor.Machine." &&
         [".Cursor.program", ".Cursor.before"].any n.toString.endsWith
      then some (mkIdent n) else none
    for n in ns do evalTactic (← `(tactic| simp only [$n:ident]))
  simp only [List.getElem?_toArray,List.append_assoc]
  change (chunk0 k++(chunk1 k++_))[i]?=(chunk0 k++chunk1 k)[i]?
  by_cases h : i < 72
  · simp only [List.getElem?_append,l0,h,↓reduceIte]
  · simp only [List.getElem?_append,l0,h,l1,show i-72 < 72 by omega,↓reduceIte]
private theorem small_mod (k i : Nat) (h : i  ≤  98) : i % Cursor.stateCount k=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
private def base (b : Bool) : Nat := if b then 83 else 68
private theorem decode_row (k i code : Nat) (b : Option Bool)
    (lo : 64 ≤ i) (hi : i < 98) (h65 : i ≠ 65) (h66 : i ≠ 66) (h67 : i ≠ 67)
    (got : (codes k)[3*(i-64)+(match b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  simp only [UniformTM.step,Cursor.machine,Cursor.q,small_mod k i (by omega),
    small_mod k 39 (by omega),small_mod k 40 (by omega),Fin.mk.injEq,
    show i ≠ 39 by omega,show i ≠ 40 by omega,↓reduceIte]
  run_tac do
    let n := (← getEnv).constants.toList.find? fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.decode"
    let id := mkIdent n.get!.1
    evalTactic (← `(tactic| simp only [$id:ident]))
  simp only [show i ≠ 57 by omega,show i ≠ 58 by omega,show ¬i < 64 by omega,h65,h66,h67,↓reduceIte]
  cases b with
  | none =>
    dsimp only [codes] at got
    dsimp only
    rw [got]
    rfl
  | some b =>
    cases b <;> dsimp only [codes] at got <;> dsimp only <;> rw [got] <;> rfl
private theorem pin_64_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 64) (some false)=(Cursor.q k 68,none,.right) := by
  have got : (codes k)[1]?=some 614 := by rw [lookup k 1 (by omega)]; rfl
  exact decode_row k 64 614 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_64_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 64) (some true)=(Cursor.q k 83,none,.right) := by
  have got : (codes k)[2]?=some 749 := by rw [lookup k 2 (by omega)]; rfl
  exact decode_row k 64 749 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_68_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 68) none=(Cursor.q k 69,none,.right) := by
  have got : (codes k)[12]?=some 623 := by rw [lookup k 12 (by omega)]; rfl
  exact decode_row k 68 623 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_68_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 68) (some false)=(Cursor.q k 68,(some false),.right) := by
  have got : (codes k)[13]?=some 617 := by rw [lookup k 13 (by omega)]; rfl
  exact decode_row k 68 617 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_68_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 68) (some true)=(Cursor.q k 68,(some true),.right) := by
  have got : (codes k)[14]?=some 620 := by rw [lookup k 14 (by omega)]; rfl
  exact decode_row k 68 620 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_69_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 69) none=(Cursor.q k 70,none,.right) := by
  have got : (codes k)[15]?=some 632 := by rw [lookup k 15 (by omega)]; rfl
  exact decode_row k 69 632 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_69_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 69) (some false)=(Cursor.q k 69,(some false),.right) := by
  have got : (codes k)[16]?=some 626 := by rw [lookup k 16 (by omega)]; rfl
  exact decode_row k 69 626 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_69_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 69) (some true)=(Cursor.q k 40,(some true),.stay) := by
  have got : (codes k)[17]?=some 367 := by rw [lookup k 17 (by omega)]; rfl
  exact decode_row k 69 367 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_70_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 70) none=(Cursor.q k 71,none,.stay) := by
  have got : (codes k)[18]?=some 640 := by rw [lookup k 18 (by omega)]; rfl
  exact decode_row k 70 640 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_70_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 70) (some false)=(Cursor.q k 70,(some false),.right) := by
  have got : (codes k)[19]?=some 635 := by rw [lookup k 19 (by omega)]; rfl
  exact decode_row k 70 635 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_70_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 70) (some true)=(Cursor.q k 70,(some true),.right) := by
  have got : (codes k)[20]?=some 638 := by rw [lookup k 20 (by omega)]; rfl
  exact decode_row k 70 638 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_71_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 71) none=(Cursor.q k 72,none,.right) := by
  have got : (codes k)[21]?=some 650 := by rw [lookup k 21 (by omega)]; rfl
  exact decode_row k 71 650 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_71_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 71) (some false)=(Cursor.q k 72,(some false),.right) := by
  have got : (codes k)[22]?=some 653 := by rw [lookup k 22 (by omega)]; rfl
  exact decode_row k 71 653 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_71_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 71) (some true)=(Cursor.q k 72,(some true),.right) := by
  have got : (codes k)[23]?=some 656 := by rw [lookup k 23 (by omega)]; rfl
  exact decode_row k 71 656 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_72_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 72) none=(Cursor.q k 72,none,.right) := by
  have got : (codes k)[24]?=some 650 := by rw [lookup k 24 (by omega)]; rfl
  exact decode_row k 72 650 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_72_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 72) (some false)=(Cursor.q k 73,(some false),.right) := by
  have got : (codes k)[25]?=some 662 := by rw [lookup k 25 (by omega)]; rfl
  exact decode_row k 72 662 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_72_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 72) (some true)=(Cursor.q k 72,(some true),.right) := by
  have got : (codes k)[26]?=some 656 := by rw [lookup k 26 (by omega)]; rfl
  exact decode_row k 72 656 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_73_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 73) none=(Cursor.q k 74,none,.right) := by
  have got : (codes k)[27]?=some 668 := by rw [lookup k 27 (by omega)]; rfl
  exact decode_row k 73 668 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_73_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 73) (some false)=(Cursor.q k 40,(some false),.stay) := by
  have got : (codes k)[28]?=some 364 := by rw [lookup k 28 (by omega)]; rfl
  exact decode_row k 73 364 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_73_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 73) (some true)=(Cursor.q k 40,(some true),.stay) := by
  have got : (codes k)[29]?=some 367 := by rw [lookup k 29 (by omega)]; rfl
  exact decode_row k 73 367 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_74_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 74) none=(Cursor.q k 75,(some true),.left) := by
  have got : (codes k)[30]?=some 681 := by rw [lookup k 30 (by omega)]; rfl
  exact decode_row k 74 681 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_74_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 74) (some false)=(Cursor.q k 40,(some false),.stay) := by
  have got : (codes k)[31]?=some 364 := by rw [lookup k 31 (by omega)]; rfl
  exact decode_row k 74 364 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_74_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 74) (some true)=(Cursor.q k 74,(some true),.right) := by
  have got : (codes k)[32]?=some 674 := by rw [lookup k 32 (by omega)]; rfl
  exact decode_row k 74 674 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_75_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 75) none=(Cursor.q k 76,none,.left) := by
  have got : (codes k)[33]?=some 684 := by rw [lookup k 33 (by omega)]; rfl
  exact decode_row k 75 684 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_75_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 75) (some false)=(Cursor.q k 40,(some false),.stay) := by
  have got : (codes k)[34]?=some 364 := by rw [lookup k 34 (by omega)]; rfl
  exact decode_row k 75 364 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_75_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 75) (some true)=(Cursor.q k 75,(some true),.left) := by
  have got : (codes k)[35]?=some 681 := by rw [lookup k 35 (by omega)]; rfl
  exact decode_row k 75 681 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_76_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 76) none=(Cursor.q k 40,none,.stay) := by
  have got : (codes k)[36]?=some 361 := by rw [lookup k 36 (by omega)]; rfl
  exact decode_row k 76 361 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_76_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 76) (some false)=(Cursor.q k 77,(some false),.left) := by
  have got : (codes k)[37]?=some 696 := by rw [lookup k 37 (by omega)]; rfl
  exact decode_row k 76 696 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_76_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 76) (some true)=(Cursor.q k 40,(some true),.stay) := by
  have got : (codes k)[38]?=some 367 := by rw [lookup k 38 (by omega)]; rfl
  exact decode_row k 76 367 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_77_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 77) none=(Cursor.q k 77,none,.left) := by
  have got : (codes k)[39]?=some 693 := by rw [lookup k 39 (by omega)]; rfl
  exact decode_row k 77 693 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_77_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 77) (some false)=(Cursor.q k 40,(some false),.stay) := by
  have got : (codes k)[40]?=some 364 := by rw [lookup k 40 (by omega)]; rfl
  exact decode_row k 77 364 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_77_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 77) (some true)=(Cursor.q k 78,(some true),.left) := by
  have got : (codes k)[41]?=some 708 := by rw [lookup k 41 (by omega)]; rfl
  exact decode_row k 77 708 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_78_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 78) none=(Cursor.q k 79,none,.left) := by
  have got : (codes k)[42]?=some 711 := by rw [lookup k 42 (by omega)]; rfl
  exact decode_row k 78 711 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_78_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 78) (some false)=(Cursor.q k 40,(some false),.stay) := by
  have got : (codes k)[43]?=some 364 := by rw [lookup k 43 (by omega)]; rfl
  exact decode_row k 78 364 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_78_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 78) (some true)=(Cursor.q k 78,(some true),.left) := by
  have got : (codes k)[44]?=some 708 := by rw [lookup k 44 (by omega)]; rfl
  exact decode_row k 78 708 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_79_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 79) none=(Cursor.q k 80,none,.left) := by
  have got : (codes k)[45]?=some 720 := by rw [lookup k 45 (by omega)]; rfl
  exact decode_row k 79 720 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_79_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 79) (some false)=(Cursor.q k 79,(some false),.left) := by
  have got : (codes k)[46]?=some 714 := by rw [lookup k 46 (by omega)]; rfl
  exact decode_row k 79 714 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_79_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 79) (some true)=(Cursor.q k 79,(some true),.left) := by
  have got : (codes k)[47]?=some 717 := by rw [lookup k 47 (by omega)]; rfl
  exact decode_row k 79 717 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_80_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 80) none=(Cursor.q k 81,none,.left) := by
  have got : (codes k)[48]?=some 729 := by rw [lookup k 48 (by omega)]; rfl
  exact decode_row k 80 729 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_80_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 80) (some false)=(Cursor.q k 80,(some false),.left) := by
  have got : (codes k)[49]?=some 723 := by rw [lookup k 49 (by omega)]; rfl
  exact decode_row k 80 723 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_80_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 80) (some true)=(Cursor.q k 40,(some true),.stay) := by
  have got : (codes k)[50]?=some 367 := by rw [lookup k 50 (by omega)]; rfl
  exact decode_row k 80 367 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_81_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 81) none=(Cursor.q k 82,(some false),.right) := by
  have got : (codes k)[51]?=some 743 := by rw [lookup k 51 (by omega)]; rfl
  exact decode_row k 81 743 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_81_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 81) (some false)=(Cursor.q k 81,(some false),.left) := by
  have got : (codes k)[52]?=some 732 := by rw [lookup k 52 (by omega)]; rfl
  exact decode_row k 81 732 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_81_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 81) (some true)=(Cursor.q k 81,(some true),.left) := by
  have got : (codes k)[53]?=some 735 := by rw [lookup k 53 (by omega)]; rfl
  exact decode_row k 81 735 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_82_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 82) none=(Cursor.q k 98,none,.stay) := by
  have got : (codes k)[54]?=some 883 := by rw [lookup k 54 (by omega)]; rfl
  exact decode_row k 82 883 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_82_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 82) (some false)=(Cursor.q k 68,none,.right) := by
  have got : (codes k)[55]?=some 614 := by rw [lookup k 55 (by omega)]; rfl
  exact decode_row k 82 614 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_82_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 82) (some true)=(Cursor.q k 83,none,.right) := by
  have got : (codes k)[56]?=some 749 := by rw [lookup k 56 (by omega)]; rfl
  exact decode_row k 82 749 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_83_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 83) none=(Cursor.q k 84,none,.right) := by
  have got : (codes k)[57]?=some 758 := by rw [lookup k 57 (by omega)]; rfl
  exact decode_row k 83 758 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_83_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 83) (some false)=(Cursor.q k 83,(some false),.right) := by
  have got : (codes k)[58]?=some 752 := by rw [lookup k 58 (by omega)]; rfl
  exact decode_row k 83 752 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_83_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 83) (some true)=(Cursor.q k 83,(some true),.right) := by
  have got : (codes k)[59]?=some 755 := by rw [lookup k 59 (by omega)]; rfl
  exact decode_row k 83 755 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_84_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 84) none=(Cursor.q k 85,none,.right) := by
  have got : (codes k)[60]?=some 767 := by rw [lookup k 60 (by omega)]; rfl
  exact decode_row k 84 767 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_84_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 84) (some false)=(Cursor.q k 84,(some false),.right) := by
  have got : (codes k)[61]?=some 761 := by rw [lookup k 61 (by omega)]; rfl
  exact decode_row k 84 761 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_84_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 84) (some true)=(Cursor.q k 40,(some true),.stay) := by
  have got : (codes k)[62]?=some 367 := by rw [lookup k 62 (by omega)]; rfl
  exact decode_row k 84 367 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_85_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 85) none=(Cursor.q k 86,none,.stay) := by
  have got : (codes k)[63]?=some 775 := by rw [lookup k 63 (by omega)]; rfl
  exact decode_row k 85 775 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_85_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 85) (some false)=(Cursor.q k 85,(some false),.right) := by
  have got : (codes k)[64]?=some 770 := by rw [lookup k 64 (by omega)]; rfl
  exact decode_row k 85 770 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_85_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 85) (some true)=(Cursor.q k 85,(some true),.right) := by
  have got : (codes k)[65]?=some 773 := by rw [lookup k 65 (by omega)]; rfl
  exact decode_row k 85 773 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_86_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 86) none=(Cursor.q k 87,none,.right) := by
  have got : (codes k)[66]?=some 785 := by rw [lookup k 66 (by omega)]; rfl
  exact decode_row k 86 785 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_86_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 86) (some false)=(Cursor.q k 87,(some false),.right) := by
  have got : (codes k)[67]?=some 788 := by rw [lookup k 67 (by omega)]; rfl
  exact decode_row k 86 788 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_86_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 86) (some true)=(Cursor.q k 87,(some true),.right) := by
  have got : (codes k)[68]?=some 791 := by rw [lookup k 68 (by omega)]; rfl
  exact decode_row k 86 791 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_87_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 87) none=(Cursor.q k 87,none,.right) := by
  have got : (codes k)[69]?=some 785 := by rw [lookup k 69 (by omega)]; rfl
  exact decode_row k 87 785 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_87_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 87) (some false)=(Cursor.q k 88,(some false),.right) := by
  have got : (codes k)[70]?=some 797 := by rw [lookup k 70 (by omega)]; rfl
  exact decode_row k 87 797 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_87_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 87) (some true)=(Cursor.q k 87,(some true),.right) := by
  have got : (codes k)[71]?=some 791 := by rw [lookup k 71 (by omega)]; rfl
  exact decode_row k 87 791 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_88_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 88) none=(Cursor.q k 89,none,.right) := by
  have got : (codes k)[72]?=some 803 := by rw [lookup k 72 (by omega)]; rfl
  exact decode_row k 88 803 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_88_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 88) (some false)=(Cursor.q k 40,(some false),.stay) := by
  have got : (codes k)[73]?=some 364 := by rw [lookup k 73 (by omega)]; rfl
  exact decode_row k 88 364 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_88_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 88) (some true)=(Cursor.q k 40,(some true),.stay) := by
  have got : (codes k)[74]?=some 367 := by rw [lookup k 74 (by omega)]; rfl
  exact decode_row k 88 367 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_89_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 89) none=(Cursor.q k 90,(some true),.left) := by
  have got : (codes k)[75]?=some 816 := by rw [lookup k 75 (by omega)]; rfl
  exact decode_row k 89 816 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_89_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 89) (some false)=(Cursor.q k 40,(some false),.stay) := by
  have got : (codes k)[76]?=some 364 := by rw [lookup k 76 (by omega)]; rfl
  exact decode_row k 89 364 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_89_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 89) (some true)=(Cursor.q k 89,(some true),.right) := by
  have got : (codes k)[77]?=some 809 := by rw [lookup k 77 (by omega)]; rfl
  exact decode_row k 89 809 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_90_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 90) none=(Cursor.q k 91,none,.left) := by
  have got : (codes k)[78]?=some 819 := by rw [lookup k 78 (by omega)]; rfl
  exact decode_row k 90 819 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_90_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 90) (some false)=(Cursor.q k 40,(some false),.stay) := by
  have got : (codes k)[79]?=some 364 := by rw [lookup k 79 (by omega)]; rfl
  exact decode_row k 90 364 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_90_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 90) (some true)=(Cursor.q k 90,(some true),.left) := by
  have got : (codes k)[80]?=some 816 := by rw [lookup k 80 (by omega)]; rfl
  exact decode_row k 90 816 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_91_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 91) none=(Cursor.q k 40,none,.stay) := by
  have got : (codes k)[81]?=some 361 := by rw [lookup k 81 (by omega)]; rfl
  exact decode_row k 91 361 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_91_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 91) (some false)=(Cursor.q k 92,(some false),.left) := by
  have got : (codes k)[82]?=some 831 := by rw [lookup k 82 (by omega)]; rfl
  exact decode_row k 91 831 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_91_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 91) (some true)=(Cursor.q k 40,(some true),.stay) := by
  have got : (codes k)[83]?=some 367 := by rw [lookup k 83 (by omega)]; rfl
  exact decode_row k 91 367 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_92_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 92) none=(Cursor.q k 92,none,.left) := by
  have got : (codes k)[84]?=some 828 := by rw [lookup k 84 (by omega)]; rfl
  exact decode_row k 92 828 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_92_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 92) (some false)=(Cursor.q k 40,(some false),.stay) := by
  have got : (codes k)[85]?=some 364 := by rw [lookup k 85 (by omega)]; rfl
  exact decode_row k 92 364 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_92_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 92) (some true)=(Cursor.q k 93,(some true),.left) := by
  have got : (codes k)[86]?=some 843 := by rw [lookup k 86 (by omega)]; rfl
  exact decode_row k 92 843 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_93_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 93) none=(Cursor.q k 94,none,.left) := by
  have got : (codes k)[87]?=some 846 := by rw [lookup k 87 (by omega)]; rfl
  exact decode_row k 93 846 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_93_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 93) (some false)=(Cursor.q k 40,(some false),.stay) := by
  have got : (codes k)[88]?=some 364 := by rw [lookup k 88 (by omega)]; rfl
  exact decode_row k 93 364 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_93_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 93) (some true)=(Cursor.q k 93,(some true),.left) := by
  have got : (codes k)[89]?=some 843 := by rw [lookup k 89 (by omega)]; rfl
  exact decode_row k 93 843 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_94_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 94) none=(Cursor.q k 95,none,.left) := by
  have got : (codes k)[90]?=some 855 := by rw [lookup k 90 (by omega)]; rfl
  exact decode_row k 94 855 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_94_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 94) (some false)=(Cursor.q k 94,(some false),.left) := by
  have got : (codes k)[91]?=some 849 := by rw [lookup k 91 (by omega)]; rfl
  exact decode_row k 94 849 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_94_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 94) (some true)=(Cursor.q k 94,(some true),.left) := by
  have got : (codes k)[92]?=some 852 := by rw [lookup k 92 (by omega)]; rfl
  exact decode_row k 94 852 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_95_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 95) none=(Cursor.q k 96,none,.left) := by
  have got : (codes k)[93]?=some 864 := by rw [lookup k 93 (by omega)]; rfl
  exact decode_row k 95 864 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_95_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 95) (some false)=(Cursor.q k 95,(some false),.left) := by
  have got : (codes k)[94]?=some 858 := by rw [lookup k 94 (by omega)]; rfl
  exact decode_row k 95 858 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_95_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 95) (some true)=(Cursor.q k 40,(some true),.stay) := by
  have got : (codes k)[95]?=some 367 := by rw [lookup k 95 (by omega)]; rfl
  exact decode_row k 95 367 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_96_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 96) none=(Cursor.q k 97,(some true),.right) := by
  have got : (codes k)[96]?=some 881 := by rw [lookup k 96 (by omega)]; rfl
  exact decode_row k 96 881 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_96_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 96) (some false)=(Cursor.q k 96,(some false),.left) := by
  have got : (codes k)[97]?=some 867 := by rw [lookup k 97 (by omega)]; rfl
  exact decode_row k 96 867 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_96_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 96) (some true)=(Cursor.q k 96,(some true),.left) := by
  have got : (codes k)[98]?=some 870 := by rw [lookup k 98 (by omega)]; rfl
  exact decode_row k 96 870 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_97_0 (k : Nat) : (Cursor.machine k).step (Cursor.q k 97) none=(Cursor.q k 98,none,.stay) := by
  have got : (codes k)[99]?=some 883 := by rw [lookup k 99 (by omega)]; rfl
  exact decode_row k 97 883 none (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_97_1 (k : Nat) : (Cursor.machine k).step (Cursor.q k 97) (some false)=(Cursor.q k 68,none,.right) := by
  have got : (codes k)[100]?=some 614 := by rw [lookup k 100 (by omega)]; rfl
  exact decode_row k 97 614 (some false) (by omega) (by omega) (by omega) (by omega) (by omega) got
private theorem pin_97_2 (k : Nat) : (Cursor.machine k).step (Cursor.q k 97) (some true)=(Cursor.q k 83,none,.right) := by
  have got : (codes k)[101]?=some 749 := by rw [lookup k 101 (by omega)]; rfl
  exact decode_row k 97 749 (some true) (by omega) (by omega) (by omega) (by omega) (by omega) got
theorem count_rows (k : Nat) (b : Bool) :
    (∀ v, (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68))) (some v)=(Cursor.q k ((if b then 83 else 68)),some v,.right)) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68))) none=(Cursor.q k ((if b then 83 else 68)+1),none,.right) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+1)) (some false)=(Cursor.q k ((if b then 83 else 68)+1),some false,.right) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+1)) none=(Cursor.q k ((if b then 83 else 68)+2),none,.right) ∧
    (∀ v, (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+2)) (some v)=(Cursor.q k ((if b then 83 else 68)+2),some v,.right)) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+2)) none=(Cursor.q k ((if b then 83 else 68)+3),none,.stay) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+3)) none=(Cursor.q k ((if b then 83 else 68)+4),none,.right) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+4)) none=(Cursor.q k ((if b then 83 else 68)+4),none,.right) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+4)) (some true)=(Cursor.q k ((if b then 83 else 68)+4),some true,.right) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+4)) (some false)=(Cursor.q k ((if b then 83 else 68)+5),some false,.right) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+5)) none=(Cursor.q k ((if b then 83 else 68)+6),none,.right) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+6)) (some true)=(Cursor.q k ((if b then 83 else 68)+6),some true,.right) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+6)) none=(Cursor.q k ((if b then 83 else 68)+7),some true,.left) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+7)) (some true)=(Cursor.q k ((if b then 83 else 68)+7),some true,.left) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+7)) none=(Cursor.q k ((if b then 83 else 68)+8),none,.left) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+8)) (some false)=(Cursor.q k ((if b then 83 else 68)+9),some false,.left) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+9)) none=(Cursor.q k ((if b then 83 else 68)+9),none,.left) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+9)) (some true)=(Cursor.q k ((if b then 83 else 68)+10),some true,.left) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+10)) (some true)=(Cursor.q k ((if b then 83 else 68)+10),some true,.left) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+10)) none=(Cursor.q k ((if b then 83 else 68)+11),none,.left) ∧
    (∀ v, (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+11)) (some v)=(Cursor.q k ((if b then 83 else 68)+11),some v,.left)) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+11)) none=(Cursor.q k ((if b then 83 else 68)+12),none,.left) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+12)) (some false)=(Cursor.q k ((if b then 83 else 68)+12),some false,.left) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+12)) none=(Cursor.q k ((if b then 83 else 68)+13),none,.left) ∧
    (∀ v, (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+13)) (some v)=(Cursor.q k ((if b then 83 else 68)+13),some v,.left)) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+13)) none=(Cursor.q k ((if b then 83 else 68)+14),some b,.right) ∧
    (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+14)) none=(Cursor.rReady k,none,.stay) ∧
    (∀ v, (Cursor.machine k).step (Cursor.q k ((if b then 83 else 68)+14)) (some v)=(Cursor.q k ((if v then 83 else 68)),none,.right)) := by
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals repeat' apply And.intro
  all_goals (try intro v; cases v)
  run_tac do
    let n := (← getEnv).constants.toList.find? fun (n,_) => n.toString.endsWith ".SuffixCap.pin_68_0"
    let pref := n.get!.1.getPrefix
    let gs ← getGoals
    for g in gs do
      setGoals [g]
      withMainContext do
        let (_,lhs,_) := (← Lean.Meta.matchEq? (← g.getType)).get!
        let args := lhs.getAppArgs
        let i := (← Lean.Meta.getNatValue? (← Lean.Meta.whnf (args[1]!.getAppArgs[1]!))).get!
        let b ← Lean.Meta.whnf args[2]!
        let sym := if b.getAppFn.isConstOf ``Option.none then 0 else
          if b.getAppArgs.back!.isConstOf ``Bool.true then 2 else 1
        let id := mkIdent (Name.str pref ("pin_"++toString i++"_"++toString sym))
        let kv := mkIdent `k
        evalTactic (← `(tactic| exact $id:ident $kv:ident))

theorem entry_rows (k : Nat) (b : Bool) :
    (Cursor.machine k).step (Cursor.q k 58) (some b)=(Cursor.q k 64,some b,.stay) ∧
    (Cursor.machine k).step (Cursor.q k 64) (some b)=(Cursor.q k (if b then 83 else 68),none,.right) := by
  constructor
  · simp only [UniformTM.step,Cursor.machine,Cursor.q,small_mod k 58 (by omega),
      small_mod k 39 (by omega),small_mod k 40 (by omega),Fin.mk.injEq]
    run_tac do
      let n := (← getEnv).constants.toList.find? fun (n,_) =>
        n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.decode"
      let id := mkIdent n.get!.1
      evalTactic (← `(tactic| simp only [$id:ident]))
    simp only [↓reduceIte]
    rfl
  · cases b <;> simp only [Bool.false_eq_true,↓reduceIte,pin_64_1,pin_64_2]
end SuffixCap
