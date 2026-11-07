import PostWeight.Target
namespace PostWeight
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
set_option maxRecDepth 10000
private def aft (k : Nat) : List Nat := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "aft" => exact OLD k
private def sym : Option Bool → Nat | none => 0 | some false => 1 | some true => 2
private def mov : Move → Nat | .left => 0 | .stay => 1 | .right => 2
private def enc (s : Nat) (b : Option Bool) (m : Move) := 9*s+3*sym b+mov m
private theorem post_row (k i s : Nat) (b w : Option Bool) (mv : Move) (lo : 330 ≤ i) (hi : i < 937)
    (got : (aft k)[3*(i-330)+sym b]?=some (enc s w mv)) :
    (Cursor.machine k).step (Cursor.q k (i+93*k)) b=(Cursor.q k s,w,mv) := by
  fromDonor "VirtualReady.Kernel" "VirtualReady" "program_split" => have split := OLD k
  fromDonor "VirtualReady.Kernel" "VirtualReady" "pref_len" => have len := OLD k
  fromDonor "VirtualReady.Kernel" "VirtualReady" "decode_actual" =>
    have row := OLD k (i+93*k) (enc s w mv) b (by omega) (by unfold Cursor.stateCount; omega) (by
      rw [split,List.getElem?_toArray,List.getElem?_append,if_neg (by rw [len]; omega)]
      rw [len]
      change (aft k)[3*(i+93*k-64)+sym b-(798+279*k)]?=some (enc s w mv)
      rw [show 3*(i+93*k-64)+sym b-(798+279*k)=3*(i-330)+sym b by omega]
      exact got)
  fromDonor "VirtualReady.Kernel" "VirtualReady" "dec_enc" => exact row.trans (OLD k s w mv)
@[simp] private theorem alen0 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after0" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen1 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after1" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen2 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after2" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen3 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after3" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen4 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after4" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen5 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after5" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen6 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after6" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen7 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after7" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen8 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after8" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen9 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after9" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen10 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after10" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen11 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after11" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen12 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after12" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen13 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after13" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen14 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after14" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen15 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after15" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen16 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after16" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen17 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after17" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen18 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after18" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen19 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after19" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen20 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after20" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen21 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after21" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen22 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after22" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen23 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after23" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen24 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after24" => exact OLD k 0).length=72 := rfl
@[simp] private theorem alen25 (k : Nat) :
    (show List Nat from by fromDonor "Cursor.Machine" "Cursor" "after25" => exact OLD k 0).length=21 := rfl
private theorem norm_row (k i s : Nat) (b w : Option Bool) (mv : Move) (lo : 330 ≤ i) (hi : i < 937)
    (got : (aft k)[3*(i-330)+sym b]?=some (enc s w mv)) :
    (Cursor.machine k).step (Cursor.q k (i+k*93)) b=(Cursor.q k s,w,mv) := by
  simpa only [Nat.mul_comm] using post_row k i s b w mv lo hi got
/-- Elaboration metadata only: unique names from the pinned environment.
No reference from the executable Cursor family to this table. -/
private def rowNames : List Name := by
  run_tac do
    let ns := (← getEnv).constants.toList.map Prod.fst
    let requests := [("VirtualReady.Kernel","VirtualReady.aft"),("Cursor.Machine","Cursor.after")] ++
      (List.range 26).map (fun j => ("Cursor.Machine","Cursor.after"++toString j))
    let mut chosen := []
    for (mod,key) in requests do
      let names := ns.filter fun n => n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++key)
      unless names.length=1 do throwError "Ambiguous pinned proof API {mod} {key}"
      logInfo m!"private-row-selection|{names.head!}"
      chosen := chosen ++ names
    evalTactic (← `(tactic| exact $(quote chosen)))
private def rowTac : TacticM Unit := do
  evalTactic (← `(tactic| conv_lhs => arg 2; arg 2; ring_nf))
  evalTactic (← `(tactic| apply norm_row))
  evalTactic (← `(tactic| all_goals first | omega | skip))
  evalTactic (← `(tactic| dsimp only [aft,sym,enc,mov]))
  let oldId := mkIdent rowNames[0]!
  evalTactic (← `(tactic| dsimp only [$oldId:ident]))
  let afterId := mkIdent rowNames[1]!
  evalTactic (← `(tactic| simp [$afterId:ident,List.getElem?_append]))
  for n in rowNames.drop 2 do
    let id := mkIdent n
    evalTactic (← `(tactic| try dsimp only [$id:ident]))
  evalTactic (← `(tactic| simp))
  unless (← getGoals).isEmpty do evalTactic (← `(tactic| first | ring | (apply congrArg some; ring)))
private theorem sample (k : Nat) :
    (Cursor.machine k).step (Cursor.q k (430+93*k)) none=(Cursor.q k (431+93*k),none,.right) := by
  run_tac rowTac
private theorem sample_shift (k : Nat) (b : Bool) :
    (Cursor.machine k).step (Cursor.q k (443+93*k+2)) (some b)=
      (Cursor.q k (443+93*k+2),some b,.left) := by
  cases b <;> run_tac rowTac
end PostWeight
