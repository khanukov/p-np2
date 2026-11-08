import AllArityBitLength.Target
namespace AllArityBitLength
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
set_option maxRecDepth 10000
/-- Proof-side codes, checked against the immutable Cursor table. -/
def instructions (k : Nat) : List Nat := [
  2783, 2786, 2789, 2791, 2786, 2789, 2801, 2804, 2807, 2801, 2813, 2807,
  2819, 2822, 2825, 2827, 2822, 2825, 2837, 2840, 2843, 2845, 2840, 2843,
  2855, 2858, 2861, 2863, 2858, 2861, 2873, 2876, 2879, 2889, 2886, 2879,
  2953, 2883, 2886, 2899, 2892, 2895, 2907, 2910, 2913, 2917, 2910, 2913,
  2925, 2928, 2931, 2935, 2928, 2931, 2943, 2946, 2949, (7183+837*k), 2946, 2949,
  2962, 2965, 2968 ]
private def selectCursor (suffix : String) : TacticM Name := do
  let names := (← getEnv).constants.toList.map Prod.fst |>.filter fun n =>
    n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith (".Cursor."++suffix)
  unless names.length=1 do throwError "Ambiguous immutable Cursor term: {names}"
  logInfo m!"private-term|{names.head!}"
  return names.head!
private abbrev codes (k : Nat) : Array Nat := by
  run_tac do
    let n ← selectCursor "program"
    let id := mkIdent n; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident))
private abbrev before (k : Nat) : List Nat := by
  run_tac do
    let n ← selectCursor "before"
    let id := mkIdent n; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident 0))
private theorem lookup (k i : Nat) (hi : i < 63) :
    (codes k)[732+i]?=(instructions k)[i]? := by
  have length : (before k).length=795 := by
    unfold before
    run_tac do
      let n ← selectCursor "before"
      let id := mkIdent n
      evalTactic (← `(tactic| simp only [$id:ident,List.length_append]))
      let names := (← getEnv).constants.toList.map Prod.fst
      for j in List.range 12 do
        if !(← getGoals).isEmpty then
          let selected := names.filter fun n => n.toString.startsWith "_private.Cursor.Machine." &&
            n.toString.endsWith (".Cursor.before"++toString j)
          unless selected.length=1 do throwError "Ambiguous immutable private chunk"
          let n := selected[0]!
          logInfo m!"private-term|{n}"
          let cid := mkIdent n; let kv := mkIdent `k
          let len := if j=11 then 3 else 72
          evalTactic (← `(tactic| have hl : ($cid:ident $kv:ident 0).length=$(quote len) := rfl))
          evalTactic (← `(tactic| rw [hl]))
      if !(← getGoals).isEmpty then evalTactic (← `(tactic| rfl))
  have split : (before k).drop 732=instructions k++(before k).drop 795 := by
    unfold before
    run_tac do
      let n ← selectCursor "before"
      let id := mkIdent n
      evalTactic (← `(tactic| simp only [$id:ident,List.append_assoc]))
    rfl
  have len : (instructions k).length=63 := rfl
  unfold codes
  run_tac do
    let n ← selectCursor "program"
    let id := mkIdent n
    evalTactic (← `(tactic| simp only [$id:ident]))
  simp only [List.getElem?_toArray,List.append_assoc]
  change (before k++_)[732+i]?=(instructions k)[i]?
  rw [List.getElem?_append,if_pos (by omega)]
  rw [← List.getElem?_drop,split,List.getElem?_append,if_pos (by simpa only [len] using hi)]
private theorem small_mod (k i : Nat) (h : i ≤ 329) : i % Cursor.stateCount k=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
private theorem decode_row (k i code : Nat) (b : Option Bool)
    (lo : 64 ≤ i) (hi : i < 329) (h65 : i ≠ 65) (h66 : i ≠ 66) (h67 : i ≠ 67)
    (got : (codes k)[3*(i-64)+(match b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  simp only [UniformTM.step,Cursor.machine,Cursor.q,small_mod k i (by omega),
    small_mod k 39 (by omega),small_mod k 40 (by omega),Fin.mk.injEq,
    show i ≠ 39 by omega,show i ≠ 40 by omega,↓reduceIte]
  run_tac do
    let n ← selectCursor "decode"
    let id := mkIdent n
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

/-- Every arithmetic instruction is pinned to the unchanged Cursor.step, with fixed k. -/
theorem phase_row (k i code : Nat) (b : Option Bool) (lo : 308 ≤ i) (hi : i < 329)
    (got : (instructions k)[3*(i-308)+(match b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  apply decode_row k i code b (by omega) hi (by omega) (by omega) (by omega)
  cases b with
  | none =>
    change (codes k)[3*(i-64)]?=some code
    rw [show 3*(i-64)=732+3*(i-308) by omega,lookup k (3*(i-308)) (by omega)]
    exact got
  | some b =>
    cases b
    · change (codes k)[3*(i-64)+1]?=some code
      rw [show 3*(i-64)+1=732+(3*(i-308)+1) by omega,lookup k (3*(i-308)+1) (by omega)]
      exact got
    · change (codes k)[3*(i-64)+2]?=some code
      rw [show 3*(i-64)+2=732+(3*(i-308)+2) by omega,lookup k (3*(i-308)+2) (by omega)]
      exact got
end AllArityBitLength
