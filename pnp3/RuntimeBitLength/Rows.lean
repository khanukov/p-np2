import RuntimeBitLength.Target
namespace RuntimeBitLength
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
set_option maxRecDepth 10000
/-- Proof-side transcription of q201..q249 exported instruction codes; never executes an input. -/
def instructions : List Nat := [
  1819, 1822, 1825, 1827, 1830, 1833, 361, 1839, 367, 1836, 364, 1851, 1855, 364, 1851, 1863, 1866, 1869,
  1873, 1866, 1869, 1882, 1885, 1888, 1892, 1895, 1898, 1899, 1895, 1940, 1909, 1902, 1905, 2773, 2776, 2779,
  1928, 1931, 1934, 2115, 1931, 1940, 2115, 2118, 1947, 1954, 1947, 1950, 1964, 1967, 1970, 1972, 1967, 1970,
  1982, 1985, 1988, 1982, 1994, 1988, 2000, 2003, 2006, 2008, 2003, 2006, 2018, 2021, 2024, 2034, 2031, 2024,
  2044, 2028, 2031, 2251, 2037, 2040, 2052, 2055, 2058, 2062, 2055, 2058, 2070, 2073, 2076, 361, 2082, 367,
  2079, 364, 2094, 2098, 364, 2094, 2106, 2109, 2112, 1918, 2109, 2112, 2125, 2118, 2121, 2135, 2138, 2141,
  2143, 2138, 2141, 2153, 2156, 2159, 2153, 2165, 2159, 2171, 2174, 2177, 2179, 2174, 2177, 2189, 2192, 2195,
  2197, 2192, 2195, 2207, 2210, 2213, 2223, 2220, 2213, 2233, 2217, 2220, 2251, 2226, 2229, 2241, 2244, 2247,
  2287, 2244, 2247
 ]
private abbrev codes (k : Nat) : Array Nat := by
  run_tac do
    let candidateNames := (← getEnv).constants.toList.filter fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.program"
    unless candidateNames.length=1 do throwError "Ambiguous immutable private term"
    let n := candidateNames[0]!.1
    logInfo m!"private-term|{n}"
    let id := mkIdent n; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident))
private abbrev before (k : Nat) : List Nat := by
  run_tac do
    let candidateNames := (← getEnv).constants.toList.filter fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.before"
    unless candidateNames.length=1 do throwError "Ambiguous immutable private term"
    let n := candidateNames[0]!.1
    logInfo m!"private-term|{n}"
    let id := mkIdent n; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident 0))
private theorem lookup (k i : Nat) (hi : i < 147) :
    (codes k)[411+i]?=instructions[i]? := by
  have length : (before k).length=795 := by
    unfold before
    run_tac do
      let candidateNames := (← getEnv).constants.toList.filter fun (n,_) =>
        n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.before"
      unless candidateNames.length=1 do throwError "Ambiguous immutable private term"
      let n := candidateNames[0]!.1
      logInfo m!"private-term|{n}"
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
  have split : (before k).drop 411=instructions++(before k).drop 558 := by
    unfold before
    run_tac do
      let candidateNames := (← getEnv).constants.toList.filter fun (n,_) =>
        n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.before"
      unless candidateNames.length=1 do throwError "Ambiguous immutable private term"
      let n := candidateNames[0]!.1
      logInfo m!"private-term|{n}"
      let id := mkIdent n
      evalTactic (← `(tactic| simp only [$id:ident,List.append_assoc]))
    rfl
  have len : instructions.length=147 := rfl
  unfold codes
  run_tac do
    let candidateNames := (← getEnv).constants.toList.filter fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.program"
    unless candidateNames.length=1 do throwError "Ambiguous immutable private term"
    let n := candidateNames[0]!.1
    logInfo m!"private-term|{n}"
    let id := mkIdent n
    evalTactic (← `(tactic| simp only [$id:ident]))
  simp only [List.getElem?_toArray,List.append_assoc]
  change (before k++_)[411+i]?=instructions[i]?
  rw [List.getElem?_append,if_pos (by omega)]
  rw [← List.getElem?_drop,split,List.getElem?_append,if_pos (by simpa only [len] using hi)]
private theorem small_mod (k i : Nat) (h : i ≤ 329) : i % Cursor.stateCount k=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
private theorem decode_row (k i code : Nat) (b : Option Bool)
    (lo : 64 ≤ i) (hi : i < 250) (h65 : i ≠ 65) (h66 : i ≠ 66) (h67 : i ≠ 67)
    (got : (codes k)[3*(i-64)+(match b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  simp only [UniformTM.step,Cursor.machine,Cursor.q,small_mod k i (by omega),
    small_mod k 39 (by omega),small_mod k 40 (by omega),Fin.mk.injEq,
    show i ≠ 39 by omega,show i ≠ 40 by omega,↓reduceIte]
  run_tac do
    let candidateNames := (← getEnv).constants.toList.filter fun (n,_) =>
      n.toString.startsWith "_private.Cursor.Machine." && n.toString.endsWith ".Cursor.decode"
    unless candidateNames.length=1 do throwError "Ambiguous immutable private term"
    let n := candidateNames[0]!.1
    logInfo m!"private-term|{n}"
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
theorem phase_row (k i code : Nat) (b : Option Bool) (lo : 201 ≤ i) (hi : i < 250)
    (got : instructions[3*(i-201)+(match b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  apply decode_row k i code b (by omega) hi (by omega) (by omega) (by omega)
  cases b with
  | none =>
    change (codes k)[3*(i-64)]?=some code
    rw [show 3*(i-64)=411+3*(i-201) by omega,lookup k (3*(i-201)) (by omega)]
    exact got
  | some b =>
    cases b
    · change (codes k)[3*(i-64)+1]?=some code
      rw [show 3*(i-64)+1=411+(3*(i-201)+1) by omega,lookup k (3*(i-201)+1) (by omega)]
      exact got
    · change (codes k)[3*(i-64)+2]?=some code
      rw [show 3*(i-64)+2=411+(3*(i-201)+2) by omega,lookup k (3*(i-201)+2) (by omega)]
      exact got
end RuntimeBitLength
