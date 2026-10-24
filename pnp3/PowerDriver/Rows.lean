import PowerDriver.Target
namespace PowerDriver
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
set_option maxRecDepth 10000
private def instructions (k j : Nat) : List Nat := [
  (2972+738*j), (2975+738*j), (2978+738*j), (2979+738*j), (2982+738*j), (2978+738*j), (3430+738*j), 364, (2991+738*j),
  (2998+738*j), (2991+738*j), (2994+738*j), (3006+738*j), (3009+738*j), (3012+738*j), (3016+738*j), (3009+738*j), (3012+738*j),
  (3024+738*j), (3027+738*j), (3030+738*j), (3034+738*j), (3027+738*j), (3030+738*j), (3042+738*j), (3045+738*j), (3048+738*j),
  (3052+738*j), (3045+738*j), (3048+738*j), (3060+738*j), (3063+738*j), (3066+738*j), 361, (3072+738*j), 367,
  (3069+738*j), 364, (3084+738*j), (3088+738*j), 364, (3084+738*j), (3096+738*j), (3099+738*j), (3102+738*j),
  (3350+738*j), (3113+738*j), (3102+738*j), (3115+738*j), (3110+738*j), (3113+738*j), (3125+738*j), (3128+738*j), (3131+738*j),
  (3125+738*j), (3137+738*j), (3131+738*j), (3143+738*j), (3146+738*j), (3149+738*j), (3151+738*j), (3146+738*j), (3149+738*j),
  (3161+738*j), (3164+738*j), (3167+738*j), (3169+738*j), (3164+738*j), (3167+738*j), (3179+738*j), (3182+738*j), (3185+738*j),
  (3187+738*j), (3182+738*j), (3185+738*j), (3197+738*j), (3200+738*j), (3203+738*j), (3205+738*j), (3200+738*j), (3203+738*j),
  (3215+738*j), (3218+738*j), (3221+738*j), (3231+738*j), (3228+738*j), (3221+738*j), (3241+738*j), (3225+738*j), (3228+738*j),
  (3628+738*j), (3234+738*j), (3237+738*j), (3249+738*j), (3252+738*j), (3255+738*j), (3259+738*j), (3252+738*j), (3255+738*j),
  (3267+738*j), (3270+738*j), (3273+738*j), (3277+738*j), (3270+738*j), (3273+738*j), (3285+738*j), (3288+738*j), (3291+738*j),
  (3295+738*j), (3288+738*j), (3291+738*j), (3303+738*j), (3306+738*j), (3309+738*j), (3313+738*j), (3306+738*j), (3309+738*j),
  (3321+738*j), (3324+738*j), (3327+738*j), 361, (3333+738*j), 367, (3330+738*j), 364, (3345+738*j),
  (3088+738*j), 364, (3345+738*j), (3358+738*j), (3353+738*j), (3353+738*j), (3368+738*j), (3371+738*j), (3374+738*j),
  (3368+738*j), (3380+738*j), (3374+738*j), (3386+738*j), (3389+738*j), (3392+738*j), (3394+738*j), (3389+738*j), (3392+738*j),
  (3404+738*j), (3407+738*j), (3410+738*j), (3412+738*j), (3407+738*j), (3410+738*j), (3422+738*j), (3425+738*j), (3428+738*j),
  (2962+738*j), (3425+738*j), (3428+738*j), (3440+738*j), (3443+738*j), (3446+738*j), (3448+738*j), (3443+738*j), (3446+738*j),
  (3458+738*j), (3461+738*j), (3464+738*j), (3465+738*j), (3468+738*j), (3464+738*j), (3610+738*j), 364, (3477+738*j),
  (3484+738*j), (3477+738*j), (3480+738*j), (3492+738*j), (3495+738*j), (3498+738*j), (3502+738*j), (3495+738*j), (3498+738*j),
  (3512+738*j), (3515+738*j), (3518+738*j), (3528+738*j), (3525+738*j), (3518+738*j), (3538+738*j), (3522+738*j), (3525+738*j),
  (3556+738*j), (3531+738*j), (3534+738*j), (3548+738*j), (3551+738*j), (3554+738*j), (3448+738*j), (3551+738*j), (3554+738*j),
  (3564+738*j), (3567+738*j), (3570+738*j), (3574+738*j), (3567+738*j), (3570+738*j), (3582+738*j), (3585+738*j), (3588+738*j),
  (3592+738*j), (3585+738*j), (3588+738*j), (3600+738*j), (3603+738*j), (3606+738*j), (7183+837*k), (3603+738*j), (3606+738*j),
  (3618+738*j), (3621+738*j), (3624+738*j), (3700+738*j), (3621+738*j), (3624+738*j), (3636+738*j), (3639+738*j), (3642+738*j),
  (3646+738*j), (3639+738*j), (3642+738*j), (3654+738*j), (3657+738*j), (3660+738*j), (3664+738*j), (3657+738*j), (3660+738*j),
  (3672+738*j), (3675+738*j), (3678+738*j), (3682+738*j), (3675+738*j), (3678+738*j), (3690+738*j), (3693+738*j), (3696+738*j),
  (7183+837*k), (3693+738*j), (3696+738*j)
]
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
private abbrev power (k j : Nat) : List Nat := by
  run_tac do
    let name ← selectCursor "power"; let id:=mkIdent name; let kv:=mkIdent `k; let jv:=mkIdent `j
    evalTactic (← `(tactic| exact $id:ident $kv:ident $jv:ident))
private abbrev tail (k : Nat) : List Nat := by
  run_tac do
    let md ← selectCursor "middle"; let ad ← selectCursor "add"; let af ← selectCursor "after"
    let mi:=mkIdent md; let ai:=mkIdent ad; let fi:=mkIdent af; let kv:=mkIdent `k
    evalTactic (← `(tactic| exact $mi:ident $kv:ident 0 ++ (List.range $kv:ident).flatMap ($ai:ident $kv:ident) ++ $fi:ident $kv:ident 0))
private theorem blen (k : Nat) : (before k).length=795 := by
  fromDonor "CappedWeight.Rows" "CappedWeight" "blen" => exact OLD k
private theorem plen (k j : Nat) : (power k j).length=246 := by
  unfold power
  run_tac do
    let name ← selectCursor "power"; let id:=mkIdent name
    evalTactic (← `(tactic| simp only [$id:ident,List.length_append]))
    for i in List.range 4 do
      let name ← selectCursor ("power"++toString i); let id:=mkIdent name
      let v:=quote (if i=3 then 30 else 72); let kv:=mkIdent `k; let jv:=mkIdent `j
      evalTactic (← `(tactic| have hl : ($id:ident $kv:ident $jv:ident).length=$v:term := rfl; rw [hl]))
    if !(← getGoals).isEmpty then evalTactic (← `(tactic| rfl))
private theorem peq (k j : Nat) : power k j=instructions k j := by
  unfold power
  run_tac do
    let name ← selectCursor "power"; let id:=mkIdent name
    evalTactic (← `(tactic| simp only [$id:ident,List.append_assoc]))
  rfl
private theorem program_eq (k : Nat) : codes k=(before k++(List.range k).flatMap (power k)++tail k).toArray := by
  unfold codes before power tail
  run_tac do
    let name ← selectCursor "program"; let id:=mkIdent name
    evalTactic (← `(tactic| simp only [$id:ident,List.append_assoc]))
private theorem flat_length (k v : Nat) : ((List.range v).flatMap (power k)).length=246*v := by
  induction v with
  | zero => rfl
  | succ v ih => simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,plen,ih]; omega
private theorem get_flat (k v j i : Nat) (hj : j<v) (hi : i<246) :
    ((List.range v).flatMap (power k))[246*j+i]?=(power k j)[i]? := by
  induction v with
  | zero => omega
  | succ v ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    by_cases eq : j=v
    · subst j
      rw [List.getElem?_append_right (by rw [flat_length]; omega),flat_length,show 246*v+i-246*v=i by omega]
    · rw [List.getElem?_append_left (by rw [flat_length]; omega)]
      exact ih (by omega)
private theorem lookup (k j i : Nat) (hj : j<k) (hi : i<246) :
    (codes k)[795+246*j+i]?=(instructions k j)[i]? := by
  rw [program_eq,List.append_assoc,List.getElem?_toArray,List.getElem?_append_right (by rw [blen]; omega),blen,
    show 795+246*j+i-795=246*j+i by omega,List.getElem?_append_left (by rw [flat_length]; omega),get_flat k k j i hj hi,peq]
private theorem small_mod (k i : Nat) (h : i ≤ 798+93*k) : i % Cursor.stateCount k=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
private theorem decode_row (k i code : Nat) (b : Option Bool)
    (lo : 64  ≤  i) (hi : i  ≤  798+93*k) (h65 : i ≠ 65) (h66 : i ≠ 66) (h67 : i ≠ 67)
    (got : (codes k)[3*(i-64)+(match b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  fromDonor "CappedWeight.Rows" "CappedWeight" "decode_row" => exact OLD k i code b lo hi h65 h66 h67 got

private theorem phase_row (k j i code : Nat) (b : Option Bool) (hj : j<k)
    (lo : 329+82*j ≤ i) (hi : i<411+82*j)
    (got : (instructions k j)[3*(i-(329+82*j))+(match (generalizing := false) b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  apply decode_row k i code b (by omega) (by omega) (by omega) (by omega) (by omega)
  cases b with
  | none =>
    change (codes k)[3*(i-64)]?=some code
    rw [show 3*(i-64)=795+246*j+3*(i-(329+82*j)) by omega,lookup k j (3*(i-(329+82*j))) hj (by omega)]
    exact got
  | some b =>
    cases b
    · change (codes k)[3*(i-64)+1]?=some code
      rw [show 3*(i-64)+1=795+246*j+(3*(i-(329+82*j))+1) by omega,lookup k j (3*(i-(329+82*j))+1) hj (by omega)]
      exact got
    · change (codes k)[3*(i-64)+2]?=some code
      rw [show 3*(i-64)+2=795+246*j+(3*(i-(329+82*j))+2) by omega,lookup k j (3*(i-(329+82*j))+2) hj (by omega)]
      exact got
end PowerDriver
