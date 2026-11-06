import CappedWeight.Target
import Complexity.PrivateInterfaceLookupResolvedCursor
namespace CappedWeight
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
set_option maxRecDepth 10000
/-- Proof-side copy of exactly the first power block; no runtime controller. -/
def instructions (k : Nat) : List Nat := [
  (2972), (2975), (2978), (2979), (2982), (2978), (3430), 364, (2991),
  (2998), (2991), (2994), (3006), (3009), (3012), (3016), (3009), (3012),
  (3024), (3027), (3030), (3034), (3027), (3030), (3042), (3045), (3048),
  (3052), (3045), (3048), (3060), (3063), (3066), 361, (3072), 367,
  (3069), 364, (3084), (3088), 364, (3084), (3096), (3099), (3102),
  (3350), (3113), (3102), (3115), (3110), (3113), (3125), (3128), (3131),
  (3125), (3137), (3131), (3143), (3146), (3149), (3151), (3146), (3149),
  (3161), (3164), (3167), (3169), (3164), (3167), (3179), (3182), (3185),
  (3187), (3182), (3185), (3197), (3200), (3203), (3205), (3200), (3203),
  (3215), (3218), (3221), (3231), (3228), (3221), (3241), (3225), (3228),
  (3628), (3234), (3237), (3249), (3252), (3255), (3259), (3252), (3255),
  (3267), (3270), (3273), (3277), (3270), (3273), (3285), (3288), (3291),
  (3295), (3288), (3291), (3303), (3306), (3309), (3313), (3306), (3309),
  (3321), (3324), (3327), 361, (3333), 367, (3330), 364, (3345),
  (3088), 364, (3345), (3358), (3353), (3353), (3368), (3371), (3374),
  (3368), (3380), (3374), (3386), (3389), (3392), (3394), (3389), (3392),
  (3404), (3407), (3410), (3412), (3407), (3410), (3422), (3425), (3428),
  (2962), (3425), (3428), (3440), (3443), (3446), (3448), (3443), (3446),
  (3458), (3461), (3464), (3465), (3468), (3464), (3610), 364, (3477),
  (3484), (3477), (3480), (3492), (3495), (3498), (3502), (3495), (3498),
  (3512), (3515), (3518), (3528), (3525), (3518), (3538), (3522), (3525),
  (3556), (3531), (3534), (3548), (3551), (3554), (3448), (3551), (3554),
  (3564), (3567), (3570), (3574), (3567), (3570), (3582), (3585), (3588),
  (3592), (3585), (3588), (3600), (3603), (3606), (7183+837*k), (3603), (3606),
  (3618), (3621), (3624), (3700), (3621), (3624), (3636), (3639), (3642),
  (3646), (3639), (3642), (3654), (3657), (3660), (3664), (3657), (3660),
  (3672), (3675), (3678), (3682), (3675), (3678), (3690), (3693), (3696),
  (7183+837*k), (3693), (3696)
]
private def selectCursor (suffix : String) : TacticM Name := do
  let n ← PartAPrivateCursor.select suffix
  logInfo m!"private-term|{n}"
  return n
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
private abbrev power (k : Nat) : List Nat := by
  run_tac do
    let n ← selectCursor "power"; let id := mkIdent n; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident 0))
private abbrev allPower (k j : Nat) : List Nat := by
  run_tac do
    let n ← selectCursor "power"; let id:=mkIdent n; let kv:=mkIdent `k; let jv:=mkIdent `j
    evalTactic (← `(tactic| exact $id:ident $kv:ident $jv:ident))
private abbrev suffix (k : Nat) : List Nat := by
  run_tac do
    let md ← selectCursor "middle"; let ad ← selectCursor "add"; let af ← selectCursor "after"
    let mi:=mkIdent md; let ai:=mkIdent ad; let fi:=mkIdent af; let kv:=mkIdent `k
    evalTactic (← `(tactic| exact ((List.range ($kv:ident-1)).map Nat.succ).flatMap (allPower $kv:ident) ++
      $mi:ident $kv:ident 0 ++ (List.range $kv:ident).flatMap ($ai:ident $kv:ident) ++ $fi:ident $kv:ident 0))
private theorem blen (k : Nat) : (before k).length=795 := by
    unfold before
    run_tac do
      let n ← selectCursor "before"
      let id := mkIdent n
      evalTactic (← `(tactic| simp only [$id:ident,List.length_append]))
      for j in List.range 12 do
        if !(← getGoals).isEmpty then
          let n ← PartAPrivateCursor.select ("before"++toString j)
          logInfo m!"private-term|{n}"
          let cid := mkIdent n; let kv := mkIdent `k
          let len := if j=11 then 3 else 72
          evalTactic (← `(tactic| have hl : ($cid:ident $kv:ident 0).length=$(quote len) := rfl))
          evalTactic (← `(tactic| rw [hl]))
      if !(← getGoals).isEmpty then evalTactic (← `(tactic| rfl))
private theorem peq (k : Nat) : power k=instructions k := by
    unfold power
    run_tac do
      let n ← selectCursor "power"; let id := mkIdent n
      evalTactic (← `(tactic| simp only [$id:ident,List.append_assoc]))
    rfl
private theorem program_eq (k : Nat) (hk : 0<k) :
    codes k=(before k++power k++suffix k).toArray := by
  obtain ⟨j,rfl⟩ : ∃ j, k=j+1 := ⟨k-1,by omega⟩
  unfold codes
  run_tac do
    let n ← selectCursor "program"; let id:=mkIdent n
    evalTactic (← `(tactic| simp only [$id:ident,List.range_succ_eq_map,List.flatMap_cons,List.append_assoc]))
  rfl
private theorem getBlock (xs ys zs : List Nat) (i : Nat) (hi : i<ys.length) :
    ((xs++ys++zs).toArray)[xs.length+i]?=ys[i]? := by
  rw [List.append_assoc,List.getElem?_toArray,List.getElem?_append_right (by omega),show xs.length+i-xs.length=i by omega,
    List.getElem?_append_left hi]
private theorem lookup (k i : Nat) (hk : 0<k) (hi : i<246) :
    (codes k)[795+i]?=(instructions k)[i]? := by
  rw [program_eq k hk,← blen k]
  have h : i<(power k).length := by rw [peq]; exact hi
  exact (getBlock (before k) (power k) (suffix k) i h).trans (congrArg (fun xs : List Nat => xs[i]?) (peq k))
private theorem small_mod (k i : Nat) (h : i ≤ 798+93*k) : i % Cursor.stateCount k=i :=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
private theorem decode_row (k i code : Nat) (b : Option Bool)
    (lo : 64  ≤  i) (hi : i  ≤  798+93*k) (h65 : i ≠ 65) (h66 : i ≠ 66) (h67 : i ≠ 67)
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

theorem phase_row (k i code : Nat) (b : Option Bool) (hk : 0<k)
    (lo : 329 ≤ i) (hi : i<411)
    (got : (instructions k)[3*(i-329)+(match (generalizing := false) b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  apply decode_row k i code b (by omega) (by omega) (by omega) (by omega) (by omega)
  cases b with
  | none =>
    change (codes k)[3*(i-64)]?=some code
    rw [show 3*(i-64)=795+3*(i-329) by omega,lookup k (3*(i-329)) hk (by omega)]
    exact got
  | some b =>
    cases b
    · change (codes k)[3*(i-64)+1]?=some code
      rw [show 3*(i-64)+1=795+(3*(i-329)+1) by omega,lookup k (3*(i-329)+1) hk (by omega)]
      exact got
    · change (codes k)[3*(i-64)+2]?=some code
      rw [show 3*(i-64)+2=795+(3*(i-329)+2) by omega,lookup k (3*(i-329)+2) hk (by omega)]
      exact got
end CappedWeight
