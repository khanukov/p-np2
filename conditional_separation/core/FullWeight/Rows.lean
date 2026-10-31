import FullWeight.Target
import Complexity.PrivateInterfaceLookupResolvedCursor
namespace FullWeight
open Pnp3.Complexity.Uniform.V1 Lean Elab Tactic
set_option maxRecDepth 10000
private def addCodes (k j : Nat) : List Nat := [
  (2981+738*k+99*j), (2984+738*k+99*j), (2987+738*k+99*j), (2997+738*k+99*j), (2994+738*k+99*j), (2987+738*k+99*j), (3007+738*k+99*j), (2991+738*k+99*j), (2994+738*k+99*j),
  (3016+738*k+99*j), (3000+738*k+99*j), (3003+738*k+99*j), (3070+738*k+99*j), (3073+738*k+99*j), (3076+738*k+99*j), (3024+738*k+99*j), (3027+738*k+99*j), (3030+738*k+99*j),
  (3034+738*k+99*j), (3027+738*k+99*j), (3030+738*k+99*j), (3042+738*k+99*j), (3045+738*k+99*j), (3048+738*k+99*j), (3052+738*k+99*j), (3045+738*k+99*j), (3048+738*k+99*j),
  (3060+738*k+99*j), (3063+738*k+99*j), (3066+738*k+99*j), (7183+837*k), (3063+738*k+99*j), (3066+738*k+99*j) ]
private abbrev codes (k : Nat) : Array Nat := by
  fromDonor "PowerDriver.Rows" "PowerDriver" "codes" => exact OLD k
private abbrev before (k : Nat) : List Nat := by
  fromDonor "PowerDriver.Rows" "PowerDriver" "before" => exact OLD k
private abbrev power (k j : Nat) : List Nat := by
  fromDonor "PowerDriver.Rows" "PowerDriver" "power" => exact OLD k j
private def select (s : String) : TacticM Name := do
  let n ← PartAPrivateCursor.select s
  logInfo m!"private-term|{n}"
  return n
private abbrev middle (k : Nat) : List Nat := by
  run_tac do
    let id:=mkIdent (← select "middle");let kv:=mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident 0))
private abbrev add (k j : Nat) : List Nat := by
  run_tac do
    let id:=mkIdent (← select "add");let kv:=mkIdent `k;let jv:=mkIdent `j
    evalTactic (← `(tactic| exact $id:ident $kv:ident $jv:ident))
private abbrev after (k : Nat) : List Nat := by
  run_tac do
    let id:=mkIdent (← select "after");let kv:=mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident 0))
private abbrev afterCodes (k : Nat) : List Nat := by
  run_tac do
    let kv:=mkIdent `k
    let mut ts : Array (TSyntax `term) := #[]
    for i in List.range 5 do
      let id:=mkIdent (← select ("after"++toString (i+0)))
      ts:=ts.push (← `($id:ident $kv:ident 0))
    let mut term:=ts[0]!
    for t in ts[1:] do term ← `($term:term ++ $t:term)
    evalTactic (← `(tactic| exact $term:term))
private abbrev afterRest (k : Nat) : List Nat := by
  run_tac do
    let kv:=mkIdent `k
    let mut ts : Array (TSyntax `term) := #[]
    for i in List.range 21 do
      let id:=mkIdent (← select ("after"++toString (i+5)))
      ts:=ts.push (← `($id:ident $kv:ident 0))
    let mut term:=ts[0]!
    for t in ts[1:] do term ← `($term:term ++ $t:term)
    evalTactic (← `(tactic| exact $term:term))
private theorem head_length (k : Nat) : (afterCodes k).length=360 := by
  unfold afterCodes
  simp only [List.length_append]
  run_tac do
    for i in List.range 5 do
      let id:=mkIdent (← select ("after"++toString i));let kv:=mkIdent `k
      evalTactic (← `(tactic| have hl : ($id:ident $kv:ident 0).length=72 := rfl;rw [hl]))
private theorem after_eq (k : Nat) : after k=afterCodes k++afterRest k := by
  unfold after afterCodes afterRest
  run_tac do
    let id:=mkIdent (← select "after")
    evalTactic (← `(tactic| simp only [$id:ident,List.append_assoc]))
private theorem program (k : Nat) : codes k=(before k++(List.range k).flatMap (power k)++middle k++(List.range k).flatMap (add k)++after k).toArray := by
  unfold codes before power middle add after
  run_tac do
    let id:=mkIdent (← select "program")
    evalTactic (← `(tactic| simp only [$id:ident,List.append_assoc]))
private theorem blen (k) : (before k).length=795 := by
  fromDonor "PowerDriver.Rows" "PowerDriver" "blen" => exact OLD k
private theorem powers (k v) : ((List.range v).flatMap (power k)).length=246*v := by
  fromDonor "PowerDriver.Rows" "PowerDriver" "flat_length" => exact OLD k v
private theorem mlen (k) : (middle k).length=3 := by
  unfold middle
  run_tac do
    let id:=mkIdent (← select "middle");let c:=mkIdent (← select "middle0")
    evalTactic (← `(tactic| simp only [$id:ident,$c:ident,List.length_append];rfl))
private theorem alen (k j) : (add k j).length=33 := by
  unfold add
  run_tac do
    let id:=mkIdent (← select "add");let c:=mkIdent (← select "add0")
    evalTactic (← `(tactic| simp only [$id:ident,$c:ident,List.length_append];rfl))
private theorem aeq (k j) : add k j=addCodes k j := by
  unfold add
  run_tac do
    let id:=mkIdent (← select "add");let c:=mkIdent (← select "add0")
    evalTactic (← `(tactic| simp only [$id:ident,$c:ident,List.append_nil]))
  rfl
private theorem adds (k v) : ((List.range v).flatMap (add k)).length=33*v := by
  induction v with
  | zero => rfl
  | succ v ih => simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,alen,ih];omega
private theorem add_get (k v j i) (hj : j<v) (hi : i<33) : ((List.range v).flatMap (add k))[33*j+i]?=(addCodes k j)[i]? := by
  induction v with
  | zero => omega
  | succ v ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    by_cases eq : j=v
    · subst j;rw [List.getElem?_append_right (by rw [adds];omega),adds,show 33*v+i-33*v=i by omega,aeq]
    · rw [List.getElem?_append_left (by rw [adds];omega)];exact ih (by omega)
private theorem head_eq (k : Nat) : (after k).take 360=afterCodes k := by
  rw [after_eq]
  exact List.take_left' (head_length k)
private theorem lookup_after (k i) (hi : i<360) : (codes k)[798+279*k+i]?=(afterCodes k)[i]? := by
  rw [program,List.append_assoc,List.append_assoc,List.append_assoc,List.getElem?_toArray,
    List.getElem?_append_right (by rw [blen];omega),blen,
    List.getElem?_append_right (by rw [powers];omega),powers,
    List.getElem?_append_right (by rw [mlen];omega),mlen,
    List.getElem?_append_right (by rw [adds];omega),adds]
  rw [show 798+279*k+i-795-246*k-3-33*k=i by omega]
  rw [← List.getElem?_take_of_lt hi,head_eq]
private theorem lookup_add (k j i) (hj : j<k) (hi : i<33) : (codes k)[798+246*k+33*j+i]?=(addCodes k j)[i]? := by
  rw [program,List.append_assoc,List.append_assoc,List.append_assoc,List.getElem?_toArray,List.getElem?_append_right (by rw [blen];omega),blen,List.getElem?_append_right (by rw [powers];omega),powers,List.getElem?_append_right (by rw [mlen];omega),mlen]
  rw [show 798+246*k+33*j+i-795-246*k-3=33*j+i by omega,List.getElem?_append_left (by rw [adds];omega),add_get k k j i hj hi]
end FullWeight
