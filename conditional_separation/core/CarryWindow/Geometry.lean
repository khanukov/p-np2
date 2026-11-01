import CarryWindow.Transport
import Complexity.PrivateInterfaceLookupResolvedCarryWindow
namespace CarryWindow
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let rows := [("VirtualLeaf.Body","VirtualLeaf","Trace","Tr"),
      ("VirtualLeaf.Body","VirtualLeaf","Trace.run","trRun"),
      ("VirtualLeaf.Body","VirtualLeaf","Trace.bound","trBound"),
      ("VirtualLeaf.Body","VirtualLeaf","nil","trNil"),
      ("VirtualLeaf.Body","VirtualLeaf","single","trSingle"),
      ("VirtualLeaf.Body","VirtualLeaf","append","trAppend"),
      ("VirtualLeaf.Body","VirtualLeaf","sweepL","trSweepL"),
      ("VirtualLeaf.Body","VirtualLeaf","sweepR","trSweepR"),
      ("CarryWindow.Rows","CarryWindow","native_row","native_row"),
      ("CarryWindow.Machine","CarryWindow","native","native")]
  let validated ← ofExcept (PartAPrivateCarryWindow.batch (← getEnv) (rows.map fun (o,ns,key,_) => (PartAPrivateCarryWindow.key o, PartAPrivateCarryWindow.key (ns++"."++key))))
  for ((mod,ns,s,key),target) in rows.zip validated do
    let _ := (mod,ns,s)
    let names := [target]
    logInfo m!"private-term|{names.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous key) names.head! :: st.openDecls}
private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i=h then b else T i
private def dest (h : Nat) : Move → Nat | .left => h-1 | .stay => h | .right => h+1
private def C {M : UniformTM} {N B : Nat} (s : Fin M.stateCount) (h : Nat) (T : Nat → Option Bool)
    (fit : h < tapeLength N B) : Config M.stateCount N B := ⟨s,⟨h,fit⟩,fun i => T i.val⟩
private theorem hop {M : UniformTM} {N B lo hi : Nat} (fit : hi < tapeLength N B)
    (s d : Fin M.stateCount) (h h' : Nat) (T : Nat → Option Bool) (w : Option Bool) (mv : Move)
    (hb : lo ≤ h ∧ h ≤ hi) (ha : lo ≤ h' ∧ h' ≤ hi)
    (row : M.step s (T h)=(d,w,mv)) (hm : dest h mv=h') :
    Tr (N:=N) (B:=B) M lo hi 1 (C s h T (by omega)) (C d h' (put T h w) (by omega)) := by
  apply trSingle _ _ hb ha
  apply Config.ext_parts
  · exact congrArg Prod.fst row
  · apply Fin.ext
    change (moveHead _ (M.step s (T h)).2.2).val=h'
    rw [row]
    cases mv with
    | left => simpa only [moveHead,dest,C] using hm
    | stay => simpa only [moveHead,dest,C] using hm
    | right =>
      have hr : h+1 < tapeLength N B := by dsimp only [dest] at hm; omega
      simpa only [moveHead,dif_pos hr,dest,C] using hm
  · funext i
    dsimp only [UniformTM.stepConfig,C]
    rw [row]
    simp only [put,Fin.ext_iff]
private theorem keep {M : UniformTM} {N B lo hi : Nat} (fit : hi < tapeLength N B)
    (s d : Fin M.stateCount) (h h' : Nat) (T : Nat → Option Bool) (mv : Move)
    (hb : lo ≤ h ∧ h ≤ hi) (ha : lo ≤ h' ∧ h' ≤ hi)
    (row : M.step s (T h)=(d,T h,mv)) (hm : dest h mv=h') :
    Tr (N:=N) (B:=B) M lo hi 1 (C s h T (by omega)) (C d h' T (by omega)) := by
  have one:=hop fit s d h h' T (T h) mv hb ha row hm
  have eq : put T h (T h)=T := by funext i; by_cases eq : i=h <;> simp [put,eq]
  simpa only [eq] using one
private def D (F r n : Nat) : Nat → Nat
  | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
  | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
private def A (T : Nat → Option Bool) (F r n W a v : Nat) : Nat → Option Bool :=
  Target.image T F r n a 0 v W 0
private structure Banks (T : Nat → Option Bool) (F r n : Nat) : Prop where
  blank : ∀ j, j ≤ 6 → T (D F r n j)=none
  bank1 : ∀ i, D F r n 1 < i → i < D F r n 2 → ∃ b, T i=some b
private def value (W a v j : Nat) := if j=0 then a else if j=3 then v else if j=4 then W else 0
private theorem atD {T F r n} (fr : Banks T F r n) (W a v j : Nat) (hj : j ≤ 6) :
    A T F r n W a v (D F r n j)=none := by
  have eq : A T F r n W a v (D F r n j)=T (D F r n j) := by
    interval_cases j <;> dsimp only [A,Target.image,D]
    all_goals repeat' first | rfl | (exfalso; omega) | split
  rw [eq]; exact fr.blank j hj
private theorem atBank (T : Nat → Option Bool) (F r n W a v j i : Nat) (hj : j ≤ 5)
    (not1 : j ≠ 1) (lo : D F r n j < i) (hi : i < D F r n (j+1)) :
    A T F r n W a v i=some (decide (i ≤ D F r n j+value W a v j)) := by
  interval_cases j <;> try contradiction
  all_goals dsimp only [D] at lo hi
  all_goals dsimp only [A,Target.image,D,value]
  all_goals split_ifs <;> first | rfl | (exfalso; omega)
private theorem occupied {T F r n} (fr : Banks T F r n) (W a v j i : Nat) (hj : j ≤ 5)
    (lo : D F r n j < i) (hi : i < D F r n (j+1)) : ∃ b, A T F r n W a v i=some b := by
  by_cases one : j=1
  · subst j
    have eq : A T F r n W a v i=T i := by
      dsimp only [D] at lo hi
      dsimp only [A,Target.image]
      repeat' rw [if_neg (by omega)]
    rw [eq]; exact fr.bank1 i lo hi
  · exact ⟨_,atBank T F r n W a v j i hj one lo hi⟩
private theorem set0 (T : Nat → Option Bool) (F r n W a v : Nat) (ar : a < r) :
    put (A T F r n W a v) (D F r n 0+a+1) (some true)=A T F r n W (a+1) v := by
  funext i
  dsimp only [A,Target.image,put,D]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm | exact decide_eq_decide.mpr (by omega))
private theorem take0 (T : Nat → Option Bool) (F r n W a v : Nat) (ar : a < r) :
    put (A T F r n W (a+1) v) (D F r n 0+a+1) (some false)=A T F r n W a v := by
  funext i
  dsimp only [A,Target.image,put,D]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm | exact decide_eq_decide.mpr (by omega))
private theorem take3 (T : Nat → Option Bool) (F r n W a v : Nat) (vr : v < r) :
    put (A T F r n W a (v+1)) (D F r n 3+v+1) (some false)=A T F r n W a v := by
  funext i
  dsimp only [A,Target.image,put,D]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; first | exact (decide_eq_true (by omega)).symm | exact (decide_eq_false (by omega)).symm | exact decide_eq_decide.mpr (by omega))
private theorem clear0 {k N B F r n : Nat} (T : Nat → Option Bool) (W v : Nat)
    (fit : D F r n 6 < tapeLength N B) (a : Nat) (ar : a ≤ r) :
    Tr (N:=N) (B:=B) (machine k) (D F r n 0) (D F r n 6) a
      (C (extra k 1) (D F r n 0+a) (A T F r n W a v) (by dsimp only [D] at fit ⊢; omega))
      (C (extra k 1) (D F r n 0) (A T F r n W 0 v) (by dsimp only [D] at fit ⊢; omega)) := by
  induction a with
  | zero => exact trNil _ ⟨le_rfl,by dsimp only [C,D]; omega⟩
  | succ a ih =>
    have cell : A T F r n W (a+1) v (D F r n 0+a+1)=some true := by
      rw [atBank T F r n W (a+1) v 0 _ (by decide) (by decide)
        (by dsimp only [D]; omega) (by dsimp only [D]; omega)]
      simp only [D,value,ite_true]
      congr 1
      exact decide_eq_true (by omega)
    have one:=hop (M:=machine k) (N:=N) (B:=B) (lo:=D F r n 0) fit (extra k 1) (extra k 1)
      (D F r n 0+(a+1)) (D F r n 0+a) (A T F r n W (a+1) v) (some false) .left
      ⟨by omega,by dsimp only [D]; omega⟩ ⟨by omega,by dsimp only [D]; omega⟩
      (by rw [show D F r n 0+(a+1)=D F r n 0+a+1 by omega,cell,native_row]; rfl)
      (by dsimp only [dest]; omega)
    have tapeEq : put (A T F r n W (a+1) v) (D F r n 0+(a+1)) (some false)=A T F r n W a v := by
      simpa only [Nat.add_assoc] using take0 T F r n W a v (by omega)
    rw [tapeEq] at one
    simpa only [Nat.add_comm 1 a] using trAppend one (ih (by omega))
end CarryWindow
