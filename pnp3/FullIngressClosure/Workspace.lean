import FullIngressClosure.Counters
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid","Grid"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mk","gridMk"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.rise","gridRise"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.mono","gridMono"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.blank","gridBlank"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.cells","gridCells"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.change_some","gridPut"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Unary","BankUnary"),
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","put","put"),
      ("FullIngressClosure.Paths","FullIngressClosure","Safe","Safe"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR","RouteR"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL","RouteL"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteR.execute","routeR"),
      ("FullIngressClosure.Paths","FullIngressClosure","RouteL.execute","routeL")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique occupied-workspace term {mod}/{key}: {found.map Prod.fst}"
private def setBank (T : Nat → Option Bool) (D : Nat → Nat) (j v : Nat) : Nat → Option Bool :=
  fun i=>if D j < i ∧ i < D (j+1) then some (decide (i-D j ≤ v)) else T i
private theorem bank_disjoint {D T} (grid : Grid D T) {a b i : Nat} (ha : a < 12) (hb : b < 12)
    (ne : a ≠ b) (lo : D a < i) (hi : i < D (a+1)) : ¬(D b < i ∧ i < D (b+1)) := by
  by_cases order : a < b
  · have d:=gridMono grid (a+1) b (by omega) (by omega)
    omega
  · have d:=gridMono grid (b+1) a (by omega) (by omega)
    omega
private theorem bank_unary (T : Nat → Option Bool) (D : Nat → Nat) (j v : Nat) :
    BankUnary D (setBank T D j v) j v := by
  intro i lo hi
  dsimp only [setBank]
  rw [if_pos ⟨lo,hi⟩]
private theorem bank_original {D T j v} (unary : BankUnary D T j v) : setBank T D j v=T := by
  funext i
  dsimp only [setBank]
  split_ifs with inside
  · exact (unary i inside.1 inside.2).symm
  · rfl
private theorem bank_idempotent (T : Nat → Option Bool) (D : Nat → Nat) (j v w : Nat) :
    setBank (setBank T D j v) D j w=setBank T D j w := by
  funext i
  dsimp only [setBank]
  split_ifs <;> rfl
private theorem bank_commute {D T} (grid : Grid D T) (a b v w : Nat)
    (ha : a < 12) (hb : b < 12) (ne : a ≠ b) :
    setBank (setBank T D a v) D b w=setBank (setBank T D b w) D a v := by
  funext i
  by_cases ia : D a < i ∧ i < D (a+1)
  · have ib : ¬(D b < i ∧ i < D (b+1)):=bank_disjoint grid ha hb ne ia.1 ia.2
    simp only [setBank,if_pos ia,if_neg ib]
  · by_cases ib : D b < i ∧ i < D (b+1)
    · simp only [setBank,if_neg ia,if_pos ib]
    · simp only [setBank,if_neg ia,if_neg ib]
private theorem bank_other {D T} (grid : Grid D T) (a b v w : Nat)
    (ha : a < 12) (hb : b < 12) (ne : a ≠ b) (unary : BankUnary D T a v) :
    BankUnary D (setBank T D b w) a v := by
  intro i lo hi
  dsimp only [setBank]
  rw [if_neg (bank_disjoint grid ha hb ne lo hi)]
  exact unary i lo hi
private theorem bank_grid {D T} (grid : Grid D T) (j v : Nat) (hj : j < 12) :
    Grid D (setBank T D j v) := by
  refine gridMk (gridRise grid) (gridMono grid) ?_ ?_
  · intro u hu
    have outside : ¬(D j < D u ∧ D u < D (j+1)) := by
      by_cases order : u ≤ j
      · have d:=gridMono grid u j order (by omega)
        omega
      · have d:=gridMono grid (j+1) u (by omega) hu
        omega
    dsimp only [setBank]
    rw [if_neg outside]
    exact gridBlank grid u hu
  · intro u i hu lo hi
    by_cases inside : D j < i ∧ i < D (j+1)
    · exact ⟨_,by dsimp only [setBank]; rw [if_pos inside]⟩
    · dsimp only [setBank]
      rw [if_neg inside]
      exact gridCells grid u i hu lo hi
private theorem bank_take {D T j v w} (_grid : Grid D T) (_hj : j < 12)
    (len : D (j+1)=D j+w+1) (unary : BankUnary D T j (v+1)) (room : v < w) :
    put T (D j+v+1) (some false)=setBank T D j v := by
  funext i
  dsimp only [put,setBank]
  by_cases hit : i=D j+v+1
  · subst i
    rw [if_pos rfl,if_pos (by omega),decide_eq_false (by omega)]
  · rw [if_neg hit]
    split_ifs with inside
    · rw [unary i inside.1 inside.2]
      congr 1
      exact decide_eq_decide.mpr (by omega)
    · rfl
private theorem bank_add {D T j v w} (_grid : Grid D T) (_hj : j < 12)
    (len : D (j+1)=D j+w+1) (unary : BankUnary D T j v) (room : v < w) :
    put T (D j+v+1) (some true)=setBank T D j (v+1) := by
  funext i
  dsimp only [put,setBank]
  by_cases hit : i=D j+v+1
  · subst i
    rw [if_pos rfl,if_pos (by omega),decide_eq_true (by omega)]
  · rw [if_neg hit]
    split_ifs with inside
    · rw [unary i inside.1 inside.2]
      congr 1
      exact decide_eq_decide.mpr (by omega)
    · rfl
end FullIngressClosure
