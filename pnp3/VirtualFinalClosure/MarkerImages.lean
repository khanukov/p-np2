import VirtualFinalClosure.Geometry
namespace VirtualFinalClosure.MarkerImages
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let found:=(← getEnv).constants.toList.filter fun (n,_)=>
    n.toString.startsWith "_private.SmallIngress.Runtime." && n.toString.endsWith ".SmallIngress.put"
  match found with
  | [(n,.defnInfo ci)]=>
    logInfo m!"private-term|{n}|kind=definition|type={ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit `put n::st.openDecls}
  | _=>throwError "Nonunique literal tape update"
/-- Proof indices describe the actual writes; no image is installed by the ROM. -/
private def unary (T : Nat → Option Bool) (base width value : Nat) : Nat → Option Bool :=
  fun i=>if base  <  i ∧ i  <  base+width+1 then some (decide (i ≤ base+value)) else T i
private def lifted (T : Nat → Option Bool) (S j : Nat) : Nat → Option Bool :=
  fun i=>if 0  <  j ∧ i=S-j then none else T i
private def image (T : Nat → Option Bool) (F r S j : Nat) : Nat → Option Bool :=
  unary (lifted T S j) (F+1) r (r-j)
private theorem unary_outside (T : Nat → Option Bool) (base width value h : Nat) (b : Option Bool)
    (outside : h ≤ base) :
    put (unary T base width value) h b=unary (put T h b) base width value := by
  funext i
  by_cases hit : i=h
  · subst i
    simp only [put,unary,ite_true,if_neg (by omega : ¬(base  <  h ∧ h  <  base+width+1))]
  · by_cases digit : base  <  i ∧ i  <  base+width+1
    · simp only [put,unary,if_neg hit,if_pos digit]
    · simp only [put,unary,if_neg hit,if_neg digit]
private theorem unary_decrement (T : Nat → Option Bool) (base width v : Nat)
    (positive : 0  <  v) (fits : v ≤ width) :
    put (unary T base width v) (base+v) (some false)=unary T base width (v-1) := by
  funext i
  by_cases hit : i=base+v
  · subst i
    have digit : base  <  base+v ∧ base+v  <  base+width+1 := by omega
    have below : ¬base+v ≤ base+(v-1) := by omega
    simp [put,unary,digit,below]
  · by_cases digit : base  <  i ∧ i  <  base+width+1
    · have same : (i ≤ base+v) ↔ (i ≤ base+(v-1)) := by omega
      simp only [put,unary,if_neg hit,if_pos digit,same]
    · simp only [put,unary,if_neg hit,if_neg digit]
private theorem lifted_step (T : Nat → Option Bool) (S j : Nat) (b : Bool)
    (room : j  <  S) (old : 0  <  j → T (S-j)=some b) :
    put (if j=0 then lifted T S j else put (lifted T S j) (S-j) (some b)) (S-j-1) none=
      lifted T S (j+1) := by
  funext i
  have address : S-j-1=S-(j+1) := by omega
  by_cases initial : j=0
  · subst j
    simp [lifted,put]
  · have positive : 0  <  j := by omega
    by_cases selected : i=S-j-1
    · have nextHit : 0  <  j+1 ∧ i=S-(j+1) := by omega
      simp only [if_neg initial,put,if_pos selected,lifted,if_pos nextHit]
    · by_cases previous : i=S-j
      · subst i
        change (if S-j=S-j-1 then none else
          (if j=0 then lifted T S j else put (lifted T S j) (S-j) (some b)) (S-j))=
          lifted T S (j+1) (S-j)
        rw [if_neg (by omega),if_neg initial]
        change (if S-j=S-j then some b else lifted T S j (S-j))=lifted T S (j+1) (S-j)
        rw [if_pos rfl]
        change some b=(if 0<j+1 ∧ S-j=S-(j+1) then none else T (S-j))
        rw [if_neg (by omega)]
        exact (old positive).symm
      · have oldMiss : ¬(0  <  j ∧ i=S-j) := by omega
        have nextMiss : ¬(0  <  j+1 ∧ i=S-(j+1)) := by omega
        simp only [if_neg initial,put,if_neg selected,if_neg previous,lifted,if_neg oldMiss,if_neg nextMiss]
private theorem marked_step (T : Nat → Option Bool) (F r S j : Nat) (b : Bool)
    (below : S ≤ F+1) (inside : j  <  r) (source : r  <  S)
    (old : 0  <  j → T (S-j)=some b) :
    let U:=put (image T F r S j) (F+1+(r-j)) (some false)
    put (if S-j=S then U else put U (S-j) (some b)) (S-j-1) none=image T F r S (j+1) := by
  intro U
  have positive : 0  <  r-j := by omega
  have decremented : U=unary (lifted T S j) (F+1) r (r-(j+1)) := by
    have eq:=unary_decrement (lifted T S j) (F+1) r (r-j) positive (by omega)
    rw [show r-j-1=r-(j+1) by omega] at eq
    exact eq
  rw [decremented]
  have swap (A B : Nat → Option Bool) :
      (if S-j=S then A else B)=(if j=0 then A else B) := by
    by_cases initial : j=0
    · rw [if_pos (by omega),if_pos initial]
    · rw [if_neg (by omega),if_neg initial]
  rw [swap]
  have moved :
      (if j=0 then unary (lifted T S j) (F+1) r (r-(j+1)) else
        put (unary (lifted T S j) (F+1) r (r-(j+1))) (S-j) (some b))=
      unary (if j=0 then lifted T S j else put (lifted T S j) (S-j) (some b)) (F+1) r (r-(j+1)) := by
    by_cases start : j=0
    · rw [if_pos start,if_pos start]
    · rw [if_neg start,if_neg start,unary_outside _ _ _ _ _ _ (by omega)]
  rw [moved,unary_outside _ _ _ _ _ _ (by omega),lifted_step T S j b (by omega) old]
  rfl
private theorem image_zero (T : Nat → Option Bool) (F r S : Nat)
    (digits : ∀ i,F+1  <  i → i  <  F+r+2 → T i=some true) : image T F r S 0=T := by
  funext i
  by_cases bank : F+1  <  i ∧ i  <  F+1+r+1
  · have hi:=digits i bank.1 (by omega)
    dsimp only [image,unary]
    rw [if_pos bank,hi]
    exact congrArg some (decide_eq_true (by omega))
  · dsimp only [image,unary,lifted]
    rw [if_neg bank]
    rfl
private theorem round_price (F S r j : Nat) (inside : j < r) (source : r < S) :
    2*(r-j)+3+(F-S+3)+(if S-j=S then 4 else 2*(S-(S-j))+5)+(F-S+3) ≤
      2*r+2*(F-S)+14 := by
  split_ifs <;> omega
private theorem total_price (R F S r : Nat) (fence : F=3*R+2) (rr : r ≤ R) (source : S ≤ F) :
    r*(2*r+2*(F-S)+14)+(F-S)+r+10 ≤ 64*(R+1)^2 := by
  have span : F-S ≤ 3*R+2 := by omega
  have price : 2*r+2*(F-S)+14 ≤ 8*R+18 := by omega
  have spent:=Nat.mul_le_mul rr price
  nlinarith only [spent,span,rr,Nat.zero_le R,Nat.zero_le (R^2)]
#print axioms unary_outside
#print axioms unary_decrement
#print axioms lifted_step
#print axioms marked_step
#print axioms image_zero
#print axioms round_price
#print axioms total_price
end VirtualFinalClosure.MarkerImages
