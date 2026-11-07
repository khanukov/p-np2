import FullBodyClosure.Buffer
namespace FullBodyClosure
private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i=>if i=h then b else T i
/-- Ghost list is only a specification of actually occupied flag/digit pairs. -/
private def place (T : Nat → Option Bool) (a : Nat) : List Bool → Nat → Option Bool
  | [] => T
  | b::bs => place (put (put T a (some true)) (a+1) (some b)) (a+2) bs
private theorem place_append (T : Nat → Option Bool) (a : Nat) (xs ys : List Bool) :
    place T a (xs++ys)=place (place T a xs) (a+2*xs.length) ys := by
  induction xs generalizing T a with
  | nil => rfl
  | cons b xs ih =>
    rw [List.cons_append,place,ih]
    change _=place (place (put (put T a (some true)) (a+1) (some b)) (a+2) xs) (a+2*(xs.length+1)) ys
    rw [show a+2+2*xs.length=a+2*(xs.length+1) by omega]
private theorem place_outside (T : Nat → Option Bool) (a : Nat) (xs : List Bool) (i : Nat)
    (outside : i<a ∨ a+2*xs.length ≤ i) : place T a xs i=T i := by
  induction xs generalizing T a with
  | nil => rfl
  | cons b xs ih =>
    have out : i<a+2 ∨ (a+2)+2*xs.length ≤ i := by simp only [List.length_cons] at outside;omega
    rw [place,ih _ _ out]
    change (if i=a+1 then some b else if i=a then some true else T i)=T i
    have ne1 : i≠a+1 := by simp only [List.length_cons] at outside;omega
    have ne0 : i≠a := by simp only [List.length_cons] at outside;omega
    rw [if_neg ne1,if_neg ne0]
private theorem place_pair (T : Nat → Option Bool) (a : Nat) (xs : List Bool) :
    ∀ j,(hj : j<xs.length) →
      place T a xs (a+2*j)=some true ∧ place T a xs (a+2*j+1)=some (xs[j]'hj) := by
  induction xs generalizing T a with
  | nil => intro j hj;simp only [List.length_nil] at hj;omega
  | cons b xs ih =>
    intro j hj
    cases j with
    | zero =>
      have first:=place_outside (put (put T a (some true)) (a+1) (some b)) (a+2) xs a (Or.inl (by omega))
      have second:=place_outside (put (put T a (some true)) (a+1) (some b)) (a+2) xs (a+1) (Or.inl (by omega))
      change place _ (a+2) xs a=some true ∧ place _ (a+2) xs (a+1)=some b
      rw [first,second]
      change (if a=a+1 then some b else if a=a then some true else T a)=some true ∧
        (if a+1=a+1 then some b else if a+1=a then some true else T (a+1))=some b
      rw [if_neg (by omega : a≠a+1),if_pos rfl,if_pos rfl]
      exact ⟨rfl,rfl⟩
    | succ j =>
      have tail:=ih (put (put T a (some true)) (a+1) (some b)) (a+2) j (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hj)
      have p0 : a+2+2*j=a+2*(j+1) := by omega
      rw [p0] at tail
      exact tail
private theorem place_snoc (T : Nat → Option Bool) (a : Nat) (xs : List Bool) (b : Bool) :
    place T a (xs++[b])=put (put (place T a xs) (a+2*xs.length) (some true)) (a+2*xs.length+1) (some b) := by
  rw [place_append]
  rfl
private theorem place_pop (T : Nat → Option Bool) (a : Nat) (xs : List Bool) (b : Bool)
    (free0 : T (a+2*xs.length)=some false) (free1 : T (a+2*xs.length+1)=some false) :
    put (put (place T a (xs++[b])) (a+2*xs.length+1) (some false)) (a+2*xs.length) (some false)=place T a xs := by
  rw [place_snoc]
  have old0:=place_outside T a xs (a+2*xs.length) (Or.inr le_rfl)
  have old1:=place_outside T a xs (a+2*xs.length+1) (Or.inr (by omega))
  rw [free0] at old0
  rw [free1] at old1
  funext i
  change (if i=a+2*xs.length then some false else if i=a+2*xs.length+1 then some false else
    if i=a+2*xs.length+1 then some b else if i=a+2*xs.length then some true else place T a xs i)=_
  by_cases at0 : i=a+2*xs.length
  · rw [if_pos at0,at0,old0]
  · rw [if_neg at0]
    by_cases at1 : i=a+2*xs.length+1
    · rw [if_pos at1,at1,old1]
    · rw [if_neg at1,if_neg at1,if_neg at0]
end FullBodyClosure
