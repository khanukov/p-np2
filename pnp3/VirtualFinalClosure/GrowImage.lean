import VirtualFinalClosure.GrowCopy
namespace VirtualFinalClosure.GrowImage
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",(2:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual growing-bank path interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual growing-bank path interface {mod}/{key}"
  for (key,aliasName) in [("copy_round","copyRound")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.GrowCopy." && name.toString.endsWith (".VirtualFinalClosure.GrowCopy."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique growing-copy orbit {key}"
private def image (T : Nat → Option Bool) (B width a : Nat) : Nat → Option Bool := fun i=>
  if B < i ∧ i < B+width+1 then some (decide (i ≤ B+a)) else
  if B+width+1 < i ∧ i ≤ B+width+1+a then some false else T i
private def cost (width : Nat) : Nat → Nat
  | 0=>0
  | a+1=>cost width a+2*width+2*a+7
private def image_type : (Nat → Option Bool) → Nat → Nat → Nat → Nat → Option Bool := image
private def cost_type : Nat → Nat → Nat := cost
private theorem initial (T : Nat → Option Bool) (B width : Nat)
    (old : ∀ i,B < i → i < B+width+1 → T i=some false) : image T B width 0=T := by
  funext i
  dsimp only [image]
  by_cases inside : B < i ∧ i < B+width+1
  · rw [if_pos inside,old i inside.1 inside.2,decide_eq_false (by omega)]
  · rw [if_neg inside,if_neg (by omega)]
private theorem outside (T : Nat → Option Bool) (B width a i : Nat)
    (hi : i ≤ B ∨ B+width+1+a < i ∨ i=B+width+1) : image T B width a i=T i := by
  dsimp only [image]
  rw [if_neg (by omega),if_neg (by omega)]
private theorem increment (T : Nat → Option Bool) (B width a : Nat) (ha : a < width) :
    put (put (image T B width a) (B+a+1) (some true)) (B+width+a+2) (some false)=
      image T B width (a+1) := by
  funext i
  dsimp only [put,image]
  by_cases newTemp : i=B+width+a+2
  · subst i
    rw [if_pos rfl,if_neg (by omega),if_pos (by omega)]
  · rw [if_neg newTemp]
    by_cases newMark : i=B+a+1
    · subst i
      rw [if_pos rfl,if_pos (by omega),decide_eq_true (by omega)]
    · rw [if_neg newMark]
      by_cases old : B < i ∧ i < B+width+1
      · rw [if_pos old,if_pos old]
        have same : (i ≤ B+a) ↔ (i ≤ B+(a+1)) := by omega
        simp only [same]
      · rw [if_neg old,if_neg old]
        have same : (B+width+1 < i ∧ i ≤ B+width+1+a) ↔ (B+width+1 < i ∧ i ≤ B+width+1+(a+1)) := by omega
        simp only [same]
private theorem copying (k P m B width : Nat) (T : Nat → Option Bool)
    (hm : m < 144) (fit : B+2*width+2 ≤ P)
    (base : T B=none) (separator : T (B+width+1)=none)
    (old : ∀ i,B < i → i < B+width+1 → T i=some false)
    (blank : ∀ i,B+width+1 < i → i ≤ B+2*width+2 → T i=none) :
    ∃ t,t ≤ width*(4*width+7) ∧
      GPath (M:=machine k) P t (C k 67 m B T) (C k 67 m B (image T B width width)) := by
  have loop (a : Nat) (ha : a ≤ width) :
      GPath (M:=machine k) P (cost width a) (C k 67 m B T) (C k 67 m B (image T B width a)) := by
    induction a with
    | zero=>
      rw [initial T B width old]
      exact nilPath _ (by change B ≤ P;omega)
    | succ a ih=>
      have prev:=ih (by omega)
      have body:=copyRound k P m B width a (image T B width a) hm (by omega) fit
        ((outside T B width a B (Or.inl le_rfl)).trans base)
        ((outside T B width a (B+width+1) (Or.inr (Or.inr rfl))).trans separator)
        (by
          intro i lo hi
          dsimp only [image]
          rw [if_pos (by omega)])
        (by
          intro i lo hi
          dsimp only [image]
          rw [if_neg (by omega),if_pos (by omega)])
        (by
          rw [outside T B width a (B+width+a+2) (Or.inr (Or.inl (by omega)))]
          exact blank _ (by omega) (by omega))
      rw [increment T B width a (by omega)] at body
      have joined:=joinPath prev body
      change GPath (M:=machine k) P (cost width a+2*width+2*a+7) _ _
      simpa only [Nat.add_assoc] using joined
  have price (a : Nat) (ha : a ≤ width) : cost width a ≤ a*(4*width+7) := by
    induction a with
    | zero=>simp only [cost,Nat.zero_mul,le_refl]
    | succ a ih=>
      have prev:=ih (by omega)
      dsimp only [cost]
      nlinarith
  exact ⟨cost width width,price width le_rfl,loop width le_rfl⟩
#print axioms image_type
#print axioms cost_type
#print axioms initial
#print axioms outside
#print axioms increment
#print axioms copying
end VirtualFinalClosure.GrowImage
