import PhysicalCallerClosure.SourcePrepare
import Body.Proof
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def support (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing Engine term {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .inductInfo _=>"inductive" | .ctorInfo _=>"constructor" | _=>"other"
  unless actual==kind do throwError "Wrong Engine kind: {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
  logInfo m!"copy-support|{actual}|{n}|{ci.type}"
  closeMainGoal `support (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for leaf in ["Node","Path","put","keep","hop","sweepL","sweepR","crossL","crossR","dest"] do
    let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
    let some ci:=e.find? n | throwError "Missing Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
    logInfo m!"copy-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac support "Node.mk" "constructor"
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private def carryCost : List Bool → Nat → Nat
  | [],_=>0
  | false::_,r=>r+1
  | true::bs,r=>1+carryCost bs (r+1)
private def CarryRows (c b : Fin M.stateCount) : Prop :=
  Safe c ∧ Safe b ∧ M.step c (some true)=(c,some false,.left) ∧
    M.step c (some false)=(b,some true,.right) ∧ (∀ x,M.step b (some x)=(b,some x,.right))
private theorem carry_path (T : Nat → Option Bool) (left r : Nat) (bs : List Bool)
    (c b : Fin M.stateCount) (code:CarryRows (Safe:=Safe) c b) (P : Nat)
    (fit:left+bs.length+r+1 ≤ P) (digits:Body.Reads T left bs)
    (occ:∀ i,left+bs.length < i → i < left+bs.length+r+1 → ∃ x,T i=some x) :
    Path M Safe P (carryCost bs r) (node c (left+bs.length) T)
      (node (if (Body.inc bs).2 then c else b)
        (if (Body.inc bs).2 then left else left+bs.length+r+1) (Body.carryTape T left bs)) := by
  obtain ⟨sc,sb,rt,rf,rb⟩:=code
  induction bs generalizing r T with
  | nil => simpa only [carryCost,Body.inc,Body.carryTape,List.length_nil,if_true,Nat.add_zero] using
      Path.nil (node c left T) (by omega : left ≤ P)
  | cons v bs ih =>
    obtain ⟨hv,hs⟩:=(Body.reads_cons T left v bs).mp digits
    cases v with
    | false =>
      let U:=put T (left+bs.length+1) (some true)
      have first:=hop c b (left+bs.length+1) (left+bs.length+2) T (some true) .right
        (P:=P) (by simp only [List.length_cons] at fit;omega) (by simp only [List.length_cons] at fit;omega) sc
        (by rw [hv];exact rf) rfl
      have rest:=sweepR b U (left+bs.length+2) r (P:=P) (by simp only [List.length_cons] at fit;omega) sb (by
        intro i lo hi
        obtain ⟨x,hx⟩:=occ i (by simp only [List.length_cons];omega) (by simp only [List.length_cons];omega)
        rw [show U i=some x by simp only [U,put,if_neg (show i≠left+bs.length+1 by omega),hx]]
        exact rb x)
      simpa only [carryCost,Body.inc,Body.carryTape,Body.put,put,List.length_cons,if_false,U,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using first.append rest
    | true =>
      let U:=put T (left+bs.length+1) (some false)
      have first:=hop c c (left+bs.length+1) (left+bs.length) T (some false) .left
        (P:=P) (by simp only [List.length_cons] at fit;omega) (by simp only [List.length_cons] at fit;omega) sc
        (by rw [hv];exact rt) (by simp [dest])
      have rest:=ih U (r+1) (by simp only [List.length_cons] at fit;omega)
        (Body.reads_put_outside T left bs hs _ _ (by omega)) (by
          intro i lo hi
          by_cases eq:i=left+bs.length+1
          · exact ⟨false,by simp only [U,put,if_pos eq]⟩
          · obtain ⟨x,hx⟩:=occ i (by simp only [List.length_cons];omega) (by simp only [List.length_cons];omega)
            exact ⟨x,by simp only [U,put,if_neg eq,hx]⟩)
      simpa only [carryCost,Body.inc,Body.carryTape,Body.put,put,List.length_cons,U,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using first.append rest
private theorem carry_price (bs : List Bool) (r : Nat) : carryCost bs r ≤ 2*bs.length+r+1 := by
  induction bs generalizing r with
  | nil => simp only [carryCost,List.length_nil];omega
  | cons v bs ih => cases v <;> simp only [carryCost,List.length_cons] <;> have h:=ih (r+1) <;> omega
private theorem overflow_cost (bs : List Bool) (r : Nat) (h:(Body.inc bs).2=true) : carryCost bs r=bs.length := by
  induction bs generalizing r with
  | nil => rfl
  | cons v bs ih =>
    cases v with
    | false => simp only [Body.inc,Bool.false_eq_true] at h
    | true => rw [carryCost,ih (r+1) h];simp only [List.length_cons];omega
private structure IncrementRows (entry normal overflow : Fin M.stateCount) where
  carry : Fin M.stateCount
  back : Fin M.stateCount
  over : Fin M.stateCount
  se : Safe entry
  sb : Safe back
  so : Safe over
  rows : CarryRows (Safe:=Safe) carry back
  enter : M.step entry none=(carry,none,.left)
  full : M.step carry none=(over,none,.right)
  backStop : M.step back none=(normal,none,.stay)
  overLoop : ∀ x,M.step over (some x)=(over,some x,.right)
  overStop : M.step over none=(overflow,none,.stay)
private theorem increment_path (T : Nat → Option Bool) (L P : Nat) (bs : List Bool)
    (entry normal overflow : Fin M.stateCount) (code:IncrementRows (Safe:=Safe) entry normal overflow)
    (fit:L+bs.length+1 ≤ P) (left:T L=none) (right:T (L+bs.length+1)=none)
    (digits:Body.Reads T L bs) :
    ∃ t,t ≤ 2*bs.length+3 ∧ Path M Safe P t (node entry (L+bs.length+1) T)
      (node (if (Body.inc bs).2 then overflow else normal) (L+bs.length+1) (Body.carryTape T L bs)) := by
  have first:=keep entry code.carry (L+bs.length+1) (L+bs.length) T .left (P:=P)
    fit (by omega) code.se (by rw [right];exact code.enter) (by simp [dest])
  have middle:=carry_path T L 0 bs code.carry code.back code.rows P (by omega) digits
    (by intro i lo hi;omega)
  let U:=Body.carryTape T L bs
  have ul:U L=none:=by change Body.carryTape T L bs L=none;rw [Body.carry_frame T L bs L (Or.inl le_rfl)];exact left
  have ur:U (L+bs.length+1)=none:=by change Body.carryTape T L bs (L+bs.length+1)=none;rw [Body.carry_frame T L bs (L+bs.length+1) (Or.inr (by omega))];exact right
  cases h:(Body.inc bs).2 with
  | false =>
    rw [h] at middle
    simp only [Nat.add_zero] at middle
    have last:=keep code.back normal (L+bs.length+1) (L+bs.length+1) U .stay (P:=P) fit fit code.sb
      (by rw [ur];exact code.backStop) rfl
    refine ⟨1+(carryCost bs 0+1),?_,?_⟩
    · have price:=carry_price bs 0;omega
    · simpa only [h,if_false] using first.append (middle.append last)
  | true =>
    rw [h] at middle
    simp only [if_true] at middle
    have take:=keep code.carry code.over L (L+1) U .right (P:=P) (by omega) (by omega) code.rows.1
      (by rw [ul];exact code.full) rfl
    have sweep:=sweepR code.over U (L+1) bs.length (P:=P) (by omega) code.so (by
      intro i lo hi
      let j:=L+bs.length-i
      have hj:j < (Body.inc bs).1.length:=by rw [Body.inc_length];dsimp only [j];omega
      have pos:L+(Body.inc bs).1.length-j=i:=by rw [Body.inc_length];dsimp only [j];omega
      have val:=Body.carry_reads T L bs digits j hj
      rw [pos] at val
      rw [show U i=some (Body.inc bs).1[j]! from val];exact code.overLoop _)
    rw [show L+1+bs.length=L+bs.length+1 by omega] at sweep
    have last:=keep code.over overflow (L+bs.length+1) (L+bs.length+1) U .stay (P:=P) fit fit code.so
      (by rw [ur];exact code.overStop) rfl
    refine ⟨1+(carryCost bs 0+(1+(bs.length+1))),?_,?_⟩
    · rw [overflow_cost bs 0 h];omega
    · simpa only [h,if_true] using first.append (middle.append (take.append (sweep.append last)))
end PhysicalCallerClosure
