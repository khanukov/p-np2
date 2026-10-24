import VirtualFinalClosure.StreamActivePaths
import Stream.Kernel
namespace VirtualFinalClosure.StreamPhasePaths
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","q","q",(0:Nat)),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","pure_row","pureRow",1),
      ("Stream.Kernel","Stream","carryCost","carryCost",0),
      ("Stream.Kernel","Stream","modeOf","modeOf",0),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong SAME counter/source phase interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique SAME counter/source phase interface {mod}/{key}"
private def unpaid (k : Nat) (f : Fin 4) (mode : Fin 3) : Fin (machine k).stateCount:=q k f (11+8*mode.val)
private def unpaid_type : ∀ k,Fin 4 → Fin 3 → Fin (machine k).stateCount:=unpaid
private theorem append {M : UniformTM} {P t u : Nat} {c d e}
    (h : GPath (M:=M) P t c d) (g : GPath (M:=M) P u d e) : GPath (M:=M) P (t+u) c e:=joinPath h g
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h)=T:=by
  funext i;by_cases hi : i=h <;> simp [put,hi]
/-- These are transported proofs of the SAME immutable Stream carry/source
microprogram, using the existing generic Path. Metadata is proved constant on
these quiet phases; the paid edge is handled separately by StreamActivePaths. -/
private theorem return_rows (k : Nat) (f : Fin 4) : ∀ mode : Fin 3, (∀ b, (machine k).step ((q k f) (8+8*mode.val)) (some b) = ((q k f) (8+8*mode.val),some b,.right)) ∧
    (machine k).step ((q k f) (8+8*mode.val)) none = ((q k f) (9+8*mode.val),none,.right) ∧
    (machine k).step ((q k f) (9+8*mode.val)) (some false) = ((q k f) (9+8*mode.val),some false,.right) ∧
    (machine k).step ((q k f) (9+8*mode.val)) none = ((q k f) (10+8*mode.val),none,.right) ∧ (∀ b, (machine k).step ((q k f) (10+8*mode.val)) (some b) = ((q k f) (10+8*mode.val),some b,.right)) ∧
    (machine k).step ((q k f) (10+8*mode.val)) none = ((unpaid k f) mode,none,.stay) := by
  intro mode
  fin_cases mode
  all_goals refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals first | (intro b;cases b <;> apply pureRow <;> decide) | (apply pureRow <;> decide)

private theorem return_path (k : Nat) (f : Fin 4) (T : Nat → Option Bool) (S z n : Nat) (mode : Fin 3) (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b) (right : T (S+z+n+3)=none) :
    GPath (S+z+n+3) (n+z+3) (node ((q k f) (9+8*mode.val)) (S+1) (T))
      (node ((unpaid k f) mode) (S+z+n+3) (T)) := by
  have rows := (return_rows k f) mode
  have a := sweepR ((q k f) (9+8*mode.val)) T (S+1) (z+1) (P := S+z+n+3) (by omega) (by
    intro i hl hu; rw [reg i (by omega) (by omega)]; exact rows.2.2.1)
  have eqL : S+1+(z+1)=S+z+2 := by omega
  rw [eqL] at a
  have b := keep ((q k f) (9+8*mode.val)) ((q k f) (10+8*mode.val)) (S+z+2) (S+z+3) T .right (P := S+z+n+3) (by omega) (by omega) (by rw [sep]; exact rows.2.2.2.1) rfl
  have c := sweepR ((q k f) (10+8*mode.val)) T (S+z+3) n (P := S+z+n+3) (by omega) (by
    intro i hl hu; obtain ⟨v,hv⟩ := assn i (by omega) (by omega)
    rw [hv]; exact rows.2.2.2.2.1 v)
  have eqR : S+z+3+n=S+z+n+3 := by omega
  rw [eqR] at c
  have d := keep ((q k f) (10+8*mode.val)) ((unpaid k f) mode) (S+z+n+3) (S+z+n+3) T .stay (P := S+z+n+3) le_rfl le_rfl (by rw [right]; exact rows.2.2.2.2.2) rfl
  convert ((a.append b).append c).append d using 1; omega
private theorem carry_rows (k : Nat) (f : Fin 4) : ∀ mode : Fin 3,
    (machine k).step ((q k f) (12+8*mode.val)) (some true) = ((q k f) (12+8*mode.val),some false,.left) ∧
    (machine k).step ((q k f) (12+8*mode.val)) (some false) = ((q k f) (13+8*mode.val),some true,.right) ∧
    ∀ b, (machine k).step ((q k f) (13+8*mode.val)) (some b) = ((q k f) (13+8*mode.val),some b,.right) := by
  intro mode
  fin_cases mode
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first | (intro b;cases b <;> apply pureRow <;> decide) | (apply pureRow <;> decide)

private theorem carry_path (k : Nat) (f : Fin 4) (T : Nat → Option Bool) (left r : Nat) (bs : List Bool) (mode : Fin 3) (digits : Body.Reads T left bs)
    (occ : ∀ i, left+bs.length < i → i < left+bs.length+r+1 → ∃ b, T i=some b) :
    GPath (left+bs.length+r+1) (carryCost bs r)
      (node ((q k f) (12+8*mode.val)) (left+bs.length) (T))
      (node ((q k f) ((if (Body.inc bs).2 then 12 else 13)+8*mode.val)) (if (Body.inc bs).2 then left else left+bs.length+r+1) (Body.carryTape T left bs)) := by
  induction bs generalizing r T with
  | nil => simpa [carryCost,Body.inc,Body.carryTape] using
      nilPath (node ((q k f) (12+8*mode.val)) (left) (T)) (by omega : left  ≤  left+0+r+1)
  | cons b bs ih =>
    obtain ⟨hb,hs⟩ := (Body.reads_cons T left b bs).1 digits
    cases b with
    | false =>
      let U := put T (left+bs.length+1) (some true)
      let R := left+(false::bs).length+r+1
      have a := hop ((q k f) (12+8*mode.val)) ((q k f) (13+8*mode.val)) (left+bs.length+1) (left+bs.length+2) T (some true) .right (P := R) (by dsimp [R]; omega) (by dsimp [R]; omega)
        (by rw [hb]; exact ((carry_rows k f) mode).2.1) rfl
      have b := sweepR ((q k f) (13+8*mode.val)) U (left+bs.length+2) r (P := R)
        (by dsimp [R]; omega) (by
          intro i hl hu
          obtain ⟨v,hv⟩ := occ i (by simp; omega) (by simp at *; omega)
          rw [show U i=some v by simp [U,put,show i≠left+bs.length+1 by omega,hv]]
          exact ((carry_rows k f) mode).2.2 v)
      have eqR : left+bs.length+2+r=R := by dsimp [R]; omega
      rw [eqR] at b
      simpa [carryCost,Body.inc,Body.carryTape,Body.put,U,put,R,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.append b
    | true =>
      let U := put T (left+bs.length+1) (some false)
      let R := left+(true::bs).length+r+1
      have a := hop ((q k f) (12+8*mode.val)) ((q k f) (12+8*mode.val)) (left+bs.length+1) (left+bs.length) T (some false) .left (P := R) (by dsimp [R]; omega) (by dsimp [R]; omega)
        (by rw [hb]; exact ((carry_rows k f) mode).1) (by simp [dest])
      have rest := ih U (r+1) (Body.reads_put_outside T left bs hs _ _ (by omega)) (by
        intro i hl hu
        by_cases hi : i=left+bs.length+1
        · exact ⟨false,by simp [U,put,hi]⟩
        · obtain ⟨v,hv⟩ := occ i (by simp; omega) (by simp at *; omega)
          exact ⟨v,by simp [U,put,hi,hv]⟩)
      have eqR : left+bs.length+(r+1)+1=R := by dsimp [R]; omega
      rw [eqR] at rest
      simpa [carryCost,Body.inc,Body.carryTape,Body.put,U,put,R,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.append rest
private theorem lift_path (k : Nat) (f : Fin 4) (T : Nat → Option Bool) (p S z n : Nat) (hps : p  ≤  S) (source : ∀ i, p  ≤  i → i < S → ∃ b, T i=some b) (eof : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none) (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b) (right : T (S+z+n+3)=none) :
    ∃ mode : Fin 3, (mode.val=2 ↔ p=S) ∧ (p < S → T p=some (InputRead.result mode)) ∧
      GPath (S+z+n+3) (n+z+(S-p)+4)
        (node ((q k f) 7) (p) (T)) (node ((unpaid k f) mode) (S+z+n+3) (put T p none)) := by
  by_cases hlt : p < S
  · obtain ⟨b,hb⟩ := source p le_rfl hlt
    let U := put T p none
    have one := hop ((q k f) 7) ((q k f) (8+8*(modeOf b).val)) p (p+1) T none .right (P := S+z+n+3) (by omega) (by omega) (by rw [hb]; cases b <;> apply pureRow <;> decide) rfl
    have rows := (return_rows k f) (modeOf b)
    have a := sweepR ((q k f) (8+8*(modeOf b).val)) U (p+1) (S-p-1)
      (P := S+z+n+3) (by omega) (by
        intro i hl hu; obtain ⟨v,hv⟩ := source i (by omega) (by omega)
        have hvU : U i=some v := by simp [U,put,show i≠p by omega,hv]
        rw [hvU]; exact rows.1 v)
    have eqS : p+1+(S-p-1)=S := by omega
    rw [eqS] at a
    have ue : U S=none := by simp [U,put,show S≠p by omega,eof]
    have c := keep ((q k f) (8+8*(modeOf b).val)) ((q k f) (9+8*(modeOf b).val)) S (S+1) U .right (P := S+z+n+3) (by omega) (by omega) (by rw [ue]; exact rows.2.1) rfl
    have ret := (return_path k f) U S z n (modeOf b) (by intro i hl hu; simp [U,put,show i≠p by omega,reg i hl hu]) (by simp [U,put,show S+z+2≠p by omega,sep])
      (by intro i hl hu; obtain ⟨v,hv⟩ := assn i hl hu; exact ⟨v,by simp [U,put,show i≠p by omega,hv]⟩) (by simp [U,put,show S+z+n+3≠p by omega,right])
    refine ⟨modeOf b,by cases b <;> simp [modeOf] <;> omega,?_,?_⟩
    · intro _; cases b <;> simpa [InputRead.result,modeOf] using hb
    · convert ((one.append a).append c).append ret using 1; omega
  · have eq : p=S := by omega
    have one := keep ((q k f) 7) ((q k f) 25) S (S+1) T .right (P := S+z+n+3) (by omega) (by omega) (by rw [eof];apply pureRow <;> decide) rfl
    have ret := (return_path k f) T S z n ⟨2,by decide⟩ reg sep assn right
    have unchanged : put T p none=T := by rw [eq,← eof,put_same]
    refine ⟨⟨2,by decide⟩,by simp [eq],by omega,?_⟩
    rw [unchanged,eq]
    convert one.append ret using 1; simp; omega
private theorem restore_path (k : Nat) (T : Nat → Option Bool) (p S z P : Nat) (rstate sstate estate : Fin (machine k).stateCount) (bit : Bool) (hp : p < S) (fit : S+z+1 ≤ P)
    (hole : T p=none) (source : ∀ i, p < i → i < S → ∃ b, T i=some b) (eof : T S=none) (reg : ∀ i, S < i → i < S+z+2 → T i=some false)
    (rr : (machine k).step rstate (some false)=(rstate,some false,.left)) (rb : (machine k).step rstate none=(sstate,none,.left))
    (sr : ∀ b, (machine k).step sstate (some b)=(sstate,some b,.left)) (sb : (machine k).step sstate none=(estate,some bit,.right)) :
    GPath P (z+(S-p)+2) (node (rstate) (S+z+1) (T)) (node (estate) (p+1) (put T p (some bit))) := by
  have a := sweepL rstate T S (z+1) (P := P) (by omega) (by intro i hl hu; rw [reg i hl (by omega)]; exact rr)
  have b := keep rstate sstate S (S-1) T .left (P := P) (by omega) (by omega) (by rw [eof]; exact rb) rfl
  have c := sweepL sstate T p (S-p-1) (P := P) (by omega) (by intro i hl hu; obtain ⟨v,hv⟩ := source i hl (by omega); rw [hv]; exact sr v)
  have eqS : p+(S-p-1)=S-1 := by omega
  rw [eqS] at c
  have d := hop sstate estate p (p+1) T (some bit) .right (P := P) (by omega) (by omega) (by rw [hole]; exact sb) rfl
  have pos : S+(z+1)=S+z+1 := by omega
  rw [pos] at a
  convert ((a.append b).append c).append d using 1; omega
private theorem advance_rows (k : Nat) (f : Fin 4) : ∀ mode : Fin 3, mode.val < 2 →
    (machine k).step ((q k f) (13+8*mode.val)) none=((q k f) (14+8*mode.val),none,.left) ∧ (∀ b, (machine k).step ((q k f) (14+8*mode.val)) (some b)=((q k f) (14+8*mode.val),some b,.left)) ∧
    (machine k).step ((q k f) (14+8*mode.val)) none=((q k f) (15+8*mode.val),none,.left) ∧
    (machine k).step ((q k f) (15+8*mode.val)) (some false)=((q k f) (15+8*mode.val),some false,.left) ∧
    (machine k).step ((q k f) (15+8*mode.val)) none=((q k f) (32+mode.val),none,.left) ∧ (∀ b, (machine k).step ((q k f) (32+mode.val)) (some b)=((q k f) (32+mode.val),some b,.left)) ∧
    (machine k).step ((q k f) (32+mode.val)) none=((q k f) 7,some (InputRead.result mode),.right) := by
  intro mode
  intro small
  fin_cases mode
  all_goals norm_num at small
  all_goals refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | (intro b;cases b <;> apply pureRow <;> decide) | (apply pureRow <;> decide)

private theorem advance_path (k : Nat) (f : Fin 4) (T : Nat → Option Bool) (p S z n : Nat) (mode : Fin 3) (hm : mode.val < 2) (hp : p < S) (hole : T p=none)
    (source : ∀ i, p < i → i < S → ∃ b, T i=some b) (eof : T S=none) (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b) (right : T (S+z+n+3)=none) :
    GPath (S+z+n+3) (n+z+(S-p)+4) (node ((q k f) (13+8*mode.val)) (S+z+n+3) (T))
      (node ((q k f) 7) (p+1) (put T p (some (InputRead.result mode)))) := by
  have rows := (advance_rows k f) mode hm
  have a := keep ((q k f) (13+8*mode.val)) ((q k f) (14+8*mode.val)) (S+z+n+3) (S+z+n+2) T .left (P := S+z+n+3) le_rfl (by omega) (by rw [right]; exact rows.1) (by simp [dest])
  have b := sweepL ((q k f) (14+8*mode.val)) T (S+z+2) n (P := S+z+n+3) (by omega) (by intro i hl hu; obtain ⟨v,hv⟩ := assn i hl (by omega); rw [hv]; exact rows.2.1 v)
  have c := keep ((q k f) (14+8*mode.val)) ((q k f) (15+8*mode.val)) (S+z+2) (S+z+1) T .left (P := S+z+n+3) (by omega) (by omega) (by rw [sep]; exact rows.2.2.1) (by simp [dest])
  have d := (restore_path k) T p S z (S+z+n+3) ((q k f) (15+8*mode.val)) ((q k f) (32+mode.val)) ((q k f) 7) (InputRead.result mode) hp (by omega) hole source eof reg
    rows.2.2.2.1 rows.2.2.2.2.1 rows.2.2.2.2.2.1 rows.2.2.2.2.2.2
  have pos : S+z+2+n=S+z+n+2 := by omega
  rw [pos] at b
  convert ((a.append b).append c).append d using 1; omega
private theorem finish_rows (k : Nat) (f : Fin 4) : ∀ mode : Fin 3, mode.val < 2 →
    (machine k).step ((q k f) (12+8*mode.val)) none=((q k f) (35+mode.val),none,.left) ∧
    (machine k).step ((q k f) (35+mode.val)) (some false)=((q k f) (35+mode.val),some false,.left) ∧
    (machine k).step ((q k f) (35+mode.val)) none=((q k f) (37+mode.val),none,.left) ∧ (∀ b, (machine k).step ((q k f) (37+mode.val)) (some b)=((q k f) (37+mode.val),some b,.left)) ∧
    (machine k).step ((q k f) (37+mode.val)) none=((q k f) 56,some (InputRead.result mode),.right) := by
  intro mode
  intro small
  fin_cases mode
  all_goals norm_num at small
  all_goals refine ⟨?_,?_,?_,?_,?_⟩
  all_goals first | (intro b;cases b <;> apply pureRow <;> decide) | (apply pureRow <;> decide)

private theorem finish_physical (k : Nat) (f : Fin 4) (T : Nat → Option Bool) (p S z n : Nat) (mode : Fin 3) (hm : mode.val < 2) (hp : p < S) (hole : T p=none)
    (source : ∀ i, p < i → i < S → ∃ b, T i=some b) (eof : T S=none) (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none) :
    GPath (S+z+n+3) (z+(S-p)+4) (node ((q k f) (12+8*mode.val)) (S+z+2) (T))
      (node ((q k f) (if p+1=S then 57 else 58)) (p+1) (put T p (some (InputRead.result mode)))) := by
  have rows := (finish_rows k f) mode hm
  have a := keep ((q k f) (12+8*mode.val)) ((q k f) (35+mode.val)) (S+z+2) (S+z+1) T .left (P := S+z+n+3) (by omega) (by omega) (by rw [sep]; exact rows.1) (by simp [dest])
  have b := (restore_path k) T p S z (S+z+n+3) ((q k f) (35+mode.val)) ((q k f) (37+mode.val)) ((q k f) 56) (InputRead.result mode) hp (by omega) hole source eof reg
    rows.2.1 rows.2.2.1 rows.2.2.2.1 rows.2.2.2.2
  let U := put T p (some (InputRead.result mode))
  have c := keep ((q k f) 56) ((q k f) (if p+1=S then 57 else 58)) (p+1) (p+1) U .stay
    (P := S+z+n+3) (by omega) (by omega) (by
      by_cases he : p+1=S
      · simp only [he,if_true]
        rw [show U S=none by simp [U,put,show S≠p by omega,eof]];apply pureRow <;> decide
      · obtain ⟨v,hv⟩ := source (p+1) (by omega) (by omega)
        rw [if_neg he,show U (p+1)=some v by simp [U,put,hv]]
        cases v <;> apply pureRow <;> decide) rfl
  convert (a.append b).append c using 1; omega
private theorem finish_virtual (k : Nat) (f : Fin 4) (T : Nat → Option Bool) (S z n : Nat) (eof : T S=none) (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none) :
    GPath (S+z+n+3) (z+3) (node ((q k f) 28) (S+z+2) (T)) (node ((q k f) 57) (S) (T)) := by
  have a := keep ((q k f) 28) ((q k f) 54) (S+z+2) (S+z+1) T .left (P := S+z+n+3) (by omega) (by omega) (by rw [sep];apply pureRow <;> decide) (by simp [dest])
  have b := sweepL ((q k f) 54) T S (z+1) (P := S+z+n+3) (by omega) (by intro i hl hu; rw [reg i hl (by omega)];apply pureRow <;> decide)
  have pos : S+(z+1)=S+z+1 := by omega
  rw [pos] at b
  have c := keep ((q k f) 54) ((q k f) 57) S S T .stay (P := S+z+n+3) (by omega) (by omega) (by rw [eof];apply pureRow <;> decide) rfl
  convert (a.append b).append c using 1; omega
#print axioms unpaid_type
#print axioms append
#print axioms put_same
#print axioms return_rows
#print axioms return_path
#print axioms carry_rows
#print axioms carry_path
#print axioms lift_path
#print axioms restore_path
#print axioms advance_rows
#print axioms advance_path
#print axioms finish_rows
#print axioms finish_physical
#print axioms finish_virtual
end VirtualFinalClosure.StreamPhasePaths
