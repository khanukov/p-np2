import InputRead.Path
import InputRead.Target
namespace InputRead
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 4000

/-- Finite row pins; mode contains one lifted bit or sticky EOF, never an address. -/
theorem return_rows : ∀ mode : Fin 3,
    (∀ b, machine.step (q (8+8*mode.val)) (some b) = (q (8+8*mode.val),some b,.right)) ∧
    machine.step (q (8+8*mode.val)) none = (q (9+8*mode.val),none,.right) ∧
    machine.step (q (9+8*mode.val)) (some false) = (q (9+8*mode.val),some false,.right) ∧
    machine.step (q (9+8*mode.val)) none = (q (10+8*mode.val),none,.right) ∧
    (∀ b, machine.step (q (10+8*mode.val)) (some b) = (q (10+8*mode.val),some b,.right)) ∧
    machine.step (q (10+8*mode.val)) none = (ready mode,none,.stay) := by decide

/-- Physical return across the actual register and counter boundaries. -/
theorem return_path (T : Nat → Option Bool) (S z n : Nat) (mode : Fin 3)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false)
    (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (right : T (S+z+n+3)=none) :
    Path (S+z+n+3) (n+z+3) ⟨q (9+8*mode.val),S+1,T⟩
      ⟨ready mode,S+z+n+3,T⟩ := by
  have rows := return_rows mode
  have a := sweepR (q (9+8*mode.val)) T (S+1) (z+1) (P := S+z+n+3) (by omega) (by
    intro i hl hu; rw [reg i (by omega) (by omega)]; exact rows.2.2.1)
  have eqL : S+1+(z+1)=S+z+2 := by omega
  rw [eqL] at a
  have b := keep (q (9+8*mode.val)) (q (10+8*mode.val)) (S+z+2) (S+z+3) T .right
    (P := S+z+n+3) (by omega) (by omega) (by rw [sep]; exact rows.2.2.2.1) rfl
  have c := sweepR (q (10+8*mode.val)) T (S+z+3) n (P := S+z+n+3) (by omega) (by
    intro i hl hu; obtain ⟨v,hv⟩ := assn i (by omega) (by omega)
    rw [hv]; exact rows.2.2.2.2.1 v)
  have eqR : S+z+3+n=S+z+n+3 := by omega
  rw [eqR] at c
  have d := keep (q (10+8*mode.val)) (ready mode) (S+z+n+3) (S+z+n+3) T .stay
    (P := S+z+n+3) le_rfl le_rfl (by rw [right]; exact rows.2.2.2.2.2) rfl
  convert ((a.append b).append c).append d using 1; omega

/-- Runtime discovers the source cursor by crossing three real blank boundaries
and the consumed gamma trail. No numeric parameter below occurs in a row. -/
theorem seek_path (T : Nat → Option Bool) (p S z n : Nat) (hp : 2 ≤ p) (hps : p ≤ S)
    (hole : T (p-2)=none) (marker : T (p-1)=some true)
    (source : ∀ i, p ≤ i → i < S → ∃ b, T i=some b)
    (eof : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false)
    (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (right : T (S+z+n+3)=none) :
    Path (S+z+n+3) (n+z+(S-p)+7) ⟨q 2,S+z+n+3,T⟩ ⟨q 7,p,T⟩ := by
  let P := S+z+n+3
  have a := keep (q 2) (q 3) P (P-1) T .left (P := P) le_rfl (by omega)
    (by rw [right]; rfl) rfl
  have b := sweepL (q 3) T (S+z+2) n (P := P) (by dsimp [P]; omega) (by
    intro i hl hu; obtain ⟨v,hv⟩ := assn i hl (by omega)
    rw [hv]; cases v <;> rfl)
  have ab : P-1=S+z+2+n := by dsimp [P]; omega
  rw [ab] at a
  have c := keep (q 3) (q 4) (S+z+2) (S+z+1) T .left (P := P)
    (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [sep]; rfl) (by simp [dest])
  have d := sweepL (q 4) T S (z+1) (P := P) (by dsimp [P]; omega) (by
    intro i hl hu; rw [reg i hl (by omega)]; rfl)
  have e := keep (q 4) (q 5) S (S-1) T .left (P := P)
    (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [eof]; rfl) rfl
  have f := sweepL (q 5) T (p-2) (S-p+1) (P := P) (by dsimp [P]; omega) (by
    intro i hl hu
    have occ : ∃ b, T i=some b := by
      by_cases hi : i=p-1
      · exact ⟨true,hi ▸ marker⟩
      · exact source i (by omega) (by omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  have ef : p-2+(S-p+1)=S-1 := by omega
  rw [ef] at f
  have g := keep (q 5) (q 6) (p-2) (p-1) T .right (P := P)
    (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [hole]; rfl) (by simp [dest]; omega)
  have h := keep (q 6) (q 7) (p-1) p T .right (P := P)
    (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [marker]; rfl) (by simp [dest]; omega)
  have eqD : S+(z+1)=S+z+1 := by omega
  rw [eqD] at d
  convert ((((((a.append b).append c).append d).append e).append f).append g).append h using 1; omega

def modeOf (b : Bool) : Fin 3 := if b then ⟨1,by decide⟩ else ⟨0,by decide⟩

/-- Generic physical-or-virtual read and a complete return frame. -/
theorem read_path (T : Nat → Option Bool) (p S z n : Nat) (hp : 2 ≤ p) (hps : p ≤ S)
    (hole : T (p-2)=none) (marker : T (p-1)=some true)
    (source : ∀ i, p ≤ i → i < S → ∃ b, T i=some b)
    (eof : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false)
    (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (right : T (S+z+n+3)=none) :
    ∃ mode : Fin 3,
      (mode.val=2 ↔ p=S) ∧ (p<S → T p=some (result mode)) ∧
      Path (S+z+n+3) (readClock n z (S-p))
        ⟨q 2,S+z+n+3,T⟩ ⟨ready mode,S+z+n+3,put T p none⟩ := by
  have seek := seek_path T p S z n hp hps hole marker source eof reg sep assn right
  by_cases hlt : p<S
  · obtain ⟨b,hb⟩ := source p le_rfl hlt
    let U := put T p none
    have one := hop (q 7) (q (8+8*(modeOf b).val)) p (p+1) T none .right
      (P := S+z+n+3) (by omega) (by omega) (by rw [hb]; cases b <;> rfl) rfl
    have rows := return_rows (modeOf b)
    have a := sweepR (q (8+8*(modeOf b).val)) U (p+1) (S-p-1)
      (P := S+z+n+3) (by omega) (by
        intro i hl hu; obtain ⟨v,hv⟩ := source i (by omega) (by omega)
        have hvU : U i=some v := by simp [U,put,show i≠p by omega,hv]
        rw [hvU]; exact rows.1 v)
    have eqS : p+1+(S-p-1)=S := by omega
    rw [eqS] at a
    have ue : U S=none := by simp [U,put,show S≠p by omega,eof]
    have c := keep (q (8+8*(modeOf b).val)) (q (9+8*(modeOf b).val)) S (S+1) U .right
      (P := S+z+n+3) (by omega) (by omega) (by rw [ue]; exact rows.2.1) rfl
    have ret := return_path U S z n (modeOf b)
      (by intro i hl hu; simp [U,put,show i≠p by omega,reg i hl hu])
      (by simp [U,put,show S+z+2≠p by omega,sep])
      (by intro i hl hu; obtain ⟨v,hv⟩ := assn i hl hu; exact ⟨v,by simp [U,put,show i≠p by omega,hv]⟩)
      (by simp [U,put,show S+z+n+3≠p by omega,right])
    refine ⟨modeOf b,by cases b <;> simp [modeOf] <;> omega,?_,?_⟩
    · intro _; cases b <;> simpa [result,modeOf] using hb
    · convert (((seek.append one).append a).append c).append ret using 1; dsimp [readClock]; omega
  · have eq : p=S := by omega
    have one := keep (q 7) (q 25) S (S+1) T .right
      (P := S+z+n+3) (by omega) (by omega) (by rw [eof]; rfl) rfl
    have ret := return_path T S z n ⟨2,by decide⟩ reg sep assn right
    have unchanged : put T p none=T := by rw [eq,← eof,put_same]
    refine ⟨⟨2,by decide⟩,by simp [eq],by omega,?_⟩
    rw [unchanged]
    rw [eq] at seek
    convert (seek.append one).append ret using 1; simp [readClock]; omega

/-- The frozen full finite-tape surface, with explicit source reconstruction. -/
theorem cursor_exact : Target.CursorRead := by
  intro N B p S z n c hp hps hfit hq hh hole marker source eof reg sep assn right
  let T := Body.extend c.tape
  have read (i : Nat) (hi : i < tapeLength N B) : T i=c.tape ⟨i,hi⟩ := by simp [T,Body.extend,hi]
  obtain ⟨mode,hm,hb,path⟩ := read_path T p S z n hp hps
    (by rw [read _ (by omega)]; exact hole)
    (by rw [read _ (by omega)]; exact marker)
    (by intro i hl hu; rw [read _ (by omega)]; exact source _ hl hu)
    (by rw [read _ (by omega)]; exact eof)
    (by intro i hl hu; rw [read _ (by omega)]; exact reg _ hl hu)
    (by rw [read _ (by omega)]; exact sep)
    (by intro i hl hu; rw [read _ (by omega)]; exact assn _ hl hu)
    (by rw [read _ hfit]; exact right)
  have he := path.execute hfit
  have hc : embed (N := N) (B := B) ⟨q 2,S+z+n+3,T⟩ hfit=c := by
    apply Config.ext_parts hq.symm (Fin.ext hh.symm)
    funext i; exact Body.extend_read c.tape i
  rw [hc] at he
  refine ⟨mode,hm,?_,?_⟩
  · intro hlt; rw [← read _ (by omega)]; exact hb hlt
  · rw [he]
    refine ⟨rfl,Fin.ext hh.symm,?_,?_⟩
    · intro i; change put T p none i.val = _
      simp only [put]; split_ifs <;> first | rfl | exact Body.extend_read c.tape i
    · intro i
      change (if i.val=p ∧ p<S then some (result mode) else put T p none i.val)=c.tape i
      by_cases hi : i.val=p
      · by_cases hlt : p<S
        · rw [if_pos ⟨hi,hlt⟩,← hb hlt,← hi]; exact Body.extend_read c.tape i
        · have eq : p=S := by omega
          rw [if_neg (by omega)]
          simp only [put,hi,if_true]
          exact (congrArg c.tape (Fin.ext (hi.trans eq))).trans eof |>.symm
      · simp only [hi,false_and,if_false,put]
        exact Body.extend_read c.tape i
end InputRead
