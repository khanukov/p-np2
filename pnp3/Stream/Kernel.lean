import Stream.BodyTarget
namespace Stream
open Pnp3.Complexity.Uniform.V1
private structure Node where
  state : Fin 64
  head : Nat
  tape : Nat → Option Bool
private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i
private def embed {N B : Nat} (c : Node) (h : c.head < tapeLength N B) : Config 64 N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩
private def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1
private structure Edge (P : Nat) (c d : Node) : Prop where
  before : c.head  ≤  P
  after : d.head  ≤  P
  row : (machine.step c.state (c.tape c.head)).1 = d.state
  move : dest c.head (machine.step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head (machine.step c.state (c.tape c.head)).2.1
private inductive Path (P : Nat) : Nat → Node → Node → Prop
  | nil (c) (h : c.head  ≤  P) : Path P 0 c c
  | cons {t c d e} : Edge P c d → Path P t d e → Path P (t+1) c e
namespace Path
private theorem bounds {P t c d} (h : Path P t c d) : c.head  ≤  P ∧ d.head  ≤  P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩
private theorem append {P t u c d e} (h : Path P t c d) (g : Path P u d e) :
    Path P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)
private theorem execute {N B P t c d} (h : Path P t c d) (hp : P < tapeLength N B) :
    machine.run t (embed c (lt_of_le_of_lt h.bounds.1 hp)) =
      embed d (lt_of_le_of_lt h.bounds.2 hp) := by
  have step {c d} (e : Edge P c d) :
      machine.stepConfig (embed c (lt_of_le_of_lt e.before hp)) =
        embed d (lt_of_le_of_lt e.after hp) := by
    apply Config.ext_parts
    · exact e.row
    · apply Fin.ext
      change (moveHead _ (machine.step c.state (c.tape c.head)).2.2).val = d.head
      have hm := e.move
      cases mv : (machine.step c.state (c.tape c.head)).2.2 with
      | left => simpa only [mv,moveHead,embed,dest] using hm
      | stay => simpa only [mv,moveHead,embed,dest] using hm
      | right =>
        rw [mv] at hm
        simp only [dest] at hm
        have hd := e.after
        have hr : c.head+1 < tapeLength N B := by omega
        simp only [moveHead,embed,hr,↓reduceDIte]
        exact hm
    · funext i
      dsimp only [UniformTM.stepConfig,embed]
      rw [e.tape]
      simp only [put,Fin.ext_iff]
  suffices aux : ∀ (hc : c.head < tapeLength N B) (hd : d.head < tapeLength N B),
      machine.run t (embed c hc) = embed d hd by exact aux _ _
  induction h with
  | nil => intro _ _; rfl
  | @cons t c d e ed path ih =>
    intro hc he
    rw [show t+1=1+t by omega,machine.run_add]
    change machine.run t (machine.stepConfig (embed c hc)) = embed e he
    rw [step ed]
    exact ih _ _
end Path
private theorem hop {P : Nat} (s s' : Fin 64) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hb : h  ≤  P) (ha : h'  ≤  P)
    (row : machine.step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]
/-- One exact public row that preserves the scanned symbol. -/
private theorem keep {P : Nat} (s s' : Fin 64) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hb : h  ≤  P) (ha : h'  ≤  P)
    (row : machine.step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hb ha row hm
  rwa [put_same] at one
private theorem sweepR {P : Nat} (s : Fin 64) (T : Nat → Option Bool) (h r : Nat) (fit : h+r  ≤  P) (rows : ∀ i, h  ≤  i → i < h+r → machine.step s (T i)=(s,T i,.right)) :
    Path P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right (P := P) (by omega) (by omega) (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {P : Nat} (s : Fin 64) (T : Nat → Option Bool) (low r : Nat) (fit : low+r  ≤  P) (rows : ∀ i, low < i → i  ≤  low+r → machine.step s (T i)=(s,T i,.left)) :
    Path P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left (P := P) (by omega) (by omega) (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
private theorem pay_rows : ∀ mode : Fin 3,
    machine.step (unpaid mode) none = (q (41+4*mode.val),none,.right) ∧
    machine.step (q (41+4*mode.val)) (some true) = (q (41+4*mode.val),some true,.right) ∧
    machine.step (q (41+4*mode.val)) none = (q (42+4*mode.val),some true,.left) ∧
    machine.step (q (41+4*mode.val)) (some false) = (machine.reject,some false,.stay) ∧
    machine.step (q (42+4*mode.val)) (some true) = (q (42+4*mode.val),some true,.left) ∧
    machine.step (q (42+4*mode.val)) none = (paid mode,none,.stay) ∧
    machine.step (paid mode) none = (q (12+8*mode.val),none,.left) := by decide
private theorem pay_path (U : Nat → Option Bool) (H r cap : Nat) (mode : Fin 3) (blank : U H=none) (marks : ∀ i, H < i → i ≤ H+r → U i=some true)
    (fresh : U (H+r+1)=none) (room : r < cap) :
    Path (H+cap+1) (2*r+3) ⟨unpaid mode,H,U⟩
      ⟨paid mode,H,put U (H+r+1) (some true)⟩ := by
  have rows := pay_rows mode
  have a := keep (unpaid mode) (q (41+4*mode.val)) H (H+1) U .right (P := H+cap+1) (by omega) (by omega) (by rw [blank]; exact rows.1) rfl
  have b := sweepR (q (41+4*mode.val)) U (H+1) r (P := H+cap+1) (by omega) (by intro i hl hu; rw [marks i (by omega) (by omega)]; exact rows.2.1)
  have pos : H+1+r=H+r+1 := by omega
  rw [pos] at b
  have c := hop (q (41+4*mode.val)) (q (42+4*mode.val)) (H+r+1) (H+r) U (some true) .left (P := H+cap+1) (by omega) (by omega) (by rw [fresh]; exact rows.2.2.1) (by simp [dest])
  let V := put U (H+r+1) (some true)
  have d := sweepL (q (42+4*mode.val)) V H r (P := H+cap+1) (by omega)
    (by intro i hl hu; have hi : i≠H+r+1 := by omega
        rw [show V i=some true by simp [V,put,hi,marks i hl hu]]
        exact rows.2.2.2.2.1)
  have e := keep (q (42+4*mode.val)) (paid mode) H H V .stay (P := H+cap+1) (by omega) (by omega)
    (by rw [show V H=none by simp [V,put,blank,show H≠H+r+1 by omega]]
        exact rows.2.2.2.2.2.1) rfl
  convert (((a.append b).append c).append d).append e using 1; omega
private theorem cutoff_path (U : Nat → Option Bool) (H cap : Nat) (mode : Fin 3) (blank : U H=none) (marks : ∀ i, H < i → i ≤ H+cap → U i=some true)
    (fence : U (H+cap+1)=some false) :
    Path (H+cap+1) (cap+2) ⟨unpaid mode,H,U⟩ ⟨machine.reject,H+cap+1,U⟩ := by
  have rows := pay_rows mode
  have a := keep (unpaid mode) (q (41+4*mode.val)) H (H+1) U .right (P := H+cap+1) (by omega) (by omega) (by rw [blank]; exact rows.1) rfl
  have b := sweepR (q (41+4*mode.val)) U (H+1) cap (P := H+cap+1) (by omega) (by intro i hl hu; rw [marks i (by omega) (by omega)]; exact rows.2.1)
  have pos : H+1+cap=H+cap+1 := by omega
  rw [pos] at b
  have c := keep (q (41+4*mode.val)) machine.reject (H+cap+1) (H+cap+1) U .stay (P := H+cap+1) le_rfl le_rfl (by rw [fence]; exact rows.2.2.2.1) rfl
  convert (a.append b).append c using 1; omega
/-- Finite row pins; mode contains one lifted bit or sticky EOF, never an address. -/
private theorem return_rows : ∀ mode : Fin 3, (∀ b, machine.step (q (8+8*mode.val)) (some b) = (q (8+8*mode.val),some b,.right)) ∧
    machine.step (q (8+8*mode.val)) none = (q (9+8*mode.val),none,.right) ∧
    machine.step (q (9+8*mode.val)) (some false) = (q (9+8*mode.val),some false,.right) ∧
    machine.step (q (9+8*mode.val)) none = (q (10+8*mode.val),none,.right) ∧ (∀ b, machine.step (q (10+8*mode.val)) (some b) = (q (10+8*mode.val),some b,.right)) ∧
    machine.step (q (10+8*mode.val)) none = (unpaid mode,none,.stay) := by decide
/-- Physical return across the actual register and counter boundaries. -/
private theorem return_path (T : Nat → Option Bool) (S z n : Nat) (mode : Fin 3) (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b) (right : T (S+z+n+3)=none) :
    Path (S+z+n+3) (n+z+3) ⟨q (9+8*mode.val),S+1,T⟩
      ⟨unpaid mode,S+z+n+3,T⟩ := by
  have rows := return_rows mode
  have a := sweepR (q (9+8*mode.val)) T (S+1) (z+1) (P := S+z+n+3) (by omega) (by
    intro i hl hu; rw [reg i (by omega) (by omega)]; exact rows.2.2.1)
  have eqL : S+1+(z+1)=S+z+2 := by omega
  rw [eqL] at a
  have b := keep (q (9+8*mode.val)) (q (10+8*mode.val)) (S+z+2) (S+z+3) T .right (P := S+z+n+3) (by omega) (by omega) (by rw [sep]; exact rows.2.2.2.1) rfl
  have c := sweepR (q (10+8*mode.val)) T (S+z+3) n (P := S+z+n+3) (by omega) (by
    intro i hl hu; obtain ⟨v,hv⟩ := assn i (by omega) (by omega)
    rw [hv]; exact rows.2.2.2.2.1 v)
  have eqR : S+z+3+n=S+z+n+3 := by omega
  rw [eqR] at c
  have d := keep (q (10+8*mode.val)) (unpaid mode) (S+z+n+3) (S+z+n+3) T .stay (P := S+z+n+3) le_rfl le_rfl (by rw [right]; exact rows.2.2.2.2.2) rfl
  convert ((a.append b).append c).append d using 1; omega
private def carryCost : List Bool → Nat → Nat
  | [], _ => 0
  | false :: _, r => r+1
  | true :: bs, r => 1+carryCost bs (r+1)
private theorem carry_rows : ∀ mode : Fin 3,
    machine.step (q (12+8*mode.val)) (some true) = (q (12+8*mode.val),some false,.left) ∧
    machine.step (q (12+8*mode.val)) (some false) = (q (13+8*mode.val),some true,.right) ∧
    ∀ b, machine.step (q (13+8*mode.val)) (some b) = (q (13+8*mode.val),some b,.right) := by decide
private theorem carry_path (T : Nat → Option Bool) (left r : Nat) (bs : List Bool) (mode : Fin 3) (digits : Body.Reads T left bs)
    (occ : ∀ i, left+bs.length < i → i < left+bs.length+r+1 → ∃ b, T i=some b) :
    Path (left+bs.length+r+1) (carryCost bs r)
      ⟨q (12+8*mode.val),left+bs.length,T⟩
      ⟨q ((if (Body.inc bs).2 then 12 else 13)+8*mode.val),
        if (Body.inc bs).2 then left else left+bs.length+r+1,Body.carryTape T left bs⟩ := by
  induction bs generalizing r T with
  | nil => simpa [carryCost,Body.inc,Body.carryTape] using
      Path.nil ⟨q (12+8*mode.val),left,T⟩ (by omega : left  ≤  left+0+r+1)
  | cons b bs ih =>
    obtain ⟨hb,hs⟩ := (Body.reads_cons T left b bs).1 digits
    cases b with
    | false =>
      let U := put T (left+bs.length+1) (some true)
      let R := left+(false::bs).length+r+1
      have a := hop (q (12+8*mode.val)) (q (13+8*mode.val)) (left+bs.length+1) (left+bs.length+2) T (some true) .right (P := R) (by dsimp [R]; omega) (by dsimp [R]; omega)
        (by rw [hb]; exact (carry_rows mode).2.1) rfl
      have b := sweepR (q (13+8*mode.val)) U (left+bs.length+2) r (P := R)
        (by dsimp [R]; omega) (by
          intro i hl hu
          obtain ⟨v,hv⟩ := occ i (by simp; omega) (by simp at *; omega)
          rw [show U i=some v by simp [U,put,show i≠left+bs.length+1 by omega,hv]]
          exact (carry_rows mode).2.2 v)
      have eqR : left+bs.length+2+r=R := by dsimp [R]; omega
      rw [eqR] at b
      simpa [carryCost,Body.inc,Body.carryTape,Body.put,U,put,R,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.append b
    | true =>
      let U := put T (left+bs.length+1) (some false)
      let R := left+(true::bs).length+r+1
      have a := hop (q (12+8*mode.val)) (q (12+8*mode.val)) (left+bs.length+1) (left+bs.length) T (some false) .left (P := R) (by dsimp [R]; omega) (by dsimp [R]; omega)
        (by rw [hb]; exact (carry_rows mode).1) (by simp [dest])
      have rest := ih U (r+1) (Body.reads_put_outside T left bs hs _ _ (by omega)) (by
        intro i hl hu
        by_cases hi : i=left+bs.length+1
        · exact ⟨false,by simp [U,put,hi]⟩
        · obtain ⟨v,hv⟩ := occ i (by simp; omega) (by simp at *; omega)
          exact ⟨v,by simp [U,put,hi,hv]⟩)
      have eqR : left+bs.length+(r+1)+1=R := by dsimp [R]; omega
      rw [eqR] at rest
      simpa [carryCost,Body.inc,Body.carryTape,Body.put,U,put,R,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using a.append rest
private theorem carry_cost_le (bs : List Bool) (r : Nat) : carryCost bs r  ≤  2*bs.length+r+1 := by
  induction bs generalizing r with
  | nil => simp [carryCost]
  | cons b bs ih => cases b <;> simp only [carryCost,List.length_cons] <;> have h := ih (r+1) <;> omega
private def modeOf (b : Bool) : Fin 3 := if b then ⟨1,by decide⟩ else ⟨0,by decide⟩
/-- Generic physical-or-virtual read and a complete return frame. -/
private theorem lift_path (T : Nat → Option Bool) (p S z n : Nat) (hps : p  ≤  S) (source : ∀ i, p  ≤  i → i < S → ∃ b, T i=some b) (eof : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none) (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b) (right : T (S+z+n+3)=none) :
    ∃ mode : Fin 3, (mode.val=2 ↔ p=S) ∧ (p < S → T p=some (InputRead.result mode)) ∧
      Path (S+z+n+3) (n+z+(S-p)+4)
        ⟨q 7,p,T⟩ ⟨unpaid mode,S+z+n+3,put T p none⟩ := by
  by_cases hlt : p < S
  · obtain ⟨b,hb⟩ := source p le_rfl hlt
    let U := put T p none
    have one := hop (q 7) (q (8+8*(modeOf b).val)) p (p+1) T none .right (P := S+z+n+3) (by omega) (by omega) (by rw [hb]; cases b <;> rfl) rfl
    have rows := return_rows (modeOf b)
    have a := sweepR (q (8+8*(modeOf b).val)) U (p+1) (S-p-1)
      (P := S+z+n+3) (by omega) (by
        intro i hl hu; obtain ⟨v,hv⟩ := source i (by omega) (by omega)
        have hvU : U i=some v := by simp [U,put,show i≠p by omega,hv]
        rw [hvU]; exact rows.1 v)
    have eqS : p+1+(S-p-1)=S := by omega
    rw [eqS] at a
    have ue : U S=none := by simp [U,put,show S≠p by omega,eof]
    have c := keep (q (8+8*(modeOf b).val)) (q (9+8*(modeOf b).val)) S (S+1) U .right (P := S+z+n+3) (by omega) (by omega) (by rw [ue]; exact rows.2.1) rfl
    have ret := return_path U S z n (modeOf b) (by intro i hl hu; simp [U,put,show i≠p by omega,reg i hl hu]) (by simp [U,put,show S+z+2≠p by omega,sep])
      (by intro i hl hu; obtain ⟨v,hv⟩ := assn i hl hu; exact ⟨v,by simp [U,put,show i≠p by omega,hv]⟩) (by simp [U,put,show S+z+n+3≠p by omega,right])
    refine ⟨modeOf b,by cases b <;> simp [modeOf] <;> omega,?_,?_⟩
    · intro _; cases b <;> simpa [InputRead.result,modeOf] using hb
    · convert ((one.append a).append c).append ret using 1; omega
  · have eq : p=S := by omega
    have one := keep (q 7) (q 25) S (S+1) T .right (P := S+z+n+3) (by omega) (by omega) (by rw [eof]; rfl) rfl
    have ret := return_path T S z n ⟨2,by decide⟩ reg sep assn right
    have unchanged : put T p none=T := by rw [eq,← eof,put_same]
    refine ⟨⟨2,by decide⟩,by simp [eq],by omega,?_⟩
    rw [unchanged,eq]
    convert one.append ret using 1; simp; omega
private theorem Path.widen {P Q t c d} (h : Path P t c d) (le : P  ≤  Q) : Path Q t c d := by
  induction h with
  | nil c hc => exact Path.nil c (hc.trans le)
  | cons e path ih => exact Path.cons ⟨e.before.trans le,e.after.trans le,e.row,e.move,e.tape⟩ ih
private theorem restore_path (T : Nat → Option Bool) (p S z P : Nat) (rstate sstate estate : Fin 64) (bit : Bool) (hp : p < S) (fit : S+z+1 ≤ P)
    (hole : T p=none) (source : ∀ i, p < i → i < S → ∃ b, T i=some b) (eof : T S=none) (reg : ∀ i, S < i → i < S+z+2 → T i=some false)
    (rr : machine.step rstate (some false)=(rstate,some false,.left)) (rb : machine.step rstate none=(sstate,none,.left))
    (sr : ∀ b, machine.step sstate (some b)=(sstate,some b,.left)) (sb : machine.step sstate none=(estate,some bit,.right)) :
    Path P (z+(S-p)+2) ⟨rstate,S+z+1,T⟩ ⟨estate,p+1,put T p (some bit)⟩ := by
  have a := sweepL rstate T S (z+1) (P := P) (by omega) (by intro i hl hu; rw [reg i hl (by omega)]; exact rr)
  have b := keep rstate sstate S (S-1) T .left (P := P) (by omega) (by omega) (by rw [eof]; exact rb) rfl
  have c := sweepL sstate T p (S-p-1) (P := P) (by omega) (by intro i hl hu; obtain ⟨v,hv⟩ := source i hl (by omega); rw [hv]; exact sr v)
  have eqS : p+(S-p-1)=S-1 := by omega
  rw [eqS] at c
  have d := hop sstate estate p (p+1) T (some bit) .right (P := P) (by omega) (by omega) (by rw [hole]; exact sb) rfl
  have pos : S+(z+1)=S+z+1 := by omega
  rw [pos] at a
  convert ((a.append b).append c).append d using 1; omega
private theorem advance_rows : ∀ mode : Fin 3, mode.val < 2 →
    machine.step (q (13+8*mode.val)) none=(q (14+8*mode.val),none,.left) ∧ (∀ b, machine.step (q (14+8*mode.val)) (some b)=(q (14+8*mode.val),some b,.left)) ∧
    machine.step (q (14+8*mode.val)) none=(q (15+8*mode.val),none,.left) ∧
    machine.step (q (15+8*mode.val)) (some false)=(q (15+8*mode.val),some false,.left) ∧
    machine.step (q (15+8*mode.val)) none=(q (32+mode.val),none,.left) ∧ (∀ b, machine.step (q (32+mode.val)) (some b)=(q (32+mode.val),some b,.left)) ∧
    machine.step (q (32+mode.val)) none=(q 7,some (InputRead.result mode),.right) := by decide
private theorem advance_path (T : Nat → Option Bool) (p S z n : Nat) (mode : Fin 3) (hm : mode.val < 2) (hp : p < S) (hole : T p=none)
    (source : ∀ i, p < i → i < S → ∃ b, T i=some b) (eof : T S=none) (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b) (right : T (S+z+n+3)=none) :
    Path (S+z+n+3) (n+z+(S-p)+4) ⟨q (13+8*mode.val),S+z+n+3,T⟩
      ⟨q 7,p+1,put T p (some (InputRead.result mode))⟩ := by
  have rows := advance_rows mode hm
  have a := keep (q (13+8*mode.val)) (q (14+8*mode.val)) (S+z+n+3) (S+z+n+2) T .left (P := S+z+n+3) le_rfl (by omega) (by rw [right]; exact rows.1) (by simp [dest])
  have b := sweepL (q (14+8*mode.val)) T (S+z+2) n (P := S+z+n+3) (by omega) (by intro i hl hu; obtain ⟨v,hv⟩ := assn i hl (by omega); rw [hv]; exact rows.2.1 v)
  have c := keep (q (14+8*mode.val)) (q (15+8*mode.val)) (S+z+2) (S+z+1) T .left (P := S+z+n+3) (by omega) (by omega) (by rw [sep]; exact rows.2.2.1) (by simp [dest])
  have d := restore_path T p S z (S+z+n+3) (q (15+8*mode.val)) (q (32+mode.val)) (q 7) (InputRead.result mode) hp (by omega) hole source eof reg
    rows.2.2.2.1 rows.2.2.2.2.1 rows.2.2.2.2.2.1 rows.2.2.2.2.2.2
  have pos : S+z+2+n=S+z+n+2 := by omega
  rw [pos] at b
  convert ((a.append b).append c).append d using 1; omega
private theorem finish_rows : ∀ mode : Fin 3, mode.val < 2 →
    machine.step (q (12+8*mode.val)) none=(q (35+mode.val),none,.left) ∧
    machine.step (q (35+mode.val)) (some false)=(q (35+mode.val),some false,.left) ∧
    machine.step (q (35+mode.val)) none=(q (37+mode.val),none,.left) ∧ (∀ b, machine.step (q (37+mode.val)) (some b)=(q (37+mode.val),some b,.left)) ∧
    machine.step (q (37+mode.val)) none=(q 56,some (InputRead.result mode),.right) := by decide
private theorem finish_physical (T : Nat → Option Bool) (p S z n : Nat) (mode : Fin 3) (hm : mode.val < 2) (hp : p < S) (hole : T p=none)
    (source : ∀ i, p < i → i < S → ∃ b, T i=some b) (eof : T S=none) (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none) :
    Path (S+z+n+3) (z+(S-p)+4) ⟨q (12+8*mode.val),S+z+2,T⟩
      ⟨q (if p+1=S then 57 else 58),p+1,put T p (some (InputRead.result mode))⟩ := by
  have rows := finish_rows mode hm
  have a := keep (q (12+8*mode.val)) (q (35+mode.val)) (S+z+2) (S+z+1) T .left (P := S+z+n+3) (by omega) (by omega) (by rw [sep]; exact rows.1) (by simp [dest])
  have b := restore_path T p S z (S+z+n+3) (q (35+mode.val)) (q (37+mode.val)) (q 56) (InputRead.result mode) hp (by omega) hole source eof reg
    rows.2.1 rows.2.2.1 rows.2.2.2.1 rows.2.2.2.2
  let U := put T p (some (InputRead.result mode))
  have c := keep (q 56) (q (if p+1=S then 57 else 58)) (p+1) (p+1) U .stay
    (P := S+z+n+3) (by omega) (by omega) (by
      by_cases he : p+1=S
      · simp only [he,if_true]
        rw [show U S=none by simp [U,put,show S≠p by omega,eof]]; rfl
      · obtain ⟨v,hv⟩ := source (p+1) (by omega) (by omega)
        rw [if_neg he,show U (p+1)=some v by simp [U,put,hv]]
        cases v <;> rfl) rfl
  convert (a.append b).append c using 1; omega
private theorem finish_virtual (T : Nat → Option Bool) (S z n : Nat) (eof : T S=none) (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none) :
    Path (S+z+n+3) (z+3) ⟨q 28,S+z+2,T⟩ ⟨q 57,S,T⟩ := by
  have a := keep (q 28) (q 54) (S+z+2) (S+z+1) T .left (P := S+z+n+3) (by omega) (by omega) (by rw [sep]; rfl) (by simp [dest])
  have b := sweepL (q 54) T S (z+1) (P := S+z+n+3) (by omega) (by intro i hl hu; rw [reg i hl (by omega)]; rfl)
  have pos : S+(z+1)=S+z+1 := by omega
  rw [pos] at b
  have c := keep (q 54) (q 57) S S T .stay (P := S+z+n+3) (by omega) (by omega) (by rw [eof]; rfl) rfl
  convert (a.append b).append c using 1; omega
private def draw (U : Nat → Option Bool) (S z n : Nat) (bs : List Bool) (p marks : Nat) (lift : Bool) : Nat → Option Bool := fun i =>
  let L := S+z+2
  let H := L+n+1
  if L < i ∧ i < H then some (bs[H-1-i]!)
  else if H < i ∧ i  ≤  H+marks then some true
  else if lift ∧ i=p ∧ i < S then none else U i
private theorem draw_reads (U : Nat → Option Bool) (S z n : Nat) (bs : List Bool) (p marks : Nat) (lift : Bool) (len : bs.length=n) :
    Body.Reads (draw U S z n bs p marks lift) (S+z+2) bs := by
  intro j hj
  have lo : S+z+2 < S+z+2+bs.length-j := by omega
  have hi : S+z+2+bs.length-j < S+z+2+n+1 := by omega
  have eq : S+z+2+n+1-1-(S+z+2+bs.length-j)=j := by omega
  simp only [draw]
  rw [if_pos ⟨lo,hi⟩,eq]
private theorem draw_carry (U : Nat → Option Bool) (S z n : Nat) (bs : List Bool) (p marks : Nat) (lift : Bool) (len : bs.length=n) :
    Body.carryTape (draw U S z n bs p marks lift) (S+z+2) bs =
      draw U S z n (Body.inc bs).1 p marks lift := by
  have digits := Body.carry_reads _ (S+z+2) bs (draw_reads U S z n bs p marks lift len)
  funext i
  by_cases inside : S+z+2 < i ∧ i < S+z+n+3
  · let j := S+z+2+n-i
    have jlt : j < (Body.inc bs).1.length := by rw [Body.inc_length]; dsimp [j]; omega
    have pos : S+z+2+(Body.inc bs).1.length-j=i := by rw [Body.inc_length]; dsimp [j]; omega
    rw [show Body.carryTape (draw U S z n bs p marks lift) (S+z+2) bs i =
        some ((Body.inc bs).1[j]!) by simpa only [pos] using digits j jlt]
    simp only [draw,show S+z+2+n+1=S+z+n+3 by omega,if_pos inside]
    congr 2
    omega
  · rw [Body.carry_frame _ _ _ i (by omega)]
    simp only [draw,show S+z+2+n+1=S+z+n+3 by omega,if_neg inside]
private theorem draw_pay (U : Nat → Option Bool) (S z n : Nat) (bs : List Bool) (p marks : Nat) (lift : Bool) :
    put (draw U S z n bs p marks lift) (S+z+n+3+marks+1) (some true)=
      draw U S z n bs p (marks+1) lift := by
  funext i
  by_cases hi : i=S+z+n+3+marks+1
  · subst i
    simp only [put,if_true,draw]
    rw [if_neg (by omega),if_pos (by omega)]
  · have range : (S+z+2+n+1 < i ∧ i ≤ S+z+2+n+1+(marks+1)) ↔ (S+z+2+n+1 < i ∧ i ≤ S+z+2+n+1+marks) := by omega
    simp only [put,if_neg hi,draw,range]
private theorem draw_restore (U : Nat → Option Bool) (S z n : Nat) (bs : List Bool) (p marks : Nat) (bit : Bool) (hp : p < S) (source : U p=some bit) :
    put (draw U S z n bs p marks true) p (some bit)=draw U S z n bs p marks false := by
  funext i
  by_cases hi : i=p
  · subst i
    simp [put,draw,show ¬ (S+z+2 < p ∧ p < S+z+2+n+1) by omega,
      show ¬ (S+z+2+n+1 < p ∧ p ≤ S+z+2+n+1+marks) by omega,source]
  · simp [put,draw,hi]
private theorem draw_lift (U : Nat → Option Bool) (S z n : Nat) (bs : List Bool) (p marks : Nat) (hp : p ≤ S) (eof : U S=none) :
    put (draw U S z n bs p marks false) p none=draw U S z n bs p marks true := by
  funext i
  by_cases hi : i=p
  · subst i
    by_cases last : p < S
    · simp [put,draw,show ¬ (S+z+2 < p ∧ p < S+z+2+n+1) by omega,
        show ¬ (S+z+2+n+1 < p ∧ p ≤ S+z+2+n+1+marks) by omega,last]
    · have eq : p=S := by omega
      simp [put,draw,eq,eof,show ¬ (S+z+2 < S ∧ S < S+z+2+n+1) by omega,
        show ¬ (S+z+2+n+1 < S ∧ S ≤ S+z+2+n+1+marks) by omega]
  · simp [put,draw,hi]
private theorem draw_low (U : Nat → Option Bool) (S z n : Nat) (bs : List Bool) (p marks i : Nat) (lift : Bool) (hi : i ≤ S+z+2) :
    draw U S z n bs p marks lift i=(if lift ∧ i=p ∧ i < S then none else U i) := by
  dsimp only [draw]
  rw [if_neg (by omega),if_neg (by omega)]
private theorem draw_high (U : Nat → Option Bool) (S z n : Nat) (bs : List Bool) (p marks : Nat) (lift : Bool) :
    draw U S z n bs p marks lift (S+z+n+3)=U (S+z+n+3) := by
  dsimp only [draw]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
private theorem draw_occupied (U : Nat → Option Bool) (S z n : Nat) (bs : List Bool) (p marks : Nat) (lift : Bool) :
    ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, draw U S z n bs p marks lift i=some b := by
  intro i hl hu
  exact ⟨_,by dsimp only [draw]; rw [if_pos (by omega)]⟩
private theorem draw_unlifted (U : Nat → Option Bool) (S z n : Nat) (bs : List Bool) (p p' marks : Nat) : draw U S z n bs p marks false=draw U S z n bs p' marks false := by
  funext i; simp only [draw,Bool.false_eq_true,false_and,if_false]
private theorem mode_correct (U : Nat → Option Bool) (p S : Nat) (b : Bool) (hp : p < S) (hb : U p=some b) : Target.mode U p S=modeOf b := by
  cases b <;> simp [Target.mode,modeOf,hb,show p≠S by omega]
private theorem read_draw (U : Nat → Option Bool) (S z n p marks : Nat) (bs : List Bool) (hp : p ≤ S) (source : ∀ i, p ≤ i → i < S → ∃ b, U i=some b)
    (eof : U S=none) (reg : ∀ i, S < i → i < S+z+2 → U i=some false) (sep : U (S+z+2)=none) (right : U (S+z+n+3)=none) :
    Path (S+z+n+3) (n+z+(S-p)+4)
      ⟨q 7,p,draw U S z n bs p marks false⟩
      ⟨unpaid (Target.mode U p S),S+z+n+3,draw U S z n bs p marks true⟩ := by
  let T := draw U S z n bs p marks false
  have low (i : Nat) (hi : i ≤ S+z+2) : T i=U i := by
    rw [show T i=draw U S z n bs p marks false i from rfl,draw_low U S z n bs p marks i false hi]
    simp
  obtain ⟨mode,hm,hb,path⟩ := lift_path T p S z n hp (by intro i hl hu; rw [low i (by omega)]; exact source i hl hu) (by rw [low S (by omega)]; exact eof)
    (by intro i hl hu; rw [low i (by omega)]; exact reg i hl hu) (by rw [low _ le_rfl]; exact sep) (draw_occupied U S z n bs p marks false)
    (by change draw U S z n bs p marks false (S+z+n+3)=none; rw [draw_high,right])
  have same : mode=Target.mode U p S := by
    by_cases last : p=S
    · apply Fin.ext
      have hv := hm.mpr last
      simpa [Target.mode,last] using hv
    · obtain ⟨b,hbit⟩ := source p le_rfl (by omega)
      have hread : InputRead.result mode=b := by
        have h := hb (by omega)
        rw [low p (by omega),hbit] at h
        exact (Option.some.inj h).symm
      have nonEOF : mode.val≠2 := by intro he; exact last (hm.mp he)
      rw [mode_correct U p S b (by omega) hbit]
      have unique : ∀ (m : Fin 3) (v : Bool), m.val≠2 → InputRead.result m=v → m=modeOf v := by decide
      exact unique mode b nonEOF hread
  rw [same,draw_lift U S z n bs p marks hp eof] at path
  exact path
private theorem draw_cells (U : Nat → Option Bool) (S z n p marks : Nat) (bs : List Bool) (hp : p  ≤  S) (source : ∀ i, p < i → i < S → ∃ b, U i=some b)
    (eof : U S=none) (reg : ∀ i, S < i → i < S+z+2 → U i=some false) (sep : U (S+z+2)=none) (right : U (S+z+n+3)=none) :
    let T := draw U S z n bs p marks true
    T p=none ∧ (∀ i, p < i → i < S → ∃ b, T i=some b) ∧ T S=none ∧ (∀ i, S < i → i < S+z+2 → T i=some false) ∧ T (S+z+2)=none ∧
    (∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b) ∧ T (S+z+n+3)=none := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,draw_occupied U S z n bs p marks true,?_⟩
  · rw [draw_low U S z n bs p marks p true (by omega)]
    by_cases last : p < S
    · simp [last]
    · have eq : p=S := by omega
      simp [eq,eof]
  · intro i hl hu; obtain ⟨b,hb⟩ := source i hl hu
    exact ⟨b,by rw [draw_low U S z n bs p marks i true (by omega),if_neg (by omega),hb]⟩
  · rw [draw_low U S z n bs p marks S true (by omega),if_neg (by omega),eof]
  · intro i hl hu
    rw [draw_low U S z n bs p marks i true (by omega),if_neg (by omega),reg i hl hu]
  · rw [draw_low U S z n bs p marks (S+z+2) true le_rfl,if_neg (by omega),sep]
  · rw [draw_high,right]
private theorem next_draw (U : Nat → Option Bool) (S z n p marks : Nat) (bs : List Bool) (hp : p  ≤  S) (source : ∀ i, p  ≤  i → i < S → ∃ b, U i=some b)
    (eof : U S=none) (reg : ∀ i, S < i → i < S+z+2 → U i=some false) (sep : U (S+z+2)=none) (right : U (S+z+n+3)=none) :
    ∃ t, t  ≤  2*(S+z+n+3)+8 ∧ Path (S+z+n+3) t
      ⟨q (13+8*(Target.mode U p S).val),S+z+n+3,draw U S z n bs p marks true⟩
      ⟨unpaid (Target.mode U (min (p+1) S) S),S+z+n+3,
        draw U S z n bs (min (p+1) S) marks true⟩ := by
  have cells := draw_cells U S z n p marks bs hp (by intro i hl hu; exact source i (by omega) hu) eof reg sep right
  by_cases last : p=S
  · have one := keep (q 29) (unpaid ⟨2,by decide⟩) (S+z+n+3) (S+z+n+3) (draw U S z n bs p marks true) .stay (P := S+z+n+3) le_rfl le_rfl (by rw [cells.2.2.2.2.2.2]; rfl) rfl
    refine ⟨1,by omega,?_⟩
    simpa [last,Target.mode,Nat.min_eq_right (by omega : S  ≤  S+1)] using one
  · have hm : (Target.mode U p S).val < 2 := by
      simp only [Target.mode,if_neg last]
      split_ifs <;> decide
    obtain ⟨bit,hbit⟩ := source p le_rfl (by omega)
    have bitpin : U p=some (InputRead.result (Target.mode U p S)) := by
      rw [mode_correct U p S bit (by omega) hbit]
      cases bit <;> simpa [InputRead.result,modeOf] using hbit
    have ad := advance_path (draw U S z n bs p marks true) p S z n (Target.mode U p S)
      hm (by omega) cells.1 cells.2.1 cells.2.2.1 cells.2.2.2.1 cells.2.2.2.2.1
      cells.2.2.2.2.2.1 cells.2.2.2.2.2.2
    rw [draw_restore U S z n bs p marks _ (by omega) bitpin,
      draw_unlifted U S z n bs p (p+1) marks] at ad
    have read := read_draw U S z n (p+1) marks bs (by omega) (by intro i hl hu; exact source i (by omega) hu) eof reg sep right
    refine ⟨(n+z+(S-p)+4)+(n+z+(S-(p+1))+4),by omega,?_⟩
    rw [Nat.min_eq_left (by omega : p+1  ≤  S)]
    exact ad.append read
private theorem finish_draw (U : Nat → Option Bool) (S z n p marks : Nat) (bs : List Bool) (hp : p  ≤  S) (source : ∀ i, p  ≤  i → i < S → ∃ b, U i=some b)
    (eof : U S=none) (reg : ∀ i, S < i → i < S+z+2 → U i=some false) (sep : U (S+z+2)=none) (right : U (S+z+n+3)=none) :
    ∃ t, t  ≤  S+z+n+7 ∧ Path (S+z+n+3) t
      ⟨q (12+8*(Target.mode U p S).val),S+z+2,draw U S z n bs p marks true⟩
      ⟨q (if min (p+1) S=S then 57 else 58),min (p+1) S,
        draw U S z n bs (min (p+1) S) marks false⟩ := by
  have cells := draw_cells U S z n p marks bs hp (by intro i hl hu; exact source i (by omega) hu) eof reg sep right
  by_cases last : p=S
  · have path := finish_virtual (draw U S z n bs p marks true) S z n
      cells.2.2.1 cells.2.2.2.1 cells.2.2.2.2.1
    have unlift : draw U S z n bs S marks true=draw U S z n bs S marks false := by
      funext i
      dsimp only [draw]
      split_ifs <;> first | rfl | omega
    refine ⟨z+3,by omega,?_⟩
    simpa [last,Target.mode,Nat.min_eq_right (by omega : S  ≤  S+1),unlift] using path
  · have hm : (Target.mode U p S).val < 2 := by
      simp only [Target.mode,if_neg last]
      split_ifs <;> decide
    obtain ⟨bit,hbit⟩ := source p le_rfl (by omega)
    have bitpin : U p=some (InputRead.result (Target.mode U p S)) := by
      rw [mode_correct U p S bit (by omega) hbit]
      cases bit <;> simpa [InputRead.result,modeOf] using hbit
    have path := finish_physical (draw U S z n bs p marks true) p S z n (Target.mode U p S)
      hm (by omega) cells.1 cells.2.1 cells.2.2.1 cells.2.2.2.1 cells.2.2.2.2.1
    rw [draw_restore U S z n bs p marks _ (by omega) bitpin,
      draw_unlifted U S z n bs p (p+1) marks] at path
    refine ⟨z+(S-p)+4,by omega,?_⟩
    simpa only [Nat.min_eq_left (by omega : p+1  ≤  S)] using path
private structure Arena (U : Nat → Option Bool) (S z n A F : Nat) : Prop where
  start_le : A  ≤  S
  room : S+z+n+3 < F
  source : ∀ i, A  ≤  i → i < S → ∃ b, U i=some b
  eof : U S=none
  reg : ∀ i, S < i → i < S+z+2 → U i=some false
  sep : U (S+z+2)=none
  right : U (S+z+n+3)=none
  scratch : ∀ i, S+z+n+3 < i → i < F → U i=none
  fence : U F=some false
private theorem row_draw (U : Nat → Option Bool) (S z n A F p r : Nat) (bs : List Bool) (arena : Arena U S z n A F) (hp : A  ≤  p ∧ p  ≤  S) (len : bs.length=n)
    (hr : r < F-(S+z+n+3)-1) :
    ∃ t, t  ≤  8*F+16 ∧ Path F t
      ⟨unpaid (Target.mode U p S),S+z+n+3,draw U S z n bs p r true⟩
      (if (Body.inc bs).2 then
        ⟨q (if min (p+1) S=S then 57 else 58),min (p+1) S,
          draw U S z n (Body.inc bs).1 (min (p+1) S) (r+1) false⟩
       else ⟨unpaid (Target.mode U (min (p+1) S) S),S+z+n+3,
          draw U S z n (Body.inc bs).1 (min (p+1) S) (r+1) true⟩) := by
  let H := S+z+n+3
  let cap := F-H-1
  have geo : H+cap+1=F := by dsimp [cap]; have h := arena.room; dsimp [H] at *; omega
  have cells := draw_cells U S z n p r bs hp.2 (by intro i hl hu; exact arena.source i (by omega) hu) arena.eof arena.reg arena.sep arena.right
  have pay := pay_path (draw U S z n bs p r true) H r cap (Target.mode U p S)
    cells.2.2.2.2.2.2 (by intro i hl hu; dsimp only [draw]; rw [if_neg (by dsimp [H] at *; omega),if_pos (by dsimp [H] at *; omega)])
    (by dsimp only [draw]; rw [if_neg (by dsimp [H] at *; omega),if_neg (by dsimp [H] at *; omega),if_neg (by dsimp [H] at *; omega)]
        exact arena.scratch _ (by dsimp [H]; omega) (by omega)) hr
  rw [geo,draw_pay] at pay
  let T := draw U S z n bs p (r+1) true
  have blank : T H=none := (draw_high U S z n bs p (r+1) true).trans arena.right
  have one := keep (paid (Target.mode U p S)) (q (12+8*(Target.mode U p S).val)) H (H-1) T .left (P := F) (by omega) (by omega) (by rw [blank]; exact (pay_rows _).2.2.2.2.2.2) rfl
  have carry := carry_path T (S+z+2) 0 bs (Target.mode U p S) (draw_reads U S z n bs p (r+1) true len) (by intro i hl hu; omega)
  have bound : S+z+2+bs.length+0+1=H := by dsimp [H]; omega
  rw [bound,draw_carry U S z n bs p (r+1) true len] at carry
  have head : S+z+2+bs.length=H-1 := by dsimp [H]; omega
  rw [head] at carry
  have price := carry_cost_le bs 0
  rw [len] at price
  have source : ∀ i, p  ≤  i → i < S → ∃ b, U i=some b := by
    intro i hl hu; exact arena.source i (hp.1.trans hl) hu
  cases over : (Body.inc bs).2 with
  | false =>
    simp only [over,Bool.false_eq_true,↓reduceIte] at carry ⊢
    obtain ⟨t,priceNext,next⟩ := next_draw U S z n p (r+1) (Body.inc bs).1 hp.2 source
      arena.eof arena.reg arena.sep arena.right
    refine ⟨(2*r+3)+1+carryCost bs 0+t,by have h := arena.room; dsimp [H] at *; omega,?_⟩
    exact ((pay.append one).append (carry.widen (by omega))).append (next.widen (by have h := arena.room; omega))
  | true =>
    simp only [over,↓reduceIte] at carry ⊢
    obtain ⟨t,priceNext,next⟩ := finish_draw U S z n p (r+1) (Body.inc bs).1 hp.2 source
      arena.eof arena.reg arena.sep arena.right
    refine ⟨(2*r+3)+1+carryCost bs 0+t,by have h := arena.room; dsimp [H] at *; omega,?_⟩
    exact ((pay.append one).append (carry.widen (by omega))).append (next.widen (by have h := arena.room; omega))
private theorem iter_succ (bs : List Bool) (r : Nat) :
    Body.iterBits bs (r+1)=(Body.inc (Body.iterBits bs r)).1 := by
  induction r generalizing bs with
  | zero => rfl
  | succ r ih => exact ih (Body.inc bs).1
private theorem iter_value (bs : List Bool) (r : Nat) (h : Body.value bs+r < 2^bs.length) :
    Body.value (Body.iterBits bs r)=Body.value bs+r := by
  induction r generalizing bs with
  | zero => simp [Body.iterBits]
  | succ r ih =>
    have no : (Body.inc bs).2=false := (Body.good_of_lt bs (r+1) h).1
    have step : Body.value (Body.inc bs).1=Body.value bs+1 := by
      have v := Body.inc_value bs
      simpa only [no,Bool.false_eq_true,↓reduceIte,Nat.add_zero] using v
    have rest := ih (Body.inc bs).1 (by rw [Body.inc_length,step]; omega)
    simpa only [Body.iterBits,step,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest
private def entry (U : Nat → Option Bool) (S z n A r : Nat) : Node :=
  ⟨unpaid (Target.mode U (Target.cursor A S r) S),S+z+n+3,Target.image U S z n A r r true⟩
private def observed (U : Nat → Option Bool) (S z n A r : Nat) : Node :=
  ⟨paid (Target.mode U (Target.cursor A S r) S),S+z+n+3,Target.image U S z n A r (r+1) true⟩
private def ended (U : Nat → Option Bool) (S z n A r : Nat) : Node :=
  ⟨q (if Target.cursor A S r=S then 57 else 58),Target.cursor A S r,Target.image U S z n A r r false⟩
private theorem image_draw (U : Nat → Option Bool) (S z n A r marks : Nat) (lift : Bool) :
    Target.image U S z n A r marks lift=
      draw U S z n (Body.iterBits (List.replicate n false) r) (Target.cursor A S r) marks lift := rfl
private theorem cursor_succ (A S r : Nat) : Target.cursor A S (r+1)=min (Target.cursor A S r+1) S := by
  unfold Target.cursor; omega
private theorem step_row (U : Nat → Option Bool) (S z n A F r : Nat) (arena : Arena U S z n A F) (hr : r < F-(S+z+n+3)-1) :
    ∃ t, t  ≤  8*F+16 ∧ Path F t (entry U S z n A r)
      (if (Body.inc (Body.iterBits (List.replicate n false) r)).2 then ended U S z n A (r+1)
       else entry U S z n A (r+1)) := by
  obtain ⟨t,price,path⟩ := row_draw U S z n A F (Target.cursor A S r) r (Body.iterBits (List.replicate n false) r) arena (by have h := arena.start_le; unfold Target.cursor; omega)
    (by rw [Body.iter_length,List.length_replicate]) hr
  refine ⟨t,price,?_⟩
  simpa only [entry,ended,image_draw,iter_succ,cursor_succ] using path
private theorem current_value (n r : Nat) (hr : r < 2^n) :
    Body.value (Body.iterBits (List.replicate n false) r)=r := by
  simpa only [Body.zero_value,Nat.zero_add] using
    iter_value (List.replicate n false) r (by simp only [Body.zero_value,List.length_replicate,Nat.zero_add]; exact hr)
private theorem before_overflow (n r : Nat) (hr : r+1 < 2^n) : (Body.inc (Body.iterBits (List.replicate n false) r)).2=false := by
  apply (Body.good_of_lt (Body.iterBits (List.replicate n false) r) 1 ?_).1
  rw [current_value n r (by omega),Body.iter_length,List.length_replicate]
  exact hr
private theorem last_overflow (n r : Nat) (hr : r < 2^n) (last : r+1=2^n) : (Body.inc (Body.iterBits (List.replicate n false) r)).2=true := by
  have inc := Body.inc_value (Body.iterBits (List.replicate n false) r)
  have limit := Body.value_lt (Body.inc (Body.iterBits (List.replicate n false) r)).1
  rw [Body.inc_length,Body.iter_length,List.length_replicate] at limit
  rw [current_value n r hr,Body.iter_length,List.length_replicate] at inc
  cases no : (Body.inc (Body.iterBits (List.replicate n false) r)).2
  · rw [no] at inc; simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero] at inc; omega
  · rfl
private theorem unpaid_orbit (U : Nat → Option Bool) (S z n A F r : Nat) (arena : Arena U S z n A F) (hr : r < 2^n) (cap : r  ≤  F-(S+z+n+3)-1) :
    ∃ t, t  ≤  r*(8*F+16) ∧ Path F t (entry U S z n A 0) (entry U S z n A r) := by
  induction r with
  | zero => exact ⟨0,by omega,Path.nil _ (Nat.le_of_lt arena.room)⟩
  | succ r ih =>
    obtain ⟨t,ht,path⟩ := ih (by omega) (by omega)
    obtain ⟨u,hu,next⟩ := step_row U S z n A F r arena (by omega)
    rw [before_overflow n r hr] at next
    simp only [Bool.false_eq_true,↓reduceIte] at next
    refine ⟨t+u,?_,path.append next⟩
    calc
      t+u  ≤  r*(8*F+16)+(8*F+16) := Nat.add_le_add ht hu
      _ = (r+1)*(8*F+16) := by ring
private theorem Path.wait {P : Nat} (c : Node) (hc : c.head  ≤  P) (rows : ∀ b, machine.step c.state b=(c.state,b,.stay)) (t : Nat) : Path P t c c := by
  induction t with
  | zero => exact Path.nil c hc
  | succ t ih =>
    have one := keep c.state c.state c.head c.head c.tape .stay hc hc (rows _) rfl
    simpa only [Nat.add_comm 1 t] using one.append ih
private theorem inert_rows : ∀ s : Fin 64, s=q 40 ∨ s=q 57 ∨ s=q 58 →
    ∀ b, machine.step s b=(s,b,.stay) := by decide
private theorem pay_row (U : Nat → Option Bool) (S z n A F r : Nat) (arena : Arena U S z n A F) (hr : r < F-(S+z+n+3)-1) :
    Path F (2*r+3) (entry U S z n A r) (observed U S z n A r) := by
  let H := S+z+n+3
  let cap := F-H-1
  have geo : H+cap+1=F := by dsimp [cap,H]; have h := arena.room; omega
  rw [entry,observed,image_draw,image_draw]
  have path := pay_path (draw U S z n (Body.iterBits (List.replicate n false) r)
      (Target.cursor A S r) r true) H r cap (Target.mode U (Target.cursor A S r) S) ((draw_high _ _ _ _ _ _ _ _).trans arena.right)
    (by intro i hl hu; dsimp only [draw]; rw [if_neg (by dsimp [H] at *; omega),if_pos (by dsimp [H] at *; omega)])
    (by dsimp only [draw]; rw [if_neg (by dsimp [H] at *; omega),if_neg (by dsimp [H] at *; omega),if_neg (by dsimp [H] at *; omega)]
        exact arena.scratch _ (by dsimp [H]; omega) (by omega)) hr
  rwa [geo,draw_pay] at path
private theorem cut_row (U : Nat → Option Bool) (S z n A F : Nat) (arena : Arena U S z n A F) :
    let cap := F-(S+z+n+3)-1
    Path F (cap+2) (entry U S z n A cap)
      ⟨machine.reject,F,Target.image U S z n A cap cap true⟩ := by
  let H := S+z+n+3
  let cap := F-H-1
  have geo : H+cap+1=F := by dsimp [cap,H]; have h := arena.room; omega
  dsimp only
  rw [entry,image_draw]
  have path := cutoff_path (draw U S z n (Body.iterBits (List.replicate n false) cap)
      (Target.cursor A S cap) cap true) H cap (Target.mode U (Target.cursor A S cap) S) ((draw_high _ _ _ _ _ _ _ _).trans arena.right)
    (by intro i hl hu; dsimp only [draw]; rw [if_neg (by dsimp [H] at *; omega),if_pos (by dsimp [H] at *; omega)])
    (by dsimp only [draw]; rw [if_neg (by dsimp [H] at *; omega),if_neg (by dsimp [H] at *; omega),if_neg (by dsimp [H] at *; omega)]
        rw [geo]; exact arena.fence)
  rwa [geo] at path
private theorem price_bound (F cap r t u : Nat) (cap_le : cap  ≤  F) (row_le : r  ≤  cap) (ht : t  ≤  r*(8*F+16)) (hu : u  ≤  8*F+16) : t+u  ≤  64*(F+1)^2 := by
  have mul := Nat.mul_le_mul_right (8*F+16) (by omega : r+1  ≤  F+1)
  nlinarith
/-- The frozen general orbit, on the literal SAME finite row table. The theorem
is conditional on a real tape arena; raw transport is a separate obligation. -/
theorem kernel : Target.Kernel := by
  intro N B S z n A F U _hA hAS room fit source eof reg sep right scratch fence
  dsimp only
  intro hH
  let H := S+z+n+3
  let cap := F-H-1
  let arena : Arena U S z n A F := ⟨hAS,room,source,eof,reg,sep,right,scratch,fence⟩
  have cap_le : cap  ≤  F := by dsimp [cap]; omega
  have hc : embed (N := N) (B := B) (entry U S z n A 0) hH =
      ⟨unpaid (Target.mode U A S),⟨H,hH⟩,fun i => Target.image U S z n A 0 0 true i.val⟩ := by
    have cursor : Target.cursor A S 0=A := by simp [Target.cursor,Nat.min_eq_left hAS]
    simp only [embed,entry,cursor,H]
  refine ⟨64*(F+1)^2,le_rfl,?_,?_⟩
  · intro r hr
    have hrpow : r < 2^n := (Nat.lt_min.mp hr).1
    have hrcap : r < cap := (Nat.lt_min.mp hr).2
    obtain ⟨t,ht,path⟩ := unpaid_orbit U S z n A F r arena hrpow (by omega)
    have paidPath := path.append (pay_row U S z n A F r arena hrcap)
    have he := paidPath.execute fit
    rw [hc] at he
    refine ⟨t+(2*r+3),price_bound F cap r t (2*r+3) cap_le (by omega) ht (by omega),?_⟩
    exact he
  · by_cases fits : 2^n ≤ cap
    · rw [if_pos fits]
      have pos : 0 < 2^n := by positivity
      let r := 2^n-1
      have hr : r < 2^n := by dsimp [r]; omega
      obtain ⟨t,ht,path⟩ := unpaid_orbit U S z n A F r arena hr (by dsimp [r,cap,H] at *; omega)
      obtain ⟨u,hu,next⟩ := step_row U S z n A F r arena (by dsimp [r,cap,H] at *; omega)
      rw [last_overflow n r hr (by dsimp [r]; omega)] at next
      simp only [↓reduceIte] at next
      have last : r+1=2^n := by dsimp [r]; omega
      rw [last] at next
      have pathEnd := path.append next
      have price := price_bound F cap r t u cap_le (by dsimp [r,cap,H] at *; omega) ht hu
      have idle := Path.wait (ended U S z n A (2^n)) pathEnd.bounds.2 (inert_rows _ (by dsimp [ended]; split_ifs <;> simp)) (64*(F+1)^2-(t+u))
      have padded := pathEnd.append idle
      have clock : t+u+(64*(F+1)^2-(t+u))=64*(F+1)^2 := by omega
      rw [clock] at padded
      have he := padded.execute fit
      rw [hc] at he
      exact ⟨lt_of_le_of_lt padded.bounds.2 fit,he⟩
    · rw [if_neg fits]
      have hr : cap < 2^n := by dsimp [cap,H] at *; omega
      obtain ⟨t,ht,path⟩ := unpaid_orbit U S z n A F cap arena hr le_rfl
      have pathEnd := path.append (cut_row U S z n A F arena)
      have hu : cap+2  ≤  8*F+16 := by omega
      have price := price_bound F cap cap t (cap+2) cap_le le_rfl ht hu
      have idle := Path.wait ⟨machine.reject,F,Target.image U S z n A cap cap true⟩ pathEnd.bounds.2 (inert_rows _ (Or.inl rfl)) (64*(F+1)^2-(t+(cap+2)))
      have padded := pathEnd.append idle
      have clock : t+(cap+2)+(64*(F+1)^2-(t+(cap+2)))=64*(F+1)^2 := by omega
      rw [clock] at padded
      have he := padded.execute fit
      rw [hc] at he
      exact ⟨fit,he⟩
open Pnp4.Frontier.ContractExpansion Pnp4.Frontier Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Runtime discovers the source cursor by crossing three real blank boundaries
and the consumed gamma trail. No numeric parameter below occurs in a row. -/
private theorem seek_path (T : Nat → Option Bool) (p S z n : Nat) (hp : 2 ≤ p) (hps : p ≤ S) (hole : T (p-2)=none) (marker : T (p-1)=some true)
    (source : ∀ i, p ≤ i → i < S → ∃ b, T i=some b) (eof : T S=none) (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b) (right : T (S+z+n+3)=none) :
    Path (S+z+n+3) (n+z+(S-p)+7) ⟨q 2,S+z+n+3,T⟩ ⟨q 7,p,T⟩ := by
  let P := S+z+n+3
  have a := keep (q 2) (q 3) P (P-1) T .left (P := P) le_rfl (by omega) (by rw [right]; rfl) rfl
  have b := sweepL (q 3) T (S+z+2) n (P := P) (by dsimp [P]; omega) (by
    intro i hl hu; obtain ⟨v,hv⟩ := assn i hl (by omega)
    rw [hv]; cases v <;> rfl)
  have ab : P-1=S+z+2+n := by dsimp [P]; omega
  rw [ab] at a
  have c := keep (q 3) (q 4) (S+z+2) (S+z+1) T .left (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [sep]; rfl) (by simp [dest])
  have d := sweepL (q 4) T S (z+1) (P := P) (by dsimp [P]; omega) (by
    intro i hl hu; rw [reg i hl (by omega)]; rfl)
  have e := keep (q 4) (q 5) S (S-1) T .left (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [eof]; rfl) rfl
  have f := sweepL (q 5) T (p-2) (S-p+1) (P := P) (by dsimp [P]; omega) (by
    intro i hl hu
    have occ : ∃ b, T i=some b := by
      by_cases hi : i=p-1
      · exact ⟨true,hi ▸ marker⟩
      · exact source i (by omega) (by omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  have ef : p-2+(S-p+1)=S-1 := by omega
  rw [ef] at f
  have g := keep (q 5) (q 6) (p-2) (p-1) T .right (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [hole]; rfl) (by simp [dest]; omega)
  have h := keep (q 6) (q 7) (p-1) p T .right (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [marker]; rfl) (by simp [dest]; omega)
  have eqD : S+(z+1)=S+z+1 := by omega
  rw [eqD] at d
  convert ((((((a.append b).append c).append d).append e).append f).append g).append h using 1; omega
private theorem seed_path (T : Nat → Option Bool) (h n : Nat) (marks : ∀ i, h ≤ i → i < h+n → T i=some true) (endBlank : T (h+n)=none) :
    Path (h+n) (n+1) ⟨q 1,h,T⟩ ⟨q 2,h+n,Body.clear T h n⟩ := by
  induction n generalizing T h with
  | zero =>
    have one := hop (q 1) (q 2) h h T none .stay (P := h) le_rfl le_rfl (by rw [show T h=none by simpa using endBlank]; rfl) rfl
    have hb : T h=none := by simpa using endBlank
    rw [← hb,put_same] at one
    have hz : Body.clear T h 0=T := by funext i; simp [Body.clear]
    simpa [hz] using one
  | succ n ih =>
    have hb := marks h le_rfl (by omega)
    let U := put T h (some false)
    have one := hop (q 1) (q 1) h (h+1) T (some false) .right (P := h+(n+1)) (by omega) (by omega) (by rw [hb]; rfl) rfl
    have rest := ih U (h+1) (by intro i h1 h2; dsimp [U]; rw [put,if_neg (by omega)]; exact marks i (by omega) (by omega))
      (by dsimp [U]; rw [put,if_neg (by omega)]; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using endBlank)
    have eqP : h+1+n=h+(n+1) := by omega
    rw [eqP] at rest
    have clearstep : Body.clear (put T h (some false)) (h+1) n = Body.clear T h (n+1) := Body.clear_step T h n
    simpa only [U,clearstep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
/-- Installation consumes actual unary marks, without assuming precleared scratch. -/
private theorem install_path (T : Nat → Option Bool) (left n : Nat) (startBlank : T left=none) (marks : ∀ i, left < i → i < left+n+1 → T i=some true)
    (endBlank : T (left+n+1)=none) :
    Path (left+n+1) (n+2) ⟨machine.start,left,T⟩
      ⟨q 2,left+n+1,Body.clear T (left+1) n⟩ := by
  have one := hop machine.start (q 1) left (left+1) T none .right (P := left+n+1) (by omega) (by omega) (by rw [startBlank]; rfl) rfl
  rw [← startBlank,put_same] at one
  have rest := seed_path T (left+1) n (by intro i h1 h2; exact marks i (by omega) (by omega)) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using endBlank)
  have eqP : left+1+n=left+n+1 := by omega
  rw [eqP] at rest
  simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using one.append rest
/-- Initial unary-to-zero installation on this exact reader table. -/
private theorem install_exact {N B : Nat} (left n : Nat) (c : Config machine.stateCount N B) (hp : left+n+1 < tapeLength N B) (hq : c.state=machine.start) (hh : c.head.val=left)
    (hl : c.tape ⟨left,by omega⟩=none) (hr : c.tape ⟨left+n+1,hp⟩=none) (marks : ∀ i : Fin (tapeLength N B), left < i.val → i.val < left+n+1 → c.tape i=some true) :
    machine.run (n+2) c = ⟨q 2,⟨left+n+1,hp⟩,Body.installedTape c.tape left n⟩ := by
  let T := Body.extend c.tape
  have hleft : T left=none := by simpa [T,Body.extend,show left < tapeLength N B by omega] using hl
  have hright : T (left+n+1)=none := by simpa [T,Body.extend,hp] using hr
  have path := install_path T left n hleft (by
    intro i h1 h2
    have hi : i < tapeLength N B := by omega
    simpa [T,Body.extend,hi] using marks ⟨i,hi⟩ h1 h2) hright
  have he := path.execute hp
  have hc : embed (N := N) (B := B) ⟨machine.start,left,T⟩ (by change left < tapeLength N B; omega) = c := by
    apply Config.ext_parts hq.symm (Fin.ext hh.symm)
    funext i; exact Body.extend_read c.tape i
  rw [hc] at he
  rw [he]
  apply Config.ext_parts
  · rfl
  · rfl
  funext i
  change Body.clear T (left+1) n i.val = Body.installedTape c.tape left n i
  simp only [Body.clear,Body.installedTape]
  have hi : left+1 ≤ i.val ↔ left < i.val := by omega
  have heq : left+1+n=left+n+1 := by omega
  simp only [hi,heq]
  split_ifs <;> first | rfl | exact Body.extend_read c.tape i
private theorem draw_zero (U : Nat → Option Bool) (S z n p : Nat) (digits : ∀ i, S+z+2 < i → i < S+z+n+3 → U i=some false) :
    draw U S z n (List.replicate n false) p 0 false=U := by
  funext i
  by_cases inside : S+z+2 < i ∧ i < S+z+n+3
  · rw [digits i inside.1 inside.2]
    simp only [draw,show S+z+2+n+1=S+z+n+3 by omega,if_pos inside]
    simp only [List.getElem!_eq_getElem?_getD,List.getElem?_replicate]
    split_ifs <;> rfl
  · simp only [draw,show S+z+2+n+1=S+z+n+3 by omega,if_neg inside]
    rw [if_neg (by omega),if_neg (by simp)]
private theorem raw_entry_parsed (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : AcceptedBody.Parsed k} (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w)=true) (hn : 3  ≤  pr.2.n) :
    ∃ z, 2  ≤  z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z → 9+2*z  ≤  a+m →
        ∃ (T : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          T  ≤  144*(pairLength a m+1)^2 ∧
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
          Arena U (a+m) z pr.2.n (9+2*z) (FixedRawLengthFence.fencePos (pairLength a m)) ∧
          rawMachine.run T (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight machine (embed (entry U (a+m) z pr.2.n (9+2*z) 0) hH)) := by
  obtain ⟨_hnr,z,C,qp,hS,hz,hg,_hh,_hC,_hfirst,success,_reject⟩ := raw_fenced_countdown_parsed_target k x w hpr htag hn
  refine ⟨z,hz,hg,?_⟩
  intro cap full
  obtain ⟨price,he⟩ := success (Nat.le_of_lt cap)
  obtain ⟨T,hT,first,arrived⟩ := Body.first_accept_whole FixedRawLengthFence.prefixed (initialConfig FixedRawLengthFence.prefixed _ (encodePair x w)) _ _ he rfl
  let B := FixedRawLengthFence.allocation (pairLength a m)
  let S := a+m
  let n := pr.2.n
  let L := S+z+2
  let H := S+z+n+3
  let A := 9+2*z
  let tape := FixedRawLengthFence.countdownTape B x w z 0 n
  let U := Body.extend (Body.installedTape tape L n)
  have resource := (FixedRawLengthFence.resource_bounds (pairLength a m)).1
  have cells := FixedRawLengthFence.countdown_success_cells x w hg resource (Nat.le_of_lt cap)
  obtain ⟨room,scratch,hF,fence⟩ := raw_budget_cells x w hg cap
  have hH : H < tapeLength (pairLength a m) B := room.trans hF
  have hR : L+n+1 < tapeLength (pairLength a m) B := by dsimp [L,H] at *; omega
  have hL : L < tapeLength (pairLength a m) B := by omega
  have rearr : a+m+2+z=L := by dsimp [L,S]; omega
  have arrivalEq : (⟨FixedRawLengthFence.prefixed.accept,⟨a+m+2+z,hS⟩,tape⟩ : Config FixedRawLengthFence.prefixed.stateCount (pairLength a m) B)=
      ⟨FixedRawLengthFence.prefixed.accept,⟨L,hL⟩,tape⟩ := Config.ext_parts rfl (Fin.ext rearr) rfl
  rw [arrivalEq] at arrived
  have read (i : Nat) (hi : i < tapeLength (pairLength a m) B) : U i=Body.installedTape tape L n ⟨i,hi⟩ := by simp [U,Body.extend,hi]
  have frame (i : Nat) (hi : i  ≤  L) : U i=tape ⟨i,by dsimp [L,H] at *; omega⟩ := by
    rw [read i (by dsimp [L,H] at *; omega),Body.installedTape,if_neg (by change ¬ (L < i ∧ i < L+n+1); omega)]
  have src (i : Nat) (lo : A  ≤  i) (hi : i < S) : ∃ b, U i=some b := by
    rw [frame i (by dsimp [L,S]; omega)]
    exact ⟨_,Body.raw_source_after_header x w hg resource (Nat.le_of_lt cap) _ (by change 8+2*z+1 ≤ i; dsimp [A] at lo; omega) hi⟩
  have eof : U S=none := by
    rw [frame S (by dsimp [L]; omega)]
    dsimp [tape,FixedRawLengthFence.countdownTape]
    rw [if_neg (by dsimp [S]; omega)]
    simp [FixedGammaTargetUnaryCountdown.loopTape,S]
  have reg : ∀ i, S < i → i < S+z+2 → U i=some false := by
    intro i lo hi
    rw [frame i (by dsimp [L]; omega)]
    exact cells.2.1 (i-S-1) (by omega) _ (by dsimp [S]; omega)
  have sep : U L=none := by rw [frame L le_rfl]; exact cells.2.2.1 _ (by dsimp [L,S]; omega)
  have digits : ∀ i, L < i → i < H → U i=some false := by
    intro i lo hi
    rw [read i (by omega),Body.installedTape,if_pos (by dsimp [H,L] at *; omega)]
  have right : U H=none := by rw [read H hH]; exact scratch _ le_rfl room
  have arena : Arena U S z n A (FixedRawLengthFence.fencePos (pairLength a m)) := by
    refine ⟨full,room,src,eof,reg,sep,right,?_,?_⟩
    · intro i lo hi; rw [read i (lt_of_lt_of_le hi (Nat.le_of_lt hF))]; exact scratch _ (by change a+m+z+pr.2.n+3 ≤ i; dsimp [H,S,n] at lo; omega) hi
    · rw [read _ hF]; exact fence
  have walk : FixedGammaTargetPayloadExhaustion.termWalk S z=z := by
    unfold FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk; dsimp [S,A] at *; omega
  have low (i : Nat) (hi : i < S) : U i=FixedGammaTargetPayloadExhaustion.finishTape B x w z ⟨i,by omega⟩ := by
    rw [frame i (by dsimp [L]; omega)]
    exact cells.1 _ hi
  have seek := seek_path U A S z n (by dsimp [A]; omega) full
    (by rw [low _ (by dsimp [A,S]; omega)]; unfold FixedGammaTargetPayloadExhaustion.finishTape
        rw [walk,if_pos (by dsimp [A]; omega)])
    (by rw [low _ (by dsimp [A,S]; omega)]; unfold FixedGammaTargetPayloadExhaustion.finishTape
        rw [walk,if_neg (by dsimp [A]; omega),if_pos (by dsimp [A]; omega)])
    src eof reg sep (by intro i lo hi; exact ⟨false,digits i lo hi⟩) right
  have readPath := read_draw U S z n A 0 (List.replicate n false) full src eof reg sep right
  rw [draw_zero U S z n A digits] at readPath
  have path := seek.append readPath
  have runtime := path.execute hH
  have word : Target.cursor A S 0=A := by change min (A+0) S=A; rw [Nat.add_zero]; exact Nat.min_eq_left full
  have target : draw U S z n (List.replicate n false) A 0 true=Target.image U S z n A 0 0 true := by rw [image_draw,word]; rfl
  change machine.run (n+z+(S-A)+7+(n+z+(S-A)+4)) (embed ⟨q 2,H,U⟩ hH)=
    ⟨unpaid (Target.mode U A S),⟨H,hH⟩,fun i => draw U S z n (List.replicate n false) A 0 true i.val⟩ at runtime
  rw [target] at runtime
  have install := install_exact L n ⟨machine.start,⟨L,hL⟩,tape⟩ hR rfl rfl (cells.2.2.1 _ (by dsimp [L,S]; omega))
    (by exact cells.2.2.2.2.1 _ (by change a+m+3+z+pr.2.n ≤ L+n+1; dsimp [L,S,n]; omega) (by change L+n+1 < FixedRawLengthFence.fencePos (pairLength a m); dsimp [L,S,n]; omega))
    (by intro i lo hi; exact cells.2.2.2.1 i (by dsimp [L,S] at *; omega) (by dsimp [L,S] at *; omega))
  have hand := FixedRawLengthFence.prefixed.seq_handoff machine (initialConfig FixedRawLengthFence.prefixed B (encodePair x w)) first (by rw [arrived])
    (n+2+InputRead.readClock n z (S-A))
  rw [arrived,machine.run_add,install] at hand
  have clocks : n+z+(S-A)+7+(n+z+(S-A)+4)=InputRead.readClock n z (S-A) := by unfold InputRead.readClock; omega
  rw [clocks] at runtime
  have start : embed (N := pairLength a m) (B := B) ⟨q 2,H,U⟩ hH=
      ⟨q 2,⟨L+n+1,hR⟩,Body.installedTape tape L n⟩ := by
    apply Config.ext_parts
    · rfl
    · apply Fin.ext; change H=L+n+1; dsimp [H,L]; omega
    · funext i; exact Body.extend_read _ i
  rw [start] at runtime
  rw [runtime] at hand
  have gammaBound := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z hg).1
  have nBound : n  ≤  3*pairLength a m := by
    dsimp [FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos,pairLength] at cap ⊢; dsimp [n] at *; omega
  have time : T+n+2+InputRead.readClock n z (S-A) ≤ 144*(pairLength a m+1)^2 := by
    have tBound : T ≤ 128*(pairLength a m+1)^2 := hT.trans price
    have pair : S ≤ pairLength a m := by dsimp [S]; simp only [pairLength]; omega
    have zg : z ≤ pairLength a m := by dsimp [S] at pair; omega
    have sub : S-A ≤ pairLength a m := (Nat.sub_le _ _).trans pair
    unfold InputRead.readClock
    nlinarith only [tBound,nBound,zg,sub]
  refine ⟨T+n+2+InputRead.readClock n z (S-A),hH,time,arena,?_⟩
  simpa only [entry,embed,word,U,S,n,L,H,A,B,tape,Nat.add_assoc] using hand
/-- Same-table raw orbit for every supported parsed body; cutoff uses no content premise. -/
theorem raw_body (k : Nat) : BodyTarget.Orbit k := by
  intro a m x w pr parsed tag hn
  obtain ⟨z,hz,gamma,stage⟩ := raw_entry_parsed k x w parsed tag hn
  refine ⟨z,hz,gamma,?_⟩
  intro cap full
  obtain ⟨Tpre,hH,prePrice,arena,pre⟩ := stage cap full
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let n := pr.2.n
  let A := 9+2*z
  let F := FixedRawLengthFence.fencePos R
  let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape B x w z 0 n) (S+z+2) n)
  obtain ⟨_room,_scratch,hF,_fence⟩ := raw_budget_cells x w gamma cap
  obtain ⟨Tb,bodyPrice,paidRows,finish⟩ := kernel R B S z n A F U (by dsimp [A]; omega) full
    arena.room hF arena.source arena.eof arena.reg arena.sep arena.right arena.scratch arena.fence hH
  have same : embed (N := R) (B := B) (entry U S z n A 0) hH=
      ⟨unpaid (Target.mode U A S),⟨S+z+n+3,hH⟩,fun i => Target.image U S z n A 0 0 true i.val⟩ := by
    have word : Target.cursor A S 0=A := by change min (A+0) S=A; rw [Nat.add_zero]; exact Nat.min_eq_left full
    simp only [embed,entry,word]
  rw [← same] at paidRows finish
  have replay (t : Nat) : rawMachine.run (Tpre+t) (initialConfig rawMachine B (encodePair x w)) =
      FixedRawLengthFence.prefixed.seqEmbedRight machine (machine.run t (embed (entry U S z n A 0) hH)) := by
    rw [rawMachine.run_add,pre]
    exact FixedRawLengthFence.prefixed.seq_run_right machine _ t
  have price : Tpre+Tb  ≤  2048*(R+1)^2 := by
    dsimp [F,FixedRawLengthFence.fencePos] at bodyPrice
    change Tpre ≤ 144*(R+1)^2 at prePrice
    nlinarith only [prePrice,bodyPrice]
  refine ⟨Tpre+Tb,hH,price,?_,?_⟩
  · intro r hr
    obtain ⟨t,ht,run⟩ := paidRows r hr
    exact ⟨Tpre+t,by omega,by rw [replay,run]⟩
  · by_cases fits : 2^n ≤ F-(S+z+n+3)-1
    · rw [if_pos fits] at finish ⊢
      obtain ⟨hp,run⟩ := finish
      exact ⟨hp,by rw [replay,run]⟩
    · rw [if_neg fits] at finish ⊢
      obtain ⟨hf,run⟩ := finish
      exact ⟨hf,by rw [replay,run]⟩
/-- Connected raw accepted orbit on this exact table and allocation. Every row
is paid; the final full Config is the real next-field cursor, including EOF. -/
theorem raw_accepted (k : Nat) : RawTarget.AcceptedOrbit k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,table,_⟩ := AcceptedBody.exact k x w accepted
  refine ⟨pr,parsed,table,?_⟩
  intro hn
  have semantic : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=true := by
    have h := accepted
    unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at h
    split at h
    · rename_i shape; cases shape; rwa [AcceptedBody.concat_eq_append] at h
    · contradiction
  have tag : FixedContentTagGate.tagMatches (Fin.append x w)=true := by
    have h := fixedTag_semantic_factorization.1 (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)
    rw [semantic] at h; simpa using h.symm
  obtain ⟨z,hz,gamma,stage⟩ := raw_body k x w parsed tag hn
  have full := GammaSupport.exact k x w parsed semantic hn z gamma
  have small : pr.2.n  ≤  a+m := by have h := Nat.lt_two_pow_self (n := pr.2.n); change 2^pr.2.n  ≤  a+m at table; omega
  have cap := AcceptedBody.strict_capacity x w gamma small
  obtain ⟨T,hH,price,rows,finish⟩ := stage cap full
  have rowsFit := accepted_rows_fit k x w accepted parsed gamma
  rw [if_pos rowsFit] at finish
  refine ⟨z,T,hH,gamma,price,?_,finish⟩
  intro r hr
  exact rows r (Nat.lt_min.mpr ⟨hr,lt_of_lt_of_le hr rowsFit⟩)
end Stream
