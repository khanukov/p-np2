import InputRead.Machine
namespace InputRead
open Pnp3.Complexity.Uniform.V1
structure Node where
  state : Fin 41
  head : Nat
  tape : Nat → Option Bool

def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i

def embed {N B : Nat} (c : Node) (h : c.head < tapeLength N B) : Config 41 N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩

def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1

structure Edge (P : Nat) (c d : Node) : Prop where
  before : c.head ≤ P
  after : d.head ≤ P
  row : (machine.step c.state (c.tape c.head)).1 = d.state
  move : dest c.head (machine.step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head (machine.step c.state (c.tape c.head)).2.1

inductive Path (P : Nat) : Nat → Node → Node → Prop
  | nil (c) (h : c.head ≤ P) : Path P 0 c c
  | cons {t c d e} : Edge P c d → Path P t d e → Path P (t+1) c e

namespace Path
theorem bounds {P t c d} (h : Path P t c d) : c.head ≤ P ∧ d.head ≤ P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩

theorem append {P t u c d e} (h : Path P t c d) (g : Path P u d e) :
    Path P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)

theorem execute {N B P t c d} (h : Path P t c d) (hp : P < tapeLength N B) :
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

theorem hop {P : Nat} (s s' : Fin 41) (h h' : Nat) (T : Nat → Option Bool)
    (b : Option Bool) (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : machine.step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha

theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]

/-- One exact public row that preserves the scanned symbol. -/
theorem keep {P : Nat} (s s' : Fin 41) (h h' : Nat) (T : Nat → Option Bool)
    (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : machine.step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hb ha row hm
  rwa [put_same] at one

theorem sweepR {P : Nat} (s : Fin 41) (T : Nat → Option Bool) (h r : Nat)
    (fit : h+r ≤ P)
    (rows : ∀ i, h ≤ i → i < h+r → machine.step s (T i)=(s,T i,.right)) :
    Path P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right (P := P) (by omega) (by omega)
      (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest

theorem sweepL {P : Nat} (s : Fin 41) (T : Nat → Option Bool) (low r : Nat)
    (fit : low+r ≤ P)
    (rows : ∀ i, low < i → i ≤ low+r → machine.step s (T i)=(s,T i,.left)) :
    Path P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left (P := P) (by omega) (by omega)
      (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest
end InputRead
