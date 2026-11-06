import Complexity.Uniform.V1.SequentialComposition
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# Executed raw-length false fence (G3r)

Infrastructure. The fixed table restores the input and installs one false cell at
`3*R+2`, using a temporary origin hole, a moving source hole and two tally marks
per input bit. Cleanup erases the tally and restores the saved origin bit.
The private paths below are proof certificates for individual `UniformTM.stepConfig`
transitions; they supply no runtime data. Neither the input length nor any budget,
parser, target or proof is an argument to the transition table.

This module proves installation only. G3q marker preservation, overflow rejection,
whole-verifier resources, parser/GN/model bridges and acceptance remain open.
-/
namespace Pnp3.Complexity.Uniform.V1.FixedRawLengthFence

/- The six shuttle modes remember either just the first bit (0/1) or both the
origin bit and current bit (2..5). Each has five controls: source-right,
tally-right, second write, tally-left, source-left. Controls 36/37 fetch the
next source bit; 38..47 scan the finished tally, write the fence, cross the gap,
erase the tally, and restore the origin. Controls 1/4/5 handle the empty word. -/
private def sh (m : Fin 6) (p : Fin 5) : Fin 48 := ⟨6+5*m.val+p.val, by omega⟩
private def pick (o : Bool) : Fin 48 := ⟨36+o.toNat, by cases o <;> decide⟩
private def clean (o : Bool) (p : Fin 5) : Fin 48 :=
  ⟨38+5*o.toNat+p.val, by have := p.isLt; cases o <;> simp_all [Bool.toNat] <;> omega⟩
private def origin (m : Fin 6) : Bool := m.val = 1 || 4 ≤ m.val
private def restored (m : Fin 6) : Option Bool :=
  if m.val < 2 then none else some (m.val % 2 == 1)
private def raw (q : Fin 48) (s : Option Bool) : Fin 48 × Option Bool × Move :=
  match q.val with
  | 0 => match s with
    | none => (1, none, .right)
    | some false => (6, none, .right)
    | some true => (11, none, .right)
  | 1 => (4, none, .right)
  | 2 => (2, s, .stay)
  | 3 => (3, s, .stay)
  | 4 => (5, some false, .left)
  | 5 => (2, none, .left)
  | 6 => if s = none then (7, none, .right) else (6, s, .right)
  | 7 => if s = none then (8, some true, .right) else (7, s, .right)
  | 8 => (9, some true, .left)
  | 9 => if s = none then (10, none, .left) else (9, s, .left)
  | 10 => if s = none then (36, none, .right) else (10, s, .left)
  | 11 => if s = none then (12, none, .right) else (11, s, .right)
  | 12 => if s = none then (13, some true, .right) else (12, s, .right)
  | 13 => (14, some true, .left)
  | 14 => if s = none then (15, none, .left) else (14, s, .left)
  | 15 => if s = none then (37, none, .right) else (15, s, .left)
  | 16 => if s = none then (17, none, .right) else (16, s, .right)
  | 17 => if s = none then (18, some true, .right) else (17, s, .right)
  | 18 => (19, some true, .left)
  | 19 => if s = none then (20, none, .left) else (19, s, .left)
  | 20 => if s = none then (36, some false, .right) else (20, s, .left)
  | 21 => if s = none then (22, none, .right) else (21, s, .right)
  | 22 => if s = none then (23, some true, .right) else (22, s, .right)
  | 23 => (24, some true, .left)
  | 24 => if s = none then (25, none, .left) else (24, s, .left)
  | 25 => if s = none then (36, some true, .right) else (25, s, .left)
  | 26 => if s = none then (27, none, .right) else (26, s, .right)
  | 27 => if s = none then (28, some true, .right) else (27, s, .right)
  | 28 => (29, some true, .left)
  | 29 => if s = none then (30, none, .left) else (29, s, .left)
  | 30 => if s = none then (37, some false, .right) else (30, s, .left)
  | 31 => if s = none then (32, none, .right) else (31, s, .right)
  | 32 => if s = none then (33, some true, .right) else (32, s, .right)
  | 33 => (34, some true, .left)
  | 34 => if s = none then (35, none, .left) else (34, s, .left)
  | 35 => if s = none then (37, some true, .right) else (35, s, .left)
  | 36 => match s with
    | none => (38, none, .right)
    | some false => (16, none, .right)
    | some true => (21, none, .right)
  | 37 => match s with
    | none => (43, none, .right)
    | some false => (26, none, .right)
    | some true => (31, none, .right)
  | 38 => if s = none then (39, none, .right) else (38, s, .right)
  | 39 => (40, some false, .left)
  | 40 => (41, none, .left)
  | 41 => if s = none then (42, none, .left) else (41, none, .left)
  | 42 => if s = none then (2, some false, .stay) else (42, s, .left)
  | 43 => if s = none then (44, none, .right) else (43, s, .right)
  | 44 => (45, some false, .left)
  | 45 => (46, none, .left)
  | 46 => if s = none then (47, none, .left) else (46, none, .left)
  | 47 => if s = none then (2, some true, .stay) else (47, s, .left)
  | _ => (3,s,.stay)

def machine : UniformTM where
  stateCount := 48
  start := 0
  accept := 2
  reject := 3
  accept_ne_reject := by decide
  rawStep := raw

def fencePos (R : Nat) : Nat := 3*R+2
def installClock (R : Nat) : Nat := if R = 0 then 4 else 3*R*R+9*R+5
def allocation (R : Nat) : Nat := 16*(R+1)^2
def fenceTape {R : Nat} (B : Nat) (input : Bitstring R) :
    Fin (tapeLength R B) → Option Bool := fun i =>
  if h : i.val < R then some (input ⟨i.val,h⟩)
  else if i.val = fencePos R then some false else none
def installedConfig {R : Nat} (B : Nat) (input : Bitstring R) :
    Config machine.stateCount R B :=
  ⟨machine.accept, ⟨0, by simp [tapeLength]⟩, fenceTape B input⟩

private theorem rows_sh (m : Fin 6) (s : Option Bool) :
    machine.step (sh m 0) s = (if s = none then (sh m 1,none,.right) else (sh m 0,s,.right)) ∧
    machine.step (sh m 1) s = (if s = none then (sh m 2,some true,.right) else (sh m 1,s,.right)) ∧
    machine.step (sh m 2) s = (sh m 3,some true,.left) ∧
    machine.step (sh m 3) s = (if s = none then (sh m 4,none,.left) else (sh m 3,s,.left)) ∧
    machine.step (sh m 4) s = (if s = none then (pick (origin m),restored m,.right) else (sh m 4,s,.left)) := by
  fin_cases m <;> cases s with
  | none => decide
  | some b => cases b <;> decide
private theorem rows_clean (o : Bool) (s : Option Bool) :
    machine.step (pick o) none = (clean o 0,none,.right) ∧
    machine.step (clean o 0) s = (if s = none then (clean o 1,none,.right) else (clean o 0,s,.right)) ∧
    machine.step (clean o 1) s = (clean o 2,some false,.left) ∧
    machine.step (clean o 2) s = (clean o 3,none,.left) ∧
    machine.step (clean o 3) s = (if s = none then (clean o 4,none,.left) else (clean o 3,none,.left)) ∧
    machine.step (clean o 4) s = (if s = none then (2,some o,.stay) else (clean o 4,s,.left)) := by
  cases o <;> cases s with
  | none => decide
  | some b => cases b <;> decide

/- Natural-address configurations occur only in the proof. Every edge supplies
positive-left and bounded-right evidence; `execute` embeds the entire path into
the original finite tape and proves the literal `UniformTM.run` equation. -/
private structure NC (k : Nat) where
  q : Fin k
  h : Nat
  tape : Nat → Option Bool
private def embed {k n B P : Nat} (c : NC k) (hc : c.h ≤ P)
    (hp : P < tapeLength n B) : Config k n B :=
  ⟨c.q, ⟨c.h, lt_of_le_of_lt hc hp⟩, fun i => c.tape i.val⟩
private def dest (h : Nat) : Move → Nat
  | .left => h-1 | .stay => h | .right => h+1
private structure Edge (M : UniformTM) (P : Nat) (c d : NC M.stateCount) : Prop where
  work : c.q ≠ M.accept ∧ c.q ≠ M.reject
  bounded : c.h ≤ P ∧ d.h ≤ P
  action : ∃ w mv, M.step c.q (c.tape c.h) = (d.q,w,mv) ∧
    (mv = .left → 0 < c.h) ∧ d.h = dest c.h mv ∧
    ∀ i, d.tape i = if i = c.h then w else c.tape i
private inductive Path (M : UniformTM) (P : Nat) : Nat → NC M.stateCount → NC M.stateCount → Prop
  | nil (c) (h : c.h ≤ P) : Path M P 0 c c
  | snoc {t c d e} : Path M P t c d → Edge M P d e → Path M P (t+1) c e
private theorem bounds {M P t c d} (p : Path M P t c d) : c.h ≤ P ∧ d.h ≤ P := by
  induction p with
  | nil _ h => exact ⟨h,h⟩
  | snoc _ e ih => exact ⟨ih.1,e.bounded.2⟩
private theorem append {M P t u c d e} (p : Path M P t c d) (q : Path M P u d e) :
    Path M P (t+u) c e := by
  induction q with
  | nil => simpa using p
  | snoc _ edge ih => exact .snoc (ih p) edge
private theorem edge_run {M P c d n B} (e : Edge M P c d) (hp : P < tapeLength n B) :
    M.stepConfig (embed c e.bounded.1 hp) = embed d e.bounded.2 hp := by
  obtain ⟨w,mv,hr,hl,hh,ht⟩ := e.action
  apply Config.ext_parts
  · exact congrArg Prod.fst hr
  · apply Fin.ext
    change (moveHead (⟨c.h, _⟩ : Fin (tapeLength n B))
      (M.step c.q (c.tape c.h)).2.2).val = d.h
    rw [hr]
    cases mv with
    | left => exact hh.symm
    | stay => exact hh.symm
    | right =>
        have h : c.h+1 < tapeLength n B := by
          have := e.bounded.2
          simp only [dest] at hh
          omega
        simpa [moveHead,h] using hh.symm
  · funext i
    change (if i = (⟨c.h,_⟩ : Fin (tapeLength n B)) then
      (M.step c.q (c.tape c.h)).2.1 else c.tape i.val) = d.tape i.val
    rw [hr, ht]
    simp only [Fin.ext_iff]
private def Good (M : UniformTM) {n B : Nat} (P : Nat) (c : Config M.stateCount n B) : Prop :=
  c.state ≠ M.accept ∧ c.state ≠ M.reject ∧ c.head.val ≤ P ∧
  let mv := (M.step c.state (c.tape c.head)).2.2
  (mv = .left → 0 < c.head.val) ∧
  (mv = .right → c.head.val + 1 < tapeLength n B)
private theorem edge_good {M P c d n B} (e : Edge M P c d) (hp : P < tapeLength n B) :
    Good M P (embed c e.bounded.1 hp) := by
  obtain ⟨w,mv,hr,hl,hh,ht⟩ := e.action
  refine ⟨e.work.1,e.work.2,e.bounded.1,?_,?_⟩
  · simpa [embed,hr] using hl
  · change (M.step c.q (c.tape c.h)).2.2 = .right → _
    rw [hr]
    intro he
    change mv = .right at he
    rw [he] at hh
    have := e.bounded.2
    simp only [dest] at hh
    change c.h+1 < tapeLength n B
    omega
private theorem execute {M P t c d n B} (p : Path M P t c d) (hp : P < tapeLength n B) :
    M.run t (embed c (bounds p).1 hp) = embed d (bounds p).2 hp ∧
    ∀ u, u < t → Good M P (M.run u (embed c (bounds p).1 hp)) := by
  induction p with
  | nil c h => exact ⟨rfl, by omega⟩
  | @snoc t c d e p edge ih =>
      refine ⟨?_,?_⟩
      · rw [UniformTM.run,ih.1]
        exact edge_run edge hp
      · intro u hu
        by_cases h : u < t
        · exact ih.2 u h
        · have : u = t := by omega
          subst u
          rw [ih.1]
          exact edge_good edge hp
private theorem pathRepeat {M P} (f : Nat → NC M.stateCount) (n : Nat)
    (h0 : (f 0).h ≤ P) (hs : ∀ i, i<n → Edge M P (f i) (f (i+1))) :
    Path M P n (f 0) (f n) := by
  have aux : ∀ k, k≤n → Path M P k (f 0) (f k) := by
    intro k hk
    induction k with
    | zero => exact .nil _ h0
    | succ k ih => exact .snoc (ih (by omega)) (hs k (by omega))
  exact aux n le_rfl

private theorem hop {M P} (q q' : Fin M.stateCount) (h h' : Nat)
    (T T' : Nat → Option Bool) (w : Option Bool) (mv : Move)
    (hw : q ≠ M.accept ∧ q ≠ M.reject) (hb : h ≤ P ∧ h' ≤ P)
    (hr : M.step q (T h) = (q',w,mv)) (hl : mv = .left → 0 < h)
    (hh : h' = dest h mv) (ht : ∀ k, T' k = if k = h then w else T k) :
    Path M P 1 ⟨q,h,T⟩ ⟨q',h',T'⟩ :=
  .snoc (.nil _ hb.1) ⟨hw,hb,⟨w,mv,hr,hl,hh,ht⟩⟩
private theorem sweepR {M P} (q : Fin M.stateCount) (T : Nat → Option Bool) (h n : Nat)
    (hw : q ≠ M.accept ∧ q ≠ M.reject) (hb : h+n ≤ P)
    (hr : ∀ k, h ≤ k → k < h+n → M.step q (T k) = (q,T k,.right)) :
    Path M P n ⟨q,h,T⟩ ⟨q,h+n,T⟩ := by
  have p := pathRepeat (M := M) (P := P) (fun i => ⟨q,h+i,T⟩) n (by dsimp; omega) ?_
  · simpa using p
  · intro i hi
    refine ⟨hw,⟨by dsimp; omega,by dsimp; omega⟩,T (h+i),.right,
      hr (h+i) (by omega) (by omega),by simp,by simp [dest]; omega,?_⟩
    intro k
    dsimp
    split_ifs with hk
    · rw [hk]
    · rfl
private theorem sweepL {M P} (q : Fin M.stateCount) (T : Nat → Option Bool) (h n : Nat)
    (hw : q ≠ M.accept ∧ q ≠ M.reject) (hb : h ≤ P) (hn : n ≤ h)
    (hr : ∀ k, h-n < k → k ≤ h → M.step q (T k) = (q,T k,.left)) :
    Path M P n ⟨q,h,T⟩ ⟨q,h-n,T⟩ := by
  have p := pathRepeat (M := M) (P := P) (fun i => ⟨q,h-i,T⟩) n (by dsimp; omega) ?_
  · simpa using p
  · intro i hi
    refine ⟨hw,⟨by dsimp; omega,by dsimp; omega⟩,T (h-i),.left,
      hr (h-i) (by omega) (by omega),?_,?_,?_⟩
    · dsimp; omega
    · dsimp [dest]; omega
    · intro k
      dsimp
      split_ifs with hk
      · rw [hk]
      · rfl

private def source {R : Nat} (x : Bitstring R) (k : Nat) : Option Bool :=
  if h : k < R then some (x ⟨k,h⟩) else none
private def tape {R : Nat} (x : Bitstring R) (hole marks : Nat) (fenced : Bool)
    (k : Nat) : Option Bool :=
  if k = 0 ∨ k = hole then none
  else if k < R then source x k
  else if R+1 ≤ k ∧ k < R+1+marks then some true
  else if fenced = true ∧ k = fencePos R then some false else none
private def finalTape {R : Nat} (x : Bitstring R) (k : Nat) : Option Bool :=
  if k < R then source x k else if k = fencePos R then some false else none
private theorem tape_src {R hole marks k : Nat} (x : Bitstring R) (f : Bool)
    (hk : k < R) (h0 : k ≠ 0) (hh : k ≠ hole) :
    tape x hole marks f k = source x k := by simp [tape,hk,h0,hh]
private theorem tape_hole {R marks : Nat} (x : Bitstring R) (f : Bool) (hole : Nat) :
    tape x hole marks f hole = none := by simp [tape]
private theorem tape_zero {R hole marks : Nat} (x : Bitstring R) (f : Bool) :
    tape x hole marks f 0 = none := by simp [tape]
private theorem tape_sep {R hole marks : Nat} (x : Bitstring R) (f : Bool) :
    tape x hole marks f R = none := by
  simp only [tape,fencePos]
  split_ifs <;> first | rfl | omega
private theorem tape_mark {R hole marks k : Nat} (x : Bitstring R) (f : Bool)
    (hh : hole ≤ R) (h1 : R+1 ≤ k) (h2 : k < R+1+marks) :
    tape x hole marks f k = some true := by
  simp only [tape]; rw [if_neg (by omega),if_neg (by omega),if_pos ⟨h1,h2⟩]
private theorem tape_high {R hole marks k : Nat} (x : Bitstring R)
    (hk : R+1+marks ≤ k) : tape x hole marks false k = none := by
  simp only [tape, Bool.false_eq_true, false_and, if_false]; split_ifs <;> first | rfl | omega
private theorem add_mark {R hole marks : Nat} (x : Bitstring R)
    (hh : hole ≤ R) : ∀ k, tape x hole (marks+1) false k =
      if k = R+1+marks then some true else tape x hole marks false k := by
  intro k
  simp only [tape, Bool.false_eq_true, false_and, if_false]
  split_ifs <;> first | rfl | omega
private theorem restore_hole {R i marks : Nat} (x : Bitstring R) (hi : i < R) :
    ∀ k, tape x R marks false k =
      if k = i then (if i = 0 then none else source x i) else tape x i marks false k := by
  intro k
  by_cases hki : k = i
  · subst k
    by_cases h0 : i = 0
    · subst i; simp [tape]
    · simp [tape,hi,h0,show i ≠ R by omega]
  · simp only [tape, Bool.false_eq_true, false_and, if_false]
    split_ifs <;> first | rfl | omega
private theorem work_sh (m : Fin 6) (p : Fin 5) :
    sh m p ≠ machine.accept ∧ sh m p ≠ machine.reject := by
  constructor <;> intro h <;> have hv := congrArg Fin.val h <;>
    simp only [sh,machine] at hv <;> omega
private theorem work_pick (o : Bool) :
    pick o ≠ machine.accept ∧ pick o ≠ machine.reject := by cases o <;> decide
private theorem work_clean (o : Bool) (p : Fin 5) :
    clean o p ≠ machine.accept ∧ clean o p ≠ machine.reject := by
  constructor <;> intro h <;> have hv := congrArg Fin.val h <;>
    simp only [clean,machine] at hv <;> omega
private theorem hopKeep {M P} (q q' : Fin M.stateCount) (h h' : Nat)
    (T : Nat → Option Bool) (mv : Move)
    (hw : q ≠ M.accept ∧ q ≠ M.reject) (hb : h ≤ P ∧ h' ≤ P)
    (hr : M.step q (T h) = (q',T h,mv)) (hl : mv = .left → 0 < h)
    (hh : h' = dest h mv) : Path M P 1 ⟨q,h,T⟩ ⟨q',h',T⟩ := by
  apply hop q q' h h' T T (T h) mv hw hb hr hl hh
  intro k; split_ifs with hk
  · rw [hk]
  · rfl

private theorem shuttle {R i : Nat} (x : Bitstring R) (m : Fin 6) (hi : i < R)
    (hm : restored m = if i = 0 then none else source x i) :
    Path machine (fencePos R) (2*R+2*i+4)
      ⟨sh m 0,i+1,tape x i (2*i) false⟩
      ⟨pick (origin m),i+1,tape x R (2*i+2) false⟩ := by
  have a := sweepR (M := machine) (P := fencePos R) (sh m 0) (tape x i (2*i) false) (i+1) (R-i-1)
    (work_sh m 0) (by unfold fencePos; omega) (by
      intro k hk hk'
      rw [(rows_sh m _).1, tape_src x false (by omega) (by omega) (by omega)]
      simp [source,show k < R by omega])
  have ar : i+1+(R-i-1) = R := by omega
  rw [ar] at a
  have b := hopKeep (M := machine) (P := fencePos R) (sh m 0) (sh m 1) R (R+1) (tape x i (2*i) false) .right
    (work_sh m 0) (by unfold fencePos; omega) (by
      rw [tape_sep,(rows_sh m none).1]; rfl) (by simp) rfl
  have c := sweepR (M := machine) (P := fencePos R) (sh m 1) (tape x i (2*i) false) (R+1) (2*i)
    (work_sh m 1) (by unfold fencePos; omega) (by
      intro k hk hk'
      rw [tape_mark x false (by omega) hk hk',(rows_sh m _).2.1]; rfl)
  have d := hop (M := machine) (P := fencePos R) (sh m 1) (sh m 2) (R+1+2*i) (R+2+2*i)
    (tape x i (2*i) false) (tape x i (2*i+1) false) (some true) .right
    (work_sh m 1) (by unfold fencePos; omega) (by
      rw [tape_high x (by omega),(rows_sh m none).2.1]; rfl) (by simp)
    (by simp [dest]; omega) (add_mark x (by omega))
  have e := hop (M := machine) (P := fencePos R) (sh m 2) (sh m 3) (R+2+2*i) (R+1+2*i)
    (tape x i (2*i+1) false) (tape x i (2*i+2) false) (some true) .left
    (work_sh m 2) (by unfold fencePos; omega) (rows_sh m _).2.2.1 (by omega)
    (by simp [dest]) (by
      simpa [show R+1+(2*i+1) = R+2+2*i by omega] using add_mark (marks := 2*i+1) x (by omega))
  have f := sweepL (M := machine) (P := fencePos R) (sh m 3) (tape x i (2*i+2) false) (R+1+2*i) (2*i+1)
    (work_sh m 3) (by unfold fencePos; omega) (by omega) (by
      intro k hk hk'
      rw [tape_mark x false (by omega) (by omega) (by omega),(rows_sh m _).2.2.2.1]; rfl)
  rw [show R+1+2*i-(2*i+1) = R by omega] at f
  have g := hopKeep (M := machine) (P := fencePos R) (sh m 3) (sh m 4) R (R-1) (tape x i (2*i+2) false) .left
    (work_sh m 3) (by unfold fencePos; omega) (by
      rw [tape_sep,(rows_sh m none).2.2.2.1]; rfl) (by omega) rfl
  have h := sweepL (M := machine) (P := fencePos R) (sh m 4) (tape x i (2*i+2) false) (R-1) (R-i-1)
    (work_sh m 4) (by unfold fencePos; omega) (by omega) (by
      intro k hk hk'
      rw [(rows_sh m _).2.2.2.2,tape_src x false (by omega) (by omega) (by omega)]
      simp [source,show k < R by omega])
  rw [show R-1-(R-i-1) = i by omega] at h
  have j := hop (M := machine) (P := fencePos R) (sh m 4) (pick (origin m)) i (i+1)
    (tape x i (2*i+2) false) (tape x R (2*i+2) false) (restored m) .right
    (work_sh m 4) (by unfold fencePos; omega) (by
      rw [tape_hole,(rows_sh m none).2.2.2.2]; rfl) (by simp) rfl (by
      rw [hm]; exact restore_hole x hi)
  have p := append (append (append (append (append (append (append (append a b) c) d) e) f) g) h) j
  convert p using 1; omega

private def mode (i : Nat) (o b : Bool) : Fin 6 :=
  if i = 0 then ⟨b.toNat, by cases b <;> decide⟩
  else ⟨2+2*o.toNat+b.toNat, by cases o <;> cases b <;> decide⟩
private def entry {R : Nat} (x : Bitstring R) (o : Bool) (i : Nat) : NC 48 :=
  ⟨if i = 0 then 0 else pick o, i, if i = 0 then source x else tape x R (2*i) false⟩
private theorem erase_entry {R i : Nat} (x : Bitstring R) (o : Bool) (hi : i < R) :
    ∀ k, tape x i (2*i) false k = if k = i then none else (entry x o i).tape k := by
  intro k
  by_cases h0 : i = 0
  · subst i
    simp only [entry,ite_true,Nat.mul_zero,tape,or_self,source,
      Bool.false_eq_true,false_and,if_false]
    split_ifs <;> first | rfl | omega
  · simp only [entry,h0,if_false,tape,Bool.false_eq_true,false_and]
    split_ifs <;> first | rfl | omega
private theorem iteration {R i : Nat} (x : Bitstring R) (o : Bool)
    (hi : i < R) (ho : source x 0 = some o) :
    Path machine (fencePos R) (2*R+2*i+5) (entry x o i) (entry x o (i+1)) := by
  let b := x ⟨i,hi⟩
  have hb : source x i = some b := by simp [source,b,hi]
  have hread : (entry x o i).tape i = some b := by
    by_cases h0 : i = 0
    · simp [entry,h0,← hb]
    · simp [entry,h0,tape,hi,show i ≠ R by omega, hb]
  have hm : origin (mode i o b) = o ∧
      restored (mode i o b) = if i = 0 then none else source x i := by
    by_cases h0 : i = 0
    · have he : b = o := by rw [h0,ho] at hb; exact Option.some.inj hb.symm
      rw [he]
      cases o <;> simp [mode,h0,origin,restored]
    · rw [hb]
      cases o <;> cases b <;> simp [mode,h0,origin,restored]
  have a := hop (M := machine) (P := fencePos R) (entry x o i).q (sh (mode i o b) 0)
    i (i+1) (entry x o i).tape (tape x i (2*i) false) none .right
    (by by_cases h0 : i = 0
        · simp [entry,h0,machine]
        · simpa [entry,h0] using work_pick o)
    (by unfold fencePos; omega) (by
      rw [hread]
      by_cases h0 : i = 0 <;> cases o <;> cases b <;>
        simp [entry,mode,h0,sh,pick,machine,UniformTM.step,raw])
    (by simp) rfl (erase_entry x o hi)
  have p := append a (shuttle x (mode i o b) hi hm.2)
  rw [hm.1] at p
  simpa [entry,show i+1 ≠ 0 by omega,show 2*(i+1) = 2*i+2 by omega,
    show 1+(2*R+2*i+4) = 2*R+2*i+5 by omega] using p
private theorem iterations {R : Nat} (x : Bitstring R) (o : Bool)
    (ho : source x 0 = some o) : ∀ i, i ≤ R →
    Path machine (fencePos R) (i*i+(2*R+4)*i) (entry x o 0) (entry x o i) := by
  intro i hi
  induction i with
  | zero => exact .nil _ (by simp [entry,fencePos])
  | succ i ih =>
      have p := append (ih (by omega)) (iteration x o (by omega) ho)
      convert p using 1; ring

private theorem add_fence {R : Nat} (x : Bitstring R) : ∀ k,
    tape x R (2*R) true k =
      if k = fencePos R then some false else tape x R (2*R) false k := by
  intro k
  simp only [tape,fencePos,Bool.false_eq_true,false_and,true_and,if_false]
  split_ifs <;> first | rfl | omega
private theorem erase_mark {R marks : Nat} (x : Bitstring R) (hm : marks < 2*R) : ∀ k,
    tape x R marks true k =
      if k = R+1+marks then none else tape x R (marks+1) true k := by
  intro k
  simp only [tape,fencePos,true_and]
  split_ifs <;> first | rfl | omega
private theorem restore_origin {R : Nat} (x : Bitstring R) (hR : 0 < R) : ∀ k,
    finalTape x k = if k = 0 then source x 0 else tape x R 0 true k := by
  intro k
  by_cases h0 : k = 0
  · subst k; simp [finalTape,hR]
  · simp only [finalTape,tape,h0,if_false,false_or,fencePos,true_and]
    split_ifs <;> first | rfl | omega
private theorem cleanup {R : Nat} (x : Bitstring R) (o : Bool)
    (hR : 0 < R) (ho : source x 0 = some o) :
    Path machine (fencePos R) (5*R+5)
      ⟨pick o,R,tape x R (2*R) false⟩ ⟨machine.accept,0,finalTape x⟩ := by
  have a := hopKeep (M := machine) (P := fencePos R) (pick o) (clean o 0) R (R+1)
    (tape x R (2*R) false) .right (work_pick o) (by unfold fencePos; omega)
    (by rw [tape_sep]; exact (rows_clean o none).1) (by simp) rfl
  have b := sweepR (M := machine) (P := fencePos R) (clean o 0)
    (tape x R (2*R) false) (R+1) (2*R) (work_clean o 0) (by unfold fencePos; omega) (by
      intro k hk hk'
      rw [tape_mark x false (by omega) hk hk',(rows_clean o _).2.1]; rfl)
  have c := hopKeep (M := machine) (P := fencePos R) (clean o 0) (clean o 1)
    (R+1+2*R) (fencePos R) (tape x R (2*R) false) .right
    (work_clean o 0) (by unfold fencePos; omega) (by
      rw [tape_high x (by omega),(rows_clean o none).2.1]; rfl) (by simp)
    (by simp [dest,fencePos]; omega)
  have d := hop (M := machine) (P := fencePos R) (clean o 1) (clean o 2)
    (fencePos R) (R+1+2*R) (tape x R (2*R) false) (tape x R (2*R) true)
    (some false) .left (work_clean o 1) (by unfold fencePos; omega)
    (rows_clean o _).2.2.1 (by unfold fencePos; omega)
    (by simp [dest,fencePos]; omega) (add_fence x)
  have e := hopKeep (M := machine) (P := fencePos R) (clean o 2) (clean o 3)
    (R+1+2*R) (3*R) (tape x R (2*R) true) .left (work_clean o 2)
    (by unfold fencePos; omega) (by
      rw [(rows_clean o _).2.2.2.1]
      congr 1
      simp [tape,fencePos,show R+1+2*R ≠ R by omega,
        show ¬ R+1+2*R < R by omega,show R+1+2*R ≠ 3*R+2 by omega])
    (by omega) (by simp [dest]; omega)
  have f := pathRepeat (M := machine) (P := fencePos R)
    (fun j => ⟨clean o 3,3*R-j,tape x R (2*R-j) true⟩) (2*R)
    (by dsimp; unfold fencePos; omega) (by
      intro j hj
      have hm : 2*R-j = (2*R-(j+1))+1 := by omega
      refine ⟨work_clean o 3,⟨by dsimp; unfold fencePos; omega,
        by dsimp; unfold fencePos; omega⟩,none,.left,?_,?_,?_,?_⟩
      · dsimp
        rw [tape_mark x true (by omega) (by omega) (by omega),(rows_clean o _).2.2.2.2.1]
        rfl
      · dsimp; omega
      · dsimp [dest]; omega
      · dsimp
        rw [hm]
        simpa [show R+1+(2*R-(j+1)) = 3*R-j by omega] using
          erase_mark (marks := 2*R-(j+1)) x (by omega))
  simp only [Nat.sub_zero,Nat.sub_self,show 3*R-2*R = R by omega] at f
  have g := hopKeep (M := machine) (P := fencePos R) (clean o 3) (clean o 4) R (R-1)
    (tape x R 0 true) .left (work_clean o 3) (by unfold fencePos; omega) (by
      rw [tape_sep,(rows_clean o none).2.2.2.2.1]; rfl) (by omega) rfl
  have h := sweepL (M := machine) (P := fencePos R) (clean o 4) (tape x R 0 true)
    (R-1) (R-1) (work_clean o 4) (by unfold fencePos; omega) le_rfl (by
      intro k hk hk'
      rw [(rows_clean o _).2.2.2.2.2,tape_src x true (by omega) (by omega) (by omega)]
      simp [source,show k < R by omega])
  simp only [Nat.sub_self] at h
  have j := hop (M := machine) (P := fencePos R) (clean o 4) machine.accept 0 0
    (tape x R 0 true) (finalTape x) (some o) .stay (work_clean o 4)
    (by unfold fencePos; omega) (by rw [tape_zero,(rows_clean o none).2.2.2.2.2]; rfl)
    (by simp) rfl (by rw [← ho]; exact restore_origin x hR)
  have p := append (append (append (append (append (append (append (append a b) c) d) e) f) g) h) j
  convert p using 1; omega

private theorem empty (x : Bitstring 0) :
    Path machine 2 4 ⟨machine.start,0,source x⟩ ⟨machine.accept,0,finalTape x⟩ := by
  let T : Nat → Option Bool := fun _ => none
  let F : Nat → Option Bool := fun k => if k = 2 then some false else none
  have a := hopKeep (M := machine) (P := 2) machine.start (1 : Fin 48) 0 1 T .right
    (by decide) (by decide) (by rfl) (by simp) rfl
  have b := hopKeep (M := machine) (P := 2) (1 : Fin 48) (4 : Fin 48) 1 2 T .right
    (by decide) (by decide) (by rfl) (by simp) rfl
  have c := hop (M := machine) (P := 2) (4 : Fin 48) (5 : Fin 48) 2 1 T F
    (some false) .left (by decide) (by decide) (by rfl) (by decide) rfl (fun _ => rfl)
  have d := hopKeep (M := machine) (P := 2) (5 : Fin 48) machine.accept 1 0 F .left
    (by decide) (by decide) (by rfl) (by decide) rfl
  have hs : source x = T := by funext k; simp [source,T]
  have hf : finalTape x = F := by funext k; simp [finalTape,fencePos,F]
  simpa [hs,hf] using append (append (append a b) c) d
private theorem install_path {R : Nat} (x : Bitstring R) :
    Path machine (fencePos R) (installClock R)
      ⟨machine.start,0,source x⟩ ⟨machine.accept,0,finalTape x⟩ := by
  by_cases hR : R = 0
  · subst R; exact empty x
  · have hp : 0 < R := by omega
    let o := x ⟨0,hp⟩
    have ho : source x 0 = some o := by simp [source,hp,o]
    have p := iterations x o ho R le_rfl
    simp only [entry,ite_true,if_neg hR] at p
    have q := append p (cleanup x o hp ho)
    change Path machine (fencePos R) (installClock R)
      ⟨(0 : Fin 48),0,source x⟩ ⟨machine.accept,0,finalTape x⟩
    convert q using 1
    simp only [installClock,if_neg hR]
    ring

/-- Fixed finite control and table; neither budget nor input length is a row argument. -/
theorem table_and_resource_pins :
    machine.stateCount = 48 ∧ Fintype.card (Fin machine.stateCount × Option Bool) = 144 ∧
    machine.start.val = 0 ∧ machine.accept.val = 2 ∧ machine.reject.val = 3 ∧
    (∀ q s, machine.step q s = machine.rawStep q s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro q s
  change Fin 48 at q
  fin_cases q <;> cases s with
  | none => decide
  | some b => cases b <;> decide

/-- Exact complete endpoint from literal raw initialization, at every sufficient allocation. -/
theorem install_exact {R B : Nat} (input : Bitstring R) (hroom : 2*R+2 ≤ B) :
    machine.run (installClock R) (initialConfig machine B input) = installedConfig B input := by
  have hp : fencePos R < tapeLength R B := by unfold fencePos tapeLength; omega
  have h := (execute (install_path input) hp).1
  change machine.run (installClock R) (initialConfig machine B input) = _ at h
  rw [h]
  apply Config.ext_parts
  · rfl
  · rfl
  · funext i
    by_cases hi : i.val < R <;> simp [embed,finalTape,fenceTape,source,installedConfig,hi]

/-- Strict first terminal arrival, bounded footprint and no attempted clamp before arrival. -/
theorem install_trace {R B : Nat} (input : Bitstring R) (hroom : 2*R+2 ≤ B) :
    (∀ t, t < installClock R →
      (machine.run t (initialConfig machine B input)).state ≠ machine.accept ∧
      (machine.run t (initialConfig machine B input)).state ≠ machine.reject) ∧
    (∀ t, t ≤ installClock R →
      (machine.run t (initialConfig machine B input)).head.val ≤ fencePos R) ∧
    (∀ t, t < installClock R →
      let c := machine.run t (initialConfig machine B input)
      let mv := (machine.step c.state (c.tape c.head)).2.2
      (mv = Move.left → 0 < c.head.val) ∧
      (mv = Move.right → c.head.val+1 < tapeLength R B)) := by
  have hp : fencePos R < tapeLength R B := by unfold fencePos tapeLength; omega
  have h := (execute (install_path input) hp).2
  change ∀ t, t < installClock R → Good machine (fencePos R)
    (machine.run t (initialConfig machine B input)) at h
  refine ⟨fun t ht => ⟨(h t ht).1,(h t ht).2.1⟩,?_,fun t ht => (h t ht).2.2.2⟩
  intro t ht
  by_cases he : t < installClock R
  · exact (h t he).2.2.1
  · have : t = installClock R := by omega
    subst t
    rw [install_exact input hroom]
    simp [installedConfig]

/-- Input restoration and the unique nonblank suffix cell, stated on the executed tape. -/
theorem installed_cells {R B : Nat} (input : Bitstring R) (hroom : 2*R+2 ≤ B) :
    let c := machine.run (installClock R) (initialConfig machine B input)
    (∀ i : Fin R, c.tape ⟨i.val, by have := i.isLt; unfold tapeLength; omega⟩ = some (input i)) ∧
    (∀ i : Fin (tapeLength R B), R ≤ i.val →
      c.tape i = if i.val = fencePos R then some false else none) ∧
    (∃ i : Fin (tapeLength R B), i.val = fencePos R ∧ c.tape i = some false) := by
  dsimp only
  rw [install_exact input hroom]
  refine ⟨?_,?_,?_⟩
  · intro i; simp [installedConfig,fenceTape,i.isLt]
  · intro i hi; simp [installedConfig,fenceTape,show ¬ i.val < R by omega]
  · refine ⟨⟨fencePos R,by unfold fencePos tapeLength; omega⟩,rfl,?_⟩
    simp [installedConfig,fenceTape,fencePos,show ¬ 3*R+2 < R by omega]

/-- An explicit quadratic allocation also dominates the exact installation clock. -/
theorem resource_bounds (R : Nat) : 2*R+2 ≤ allocation R ∧ installClock R ≤ allocation R := by
  unfold allocation installClock
  split_ifs with h
  · subst R; decide
  · constructor <;> nlinarith

/-- Hypothesis-free raw installation at the fixed polynomial allocation. -/
theorem raw_install_exact {R : Nat} (input : Bitstring R) :
    machine.run (installClock R) (initialConfig machine (allocation R) input) =
      installedConfig (allocation R) input := install_exact input (resource_bounds R).1

end Pnp3.Complexity.Uniform.V1.FixedRawLengthFence
