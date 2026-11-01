import UniformClassBridgeClosure.TM0StepBundle

/-! SG3 head-relative windows. Center rails plus independent six-symbol cell
rails are composable; no truth table enumerates a whole tape window. -/
namespace UniformClassBridgeClosure.TM0DAG.Window
open Turing Pnp3.ComplexityInterfaces

def coord (r : Nat) (i : Fin (2*r+1)) : Int := (i.val : Int) - r

def slot (r : Nat) (i : Fin (2*r+1)) (d : Fin 3) : Fin (2*(r+1)+1) :=
  ⟨i.val+d.val, by omega⟩

def near (r : Nat) (d : Fin 3) : Fin (2*(r+1)+1) := ⟨r+d.val, by omega⟩

def width {Λ : Type} (labels : List Λ) (r : Nat) : Nat :=
  (centers labels).length + (2*r+1)*symbols.length

def tagWire {Λ : Type} (labels : List Λ) (r : Nat)
    (j : Fin (centers labels).length) : Fin (width labels r) :=
  Fin.castAdd ((2*r+1)*symbols.length) j

def cellWire {Λ : Type} (labels : List Λ) (r : Nat)
    (i : Fin (2*r+1)) (a : Fin symbols.length) : Fin (width labels r) :=
  Fin.natAdd (centers labels).length (finProdFinEquiv (i,a))

def encodeWindow {Λ : Type} [DecidableEq Λ] (labels : List Λ) (r : Nat)
    (s : Bool × TM0.Cfg Symbol Λ) : Bitstring (width labels r) :=
  Fin.addCases (fun j => decide ((centers labels)[j] = center s))
    (fun j => let p := finProdFinEquiv.symm j
              decide (symbols[p.2] = s.2.Tape.nth (coord r p.1)))

def action {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (t : Center Λ) : Option (Λ × TM0.Stmt Symbol) :=
  if t.1 then none else T t.2.1 t.2.2

def direction {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (t : Center Λ) : Fin 3 :=
  match action T t with
  | some (_, .move .left) => 0
  | some (_, .move .right) => 2
  | _ => 1

def nextTag {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (t : Center Λ) (a : Symbol) : Center Λ :=
  match action T t with
  | none => (true,t.2.1,t.2.2)
  | some (q, .write b) => (false,q,b)
  | some (q, .move _) => (false,q,a)

def nextCell {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (r : Nat) (i : Fin (2*r+1)) (t : Center Λ) (a : Symbol) : Symbol :=
  match action T t with
  | some (_, .write b) => if i.val=r then b else a
  | _ => a

theorem slot_coord (r : Nat) (i : Fin (2*r+1)) (d : Fin 3) :
    coord (r+1) (slot r i d) = coord r i + (d.val : Int) - 1 := by
  simp only [coord, slot]; omega

theorem near_coord (r : Nat) (d : Fin 3) :
    coord (r+1) (near r d) = (d.val : Int) - 1 := by
  simp only [coord, near]; omega

theorem tag_spec {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (r : Nat) (s : Bool × TM0.Cfg Symbol Λ) :
    nextTag T (center s) (s.2.Tape.nth (coord (r+1) (near r (direction T (center s))))) =
      center (saturatedStep T s) := by
  rw [← localStep_correct T s]
  rcases s with ⟨h,q,tape⟩
  cases h
  · cases e : T q tape.head with
    | none => simp [nextTag, action, center, localStep, observe, e]
    | some v =>
      rcases v with ⟨q',a⟩
      cases a with
      | write b => simp [nextTag, action, center, localStep, observe, e]
      | move d =>
        cases d <;> simp [nextTag, action, direction, center, localStep, observe, e, near_coord]
  · rfl

theorem cell_spec {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (r : Nat) (i : Fin (2*r+1)) (s : Bool × TM0.Cfg Symbol Λ) :
    nextCell T r i (center s)
      (s.2.Tape.nth (coord (r+1) (slot r i (direction T (center s))))) =
      (saturatedStep T s).2.Tape.nth (coord r i) := by
  have zero : coord r i = 0 ↔ i.val=r := by unfold coord; omega
  rcases s with ⟨h,q,tape⟩
  cases h
  · cases e : T q tape.head with
    | none => simp [nextCell, direction, action, center, saturatedStep, TM0.step, e, slot_coord]
    | some v =>
      rcases v with ⟨q',a⟩
      cases a with
      | write b =>
        simp [nextCell, direction, action, center, saturatedStep, TM0.step, e,
          slot_coord, Tape.write_nth, zero]
      | move d =>
        cases d
        · simp [nextCell, direction, action, center, saturatedStep, TM0.step, e,
            slot_coord, Tape.move_left_nth]
        · simp [nextCell, direction, action, center, saturatedStep, TM0.step, e,
            slot_coord, Tape.move_right_nth]
          congr 1; omega
  · simp [nextCell, direction, action, center, saturatedStep, slot_coord]
-- SG3_LITERAL_AUDIT: mechanical checks, not independent mathematical reproof.
theorem check_slot_coord (r : Nat) (i : Fin (2*r+1)) (d : Fin 3) :
    coord (r+1) (slot r i d) = coord r i + (d.val : Int) - 1 :=
  slot_coord r i d

theorem check_near_coord (r : Nat) (d : Fin 3) :
    coord (r+1) (near r d) = (d.val : Int) - 1 :=
  near_coord r d

theorem check_tag_spec {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (r : Nat) (s : Bool × TM0.Cfg Symbol Λ) :
    nextTag T (center s) (s.2.Tape.nth (coord (r+1) (near r (direction T (center s))))) =
      center (saturatedStep T s) :=
  tag_spec T r s

theorem check_cell_spec {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (r : Nat) (i : Fin (2*r+1)) (s : Bool × TM0.Cfg Symbol Λ) :
    nextCell T r i (center s)
      (s.2.Tape.nth (coord (r+1) (slot r i (direction T (center s))))) =
      (saturatedStep T s).2.Tape.nth (coord r i) :=
  cell_spec T r i s

#check (@coord : ∀ (_r : Nat) (_i : Fin (2*_r+1)),
    Int)
#check (@slot : ∀ (_r : Nat) (_i : Fin (2*_r+1)) (_d : Fin 3),
    Fin (2*(_r+1)+1))
#check (@near : ∀ (_r : Nat) (_d : Fin 3),
    Fin (2*(_r+1)+1))
#check (@width : ∀ {_Λ : Type} (_labels : List _Λ) (_r : Nat),
    Nat)
#check (@tagWire : ∀ {_Λ : Type} (_labels : List _Λ) (_r : Nat)
    (_j : Fin (centers _labels).length),
    Fin (width _labels _r))
#check (@cellWire : ∀ {_Λ : Type} (_labels : List _Λ) (_r : Nat)
    (_i : Fin (2*_r+1)) (_a : Fin symbols.length),
    Fin (width _labels _r))
#check (@encodeWindow : ∀ {_Λ : Type} [DecidableEq _Λ] (_labels : List _Λ) (_r : Nat)
    (_s : Bool × TM0.Cfg Symbol _Λ),
    Bitstring (width _labels _r))
#check (@action : ∀ {_Λ : Type} [Inhabited _Λ] (_T : TM0.Machine Symbol _Λ)
    (_t : Center _Λ),
    Option (_Λ × TM0.Stmt Symbol))
#check (@direction : ∀ {_Λ : Type} [Inhabited _Λ] (_T : TM0.Machine Symbol _Λ)
    (_t : Center _Λ),
    Fin 3)
#check (@nextTag : ∀ {_Λ : Type} [Inhabited _Λ] (_T : TM0.Machine Symbol _Λ)
    (_t : Center _Λ) (_a : Symbol),
    Center _Λ)
#check (@nextCell : ∀ {_Λ : Type} [Inhabited _Λ] (_T : TM0.Machine Symbol _Λ)
    (_r : Nat) (_i : Fin (2*_r+1)) (_t : Center _Λ) (_a : Symbol),
    Symbol)
#check (@slot_coord : ∀ (_r : Nat) (_i : Fin (2*_r+1)) (_d : Fin 3),
    coord (_r+1) (slot _r _i _d) = coord _r _i + (_d.val : Int) - 1)
#check (@near_coord : ∀ (_r : Nat) (_d : Fin 3),
    coord (_r+1) (near _r _d) = (_d.val : Int) - 1)
#check (@tag_spec : ∀ {_Λ : Type} [Inhabited _Λ] (_T : TM0.Machine Symbol _Λ)
    (_r : Nat) (_s : Bool × TM0.Cfg Symbol _Λ),
    nextTag _T (center _s) (_s.2.Tape.nth (coord (_r+1) (near _r (direction _T (center _s))))) =
      center (saturatedStep _T _s))
#check (@cell_spec : ∀ {_Λ : Type} [Inhabited _Λ] (_T : TM0.Machine Symbol _Λ)
    (_r : Nat) (_i : Fin (2*_r+1)) (_s : Bool × TM0.Cfg Symbol _Λ),
    nextCell _T _r _i (center _s)
      (_s.2.Tape.nth (coord (_r+1) (slot _r _i (direction _T (center _s))))) =
      (saturatedStep _T _s).2.Tape.nth (coord _r _i))
#check (@check_slot_coord : ∀ (_r : Nat) (_i : Fin (2*_r+1)) (_d : Fin 3),
    coord (_r+1) (slot _r _i _d) = coord _r _i + (_d.val : Int) - 1)
#check (@check_near_coord : ∀ (_r : Nat) (_d : Fin 3),
    coord (_r+1) (near _r _d) = (_d.val : Int) - 1)
#check (@check_tag_spec : ∀ {_Λ : Type} [Inhabited _Λ] (_T : TM0.Machine Symbol _Λ)
    (_r : Nat) (_s : Bool × TM0.Cfg Symbol _Λ),
    nextTag _T (center _s) (_s.2.Tape.nth (coord (_r+1) (near _r (direction _T (center _s))))) =
      center (saturatedStep _T _s))
#check (@check_cell_spec : ∀ {_Λ : Type} [Inhabited _Λ] (_T : TM0.Machine Symbol _Λ)
    (_r : Nat) (_i : Fin (2*_r+1)) (_s : Bool × TM0.Cfg Symbol _Λ),
    nextCell _T _r _i (center _s)
      (_s.2.Tape.nth (coord (_r+1) (slot _r _i (direction _T (center _s))))) =
      (saturatedStep _T _s).2.Tape.nth (coord _r _i))
#print axioms coord
#print axioms slot
#print axioms near
#print axioms width
#print axioms tagWire
#print axioms cellWire
#print axioms encodeWindow
#print axioms action
#print axioms direction
#print axioms nextTag
#print axioms nextCell
#print axioms slot_coord
#print axioms near_coord
#print axioms tag_spec
#print axioms cell_spec
#print axioms check_slot_coord
#print axioms check_near_coord
#print axioms check_tag_spec
#print axioms check_cell_spec

end UniformClassBridgeClosure.TM0DAG.Window
