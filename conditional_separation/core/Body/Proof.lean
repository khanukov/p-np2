import Body.Path
import Body.Target
namespace Body
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 4000

def Reads (T : Nat → Option Bool) (left : Nat) (bs : List Bool) : Prop :=
  ∀ j, j < bs.length → T (left+bs.length-j) = some bs[j]!

theorem reads_cons (T : Nat → Option Bool) (left : Nat) (b : Bool) (bs : List Bool) :
    Reads T left (b::bs) ↔ T (left+bs.length+1) = some b ∧ Reads T left bs := by
  constructor
  · intro h
    refine ⟨by simpa [Reads] using h 0 (by simp), ?_⟩
    intro j hj
    simpa [List.length_cons,show left+(bs.length+1)-(j+1)=left+bs.length-j by omega] using h (j+1) (by simp; omega)
  · rintro ⟨h,hs⟩ j hj
    cases j with
    | zero => simpa using h
    | succ j =>
      simpa [show left+(bs.length+1)-(j+1)=left+bs.length-j by omega] using hs j (by simpa using hj)

def carryTape (T : Nat → Option Bool) (left : Nat) : List Bool → Nat → Option Bool
  | [] => T
  | false :: bs => put T (left+bs.length+1) (some true)
  | true :: bs => carryTape (put T (left+bs.length+1) (some false)) left bs

theorem inc_length (bs : List Bool) : (inc bs).1.length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [inc,ih]

theorem carry_frame (T : Nat → Option Bool) (left : Nat) (bs : List Bool) (i : Nat)
    (hi : i ≤ left ∨ left+bs.length < i) : carryTape T left bs i = T i := by
  induction bs generalizing T with
  | nil => rfl
  | cons b bs ih =>
    have hn : i ≠ left+bs.length+1 := by simp only [List.length_cons] at hi; omega
    cases b
    · simp [carryTape,put,hn]
    · rw [carryTape,ih _ (by simp only [List.length_cons] at hi; omega)]
      simp [put,hn]

theorem reads_put_outside (T : Nat → Option Bool) (left : Nat) (bs : List Bool)
    (h : Reads T left bs) (pos : Nat) (b : Option Bool) (hp : left+bs.length < pos) :
    Reads (put T pos b) left bs := by
  intro j hj
  rw [put,if_neg (by omega)]
  exact h j hj

theorem carry_reads (T : Nat → Option Bool) (left : Nat) (bs : List Bool)
    (h : Reads T left bs) : Reads (carryTape T left bs) left (inc bs).1 := by
  induction bs generalizing T with
  | nil => intro j hj; simp [inc] at hj
  | cons b bs ih =>
    obtain ⟨hb,hs⟩ := (reads_cons T left b bs).1 h
    cases b
    · apply (reads_cons _ left true bs).2
      exact ⟨by simp [carryTape,put],reads_put_outside T left bs hs _ _ (by omega)⟩
    · change Reads (carryTape (put T (left+bs.length+1) (some false)) left bs) left
        (false :: (inc bs).1)
      apply (reads_cons _ left false (inc bs).1).2
      constructor
      · rw [inc_length,carry_frame _ left bs _ (Or.inr (by omega))]
        simp [put]
      · exact ih _ (reads_put_outside T left bs hs _ _ (by omega))

theorem carry_path (T : Nat → Option Bool) (left r : Nat) (bs : List Bool)
    (hl : T left = none) (hr : T (left+bs.length+r+1) = none)
    (digits : Reads T left bs)
    (occ : ∀ i, left+bs.length < i → i < left+bs.length+r+1 → ∃ b, T i = some b) :
    Path (left+bs.length+r+1) (carryClock bs r)
      ⟨q 3,left+bs.length,T⟩
      ⟨if (inc bs).2 then machine.accept else q 2,
        if (inc bs).2 then left+1 else left+bs.length+r+1,carryTape T left bs⟩ := by
  induction bs generalizing r T with
  | nil =>
    have one := hop (q 3) machine.accept left (left+1) T none .right (P := left+0+r+1)
        (by omega) (by omega) (by rw [hl]; rfl) rfl
    rw [← hl,put_same] at one
    simpa [carryClock,inc,carryTape] using one
  | cons b bs ih =>
    obtain ⟨hb,hs⟩ := (reads_cons T left b bs).1 digits
    cases b with
    | false =>
      let U := put T (left+bs.length+1) (some true)
      let R := left+(false::bs).length+r+1
      have one := hop (q 3) (q 4) (left+bs.length+1) (left+bs.length+2) T (some true) .right
        (P := R) (by dsimp [R]; omega) (by dsimp [R]; omega) (by rw [hb]; rfl) rfl
      have sw := sweep U (left+bs.length+2) r (by
        intro i hlo hhi
        dsimp [U]; rw [put,if_neg (by omega)]
        exact occ i (by simp; omega) (by simp at *; omega))
      have eqR : left+bs.length+2+r=R := by dsimp [R]; omega
      rw [eqR] at sw
      have last := hop (q 4) (q 2) R R U none .stay (P := R) le_rfl le_rfl
        (by dsimp [U]; rw [put,if_neg (by dsimp [R]; omega)]; rw [show R=left+(false::bs).length+r+1 from rfl,hr]; rfl) rfl
      have hUr : U R=none := by dsimp [U]; rw [put,if_neg (by dsimp [R]; omega)]; exact hr
      rw [← hUr,put_same] at last
      simpa [carryClock,inc,carryTape,U,R,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (one.append sw).append last
    | true =>
      let U := put T (left+bs.length+1) (some false)
      let R := left+(true::bs).length+r+1
      have one := hop (q 3) (q 3) (left+bs.length+1) (left+bs.length) T (some false) .left
        (P := R) (by dsimp [R]; omega) (by dsimp [R]; omega) (by rw [hb]; rfl) (by simp [dest])
      have rest := ih U (r+1)
        (by dsimp [U]; simp [put,show left≠left+bs.length+1 by omega,hl])
        (by dsimp [U]; rw [put,if_neg (by omega)]; simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr)
        (reads_put_outside T left bs hs _ _ (by omega))
        (by
          intro i hlo hhi
          by_cases he : i=left+bs.length+1
          · exact ⟨false,by simp [U,put,he]⟩
          · dsimp [U]; rw [put,if_neg he]
            exact occ i (by simp; omega) (by simp at *; omega))
      have eqR : left+bs.length+(r+1)+1=R := by dsimp [R]; omega
      rw [eqR] at rest
      simpa [carryClock,inc,carryTape,U,R,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest

theorem round_path (T : Nat → Option Bool) (left : Nat) (bs : List Bool)
    (hl : T left = none) (hr : T (left+bs.length+1) = none) (digits : Reads T left bs) :
    Path (left+bs.length+1) (roundClock bs)
      ⟨q 2,left+bs.length+1,T⟩
      ⟨if (inc bs).2 then machine.accept else q 2,
        if (inc bs).2 then left+1 else left+bs.length+1,carryTape T left bs⟩ := by
  have one := hop (q 2) (q 3) (left+bs.length+1) (left+bs.length) T none .left
    (P := left+bs.length+1) le_rfl (by omega) (by rw [hr]; rfl) (by simp [dest])
  rw [← hr,put_same] at one
  have rest := carry_path T left 0 bs hl (by simpa using hr) digits (by intro i h1 h2; omega)
  simpa [roundClock] using one.append rest

def extend {N B : Nat} (T : Fin (tapeLength N B) → Option Bool) : Nat → Option Bool :=
  fun i => if h : i < tapeLength N B then T ⟨i,h⟩ else none

@[simp] theorem extend_read {N B : Nat} (T : Fin (tapeLength N B) → Option Bool)
    (i : Fin (tapeLength N B)) : extend T i.val = T i := by simp [extend]

/-- Full Config theorem: variable width, leading false digits, zero width,
overflow and untouched exterior tape. Ready can be used as the next round entry. -/
theorem round_exact : Target.Round := by
  intro N B left bs c hp hq hh hs
  let T := extend c.tape
  have hl : T left=none := by
    have hx : left < tapeLength N B := by omega
    simpa [T,extend,hx] using (hs ⟨left,hx⟩).1 rfl
  have hr : T (left+bs.length+1)=none := by simpa [T,extend,hp] using (hs ⟨_,hp⟩).2.1 rfl
  have hd : Reads T left bs := by
    intro j hj
    have hx : left+bs.length-j < tapeLength N B := by omega
    simpa [T,extend,hx] using (hs ⟨_,hx⟩).2.2 j hj rfl
  have path := round_path T left bs hl hr hd
  have he := path.execute hp
  have hc : embed (N := N) (B := B) ⟨q 2,left+bs.length+1,T⟩ hp = c := by
    apply Config.ext_parts hq.symm (Fin.ext hh.symm)
    funext i; exact extend_read c.tape i
  rw [hc] at he
  dsimp only
  rw [he]
  refine ⟨rfl,rfl,?_,?_⟩
  · intro i
    refine ⟨?_,?_,?_⟩
    · intro hi
      change carryTape T left bs i.val=none
      rw [hi,carry_frame T left bs left (Or.inl le_rfl)]
      exact hl
    · intro hi
      rw [inc_length] at hi
      change carryTape T left bs i.val=none
      rw [hi,carry_frame T left bs _ (Or.inr (by omega))]
      exact hr
    · intro j hj hij
      change carryTape T left bs i.val=some ((inc bs).1[j]!)
      rw [hij]
      exact carry_reads T left bs hd j hj
  · intro i hi
    change carryTape T left bs i.val=c.tape i
    rw [carry_frame T left bs i.val hi]
    exact extend_read c.tape i

/-- Numeric meaning of the physical word, including the overflow bit. -/
theorem inc_value (bs : List Bool) :
    value (inc bs).1 + (if (inc bs).2 then 2^bs.length else 0) = value bs + 1 := by
  induction bs with
  | nil => simp [inc,value]
  | cons b bs ih =>
    cases b
    · simp [inc,value]; omega
    · cases h : (inc bs).2 <;> simp [inc,value,h,Nat.pow_succ] at * <;> omega

def clear (T : Nat → Option Bool) (h n : Nat) : Nat → Option Bool :=
  fun i => if h ≤ i ∧ i < h+n then some false else T i

theorem clear_step (T : Nat → Option Bool) (h n : Nat) :
    clear (put T h (some false)) (h+1) n = clear T h (n+1) := by
  funext i
  simp only [clear,put]
  split_ifs <;> simp_all <;> omega

theorem seed_path (T : Nat → Option Bool) (h n : Nat)
    (marks : ∀ i, h ≤ i → i < h+n → T i=some true) (endBlank : T (h+n)=none) :
    Path (h+n) (n+1) ⟨q 1,h,T⟩ ⟨q 2,h+n,clear T h n⟩ := by
  induction n generalizing T h with
  | zero =>
    have one := hop (q 1) (q 2) h h T none .stay (P := h) le_rfl le_rfl
      (by rw [show T h=none by simpa using endBlank]; rfl) rfl
    have hb : T h=none := by simpa using endBlank
    rw [← hb,put_same] at one
    have hz : clear T h 0=T := by funext i; simp [clear]
    simpa [hz] using one
  | succ n ih =>
    have hb := marks h le_rfl (by omega)
    let U := put T h (some false)
    have one := hop (q 1) (q 1) h (h+1) T (some false) .right (P := h+(n+1))
      (by omega) (by omega) (by rw [hb]; rfl) rfl
    have rest := ih U (h+1)
      (by intro i h1 h2; dsimp [U]; rw [put,if_neg (by omega)]; exact marks i (by omega) (by omega))
      (by dsimp [U]; rw [put,if_neg (by omega)]; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using endBlank)
    have eqP : h+1+n=h+(n+1) := by omega
    rw [eqP] at rest
    simpa [U,clear_step,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest

/-- Installation consumes actual unary marks, without assuming precleared scratch. -/
theorem install_path (T : Nat → Option Bool) (left n : Nat)
    (startBlank : T left=none)
    (marks : ∀ i, left < i → i < left+n+1 → T i=some true)
    (endBlank : T (left+n+1)=none) :
    Path (left+n+1) (n+2) ⟨machine.start,left,T⟩
      ⟨q 2,left+n+1,clear T (left+1) n⟩ := by
  have one := hop machine.start (q 1) left (left+1) T none .right (P := left+n+1)
    (by omega) (by omega) (by rw [startBlank]; rfl) rfl
  rw [← startBlank,put_same] at one
  have rest := seed_path T (left+1) n
    (by intro i h1 h2; exact marks i (by omega) (by omega))
    (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using endBlank)
  have eqP : left+1+n=left+n+1 := by omega
  rw [eqP] at rest
  simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using one.append rest

def iterBits (bs : List Bool) : Nat → List Bool
  | 0 => bs
  | r+1 => iterBits (inc bs).1 r

def iterClock (bs : List Bool) : Nat → Nat
  | 0 => 0
  | r+1 => roundClock bs + iterClock (inc bs).1 r

def Good (bs : List Bool) : Nat → Prop
  | 0 => True
  | r+1 => (inc bs).2=false ∧ Good (inc bs).1 r

theorem iter_length (bs : List Bool) (r : Nat) : (iterBits bs r).length=bs.length := by
  induction r generalizing bs with
  | zero => rfl
  | succ r ih => simp only [iterBits,ih,inc_length]

theorem value_lt (bs : List Bool) : value bs < 2^bs.length := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih => cases b <;> simp only [value,Bool.toNat_false,Bool.toNat_true,List.length_cons,Nat.pow_succ] <;> omega

theorem good_of_lt (bs : List Bool) (r : Nat) (h : value bs+r < 2^bs.length) : Good bs r := by
  induction r generalizing bs with
  | zero => trivial
  | succ r ih =>
    have hv := inc_value bs
    have ho : (inc bs).2=false := by
      cases hb : (inc bs).2
      · rfl
      · rw [hb] at hv; simp only [ite_true] at hv; omega
    have hi : value (inc bs).1=value bs+1 := by simpa only [ho,Bool.false_eq_true,↓reduceIte,Nat.add_zero] using hv
    exact ⟨ho,ih _ (by rw [inc_length,hi]; omega)⟩

theorem round_clock_le (bs : List Bool) : roundClock bs ≤ 2*bs.length+3 := by
  have aux : ∀ (bs : List Bool) (r : Nat), carryClock bs r ≤ 2*bs.length+r+2 := by
    intro bs
    induction bs with
    | nil => intro r; simp [carryClock]
    | cons b bs ih => intro r; cases b <;> simp only [carryClock,List.length_cons] <;> have h := ih (r+1) <;> omega
  have h := aux bs 0
  unfold roundClock; omega

theorem iter_clock_le (bs : List Bool) (r : Nat) : iterClock bs r ≤ r*(2*bs.length+3) := by
  induction r generalizing bs with
  | zero => simp [iterClock]
  | succ r ih =>
    have h1 := round_clock_le bs
    have h2 := ih (inc bs).1
    rw [inc_length] at h2
    change roundClock bs + iterClock (inc bs).1 r ≤ (r+1)*(2*bs.length+3)
    calc
      _ ≤ (2*bs.length+3) + r*(2*bs.length+3) := Nat.add_le_add h1 h2
      _ = _ := by ring

/-- Any number of nonoverflow rounds, starting from a real prior Config.
The frame equality is threaded at every reentry. -/
theorem repeated_exact {N B : Nat} (left : Nat) (bs : List Bool) (r : Nat)
    (c : Config machine.stateCount N B)
    (hp : left+bs.length+1 < tapeLength N B) (hq : c.state=q 2)
    (hh : c.head.val=left+bs.length+1) (hs : Target.Span c.tape left bs) (hg : Good bs r) :
    let e := machine.run (iterClock bs r) c
    e.state=q 2 ∧ e.head.val=left+bs.length+1 ∧ Target.Span e.tape left (iterBits bs r) ∧
    ∀ i : Fin (tapeLength N B), i.val ≤ left ∨ left+bs.length < i.val → e.tape i=c.tape i := by
  induction r generalizing c bs with
  | zero => exact ⟨hq,hh,hs,fun _ _ => rfl⟩
  | succ r ih =>
    obtain ⟨no,good⟩ := hg
    obtain ⟨q1,h1,s1,f1⟩ := round_exact N B left bs c hp hq hh hs
    simp only [no,Bool.false_eq_true,↓reduceIte] at q1 h1
    have he := ih (inc bs).1 (machine.run (roundClock bs) c)
      (by simpa only [inc_length] using hp) q1 (by simpa only [inc_length] using h1) s1 good
    dsimp only
    rw [iterClock,machine.run_add]
    refine ⟨he.1,by simpa only [inc_length] using he.2.1,he.2.2.1,?_⟩
    intro i hi
    exact (he.2.2.2 i (by simpa only [inc_length] using hi)).trans (f1 i hi)
end Body
