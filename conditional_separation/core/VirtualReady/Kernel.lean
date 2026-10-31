import VirtualReady.Target
import Complexity.PrivateInterfaceLookupResolvedCursor
namespace VirtualReady
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Tactic
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
private def sym : Option Bool → Nat | none => 0 | some false => 1 | some true => 2
private def mov : Move → Nat | .left => 0 | .stay => 1 | .right => 2
private def enc (s : Nat) (b : Option Bool) (m : Move) := 9*s+3*sym b+mov m
private def selectCursor (key : String) : TacticM Name := do
  let n ← PartAPrivateCursor.select key
  return n
private def codes (k : Nat) : Array Nat := by
  run_tac do
    let n ← selectCursor "program"; let id := mkIdent n; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident))
private def bef (k : Nat) : List Nat := by
  run_tac do
    let n ← selectCursor "before"; let id := mkIdent n; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident 0))
private def aft (k : Nat) : List Nat := by
  run_tac do
    let n ← selectCursor "after"; let id := mkIdent n; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident 0))
private def pow (k : Nat) : Nat → List Nat := by
  run_tac do
    let n ← selectCursor "power"; let id := mkIdent n; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident))
private def add (k : Nat) : Nat → List Nat := by
  run_tac do
    let n ← selectCursor "add"; let id := mkIdent n; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident))
private def mid (k : Nat) : List Nat := by
  run_tac do
    let n ← selectCursor "middle"; let id := mkIdent n; let kv := mkIdent `k
    evalTactic (← `(tactic| exact $id:ident $kv:ident 0))
private def pref (k : Nat) := bef k++(List.range k).flatMap (pow k)++mid k++(List.range k).flatMap (add k)
attribute [local irreducible] codes bef pow add mid aft pref
private theorem pref_len (k : Nat) : (pref k).length=798+279*k := by
  have a : (bef k).length=795 := by
    unfold bef
    run_tac do
      let n ← selectCursor "before"; let id := mkIdent n
      evalTactic (← `(tactic| simp only [$id:ident,List.length_append]))
      for j in List.range 12 do
        let n ← selectCursor ("before"++toString j); let id := mkIdent n; let kv := mkIdent `k
        let len := if j=11 then 3 else 72
        evalTactic (← `(tactic| have hl : ($id:ident $kv:ident 0).length=$(quote len) := rfl))
        evalTactic (← `(tactic| rw [hl]))
  have b (j : Nat) : (pow k j).length=246 := by unfold pow; rfl
  have c : (mid k).length=3 := by unfold mid; rfl
  have d (j : Nat) : (add k j).length=33 := by unfold add; rfl
  simp [pref,List.length_flatMap,a,b,c,d]
  omega
private theorem program_split (k : Nat) : codes k=(pref k++aft k).toArray := by
  unfold codes pref bef pow mid add aft
  run_tac do
    let n ← selectCursor "program"; let id := mkIdent n
    evalTactic (← `(tactic| simp only [$id:ident,List.append_assoc]))
private abbrev ins (k : Nat) : List Nat := [(8012+837*k), (8015+837*k), (8018+837*k), (8019+837*k), (8015+837*k), (8015+837*k), (8029+837*k), (8022+837*k), (8025+837*k), (8039+837*k), (8042+837*k), (8045+837*k), (8047+837*k), (8042+837*k), (8045+837*k), (8057+837*k), (8060+837*k), (8063+837*k), (8064+837*k), (8060+837*k), (8060+837*k), (8074+837*k), (8067+837*k), (8070+837*k), (8084+837*k), (8087+837*k), (8090+837*k), (8092+837*k), (8087+837*k), (8090+837*k), (8102+837*k), (8105+837*k), (8108+837*k), (8109+837*k), (8105+837*k), (8105+837*k), (8119+837*k), (8112+837*k), (8115+837*k), (8129+837*k), (8132+837*k), (8135+837*k), (8137+837*k), (8132+837*k), (8135+837*k), (8147+837*k), (8150+837*k), (8153+837*k), (8154+837*k), (8150+837*k), (8150+837*k), (8164+837*k), (8157+837*k), (8160+837*k), (8174+837*k), (8177+837*k), (8180+837*k), (8182+837*k), (8177+837*k), (8180+837*k), (8192+837*k), (8195+837*k), (8198+837*k), (8199+837*k), (8195+837*k), (8195+837*k), (8209+837*k), (8202+837*k), (8205+837*k), (8219+837*k), (8222+837*k), (8225+837*k), (8227+837*k), (8222+837*k), (8225+837*k), (8237+837*k), (8240+837*k), (8243+837*k), (8244+837*k), (8240+837*k), (8240+837*k), (8254+837*k), (8247+837*k), (8250+837*k), (8262+837*k), (8265+837*k), (8268+837*k), (8272+837*k), (8265+837*k), (8268+837*k), (8280+837*k), (8283+837*k), (8286+837*k), (8290+837*k), (8283+837*k), (8286+837*k), (8298+837*k), (8301+837*k), (8304+837*k), (8308+837*k), (8301+837*k), (8304+837*k), (8316+837*k), (8319+837*k), (8322+837*k), (8326+837*k), (8319+837*k), (8322+837*k), (8334+837*k), (8337+837*k), (8340+837*k), (8344+837*k), (8337+837*k), (8340+837*k), (8352+837*k), (8355+837*k), (8358+837*k), 361, (8364+837*k), 367, (8361+837*k), 364, (8376+837*k), (8380+837*k), 364, (8376+837*k), (8388+837*k), (8391+837*k), (8394+837*k), (8399+837*k), (8391+837*k), (8391+837*k), (8425+837*k), (8402+837*k), (8402+837*k)]
private theorem after_drop (k : Nat) : (aft k).drop 1677=ins k++(aft k).drop 1812 := by
  unfold aft
  run_tac do
    let n ← selectCursor "after"; let id := mkIdent n
    evalTactic (← `(tactic| simp only [$id:ident,List.append_assoc]))
  rfl
private theorem clean_lookup (k j : Nat) (hj : j < 135) :
    (codes k)[2475+279*k+j]?=(ins k)[j]? := by
  rw [program_split,List.getElem?_toArray,List.getElem?_append,if_neg (by rw [pref_len]; omega)]
  rw [show 2475+279*k+j-(pref k).length=1677+j by rw [pref_len]; omega,
    ← List.getElem?_drop,after_drop,List.getElem?_append,if_pos (by change j < 135; exact hj)]
private theorem gate_lookup (k b : Nat) (hb : b < 3) :
    (codes k)[2202+279*k+b]?=some (8002+837*k+3*b) := by
  rw [program_split,List.getElem?_toArray,List.getElem?_append,if_neg (by rw [pref_len]; omega)]
  rw [show 2202+279*k+b-(pref k).length=1404+b by rw [pref_len]; omega]
  have tail : (aft k).drop 1404=[8002+837*k,8005+837*k,8008+837*k]++(aft k).drop 1407 := by
    unfold aft
    run_tac do
      let n ← selectCursor "after"; let id := mkIdent n
      evalTactic (← `(tactic| simp only [$id:ident,List.append_assoc]))
    rfl
  rw [← List.getElem?_drop,tail,List.getElem?_append,if_pos (by simpa using hb)]
  interval_cases b <;> (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]) <;> congr 1 <;> omega
private theorem decode_actual (k i code : Nat) (b : Option Bool) (lo : 68 ≤ i)
    (hi : i < Cursor.stateCount k)
    (got : (codes k)[3*(i-64)+sym b]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  have mod : i%Cursor.stateCount k=i := Nat.mod_eq_of_lt hi
  simp only [UniformTM.step,Cursor.machine,Cursor.q,mod,
    Nat.mod_eq_of_lt (show 39 < Cursor.stateCount k by unfold Cursor.stateCount; omega),
    Nat.mod_eq_of_lt (show 40 < Cursor.stateCount k by unfold Cursor.stateCount; omega),Fin.mk.injEq,
    show i≠39 by omega,show i≠40 by omega,↓reduceIte]
  run_tac do
    let n ← selectCursor "decode"; let id := mkIdent n
    evalTactic (← `(tactic| simp only [$id:ident]))
  simp only [show i≠57 by omega,show i≠58 by omega,show ¬i < 64 by omega,
    show i≠65 by omega,show i≠66 by omega,show i≠67 by omega,↓reduceIte]
  unfold codes at got
  cases b with
  | none => dsimp only [sym] at got; dsimp only; rw [got]; rfl
  | some b => cases b <;> dsimp only [sym] at got <;> dsimp only <;> rw [got] <;> rfl
private theorem dec_enc (k s : Nat) (b : Option Bool) (m : Move) :
    (Cursor.q k (enc s b m/9),(if enc s b m/3%3=0 then none else some (decide (enc s b m/3%3=2))),
      if enc s b m%3=0 then Move.left else if enc s b m%3=1 then Move.stay else Move.right)=
      (Cursor.q k s,b,m) := by
  cases b with
  | none => cases m <;> simp [enc,sym,mov,Nat.add_div,Nat.add_mod,Nat.mul_mod] <;> omega
  | some b => cases b <;> cases m <;> simp [enc,sym,mov,Nat.add_div,Nat.add_mod,Nat.mul_mod] <;> omega
private theorem clean_row (k j s : Nat) (b w : Option Bool) (m : Move) (hj : j < 45)
    (got : (ins k)[3*j+sym b]?=some (enc s w m)) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+j)) b=(Cursor.q k s,w,m) := by
  apply Eq.trans (decode_actual k (889+93*k+j) (enc s w m) b (by omega) (by unfold Cursor.stateCount; omega) _) (dec_enc k s w m)
  rw [show 3*(889+93*k+j-64)+sym b=2475+279*k+(3*j+sym b) by omega,clean_lookup k _ (by cases b with | none => simp [sym]; omega | some b => cases b <;> simp [sym] <;> omega)]
  exact got
private theorem gate_row (k : Nat) (b : Option Bool) :
    (Cursor.machine k).step (Cursor.q k (798+93*k)) b=(Cursor.q k (889+93*k),b,.stay) := by
  apply Eq.trans (decode_actual k (798+93*k) (enc (889+93*k) b .stay) b (by omega) (by unfold Cursor.stateCount; omega) _) (dec_enc k _ b .stay)
  rw [show 3*(798+93*k-64)+sym b=2202+279*k+sym b by omega,gate_lookup k _ (by cases b with | none => decide | some b => cases b <;> decide)]
  congr 1
  unfold enc mov
  ring
private structure Node (k : Nat) where
  state : Fin (Cursor.stateCount k)
  head : Nat
  tape : Nat → Option Bool
private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i
private def embed {k N B : Nat} (c : Node k) (h : c.head < tapeLength N B) : Config (Cursor.stateCount k) N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩
private def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1
private structure Edge (k P : Nat) (c d : Node k) : Prop where
  before : c.head   ≤   P
  after : d.head   ≤   P
  row : ((Cursor.machine k).step c.state (c.tape c.head)).1 = d.state
  move : dest c.head ((Cursor.machine k).step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head ((Cursor.machine k).step c.state (c.tape c.head)).2.1
private inductive Path (k P : Nat) : Nat → Node k → Node k → Prop
  | nil (c) (h : c.head   ≤   P) : Path k P 0 c c
  | cons {t c d e} : Edge k P c d → Path k P t d e → Path k P (t+1) c e
namespace Path
private theorem bounds {k P t c d} (h : Path k P t c d) : c.head   ≤   P ∧ d.head   ≤   P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩
private theorem append {k P t u c d e} (h : Path k P t c d) (g : Path k P u d e) :
    Path k P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)
private theorem execute {k N B P t c d} (h : Path k P t c d) (hp : P < tapeLength N B) :
    (Cursor.machine k).run t (embed c (lt_of_le_of_lt h.bounds.1 hp)) =
      embed d (lt_of_le_of_lt h.bounds.2 hp) := by
  have step {c d} (e : Edge k P c d) :
      (Cursor.machine k).stepConfig (embed c (lt_of_le_of_lt e.before hp)) =
        embed d (lt_of_le_of_lt e.after hp) := by
    apply Config.ext_parts
    · exact e.row
    · apply Fin.ext
      change (moveHead _ ((Cursor.machine k).step c.state (c.tape c.head)).2.2).val = d.head
      have hm := e.move
      cases mv : ((Cursor.machine k).step c.state (c.tape c.head)).2.2 with
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
      (Cursor.machine k).run t (embed c hc) = embed d hd by exact aux _ _
  induction h with
  | nil => intro _ _; simp only [UniformTM.run]
  | @cons t c d e ed path ih =>
    intro hc he
    rw [show t+1=1+t by omega,(Cursor.machine k).run_add]
    rw [show (Cursor.machine k).run 1 (embed c hc)=(Cursor.machine k).stepConfig (embed c hc) by simp only [UniformTM.run]]
    rw [step ed]
    exact ih _ _
end Path
private theorem hop {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (b : Option Bool) (m : Move) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]
private theorem keep {k P : Nat} (s s' : Fin (Cursor.stateCount k)) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (hb : h   ≤   P) (ha : h'   ≤   P)
    (row : (Cursor.machine k).step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path k P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop s s' h h' T (T h) m hb ha row hm
  rwa [put_same] at one
private theorem sweepR {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h r : Nat) (fit : h+r   ≤   P) (rows : ∀ i, h   ≤   i → i < h+r → (Cursor.machine k).step s (T i)=(s,T i,.right)) :
    Path k P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep s s h (h+1) T .right (P := P) (by omega) (by omega) (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
private theorem sweepL {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (low r : Nat) (fit : low+r   ≤   P) (rows : ∀ i, low < i → i   ≤   low+r → (Cursor.machine k).step s (T i)=(s,T i,.left)) :
    Path k P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep s s (low+(r+1)) (low+r) T .left (P := P) (by omega) (by omega) (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest
private def paint (T : Nat → Option Bool) (lo hi : Nat) : Nat → Option Bool :=
  fun i => if lo ≤ i ∧ i < hi then some false else T i
private theorem paint_old (T : Nat → Option Bool) (lo hi i : Nat) (h : i < lo ∨ hi ≤ i) : paint T lo hi i=T i := by
  simp only [paint]; rw [if_neg (by omega)]
private theorem eraseR {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (h n : Nat)
    (fit : h+n ≤ P) (cells : ∀ i, h ≤ i → i < h+n → ∃ b, T i=some b)
    (row : ∀ b, (Cursor.machine k).step s (some b)=(s,some false,.right)) :
    Path k P n ⟨s,h,T⟩ ⟨s,h+n,paint T h (h+n)⟩ := by
  induction n generalizing h T with
  | zero =>
    have eq : paint T h (h+0)=T := by funext i; simp only [paint]; rw [if_neg (by omega)]
    rw [eq]; simpa using Path.nil ⟨s,h,T⟩ fit
  | succ n ih =>
    obtain ⟨b,hb⟩ := cells h le_rfl (by omega)
    have one := hop s s h (h+1) T (some false) .right (P:=P) (by omega) (by omega)
      (by rw [hb]; exact row b) rfl
    have rest := ih (put T h (some false)) (h+1) (by omega) (by
      intro i lo hi
      rw [put,if_neg (by omega)]
      exact cells i (by omega) (by omega))
    have image : paint (put T h (some false)) (h+1) (h+1+n)=paint T h (h+(n+1)) := by
      funext i
      simp only [paint,put]
      split_ifs <;> first | rfl | omega
    have joined := one.append rest
    rw [image] at joined
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using joined
private theorem eraseL {k P : Nat} (s : Fin (Cursor.stateCount k)) (T : Nat → Option Bool) (lo n : Nat)
    (fit : lo+n ≤ P) (cells : ∀ i, lo < i → i ≤ lo+n → ∃ b, T i=some b)
    (row : ∀ b, (Cursor.machine k).step s (some b)=(s,some false,.left)) :
    Path k P n ⟨s,lo+n,T⟩ ⟨s,lo,paint T (lo+1) (lo+n+1)⟩ := by
  induction n generalizing T with
  | zero =>
    have eq : paint T (lo+1) (lo+0+1)=T := by funext i; simp only [paint]; rw [if_neg (by omega)]
    rw [eq]; simpa using Path.nil ⟨s,lo,T⟩ fit
  | succ n ih =>
    obtain ⟨b,hb⟩ := cells (lo+(n+1)) (by omega) le_rfl
    have one := hop s s (lo+(n+1)) (lo+n) T (some false) .left (P:=P) (by omega) (by omega)
      (by rw [hb]; exact row b) (by simp [dest])
    have rest := ih (put T (lo+(n+1)) (some false)) (by omega) (by
      intro i hl hh
      rw [put,if_neg (by omega)]
      exact cells i hl (by omega))
    have image : paint (put T (lo+(n+1)) (some false)) (lo+1) (lo+n+1)=paint T (lo+1) (lo+(n+1)+1) := by
      funext i
      simp only [paint,put]
      split_ifs <;> first | rfl | omega
    simpa only [image,Nat.add_comm] using one.append rest
private theorem clean_at (k i s : Nat) (b w : Option Bool) (m : Move)
    (lo : 889+93*k ≤ i) (hi : i < 934+93*k)
    (got : (ins k)[3*(i-(889+93*k))+sym b]?=some (enc s w m)) :
    (Cursor.machine k).step (Cursor.q k i) b=(Cursor.q k s,w,m) := by
  have eq : i=889+93*k+(i-(889+93*k)) := by omega
  conv_lhs => rw [eq]
  exact clean_row k _ s b w m (by omega) got
private theorem bank_row (k : Nat) (j : Fin 6) (o s : Nat) (b w : Option Bool) (m : Move)
    (ho : o ≤ 4) (got : (ins k)[3*(5*j.val+o)+sym b]?=some (enc s w m)) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+5*j.val+o)) b=(Cursor.q k s,w,m) := by
  simpa only [Nat.add_assoc] using clean_row k (5*j.val+o) s b w m (by have h:=j.isLt; omega) got
private theorem erase_rows (k : Nat) (j : Fin 6) (b : Bool) :
    let s := 889+93*k+5*j.val
    (Cursor.machine k).step (Cursor.q k s) none=(Cursor.q k (s+1),none,.right) ∧
    (Cursor.machine k).step (Cursor.q k (s+1)) (some b)=(Cursor.q k (s+1),some false,.right) ∧
    (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k (s+2),none,.left) ∧
    (Cursor.machine k).step (Cursor.q k (s+2)) (some b)=(Cursor.q k (s+2),some b,.left) ∧
    (Cursor.machine k).step (Cursor.q k (s+2)) none=(Cursor.q k (s+3),none,.stay) := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply bank_row k j 0 _ _ _ _ (by decide)
    fin_cases j <;> dsimp only [ins,enc,sym,mov] <;> (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]) <;> (congr 1; ring; all_goals rfl)
  all_goals apply bank_row <;> try decide
  all_goals fin_cases j <;> cases b <;> dsimp only [ins,enc,sym,mov] <;> (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]) <;> (congr 1; ring)
private theorem forward_rows (k : Nat) (j : Fin 5) (b : Bool) :
    let s := 889+93*k+5*j.val
    (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k (s+4),none,.right) ∧
    (Cursor.machine k).step (Cursor.q k (s+4)) (some b)=(Cursor.q k (s+4),some b,.right) ∧
    (Cursor.machine k).step (Cursor.q k (s+4)) none=(Cursor.q k (s+5),none,.stay) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  all_goals apply bank_row k ⟨j.val,by omega⟩ <;> try decide
  all_goals fin_cases j <;> cases b <;> dsimp only [ins,enc,sym,mov] <;> (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]) <;> (congr 1; ring)
private theorem round_clear (k P low len : Nat) (j : Fin 6) (T : Nat → Option Bool)
    (fit : low+len+1 ≤ P) (left : T low=none) (right : T (low+len+1)=none)
    (cells : ∀ i, low < i → i < low+len+1 → ∃ b, T i=some b) :
    Path k P (2*len+3) ⟨Cursor.q k (889+93*k+5*j.val),low,T⟩
      ⟨Cursor.q k (889+93*k+5*j.val+3),low,paint T (low+1) (low+len+1)⟩ := by
  let s := 889+93*k+5*j.val
  let U := paint T (low+1) (low+len+1)
  have UL : U low=none := by change paint T (low+1) (low+len+1) low=none; rw [paint_old T _ _ low (Or.inl (by omega))]; exact left
  have UR : U (low+len+1)=none := by change paint T (low+1) (low+len+1) (low+len+1)=none; rw [paint_old T _ _ (low+len+1) (Or.inr le_rfl)]; exact right
  have zero (i : Nat) (hl : low < i) (hh : i < low+len+1) : U i=some false := by simp only [U,paint]; rw [if_pos (by omega)]
  have a := keep (Cursor.q k s) (Cursor.q k (s+1)) low (low+1) T .right (P:=P) (by omega) (by omega)
    (by rw [left]; exact (erase_rows k j false).1) rfl
  have b := eraseR (Cursor.q k (s+1)) T (low+1) len (P:=P) (by omega)
    (by intro i hl hh; exact cells i (by omega) (by omega)) (fun b => (erase_rows k j b).2.1)
  rw [show low+1+len=low+len+1 by omega] at b
  have c := keep (Cursor.q k (s+1)) (Cursor.q k (s+2)) (low+len+1) (low+len) U .left (P:=P) (by omega) (by omega)
    (by rw [UR]; exact (erase_rows k j false).2.2.1) (by simp [dest])
  have d := sweepL (Cursor.q k (s+2)) U low len (P:=P) (by omega) (by
    intro i hl hh
    rw [zero i hl (by omega)]
    exact (erase_rows k j false).2.2.2.1)
  have e := keep (Cursor.q k (s+2)) (Cursor.q k (s+3)) low low U .stay (P:=P) (by omega) (by omega)
    (by rw [UL]; exact (erase_rows k j false).2.2.2.2) rfl
  convert a.append (b.append (c.append (d.append e))) using 1; omega
private theorem bank_clear (k P low len : Nat) (j : Fin 5) (T : Nat → Option Bool)
    (fit : low+len+1 ≤ P) (left : T low=none) (right : T (low+len+1)=none)
    (cells : ∀ i, low < i → i < low+len+1 → ∃ b, T i=some b) :
    Path k P (3*len+5) ⟨Cursor.q k (889+93*k+5*j.val),low,T⟩
      ⟨Cursor.q k (889+93*k+5*j.val+5),low+len+1,paint T (low+1) (low+len+1)⟩ := by
  let s := 889+93*k+5*j.val
  let U := paint T (low+1) (low+len+1)
  have UL : U low=none := by change paint T (low+1) (low+len+1) low=none; rw [paint_old T _ _ low (Or.inl (by omega))]; exact left
  have UR : U (low+len+1)=none := by change paint T (low+1) (low+len+1) (low+len+1)=none; rw [paint_old T _ _ (low+len+1) (Or.inr le_rfl)]; exact right
  have a := round_clear k P low len ⟨j.val,by omega⟩ T fit left right cells
  have b := keep (Cursor.q k (s+3)) (Cursor.q k (s+4)) low (low+1) U .right
    (P:=P) (by omega) (by omega) (by rw [UL]; exact (forward_rows k j false).1) rfl
  have c := sweepR (Cursor.q k (s+4)) U (low+1) len (P:=P) (by omega) (by
    intro i hl hh
    have z : U i=some false := by simp only [U,paint]; rw [if_pos (by omega)]
    rw [z]; exact (forward_rows k j false).2.1)
  rw [show low+1+len=low+len+1 by omega] at c
  have d := keep (Cursor.q k (s+4)) (Cursor.q k (s+5)) (low+len+1) (low+len+1) U .stay
    (P:=P) fit fit (by rw [UR]; exact (forward_rows k j false).2.2) rfl
  convert a.append (b.append (c.append d)) using 1; omega
private def D (F r n : Nat) : Nat → Nat
  | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
  | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
private def len (n r j : Nat) := if j=1 then n else r
private theorem Dstep (F r n j : Nat) (hj : j < 6) : D F r n (j+1)=D F r n j+len n r j+1 := by
  interval_cases j <;> simp [D,len] <;> omega
private theorem Dmono (F r n a b : Nat) (ha : a ≤ b) (hb : b ≤ 6) : D F r n a ≤ D F r n b := by
  interval_cases b <;> interval_cases a <;> simp only [D] <;> omega
private def stage (T : Nat → Option Bool) (F r n : Nat) : Nat → Nat → Option Bool
  | 0 => T
  | j+1 => paint (stage T F r n j) (D F r n j+1) (D F r n (j+1))
private theorem stage_old (T : Nat → Option Bool) (F r n j i : Nat)
    (outside : ∀ b, b < j → i ≤ D F r n b ∨ D F r n (b+1) ≤ i) : stage T F r n j i=T i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [stage,paint_old _ _ _ _ (by have h := outside j (by omega); omega)]
    exact ih (by intro b hb; exact outside b (by omega))
private theorem stage_blank (T : Nat → Option Bool) (F r n j d : Nat) (hj : j ≤ 6) (hd : d ≤ 6)
    (blank : T (D F r n d)=none) : stage T F r n j (D F r n d)=none := by
  rw [stage_old]
  · exact blank
  · intro b hb
    by_cases lower : d ≤ b
    · exact Or.inl (Dmono F r n d b lower (by omega))
    · exact Or.inr (Dmono F r n (b+1) d (by omega) hd)
private theorem stage_cell (T : Nat → Option Bool) (F r n j i : Nat) (cell : ∃ b, T i=some b) :
    ∃ b, stage T F r n j i=some b := by
  induction j with
  | zero => exact cell
  | succ j ih =>
    simp only [stage,paint]
    split_ifs
    · exact ⟨false,rfl⟩
    · exact ih
private structure Frame (T : Nat → Option Bool) (L n Q F r : Nat) : Prop where
  paid : 0 < Q
  room : L+n+1+Q < F
  blank : ∀ j, j ≤ 6 → T (D F r n j)=none
  cells : ∀ j, j < 6 → ∀ i, D F r n j < i → i < D F r n (j+1) → ∃ b, T i=some b
  fence : T F=some false
  gap : ∀ i, L+n+1+Q < i → i < F → T i=none
  marks : ∀ i, L+n+1 < i → i ≤ L+n+1+Q → T i=some true
  sep : T L=none
  right : T (L+n+1)=none
  assn : ∀ i, L < i → i < L+n+1 → ∃ b, T i=some b
private def bankCost (n r : Nat) : Nat → Nat
  | 0 => 0 | j+1 => bankCost n r j+3*len n r j+5
private theorem banks (k P L n Q F r : Nat) (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (fit : D F r n 6 ≤ P) (j : Nat) (hj : j ≤ 5) :
    Path k P (bankCost n r j) ⟨Cursor.q k (889+93*k),D F r n 0,T⟩
      ⟨Cursor.q k (889+93*k+5*j),D F r n j,stage T F r n j⟩ := by
  induction j with
  | zero => simpa only [bankCost,stage,Nat.mul_zero,Nat.add_zero] using Path.nil ⟨Cursor.q k (889+93*k),D F r n 0,T⟩ (by change D F r n 0 ≤ P; exact (Dmono F r n 0 6 (by omega) le_rfl).trans fit)
  | succ j ih =>
    have a := ih (by omega)
    have ds := Dstep F r n j (by omega)
    have b := bank_clear k P (D F r n j) (len n r j) ⟨j,by omega⟩ (stage T F r n j)
      (by rw [← ds]; exact (Dmono F r n (j+1) 6 (by omega) le_rfl).trans fit)
      (stage_blank T F r n j j (by omega) (by omega) (fr.blank j (by omega)))
      (by rw [← ds]; exact stage_blank T F r n j (j+1) (by omega) (by omega) (fr.blank _ (by omega)))
      (by intro i lo hi; rw [← ds] at hi; rw [stage_old _ _ _ _ _ i (by intro q hq; right; exact (Dmono F r n (q+1) j (by omega) (by omega)).trans (Nat.le_of_lt lo))]; exact fr.cells j (by omega) i lo hi)
    have qs : 889+93*k+5*j+5=889+93*k+5*(j+1) := by omega
    rw [qs,← ds] at b
    simpa only [bankCost,stage,Nat.add_assoc] using a.append b
private theorem back_rows (k : Nat) (j : Fin 5) (b : Option Bool) (v : Bool) :
    let s := 889+93*k
    (Cursor.machine k).step (Cursor.q k (s+(28+2*j.val))) b=(Cursor.q k (s+(29+2*j.val)),b,.left) ∧
    (Cursor.machine k).step (Cursor.q k (s+(29+2*j.val))) (some v)=(Cursor.q k (s+(29+2*j.val)),some v,.left) ∧
    (Cursor.machine k).step (Cursor.q k (s+(29+2*j.val))) none=(Cursor.q k (s+(30+2*j.val)),none,.stay) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · apply clean_row k (28+2*j.val) _ _ _ _ (by omega)
    fin_cases j <;> cases b with
    | none => dsimp only [ins,enc,sym,mov]; (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]); (congr 1; ring)
    | some b => cases b <;> dsimp only [ins,enc,sym,mov] <;> (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]) <;> (congr 1; ring)
  · apply clean_row k (29+2*j.val) _ _ _ _ (by omega)
    fin_cases j <;> cases v <;> dsimp only [ins,enc,sym,mov] <;> (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]) <;> (congr 1; ring)
  · apply clean_row k (29+2*j.val) _ _ _ _ (by omega)
    fin_cases j <;> dsimp only [ins,enc,sym,mov] <;> (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]) <;> (congr 1; ring)
private theorem back_once (k P low width : Nat) (j : Fin 5) (T : Nat → Option Bool)
    (fit : low+width+1 ≤ P) (blank : T low=none)
    (cells : ∀ i, low < i → i ≤ low+width → ∃ b, T i=some b) :
    Path k P (width+2) ⟨Cursor.q k (889+93*k+(28+2*j.val)),low+width+1,T⟩
      ⟨Cursor.q k (889+93*k+(30+2*j.val)),low,T⟩ := by
  let s := 889+93*k
  have a := keep (Cursor.q k (s+(28+2*j.val))) (Cursor.q k (s+(29+2*j.val))) (low+width+1) (low+width) T .left
    (P:=P) fit (by omega) (back_rows k j (T (low+width+1)) false).1 (by simp [dest])
  have b := sweepL (Cursor.q k (s+(29+2*j.val))) T low width (P:=P) (by omega) (by
    intro i hl hh; obtain ⟨v,hv⟩ := cells i hl hh; rw [hv]; exact (back_rows k j none v).2.1)
  have c := keep (Cursor.q k (s+(29+2*j.val))) (Cursor.q k (s+(30+2*j.val))) low low T .stay
    (P:=P) (by omega) (by omega) (by rw [blank]; exact (back_rows k j none false).2.2) rfl
  convert a.append (b.append c) using 1; omega
private theorem leave0 (k : Nat) (b : Option Bool) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+38)) (b)=(Cursor.q k (889+93*k+39),(b),.left) := by
  apply clean_row k 38 _ _ _ _ (by decide)
  cases b with
  | none => dsimp only [ins,enc,sym,mov]; (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]); (congr 1; ring)
  | some b => cases b <;> dsimp only [ins,enc,sym,mov] <;> (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]) <;> (congr 1; ring)
private theorem fence_step (k : Nat) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+39)) (some false)=(Cursor.q k (889+93*k+40),(some false),.left) := by
  apply clean_row k 39 _ _ _ _ (by decide)
  dsimp only [ins,enc,sym,mov]; (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ])
  (congr 1; ring)
private theorem blank_seek (k : Nat) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+40)) (none)=(Cursor.q k (889+93*k+40),(none),.left) := by
  apply clean_row k 40 _ _ _ _ (by decide)
  dsimp only [ins,enc,sym,mov]; (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ])
  (congr 1; ring)
private theorem mark_enter (k : Nat) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+40)) (some true)=(Cursor.q k (889+93*k+41),(some true),.left) := by
  apply clean_row k 40 _ _ _ _ (by decide)
  dsimp only [ins,enc,sym,mov]; (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ])
  (congr 1; ring)
private theorem mark_seek (k : Nat) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+41)) (some true)=(Cursor.q k (889+93*k+41),(some true),.left) := by
  apply clean_row k 41 _ _ _ _ (by decide)
  dsimp only [ins,enc,sym,mov]; (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ])
  (congr 1; ring)
private theorem mark_exit (k : Nat) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+41)) (none)=(Cursor.q k (889+93*k+42),(none),.stay) := by
  apply clean_row k 41 _ _ _ _ (by decide)
  dsimp only [ins,enc,sym,mov]; (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ])
  (congr 1; ring)
private theorem assignment_enter (k : Nat) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+42)) (none)=(Cursor.q k (889+93*k+43),(none),.left) := by
  apply clean_row k 42 _ _ _ _ (by decide)
  dsimp only [ins,enc,sym,mov]; (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ])
  (congr 1; ring)
private theorem assignment_erase (k : Nat) (v : Bool) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+43)) (some v)=(Cursor.q k (889+93*k+43),(some false),.left) := by
  apply clean_row k 43 _ _ _ _ (by decide)
  cases v <;> dsimp only [ins,enc,sym,mov] <;> (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]) <;> (congr 1; ring)
private theorem assignment_back (k : Nat) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+43)) (none)=(Cursor.q k (889+93*k+44),(none),.right) := by
  apply clean_row k 43 _ _ _ _ (by decide)
  dsimp only [ins,enc,sym,mov]; (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ])
  (congr 1; ring)
private theorem assignment_forward (k : Nat) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+44)) (some false)=(Cursor.q k (889+93*k+44),(some false),.right) := by
  apply clean_row k 44 _ _ _ _ (by decide)
  dsimp only [ins,enc,sym,mov]; (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ])
  (congr 1; ring)
private theorem ready_step (k : Nat) :
    (Cursor.machine k).step (Cursor.q k (889+93*k+44)) (none)=(Cursor.q k (889+93*k+47),(none),.stay) := by
  apply clean_row k 44 _ _ _ _ (by decide)
  dsimp only [ins,enc,sym,mov]; (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ])
  (congr 1; ring)
private theorem finish (k P L n Q F r : Nat) (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (fit : D F r n 6 ≤ P) :
    Path k P (F-(L+n+1)+2*n+5) ⟨Cursor.q k (889+93*k+38),F+1,T⟩
      ⟨Cursor.q k (889+93*k+47),L+n+1,paint T (L+1) (L+n+1)⟩ := by
  let s := 889+93*k
  let H := L+n+1
  let g := F-(H+Q+1)
  let U := paint T (L+1) H
  have room := fr.room
  have paid := fr.paid
  have fP : F+1 ≤ P := by have h:=Dmono F r n 0 6 (by omega) le_rfl; change F+1 ≤ D F r n 6 at h; omega
  have a := keep (Cursor.q k (s+38)) (Cursor.q k (s+39)) (F+1) F T .left (P:=P) fP (by omega) (leave0 k (T (F+1))) (by simp [dest])
  have b := keep (Cursor.q k (s+39)) (Cursor.q k (s+40)) F (F-1) T .left (P:=P) (by omega) (by omega)
    (by rw [fr.fence]; exact fence_step k) rfl
  have gapEq : H+Q+g=F-1 := by dsimp [g,H]; omega
  have c := sweepL (Cursor.q k (s+40)) T (H+Q) g (P:=P) (by omega) (by
    intro i lo hi
    have z := fr.gap i (by dsimp [H] at lo; omega) (by omega)
    rw [z]; exact blank_seek k)
  rw [gapEq] at c
  have d := keep (Cursor.q k (s+40)) (Cursor.q k (s+41)) (H+Q) (H+Q-1) T .left (P:=P) (by omega) (by omega)
    (by rw [fr.marks _ (by dsimp [H]; omega) (by dsimp [H]; omega)]; exact mark_enter k) rfl
  have e := sweepL (Cursor.q k (s+41)) T H (Q-1) (P:=P) (by omega) (by
    intro i lo hi; rw [fr.marks i (by change H < i; exact lo) (by change i ≤ H+Q; omega)]; exact mark_seek k)
  rw [show H+(Q-1)=H+Q-1 by omega] at e
  have f := keep (Cursor.q k (s+41)) (Cursor.q k (s+42)) H H T .stay (P:=P) (by omega) (by omega)
    (by rw [fr.right]; exact mark_exit k) rfl
  have h := keep (Cursor.q k (s+42)) (Cursor.q k (s+43)) H (L+n) T .left (P:=P) (by omega) (by omega)
    (by rw [fr.right]; exact assignment_enter k) (by simp [dest,H])
  have i := eraseL (Cursor.q k (s+43)) T L n (P:=P) (by omega)
    (by intro i lo hi; exact fr.assn i lo (by change i < H; dsimp [H]; omega)) (assignment_erase k)
  have UL : U L=none := by change paint T (L+1) H L=none; rw [paint_old T (L+1) H L (Or.inl (by omega))]; exact fr.sep
  have UH : U H=none := by change paint T (L+1) H H=none; rw [paint_old T (L+1) H H (Or.inr le_rfl)]; exact fr.right
  have j := keep (Cursor.q k (s+43)) (Cursor.q k (s+44)) L (L+1) U .right (P:=P) (by omega) (by omega)
    (by rw [UL]; exact assignment_back k) rfl
  have u := sweepR (Cursor.q k (s+44)) U (L+1) n (P:=P) (by omega) (by
    intro i lo hi
    have z : U i=some false := by dsimp only [U,paint]; rw [if_pos (by omega)]
    rw [z]; exact assignment_forward k)
  rw [show L+1+n=H by dsimp [H]; omega] at u
  have v := keep (Cursor.q k (s+44)) (Cursor.q k (s+47)) H H U .stay (P:=P) (by omega) (by omega)
    (by rw [UH]; exact ready_step k) rfl
  have path := a.append (b.append (c.append (d.append (e.append (f.append (h.append (i.append (j.append (u.append v)))))))))
  convert path using 1
  dsimp only [g,H]
  omega
private theorem cleanup_path (k P L n Q F r : Nat) (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (fit : D F r n 6 ≤ P) :
    Path k P (F-(L+n+1)+18*r+6*n+44) ⟨Cursor.q k (798+93*k),F+1,T⟩
      ⟨Cursor.q k (889+93*k+47),L+n+1,paint (stage T F r n 6) (L+1) (L+n+1)⟩ := by
  let Z := stage T F r n 6
  have old (i : Nat) (hi : i ≤ F) : Z i=T i := by
    apply stage_old
    intro b hb
    left
    have step := Dmono F r n 0 b (by omega) (by omega)
    change F+1 ≤ D F r n b at step
    omega
  have zf : Frame Z L n Q F r := ⟨fr.paid,fr.room,
    fun j hj => stage_blank T F r n 6 j le_rfl hj (fr.blank j hj),
    fun j hj i lo hi => stage_cell T F r n 6 i (fr.cells j hj i lo hi),
    by rw [old F le_rfl]; exact fr.fence,
    by intro i lo hi; rw [old i (by omega)]; exact fr.gap i lo hi,
    by intro i lo hi; rw [old i (by have h:=fr.room; omega)]; exact fr.marks i lo hi,
    by rw [old L (by have h:=fr.room; omega)]; exact fr.sep,
    by rw [old (L+n+1) (by have h:=fr.room; omega)]; exact fr.right,
    by intro i lo hi; rw [old i (by have h:=fr.room; omega)]; exact fr.assn i lo hi⟩
  have a := keep (Cursor.q k (798+93*k)) (Cursor.q k (889+93*k)) (F+1) (F+1) T .stay
    (P:=P) ((Dmono F r n 0 6 (by omega) le_rfl).trans fit) ((Dmono F r n 0 6 (by omega) le_rfl).trans fit) (gate_row k _) rfl
  have b := banks k P L n Q F r T fr fit 5 (by decide)
  have ds := Dstep F r n 5 (by decide)
  have c := round_clear k P (D F r n 5) r ⟨5,by decide⟩ (stage T F r n 5)
    (by rw [show D F r n 5+r+1=D F r n 6 by simp only [D]; omega]; exact fit)
    (stage_blank T F r n 5 5 (by decide) (by decide) (fr.blank _ (by decide)))
    (by rw [show D F r n 5+r+1=D F r n 6 by simp only [D]; omega]; exact stage_blank T F r n 5 6 (by decide) (by decide) (fr.blank _ (by decide)))
    (by intro i lo hi; rw [show D F r n 5+r+1=D F r n 6 by simp only [D]; omega] at hi; exact stage_cell T F r n 5 i (fr.cells 5 (by decide) i lo hi))
  rw [show D F r n 5+r+1=D F r n 6 by simp only [D]; omega] at c
  have back (j : Fin 5) :
      Path k P (len n r (4-j.val)+2) ⟨Cursor.q k (889+93*k+(28+2*j.val)),D F r n (5-j.val),Z⟩
        ⟨Cursor.q k (889+93*k+(30+2*j.val)),D F r n (4-j.val),Z⟩ := by
    have jb := j.isLt
    have dstep := Dstep F r n (4-j.val) (by omega)
    have h := back_once k P (D F r n (4-j.val)) (len n r (4-j.val)) j Z
      (by rw [← dstep]; exact (Dmono F r n (4-j.val+1) 6 (by omega) le_rfl).trans fit)
      (zf.blank _ (by omega)) (by intro i lo hi; exact zf.cells _ (by omega) i lo (by rw [dstep]; omega))
    rw [← dstep,show 4-j.val+1=5-j.val by omega] at h
    exact h
  have d := back ⟨0,by decide⟩
  have e := back ⟨1,by decide⟩
  have f := back ⟨2,by decide⟩
  have g := back ⟨3,by decide⟩
  have h := back ⟨4,by decide⟩
  have last := finish k P L n Q F r Z zf fit
  have whole := a.append (b.append (c.append (d.append (e.append (f.append (g.append (h.append last)))))))
  convert whole using 1
  simp [bankCost,len]
  omega
private theorem low_row (k i s : Nat) (b w : Option Bool) (m : Move) (lo : 201 ≤ i) (hi : i < 308)
    (got : (BitLengthDriver.instructions k)[3*(i-201)+sym b]?=some (enc s w m)) :
    (Cursor.machine k).step (Cursor.q k i) b=(Cursor.q k s,w,m) :=
  (BitLengthDriver.phase_row k i (enc s w m) b lo hi got).trans (dec_enc k s w m)
private theorem route_rows (k : Nat) (odd : Bool) (b : Option Bool) (v : Bool) :
    let s := if odd then 250 else 304
    (Cursor.machine k).step (Cursor.q k s) b=(Cursor.q k (s+1),b,.left) ∧
    (Cursor.machine k).step (Cursor.q k (s+1)) (some v)=(Cursor.q k (s+1),some v,.left) ∧
    (Cursor.machine k).step (Cursor.q k (s+1)) none=(Cursor.q k (s+2),none,.stay) ∧
    (Cursor.machine k).step (Cursor.q k (s+2)) b=(Cursor.q k (s+3),b,.left) ∧
    (Cursor.machine k).step (Cursor.q k (s+3)) (some v)=(Cursor.q k (s+3),some v,.left) ∧
    (Cursor.machine k).step (Cursor.q k (s+3)) none=(Cursor.q k (798+93*k),none,.stay) := by
  cases odd <;> simp only [Bool.false_eq_true,↓reduceIte]
  all_goals repeat' apply And.intro
  all_goals apply low_row k _ _ _ _ _ (by decide) (by decide)
  all_goals cases b with
  | none => cases v <;> dsimp only [BitLengthDriver.instructions,enc,sym,mov] <;> (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]) <;> (congr 1; ring)
  | some b => cases b <;> cases v <;> dsimp only [BitLengthDriver.instructions,enc,sym,mov] <;> (try simp only [List.getElem?_cons_zero,List.getElem?_cons_succ]) <;> (congr 1; ring)
private theorem route_path (k P L n Q F r : Nat) (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (fit : D F r n 6 ≤ P) (odd : Bool) :
    Path k P (n+r+4) ⟨Cursor.q k (if odd then 250 else 304),F+r+n+3,T⟩
      ⟨Cursor.q k (798+93*k),F+1,T⟩ := by
  let s := if odd then 250 else 304
  have small : F+r+n+3 ≤ P := (Dmono F r n 2 6 (by omega) le_rfl).trans fit
  have a := keep (Cursor.q k s) (Cursor.q k (s+1)) (F+r+n+3) (F+r+n+2) T .left
    (P:=P) small (by omega) (route_rows k odd (T (F+r+n+3)) false).1 (by simp [dest])
  have b := sweepL (Cursor.q k (s+1)) T (F+r+2) n (P:=P) (by omega) (by
    intro i lo hi
    obtain ⟨v,hv⟩ := fr.cells 1 (by decide) i lo (by change i < F+r+n+3; omega)
    rw [hv]; exact (route_rows k odd none v).2.1)
  rw [show F+r+2+n=F+r+n+2 by omega] at b
  have c := keep (Cursor.q k (s+1)) (Cursor.q k (s+2)) (F+r+2) (F+r+2) T .stay
    (P:=P) (by omega) (by omega) (by have h:=fr.blank 1 (by decide); change T (F+r+2)=none at h; rw [h]; exact (route_rows k odd none false).2.2.1) rfl
  have d := keep (Cursor.q k (s+2)) (Cursor.q k (s+3)) (F+r+2) (F+r+1) T .left
    (P:=P) (by omega) (by omega) (route_rows k odd (T (F+r+2)) false).2.2.2.1 (by simp [dest])
  have e := sweepL (Cursor.q k (s+3)) T (F+1) r (P:=P) (by omega) (by
    intro i lo hi
    obtain ⟨v,hv⟩ := fr.cells 0 (by decide) i lo (by change i < F+r+2; omega)
    rw [hv]; exact (route_rows k odd none v).2.2.2.2.1)
  rw [show F+1+r=F+r+1 by omega] at e
  have f := keep (Cursor.q k (s+3)) (Cursor.q k (798+93*k)) (F+1) (F+1) T .stay
    (P:=P) (by omega) (by omega) (by have h:=fr.blank 0 (by decide); change T (F+1)=none at h; rw [h]; exact (route_rows k odd none false).2.2.2.2.2) rfl
  convert a.append (b.append (c.append (d.append (e.append f)))) using 1; omega
private theorem cleanup_run (k N B L n Q F r : Nat) (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (fit : F+5*r+n+7 < tapeLength N B) (hd : F+r+n+3 < tapeLength N B) (hh : L+n+1 < tapeLength N B) :
    (Cursor.machine k).run (F-(L+n+1)+19*r+7*n+48)
      ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),⟨F+r+n+3,hd⟩,fun i => T i.val⟩=
      ⟨Cursor.mReady k ⟨2,by decide⟩,⟨L+n+1,hh⟩,
        fun i => paint (stage T F r n 6) (L+1) (L+n+1) i.val⟩ := by
  have full := cleanup_path k (F+5*r+n+7) L n Q F r T fr le_rfl
  have route : Path k (F+5*r+n+7) (n+r+4)
      ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),F+r+n+3,T⟩
      ⟨Cursor.q k (798+93*k),F+1,T⟩ := by
    by_cases odd : (r+1)%2=1
    · rw [if_pos odd]; exact route_path k _ L n Q F r T fr le_rfl true
    · rw [if_neg odd]; exact route_path k _ L n Q F r T fr le_rfl false
  have run := (route.append full).execute (N:=N) (B:=B) fit
  have ready : Cursor.q k (889+93*k+47)=Cursor.mReady k ⟨2,by decide⟩ := by
    apply Fin.ext
    change (889+93*k+47)%Cursor.stateCount k=(64+265+82*k+1+11*k+604+2)%Cursor.stateCount k
    congr 1
    omega
  have direct : (Cursor.machine k).run (n+r+4+(F-(L+n+1)+18*r+6*n+44))
      ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),⟨F+r+n+3,hd⟩,fun i => T i.val⟩=
      ⟨Cursor.q k (889+93*k+47),⟨L+n+1,hh⟩,fun i => paint (stage T F r n 6) (L+1) (L+n+1) i.val⟩ := run
  rw [ready] at direct
  rw [show n+r+4+(F-(L+n+1)+18*r+6*n+44)=F-(L+n+1)+19*r+7*n+48 by omega] at direct
  exact direct
end VirtualReady
