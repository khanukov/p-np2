import InputRead.Raw

/-! Infrastructure: R1 connected-reader surface derived from the historical G1 rehearsal.
The preserved R1 source has actual compiler/type/direct-root evidence; its earlier
PENDING note described the pre-elaboration snapshot. This correction changes only
comments and is not a fresh Lean run. Proofs reuse the original theorems; these
are literal contracts, not independent proofs. Raw guards and the accepted-side
full-gamma implication remain literal. -/
namespace Pnp3.Tests.PartAInputReadSurfaceTests
open Pnp3.Complexity.Uniform.V1
open Pnp4.Frontier.ContractExpansion Pnp4.Frontier Pnp4.AlgorithmsToLowerBounds PairEncoding
open InputRead

-- Explicit definition, proposition-alias, structure and constructor arities.
#check (InputRead.q : Nat → Fin 41)
#check (InputRead.ready : Fin 3 → Fin 41)
#check (InputRead.result : Fin 3 → Bool)
#check (InputRead.rows : Fin 41 → Option Bool → Fin 41 × Option Bool × Move)
#check (InputRead.machine : UniformTM)
#check (InputRead.rawMachine : UniformTM)
#check (InputRead.readClock : Nat → Nat → Nat → Nat)
#check (InputRead.Node : Type)
#check (InputRead.Node.mk : Fin 41 → Nat → (Nat → Option Bool) → Node)
#check (InputRead.Node.state : Node → Fin 41)
#check (InputRead.Node.head : Node → Nat)
#check (InputRead.Node.tape : Node → Nat → Option Bool)
#check (InputRead.put : (Nat → Option Bool) → Nat → Option Bool → Nat → Option Bool)
#check (@InputRead.embed : ∀ {N B : Nat} (c : Node), c.head < tapeLength N B → Config 41 N B)
#check (InputRead.dest : Nat → Move → Nat)
#check (InputRead.Edge : Nat → Node → Node → Prop)
#check (@InputRead.Edge.mk : ∀ {P : Nat} {c d : Node}, c.head ≤ P → d.head ≤ P →
  (machine.step c.state (c.tape c.head)).1 = d.state →
  dest c.head (machine.step c.state (c.tape c.head)).2.2 = d.head →
  d.tape = put c.tape c.head (machine.step c.state (c.tape c.head)).2.1 → Edge P c d)
#check (@InputRead.Edge.before : ∀ {P : Nat} {c d : Node}, Edge P c d → c.head ≤ P)
#check (@InputRead.Edge.after : ∀ {P : Nat} {c d : Node}, Edge P c d → d.head ≤ P)
#check (@InputRead.Edge.row : ∀ {P : Nat} {c d : Node}, Edge P c d →
  (machine.step c.state (c.tape c.head)).1 = d.state)
#check (@InputRead.Edge.move : ∀ {P : Nat} {c d : Node}, Edge P c d →
  dest c.head (machine.step c.state (c.tape c.head)).2.2 = d.head)
#check (@InputRead.Edge.tape : ∀ {P : Nat} {c d : Node}, Edge P c d →
  d.tape = put c.tape c.head (machine.step c.state (c.tape c.head)).2.1)
#check (InputRead.Path : Nat → Nat → Node → Node → Prop)
#check (@InputRead.Path.nil : ∀ {P : Nat} (c : Node), c.head ≤ P → Path P 0 c c)
#check (@InputRead.Path.cons : ∀ {P t : Nat} {c d e : Node},
  Edge P c d → Path P t d e → Path P (t+1) c e)
#check (InputRead.Target.CursorRead : Prop)
#check (InputRead.Target.PartA : (Nat → UniformTM) → (Nat → Nat) → Prop)
#check (InputRead.modeOf : Bool → Fin 3)
#check (InputRead.stageDeadline : Nat → Nat)

-- Proposition-valued generated structure projections, separately from source theorems.
theorem check_InputRead_Edge_before (P : Nat) (c d : Node) (e : Edge P c d) : c.head ≤ P := by
  exact InputRead.Edge.before e
theorem check_InputRead_Edge_after (P : Nat) (c d : Node) (e : Edge P c d) : d.head ≤ P := by
  exact InputRead.Edge.after e
theorem check_InputRead_Edge_row (P : Nat) (c d : Node) (e : Edge P c d) :
    (machine.step c.state (c.tape c.head)).1 = d.state := by
  exact InputRead.Edge.row e
theorem check_InputRead_Edge_move (P : Nat) (c d : Node) (e : Edge P c d) :
    dest c.head (machine.step c.state (c.tape c.head)).2.2 = d.head := by
  exact InputRead.Edge.move e
theorem check_InputRead_Edge_tape (P : Nat) (c d : Node) (e : Edge P c d) :
    d.tape = put c.tape c.head (machine.step c.state (c.tape c.head)).2.1 := by
  exact InputRead.Edge.tape e

theorem check_InputRead_Path_bounds {P t : Nat} {c d : Node} (h : Path P t c d) :
    c.head ≤ P ∧ d.head ≤ P := by
  exact InputRead.Path.bounds h

theorem check_InputRead_Path_append {P t u : Nat} {c d e : Node}
    (h : Path P t c d) (g : Path P u d e) : Path P (t+u) c e := by
  exact InputRead.Path.append h g

theorem check_InputRead_Path_execute {N B P t : Nat} {c d : Node}
    (h : Path P t c d) (hp : P < tapeLength N B) :
    machine.run t (embed c (lt_of_le_of_lt h.bounds.1 hp)) =
      embed d (lt_of_le_of_lt h.bounds.2 hp) := by
  exact InputRead.Path.execute h hp

theorem check_InputRead_hop {P : Nat} (s s' : Fin 41) (h h' : Nat) (T : Nat → Option Bool)
    (b : Option Bool) (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : machine.step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  exact InputRead.hop s s' h h' T b m hb ha row hm

theorem check_InputRead_put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  exact InputRead.put_same T h

theorem check_InputRead_keep {P : Nat} (s s' : Fin 41) (h h' : Nat) (T : Nat → Option Bool)
    (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : machine.step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  exact InputRead.keep s s' h h' T m hb ha row hm

theorem check_InputRead_sweepR {P : Nat} (s : Fin 41) (T : Nat → Option Bool) (h r : Nat)
    (fit : h+r ≤ P)
    (rows : ∀ i, h ≤ i → i < h+r → machine.step s (T i)=(s,T i,.right)) :
    Path P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  exact InputRead.sweepR s T h r fit rows

theorem check_InputRead_sweepL {P : Nat} (s : Fin 41) (T : Nat → Option Bool) (low r : Nat)
    (fit : low+r ≤ P)
    (rows : ∀ i, low < i → i ≤ low+r → machine.step s (T i)=(s,T i,.left)) :
    Path P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  exact InputRead.sweepL s T low r fit rows

theorem check_InputRead_return_rows : ∀ mode : Fin 3,
    (∀ b, machine.step (q (8+8*mode.val)) (some b) = (q (8+8*mode.val),some b,.right)) ∧
    machine.step (q (8+8*mode.val)) none = (q (9+8*mode.val),none,.right) ∧
    machine.step (q (9+8*mode.val)) (some false) = (q (9+8*mode.val),some false,.right) ∧
    machine.step (q (9+8*mode.val)) none = (q (10+8*mode.val),none,.right) ∧
    (∀ b, machine.step (q (10+8*mode.val)) (some b) = (q (10+8*mode.val),some b,.right)) ∧
    machine.step (q (10+8*mode.val)) none = (ready mode,none,.stay) := by
  exact InputRead.return_rows

theorem check_InputRead_return_path (T : Nat → Option Bool) (S z n : Nat) (mode : Fin 3)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false)
    (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (right : T (S+z+n+3)=none) :
    Path (S+z+n+3) (n+z+3) ⟨q (9+8*mode.val),S+1,T⟩
      ⟨ready mode,S+z+n+3,T⟩ := by
  exact InputRead.return_path T S z n mode reg sep assn right

theorem check_InputRead_seek_path (T : Nat → Option Bool) (p S z n : Nat)
    (hp : 2 ≤ p) (hps : p ≤ S)
    (hole : T (p-2)=none) (marker : T (p-1)=some true)
    (source : ∀ i, p ≤ i → i < S → ∃ b, T i=some b) (eof : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (right : T (S+z+n+3)=none) :
    Path (S+z+n+3) (n+z+(S-p)+7) ⟨q 2,S+z+n+3,T⟩ ⟨q 7,p,T⟩ := by
  exact InputRead.seek_path T p S z n hp hps hole marker source eof reg sep assn right

theorem check_InputRead_read_path (T : Nat → Option Bool) (p S z n : Nat)
    (hp : 2 ≤ p) (hps : p ≤ S)
    (hole : T (p-2)=none) (marker : T (p-1)=some true)
    (source : ∀ i, p ≤ i → i < S → ∃ b, T i=some b) (eof : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (right : T (S+z+n+3)=none) :
    ∃ mode : Fin 3,
      (mode.val=2 ↔ p=S) ∧ (p<S → T p=some (result mode)) ∧
      Path (S+z+n+3) (readClock n z (S-p))
        ⟨q 2,S+z+n+3,T⟩ ⟨ready mode,S+z+n+3,put T p none⟩ := by
  exact InputRead.read_path T p S z n hp hps hole marker source eof reg sep assn right

-- Expand CursorRead rather than using the target alias as the proposition.
theorem check_InputRead_cursor_exact :
    ∀ (N B p S z n : Nat) (c : Config machine.stateCount N B),
      ∀ (_hp : 2 ≤ p) (_hps : p ≤ S) (_hfit : S+z+n+3 < tapeLength N B),
      c.state=q 2 → c.head.val=S+z+n+3 →
      c.tape ⟨p-2,by omega⟩=none → c.tape ⟨p-1,by omega⟩=some true →
      (∀ i, p ≤ i.val → i.val < S → ∃ b, c.tape i=some b) →
      c.tape ⟨S,by omega⟩=none →
      (∀ i, S < i.val → i.val < S+z+2 → c.tape i=some false) →
      c.tape ⟨S+z+2,by omega⟩=none →
      (∀ i, S+z+2 < i.val → i.val < S+z+n+3 → ∃ b, c.tape i=some b) →
      c.tape ⟨S+z+n+3,by omega⟩=none →
      ∃ mode : Fin 3,
        (mode.val=2 ↔ p=S) ∧
        (p<S → c.tape ⟨p,by omega⟩=some (result mode)) ∧
        let e := machine.run (readClock n z (S-p)) c
        e.state=ready mode ∧ e.head=c.head ∧
        (∀ i, e.tape i=if i.val=p then none else c.tape i) ∧
        (∀ i, (if i.val=p ∧ p<S then some (result mode) else e.tape i)=c.tape i) := by
  exact InputRead.cursor_exact

theorem check_InputRead_seed_path (T : Nat → Option Bool) (h n : Nat)
    (marks : ∀ i, h ≤ i → i < h+n → T i=some true) (endBlank : T (h+n)=none) :
    Path (h+n) (n+1) ⟨q 1,h,T⟩ ⟨q 2,h+n,Body.clear T h n⟩ := by
  exact InputRead.seed_path T h n marks endBlank

theorem check_InputRead_install_path (T : Nat → Option Bool) (left n : Nat)
    (startBlank : T left=none)
    (marks : ∀ i, left < i → i < left+n+1 → T i=some true)
    (endBlank : T (left+n+1)=none) :
    Path (left+n+1) (n+2) ⟨machine.start,left,T⟩
      ⟨q 2,left+n+1,Body.clear T (left+1) n⟩ := by
  exact InputRead.install_path T left n startBlank marks endBlank

theorem check_InputRead_install_exact {N B : Nat} (left n : Nat)
    (c : Config machine.stateCount N B)
    (hp : left+n+1 < tapeLength N B) (hq : c.state=machine.start) (hh : c.head.val=left)
    (hl : c.tape ⟨left,by omega⟩=none) (hr : c.tape ⟨left+n+1,hp⟩=none)
    (marks : ∀ i : Fin (tapeLength N B), left < i.val → i.val < left+n+1 → c.tape i=some true) :
    machine.run (n+2) c = ⟨q 2,⟨left+n+1,hp⟩,Body.installedTape c.tape left n⟩ := by
  exact InputRead.install_exact left n c hp hq hh hl hr marks

theorem check_InputRead_raw_cursor_parsed (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : AcceptedBody.Parsed k}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w)=true) (hn : 3 ≤ pr.2.n) :
    let B := FixedRawLengthFence.allocation (pairLength a m)
    ∃ z T, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      T ≤ FixedRawLengthFence.countdownDeadline (pairLength a m) ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z → 9+2*z ≤ a+m →
        ∃ (hR : a+m+2+z+pr.2.n+1 < tapeLength (pairLength a m) B) (mode : Fin 3),
          (mode.val=2 ↔ 9+2*z=a+m) ∧
          (∀ hi : 9+2*z < a+m, result mode=Fin.append x w ⟨9+2*z,hi⟩) ∧
          rawMachine.run (T+pr.2.n+2+readClock pr.2.n z (a+m-(9+2*z)))
            (initialConfig rawMachine B (encodePair x w)) =
          FixedRawLengthFence.prefixed.seqEmbedRight machine
            ⟨ready mode,⟨a+m+2+z+pr.2.n+1,hR⟩,
             fun i => if i.val=9+2*z then none else
               Body.installedTape (FixedRawLengthFence.countdownTape B x w z 0 pr.2.n)
                 (a+m+2+z) pr.2.n i⟩) := by
  exact InputRead.raw_cursor_parsed k x w hpr htag hn

theorem check_InputRead_stage_clock (R n z S p T : Nat) (hn : n ≤ R) (hz : z ≤ R) (hs : S ≤ R)
    (ht : T ≤ 128*(R+1)^2) : T+n+2+readClock n z (S-p) ≤ stageDeadline R := by
  exact InputRead.stage_clock R n z S p T hn hz hs ht

theorem check_InputRead_accepted_cursor (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) :
    ∃ pr : AcceptedBody.Parsed k,
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      (3 ≤ pr.2.n → ∃ z T,
        2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        (9+2*z ≤ a+m →
          ∃ (hR : a+m+2+z+pr.2.n+1 < tapeLength (pairLength a m)
                (FixedRawLengthFence.allocation (pairLength a m))) (mode : Fin 3),
            T+pr.2.n+2+readClock pr.2.n z (a+m-(9+2*z)) ≤ stageDeadline (pairLength a m) ∧
            (mode.val=2 ↔ 9+2*z=a+m) ∧
            (∀ hi : 9+2*z < a+m, result mode=Fin.append x w ⟨9+2*z,hi⟩) ∧
            rawMachine.run (T+pr.2.n+2+readClock pr.2.n z (a+m-(9+2*z)))
              (initialConfig rawMachine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight machine
              ⟨ready mode,⟨a+m+2+z+pr.2.n+1,hR⟩,
                fun i => if i.val=9+2*z then none else
                  Body.installedTape (FixedRawLengthFence.countdownTape
                    (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n)
                    (a+m+2+z) pr.2.n i⟩)) := by
  exact InputRead.accepted_cursor k x w accepted

end Pnp3.Tests.PartAInputReadSurfaceTests
