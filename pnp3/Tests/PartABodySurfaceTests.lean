import AcceptedBody.Closure

/-! Infrastructure contracts for the seven-module Body / AcceptedBody slice.
These named mirrors restate propositions; the two endpoint aliases are expanded.
Expression pins below separately fix definition, structure and constructor types. -/
namespace Pnp3.Tests.PartABodySurfaceTests
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
open Body Body.Target AcceptedBody

#check (Body.q : Nat → Fin 9)
#check (Body.raw : Fin 9 → Option Bool → Fin 9 × Option Bool × Move)
#check (Body.machine : UniformTM)
#check (Body.rawMachine : UniformTM)
#check (Body.inc : List Bool → List Bool × Bool)
#check (Body.value : List Bool → Nat)
#check (Body.carryClock : List Bool → Nat → Nat)
#check (Body.roundClock : List Bool → Nat)
#check (Body.Node : Type)
#check (Body.Node.mk : Fin 9 → Nat → (Nat → Option Bool) → Node)
#check (Body.Node.state : Node → Fin 9)
#check (Body.Node.head : Node → Nat)
#check (Body.Node.tape : Node → Nat → Option Bool)
#check (Body.put : (Nat → Option Bool) → Nat → Option Bool → Nat → Option Bool)
#check (@Body.embed : ∀ {N B : Nat} (c : Node), c.head < tapeLength N B → Config 9 N B)
#check (Body.dest : Nat → Move → Nat)
#check (Body.Edge : Nat → Node → Node → Prop)
#check (@Body.Edge.mk : ∀ {P : Nat} {c d : Node}, c.head ≤ P → d.head ≤ P →
  (machine.step c.state (c.tape c.head)).1 = d.state →
  dest c.head (machine.step c.state (c.tape c.head)).2.2 = d.head →
  d.tape = put c.tape c.head (machine.step c.state (c.tape c.head)).2.1 → Edge P c d)
#check (Body.Path : Nat → Nat → Node → Node → Prop)
#check (@Body.Path.nil : ∀ {P : Nat} (c : Node), c.head ≤ P → Path P 0 c c)
#check (@Body.Path.cons : ∀ {P t : Nat} {c d e : Node},
  Edge P c d → Path P t d e → Path P (t+1) c e)
#check (Body.Target.PartA : (Nat → UniformTM) → (Nat → Nat) → Prop)
#check (@Body.Target.Span : ∀ {N B : Nat},
  (Fin (tapeLength N B) → Option Bool) → Nat → List Bool → Prop)
#check (Body.Target.Round : Prop)
#check (Body.Reads : (Nat → Option Bool) → Nat → List Bool → Prop)
#check (Body.carryTape : (Nat → Option Bool) → Nat → List Bool → Nat → Option Bool)
#check (@Body.extend : ∀ {N B : Nat}, (Fin (tapeLength N B) → Option Bool) → Nat → Option Bool)
#check (Body.clear : (Nat → Option Bool) → Nat → Nat → Nat → Option Bool)
#check (Body.iterBits : List Bool → Nat → List Bool)
#check (Body.iterClock : List Bool → Nat → Nat)
#check (Body.Good : List Bool → Nat → Prop)
#check (@Body.installedTape : ∀ {N B : Nat},
  (Fin (tapeLength N B) → Option Bool) → Nat → Nat → Fin (tapeLength N B) → Option Bool)
#check (AcceptedBody.Parsed : Nat → Type)
#check (AcceptedBody.deadline : Nat → Nat)
#check (AcceptedBody.AcceptedOrbit : Nat → Prop)

theorem check_Body_Edge_before (P : Nat) (c d : Node) (e : Edge P c d) : c.head ≤ P := by
  exact Body.Edge.before e
theorem check_Body_Edge_after (P : Nat) (c d : Node) (e : Edge P c d) : d.head ≤ P := by
  exact Body.Edge.after e
theorem check_Body_Edge_row (P : Nat) (c d : Node) (e : Edge P c d) :
    (machine.step c.state (c.tape c.head)).1 = d.state := by
  exact Body.Edge.row e
theorem check_Body_Edge_move (P : Nat) (c d : Node) (e : Edge P c d) :
    dest c.head (machine.step c.state (c.tape c.head)).2.2 = d.head := by
  exact Body.Edge.move e
theorem check_Body_Edge_tape (P : Nat) (c d : Node) (e : Edge P c d) :
    d.tape = put c.tape c.head (machine.step c.state (c.tape c.head)).2.1 := by
  exact Body.Edge.tape e

theorem check_Body_Path_bounds {P t c d} (h : Path P t c d) : c.head ≤ P ∧ d.head ≤ P := by
  exact Body.Path.bounds h
theorem check_Body_Path_append {P t u c d e} (h : Path P t c d) (g : Path P u d e) :
    Path P (t+u) c e := by
  exact Body.Path.append h g
theorem check_Body_Path_execute {N B P t c d} (h : Path P t c d) (hp : P < tapeLength N B) :
    machine.run t (embed c (lt_of_le_of_lt h.bounds.1 hp)) =
      embed d (lt_of_le_of_lt h.bounds.2 hp) := by
  exact Body.Path.execute h hp
theorem check_Body_hop {P : Nat} (s s' : Fin 9) (h h' : Nat) (T : Nat → Option Bool)
    (b : Option Bool) (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : machine.step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  exact Body.hop s s' h h' T b m hb ha row hm
theorem check_Body_put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  exact Body.put_same T h
theorem check_Body_sweep (T : Nat → Option Bool) (h r : Nat)
    (occ : ∀ i, h ≤ i → i < h+r → ∃ b, T i = some b) :
    Path (h+r) r ⟨q 4,h,T⟩ ⟨q 4,h+r,T⟩ := by
  exact Body.sweep T h r occ

theorem check_Body_reads_cons (T : Nat → Option Bool) (left : Nat) (b : Bool) (bs : List Bool) :
    Reads T left (b::bs) ↔ T (left+bs.length+1) = some b ∧ Reads T left bs := by
  exact Body.reads_cons T left b bs
theorem check_Body_inc_length (bs : List Bool) : (inc bs).1.length = bs.length := by
  exact Body.inc_length bs
theorem check_Body_carry_frame (T : Nat → Option Bool) (left : Nat) (bs : List Bool) (i : Nat)
    (hi : i ≤ left ∨ left+bs.length < i) : carryTape T left bs i = T i := by
  exact Body.carry_frame T left bs i hi
theorem check_Body_reads_put_outside (T : Nat → Option Bool) (left : Nat) (bs : List Bool)
    (h : Reads T left bs) (pos : Nat) (b : Option Bool) (hp : left+bs.length < pos) :
    Reads (put T pos b) left bs := by
  exact Body.reads_put_outside T left bs h pos b hp
theorem check_Body_carry_reads (T : Nat → Option Bool) (left : Nat) (bs : List Bool)
    (h : Reads T left bs) : Reads (carryTape T left bs) left (inc bs).1 := by
  exact Body.carry_reads T left bs h
theorem check_Body_carry_path (T : Nat → Option Bool) (left r : Nat) (bs : List Bool)
    (hl : T left = none) (hr : T (left+bs.length+r+1) = none)
    (digits : Reads T left bs)
    (occ : ∀ i, left+bs.length < i → i < left+bs.length+r+1 → ∃ b, T i = some b) :
    Path (left+bs.length+r+1) (carryClock bs r)
      ⟨q 3,left+bs.length,T⟩
      ⟨if (inc bs).2 then machine.accept else q 2,
        if (inc bs).2 then left+1 else left+bs.length+r+1,carryTape T left bs⟩ := by
  exact Body.carry_path T left r bs hl hr digits occ
theorem check_Body_round_path (T : Nat → Option Bool) (left : Nat) (bs : List Bool)
    (hl : T left = none) (hr : T (left+bs.length+1) = none) (digits : Reads T left bs) :
    Path (left+bs.length+1) (roundClock bs)
      ⟨q 2,left+bs.length+1,T⟩
      ⟨if (inc bs).2 then machine.accept else q 2,
        if (inc bs).2 then left+1 else left+bs.length+1,carryTape T left bs⟩ := by
  exact Body.round_path T left bs hl hr digits
theorem check_Body_extend_read {N B : Nat} (T : Fin (tapeLength N B) → Option Bool)
    (i : Fin (tapeLength N B)) : extend T i.val = T i := by
  exact Body.extend_read T i
theorem check_Body_round_exact :
    ∀ (N B left : Nat) (bits : List Bool)
      (c : Config machine.stateCount N B),
      left + bits.length + 1 < tapeLength N B →
      c.state = q 2 → c.head.val = left + bits.length + 1 →
      Span c.tape left bits →
      let e := machine.run (roundClock bits) c
      e.state = (if (inc bits).2 then machine.accept else q 2) ∧
      e.head.val = (if (inc bits).2 then left + 1 else left + bits.length + 1) ∧
      Span e.tape left (inc bits).1 ∧
      ∀ i, i.val ≤ left ∨ left + bits.length < i.val → e.tape i = c.tape i := by
  exact Body.round_exact
theorem check_Body_inc_value (bs : List Bool) :
    value (inc bs).1 + (if (inc bs).2 then 2^bs.length else 0) = value bs + 1 := by
  exact Body.inc_value bs
theorem check_Body_clear_step (T : Nat → Option Bool) (h n : Nat) :
    clear (put T h (some false)) (h+1) n = clear T h (n+1) := by
  exact Body.clear_step T h n
theorem check_Body_seed_path (T : Nat → Option Bool) (h n : Nat)
    (marks : ∀ i, h ≤ i → i < h+n → T i=some true) (endBlank : T (h+n)=none) :
    Path (h+n) (n+1) ⟨q 1,h,T⟩ ⟨q 2,h+n,clear T h n⟩ := by
  exact Body.seed_path T h n marks endBlank
theorem check_Body_install_path (T : Nat → Option Bool) (left n : Nat)
    (startBlank : T left=none)
    (marks : ∀ i, left < i → i < left+n+1 → T i=some true)
    (endBlank : T (left+n+1)=none) :
    Path (left+n+1) (n+2) ⟨machine.start,left,T⟩
      ⟨q 2,left+n+1,clear T (left+1) n⟩ := by
  exact Body.install_path T left n startBlank marks endBlank
theorem check_Body_iter_length (bs : List Bool) (r : Nat) : (iterBits bs r).length=bs.length := by
  exact Body.iter_length bs r
theorem check_Body_value_lt (bs : List Bool) : value bs < 2^bs.length := by
  exact Body.value_lt bs
theorem check_Body_good_of_lt (bs : List Bool) (r : Nat) (h : value bs+r < 2^bs.length) : Good bs r := by
  exact Body.good_of_lt bs r h
theorem check_Body_round_clock_le (bs : List Bool) : roundClock bs ≤ 2*bs.length+3 := by
  exact Body.round_clock_le bs
theorem check_Body_iter_clock_le (bs : List Bool) (r : Nat) : iterClock bs r ≤ r*(2*bs.length+3) := by
  exact Body.iter_clock_le bs r
theorem check_Body_repeated_exact {N B : Nat} (left : Nat) (bs : List Bool) (r : Nat)
    (c : Config machine.stateCount N B)
    (hp : left+bs.length+1 < tapeLength N B) (hq : c.state=q 2)
    (hh : c.head.val=left+bs.length+1) (hs : Target.Span c.tape left bs) (hg : Good bs r) :
    let e := machine.run (iterClock bs r) c
    e.state=q 2 ∧ e.head.val=left+bs.length+1 ∧ Target.Span e.tape left (iterBits bs r) ∧
    ∀ i : Fin (tapeLength N B), i.val ≤ left ∨ left+bs.length < i.val → e.tape i=c.tape i := by
  exact Body.repeated_exact left bs r c hp hq hh hs hg

theorem check_Body_install_exact {N B : Nat} (left n : Nat) (c : Config machine.stateCount N B)
    (hp : left+n+1 < tapeLength N B) (hq : c.state=machine.start) (hh : c.head.val=left)
    (hl : c.tape ⟨left,by omega⟩=none)
    (hr : c.tape ⟨left+n+1,hp⟩=none)
    (marks : ∀ i : Fin (tapeLength N B), left < i.val → i.val < left+n+1 → c.tape i=some true) :
    machine.run (n+2) c = ⟨q 2,⟨left+n+1,hp⟩,installedTape c.tape left n⟩ ∧
    Target.Span (installedTape c.tape left n) left (List.replicate n false) := by
  exact Body.install_exact left n c hp hq hh hl hr marks
theorem check_Body_first_accept_whole (M : UniformTM) {N B : Nat} (c : Config M.stateCount N B)
    (deadline : Nat) (endConfig : Config M.stateCount N B)
    (he : M.run deadline c=endConfig) (ha : endConfig.state=M.accept) :
    ∃ T, T ≤ deadline ∧ (∀ t, t < T → (M.run t c).state≠M.accept) ∧ M.run T c=endConfig := by
  exact Body.first_accept_whole M c deadline endConfig he ha
theorem check_Body_raw_counter_parsed (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w)=true) (hn : 3 ≤ pr.2.n) :
    let B := FixedRawLengthFence.allocation (pairLength a m)
    pr.2.n=pr.1 ∧ ∃ z,
      2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z →
        ∃ (T : Nat) (hR : a+m+2+z+pr.2.n+1 < tapeLength (pairLength a m) B),
          T ≤ FixedRawLengthFence.countdownDeadline (pairLength a m) ∧
          let startTape := FixedRawLengthFence.countdownTape B x w z 0 pr.2.n
          let ready : Config machine.stateCount (pairLength a m) B :=
            ⟨q 2,⟨a+m+2+z+pr.2.n+1,hR⟩,installedTape startTape (a+m+2+z) pr.2.n⟩
          Target.Span ready.tape (a+m+2+z) (List.replicate pr.2.n false) ∧
          (∀ i : Fin (tapeLength (pairLength a m) B), i.val ≤ a+m+2+z ∨ a+m+2+z+pr.2.n+1 ≤ i.val → ready.tape i=startTape i) ∧
          ∀ s, rawMachine.run (T+pr.2.n+2+s)
            (initialConfig rawMachine B (encodePair x w)) =
              FixedRawLengthFence.prefixed.seqEmbedRight machine (machine.run s ready)) := by
  exact Body.raw_counter_parsed k x w hpr htag hn
theorem check_Body_zero_value (n : Nat) : value (List.replicate n false)=0 := by
  exact Body.zero_value n
theorem check_Body_raw_source_after_header {a m B z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (hg : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (hr : 2*pairLength a m+2 ≤ B) (hn : n ≤ FixedRawLengthFence.capacity a m z)
    (i : Fin (tapeLength (pairLength a m) B)) (lo : 8+2*z+1 ≤ i.val) (hi : i.val < a+m) :
    FixedRawLengthFence.countdownTape B x w z 0 n i = some (Fin.append x w ⟨i.val,hi⟩) := by
  exact Body.raw_source_after_header x w hg hr hn i lo hi
theorem check_Body_raw_repeated_parsed (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : Sigma fun r : Nat =>
      PrefixInput (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hpr : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w)=true) (hn : 3 ≤ pr.2.n) :
    let B := FixedRawLengthFence.allocation (pairLength a m)
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z →
        ∃ T, T ≤ FixedRawLengthFence.countdownDeadline (pairLength a m) ∧
          ∀ r, r < 2^pr.2.n →
            let e := rawMachine.run (T+pr.2.n+2+iterClock (List.replicate pr.2.n false) r)
              (initialConfig rawMachine B (encodePair x w))
            e.state=FixedRawLengthFence.prefixed.seqRight machine (q 2) ∧
            e.head.val=a+m+2+z+pr.2.n+1 ∧
            Target.Span e.tape (a+m+2+z) (iterBits (List.replicate pr.2.n false) r) ∧
            ∀ (i : Fin (tapeLength (pairLength a m) B)) (_lo : 8+2*z+1 ≤ i.val) (hi : i.val < a+m),
              e.tape i=some (Fin.append x w ⟨i.val,hi⟩)) := by
  exact Body.raw_repeated_parsed k x w hpr htag hn

theorem check_AcceptedBody_concat_eq_append {a m : Nat} (x : Bitstring a) (w : Bitstring m) :
    PartAEndpoint.concatV1ToPrefixBitVec x w = Fin.append x w := by
  exact AcceptedBody.concat_eq_append x w
theorem check_AcceptedBody_table_support (k : Nat) {N : Nat} (z : PrefixBitVec N) {pr : Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) z = some pr)
    (accepted : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z = true) :
    Pnp3.Models.Partial.tableLen pr.2.n ≤ N := by
  exact AcceptedBody.table_support k z parsed accepted
theorem check_AcceptedBody_strict_capacity {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z)
    (target : n ≤ a+m) : n < FixedRawLengthFence.capacity a m z := by
  exact AcceptedBody.strict_capacity x w gamma target
theorem check_AcceptedBody_clock_bound (R n r T : Nat) (hn : n ≤ R) (hr : r ≤ R)
    (ht : T ≤ 128*(R+1)^2) :
    T+n+2+Body.iterClock (List.replicate n false) r ≤ deadline R := by
  exact AcceptedBody.clock_bound R n r T hn hr ht
theorem check_AcceptedBody_exact (k : Nat) :
    ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
      PartAEndpoint.thresholdContentWitnessRelation k a m x w = true →
      ∃ pr : Parsed k,
        contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w) = some pr ∧
        Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
        (3 ≤ pr.2.n → ∃ z T,
          2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w) = some z ∧
          pr.2.n < FixedRawLengthFence.capacity a m z ∧
          T ≤ FixedRawLengthFence.countdownDeadline (pairLength a m) ∧
          ∀ r, r < 2^pr.2.n →
            T+pr.2.n+2+Body.iterClock (List.replicate pr.2.n false) r ≤ deadline (pairLength a m) ∧
            let e := Body.rawMachine.run (T+pr.2.n+2+Body.iterClock (List.replicate pr.2.n false) r)
              (initialConfig Body.rawMachine (FixedRawLengthFence.allocation (pairLength a m))
                (encodePair x w))
            e.state = FixedRawLengthFence.prefixed.seqRight Body.machine (Body.q 2) ∧
            e.head.val = a+m+2+z+pr.2.n+1 ∧
            Body.Target.Span e.tape (a+m+2+z) (Body.iterBits (List.replicate pr.2.n false) r) ∧
            ∀ (i : Fin (tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))))
              (_lo : 8+2*z+1 ≤ i.val) (hi : i.val < a+m),
              e.tape i = some (Fin.append x w ⟨i.val,hi⟩)) := by
  exact AcceptedBody.exact k
end Pnp3.Tests.PartABodySurfaceTests
