import SmallIngress.Runtime
import SmallIngress.Fixtures
import Lean
namespace SmallOrbit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding SmallIngress
namespace Target
/-- Frozen full accepted raw target, with the SAME dependent parsed input and
all arities. Work exits are explicitly not semantic acceptance. -/
def AcceptedOrbit (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : AcceptedBody.Parsed k,
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      ∃ (z T : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        T ≤ 4096*(pairLength a m+1)^2 ∧
        let U := Body.extend (Body.installedTape (prepared
          (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) (a+m+z+2) pr.2.n)
        (∀ r, r<2^pr.2.n → ∃ t, t ≤ T ∧
          machine.run t (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.paid (Stream.Target.mode U (Stream.Target.cursor (9+2*z) (a+m) r) (a+m)),⟨a+m+z+pr.2.n+3,hH⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) r (r+1) true i.val⟩) ∧
        ∃ hp : Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n) <
          tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          machine.run T (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.q (if Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m then 57 else 58),
                ⟨Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n),hp⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false i.val⟩
/-- Same parsed target, physical small branch of the original accepted orbit. -/
def SmallAcceptedOrbit (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∀ (pr : AcceptedBody.Parsed k),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
      pr.2.n < 3 →
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      ∃ (z T : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        T ≤ 4096*(pairLength a m+1)^2 ∧
        let U := Body.extend (Body.installedTape (prepared
          (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) (a+m+z+2) pr.2.n)
        (∀ r, r<2^pr.2.n → ∃ t, t ≤ T ∧
          machine.run t (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.paid (Stream.Target.mode U (Stream.Target.cursor (9+2*z) (a+m) r) (a+m)),⟨a+m+z+pr.2.n+3,hH⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) r (r+1) true i.val⟩) ∧
        ∃ hp : Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n) <
          tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          machine.run T (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.q (if Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m then 57 else 58),
                ⟨Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n),hp⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false i.val⟩
end Target
end SmallOrbit

namespace SmallOrbit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding SmallIngress
set_option maxRecDepth 4000
private theorem accepted_facts (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) :
    m=a+1 ∧ contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=true := by
  unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at accepted
  split at accepted
  · rename_i shape
    refine ⟨by simpa [Pnp3.ComplexityInterfaces.certificateLength] using shape,?_⟩
    cases shape
    rwa [AcceptedBody.concat_eq_append] at accepted
  · contradiction
private theorem physical_read {S i : Nat} (v : PrefixBitVec S) (hi : i<S) :
    FixedContentTagGate.physicalSymbol v i=some (padRead v i) := by
  simp [FixedContentTagGate.physicalSymbol,padRead,hi]
/-- Exact accepted length parity excludes a virtual trailing n1 payload.
The parsed Sigma is the authoritative same pr, without length injectivity. -/
theorem small_header_physical (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (small : pr.2.n<3) :
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some (if pr.2.n=0 then 0 else 1) ∧
    (if pr.2.n=0 then 9 else 11) ≤ a+m ∧
    FixedContentTagGate.physicalSymbol (Fin.append x w) 8=some (pr.2.n==0) ∧
    (pr.2.n≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 9=some true) ∧
    (pr.2.n≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 10=some (pr.2.n==2)) := by
  have shape := (accepted_facts k x w accepted).1
  obtain ⟨consumed,header,target⟩ := contentInput?_target_eq_contentHeader _ (Fin.append x w) parsed
  rw [← target] at header
  obtain ⟨z,payload,gamma,read,value,_⟩ := (contentHeader?_eq_some_iff_gammaZeros_payload _).1 header
  obtain ⟨support,term,zero⟩ := (FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma
  have hz : z≤1 := by
    by_contra h
    have hp : 4≤2^z := Nat.pow_le_pow_right (show 0<(2:Nat) by decide) (show 2≤z by omega)
    omega
  interval_cases z
  · have hp : payload=0 := by simpa [VirtualZeroTailReader.readNatBE] using read.symm
    have hn : pr.2.n=0 := by simp only [pow_zero] at value; omega
    simp only [hn,ite_true,beq_self_eq_true,ne_eq,not_true_eq_false,false_implies,and_true]
    exact ⟨gamma,by omega,by simpa using term⟩
  · have hn : pr.2.n≠0 := by simp only [pow_one] at value; omega
    have full : 11≤a+m := by omega
    have logical : 10<2*(a+m)+1 := by omega
    have one : VirtualZeroTailReader.readNatBE (Fin.append x w) (2*(a+m)+1) 10 1 =
        some (if padRead (Fin.append x w) 10 then 1 else 0) := by
      simp [VirtualZeroTailReader.readNatBE,VirtualZeroTailReader.readBit?,logical]
    have hp : (if padRead (Fin.append x w) 10 then 1 else 0)=payload := by
      simpa only [show 9+1=10 by decide,one,Option.some.injEq] using read
    have bit : padRead (Fin.append x w) 10=(pr.2.n==2) := by
      cases hb : padRead (Fin.append x w) 10
      · have pzero : payload=0 := by simpa only [hb,Bool.false_eq_true,ite_false] using hp.symm
        have n1 : pr.2.n=1 := by simp only [pow_one] at value; omega
        simp [n1]
      · have pone : payload=1 := by simpa only [hb,ite_true] using hp.symm
        have n2 : pr.2.n=2 := by simp only [pow_one] at value; omega
        simp [n2]
    refine ⟨by simpa only [if_neg hn] using gamma,by simpa only [if_neg hn] using full,?_,?_,?_⟩
    · have h := zero 0 (by decide)
      simpa only [Nat.add_zero,show (pr.2.n==0)=false from beq_eq_false_iff_ne.mpr hn] using h
    · intro _; simpa using term
    · intro _; rw [physical_read _ (by omega),bit]
end SmallOrbit

namespace SmallOrbit
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 4000
private structure Node (M : UniformTM) where
  state : Fin M.stateCount
  head : Nat
  tape : Nat → Option Bool

private def put (T : Nat → Option Bool) (h : Nat) (b : Option Bool) : Nat → Option Bool :=
  fun i => if i = h then b else T i

private def embed {M : UniformTM} {N B : Nat} (c : Node M) (h : c.head < tapeLength N B) : Config M.stateCount N B :=
  ⟨c.state,⟨c.head,h⟩,fun i => c.tape i.val⟩

private def dest (h : Nat) : Move → Nat
  | .left => h-1
  | .stay => h
  | .right => h+1

private structure Edge {M : UniformTM} (P : Nat) (c d : Node M) : Prop where
  before : c.head ≤ P
  after : d.head ≤ P
  row : (M.step c.state (c.tape c.head)).1 = d.state
  move : dest c.head (M.step c.state (c.tape c.head)).2.2 = d.head
  tape : d.tape = put c.tape c.head (M.step c.state (c.tape c.head)).2.1

private inductive Path {M : UniformTM} (P : Nat) : Nat → Node M → Node M → Prop
  | nil (c) (h : c.head ≤ P) : Path (M := M) P 0 c c
  | cons {t c d e} : Edge (M := M) P c d → Path (M := M) P t d e → Path (M := M) P (t+1) c e

namespace Path
private theorem bounds {M : UniformTM} {P t c d} (h : Path (M := M) P t c d) : c.head ≤ P ∧ d.head ≤ P := by
  induction h with
  | nil _ h => exact ⟨h,h⟩
  | cons e _ ih => exact ⟨e.before,ih.2⟩

private theorem append {M : UniformTM} {P t u c d e} (h : Path (M := M) P t c d) (g : Path (M := M) P u d e) :
    Path (M := M) P (t+u) c e := by
  induction h with
  | nil => simpa using g
  | cons ed _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Path.cons ed (ih g)

private theorem execute {M : UniformTM} {N B P t c d} (h : Path (M := M) P t c d) (hp : P < tapeLength N B) :
    M.run t (embed c (lt_of_le_of_lt h.bounds.1 hp)) =
      embed d (lt_of_le_of_lt h.bounds.2 hp) := by
  have step {c d} (e : Edge (M := M) P c d) :
      M.stepConfig (embed c (lt_of_le_of_lt e.before hp)) =
        embed d (lt_of_le_of_lt e.after hp) := by
    apply Config.ext_parts
    · exact e.row
    · apply Fin.ext
      change (moveHead _ (M.step c.state (c.tape c.head)).2.2).val = d.head
      have hm := e.move
      cases mv : (M.step c.state (c.tape c.head)).2.2 with
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
      M.run t (embed c hc) = embed d hd by exact aux _ _
  induction h with
  | nil => intro _ _; rfl
  | @cons t c d e ed path ih =>
    intro hc he
    rw [show t+1=1+t by omega,M.run_add]
    change M.run t (M.stepConfig (embed c hc)) = embed e he
    rw [step ed]
    exact ih _ _
end Path

private theorem hop {M : UniformTM} {P : Nat} (s s' : Fin M.stateCount) (h h' : Nat) (T : Nat → Option Bool)
    (b : Option Bool) (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : M.step s (T h) = (s',b,m)) (hm : dest h m = h') :
    Path (M := M) P 1 ⟨s,h,T⟩ ⟨s',h',put T h b⟩ := by
  apply Path.cons (d := ⟨s',h',put T h b⟩)
  · exact ⟨hb,ha,by rw [row],by rw [row]; exact hm,by rw [row]⟩
  · exact Path.nil _ ha

private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h) = T := by
  funext i; by_cases hi : i=h <;> simp [put,hi]

/-- One exact public row that preserves the scanned symbol. -/
private theorem keep {M : UniformTM} {P : Nat} (s s' : Fin M.stateCount) (h h' : Nat) (T : Nat → Option Bool)
    (m : Move) (hb : h ≤ P) (ha : h' ≤ P)
    (row : M.step s (T h) = (s',T h,m)) (hm : dest h m=h') :
    Path (M := M) P 1 ⟨s,h,T⟩ ⟨s',h',T⟩ := by
  have one := hop (M := M) s s' h h' T (T h) m hb ha row hm
  rwa [put_same] at one

private theorem sweepR {M : UniformTM} {P : Nat} (s : Fin M.stateCount) (T : Nat → Option Bool) (h r : Nat)
    (fit : h+r ≤ P)
    (rows : ∀ i, h ≤ i → i < h+r → M.step s (T i)=(s,T i,.right)) :
    Path (M := M) P r ⟨s,h,T⟩ ⟨s,h+r,T⟩ := by
  induction r generalizing h with
  | zero => simpa using Path.nil ⟨s,h,T⟩ fit
  | succ r ih =>
    have one := keep (M := M) s s h (h+1) T .right (P := P) (by omega) (by omega)
      (rows h le_rfl (by omega)) rfl
    have rest := ih (h+1) (by omega) (by intro i hl hu; exact rows i (by omega) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest

private theorem sweepL {M : UniformTM} {P : Nat} (s : Fin M.stateCount) (T : Nat → Option Bool) (low r : Nat)
    (fit : low+r ≤ P)
    (rows : ∀ i, low < i → i ≤ low+r → M.step s (T i)=(s,T i,.left)) :
    Path (M := M) P r ⟨s,low+r,T⟩ ⟨s,low,T⟩ := by
  induction r with
  | zero => simpa using Path.nil ⟨s,low,T⟩ fit
  | succ r ih =>
    have one := keep (M := M) s s (low+(r+1)) (low+r) T .left (P := P) (by omega) (by omega)
      (rows _ (by omega) le_rfl) (by simp [dest])
    have rest := ih (by omega) (by intro i hl hu; exact rows i hl (by omega))
    simpa [Nat.add_comm] using one.append rest

end SmallOrbit

namespace SmallOrbit
open Pnp3.Complexity.Uniform.V1
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private theorem stream_seed_path (T : Nat → Option Bool) (h n : Nat) (marks : ∀ i, h ≤ i → i < h+n → T i=some true) (endBlank : T (h+n)=none) :
    Path (M := Stream.machine) (h+n) (n+1) ⟨Stream.q 1,h,T⟩ ⟨Stream.q 2,h+n,Body.clear T h n⟩ := by
  induction n generalizing T h with
  | zero =>
    have one := hop (M := Stream.machine) (Stream.q 1) (Stream.q 2) h h T none .stay (P := h) le_rfl le_rfl (by rw [show T h=none by simpa using endBlank]; rfl) rfl
    have hb : T h=none := by simpa using endBlank
    rw [← hb,put_same] at one
    have hz : Body.clear T h 0=T := by funext i; simp [Body.clear]
    simpa [hz] using one
  | succ n ih =>
    have hb := marks h le_rfl (by omega)
    let U := put T h (some false)
    have one := hop (M := Stream.machine) (Stream.q 1) (Stream.q 1) h (h+1) T (some false) .right (P := h+(n+1)) (by omega) (by omega) (by rw [hb]; rfl) rfl
    have rest := ih U (h+1) (by intro i h1 h2; dsimp [U]; rw [put,if_neg (by omega)]; exact marks i (by omega) (by omega))
      (by dsimp [U]; rw [put,if_neg (by omega)]; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using endBlank)
    have eqP : h+1+n=h+(n+1) := by omega
    rw [eqP] at rest
    have clearstep : Body.clear (put T h (some false)) (h+1) n = Body.clear T h (n+1) := Body.clear_step T h n
    simpa only [U,clearstep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
/-- Installation consumes actual unary marks, without assuming precleared scratch. -/
private theorem stream_install_path (T : Nat → Option Bool) (left n : Nat) (startBlank : T left=none) (marks : ∀ i, left < i → i < left+n+1 → T i=some true)
    (endBlank : T (left+n+1)=none) :
    Path (M := Stream.machine) (left+n+1) (n+2) ⟨Stream.machine.start,left,T⟩
      ⟨Stream.q 2,left+n+1,Body.clear T (left+1) n⟩ := by
  have one := hop (M := Stream.machine) Stream.machine.start (Stream.q 1) left (left+1) T none .right (P := left+n+1) (by omega) (by omega) (by rw [startBlank]; rfl) rfl
  rw [← startBlank,put_same] at one
  have rest := stream_seed_path T (left+1) n (by intro i h1 h2; exact marks i (by omega) (by omega)) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using endBlank)
  have eqP : left+1+n=left+n+1 := by omega
  rw [eqP] at rest
  simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using one.append rest

/-- Finite row pins; mode contains one lifted bit or sticky EOF, never an address. -/
private theorem stream_return_rows : ∀ mode : Fin 3,
    (∀ b, Stream.machine.step (Stream.q (8+8*mode.val)) (some b) = (Stream.q (8+8*mode.val),some b,.right)) ∧
    Stream.machine.step (Stream.q (8+8*mode.val)) none = (Stream.q (9+8*mode.val),none,.right) ∧
    Stream.machine.step (Stream.q (9+8*mode.val)) (some false) = (Stream.q (9+8*mode.val),some false,.right) ∧
    Stream.machine.step (Stream.q (9+8*mode.val)) none = (Stream.q (10+8*mode.val),none,.right) ∧
    (∀ b, Stream.machine.step (Stream.q (10+8*mode.val)) (some b) = (Stream.q (10+8*mode.val),some b,.right)) ∧
    Stream.machine.step (Stream.q (10+8*mode.val)) none = (Stream.unpaid mode,none,.stay) := by decide

/-- Physical return across the actual register and counter boundaries. -/
private theorem stream_return_path (T : Nat → Option Bool) (S z n : Nat) (mode : Fin 3)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false)
    (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (right : T (S+z+n+3)=none) :
    Path (M := Stream.machine) (S+z+n+3) (n+z+3) ⟨Stream.q (9+8*mode.val),S+1,T⟩
      ⟨Stream.unpaid mode,S+z+n+3,T⟩ := by
  have rows := stream_return_rows mode
  have a := sweepR (M := Stream.machine) (Stream.q (9+8*mode.val)) T (S+1) (z+1) (P := S+z+n+3) (by omega) (by
    intro i hl hu; rw [reg i (by omega) (by omega)]; exact rows.2.2.1)
  have eqL : S+1+(z+1)=S+z+2 := by omega
  rw [eqL] at a
  have b := keep (M := Stream.machine) (Stream.q (9+8*mode.val)) (Stream.q (10+8*mode.val)) (S+z+2) (S+z+3) T .right
    (P := S+z+n+3) (by omega) (by omega) (by rw [sep]; exact rows.2.2.2.1) rfl
  have c := sweepR (M := Stream.machine) (Stream.q (10+8*mode.val)) T (S+z+3) n (P := S+z+n+3) (by omega) (by
    intro i hl hu; obtain ⟨v,hv⟩ := assn i (by omega) (by omega)
    rw [hv]; exact rows.2.2.2.2.1 v)
  have eqR : S+z+3+n=S+z+n+3 := by omega
  rw [eqR] at c
  have d := keep (M := Stream.machine) (Stream.q (10+8*mode.val)) (Stream.unpaid mode) (S+z+n+3) (S+z+n+3) T .stay
    (P := S+z+n+3) le_rfl le_rfl (by rw [right]; exact rows.2.2.2.2.2) rfl
  convert ((a.append b).append c).append d using 1; omega

/-- Runtime discovers the source cursor by crossing three real blank boundaries
and the consumed gamma trail. No numeric parameter below occurs in a row. -/
private theorem stream_seek_path (T : Nat → Option Bool) (p S z n : Nat) (hp : 2 ≤ p) (hps : p ≤ S)
    (hole : T (p-2)=none) (marker : T (p-1)=some true)
    (source : ∀ i, p ≤ i → i < S → ∃ b, T i=some b)
    (eof : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false)
    (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (right : T (S+z+n+3)=none) :
    Path (M := Stream.machine) (S+z+n+3) (n+z+(S-p)+7) ⟨Stream.q 2,S+z+n+3,T⟩ ⟨Stream.q 7,p,T⟩ := by
  let P := S+z+n+3
  have a := keep (M := Stream.machine) (Stream.q 2) (Stream.q 3) P (P-1) T .left (P := P) le_rfl (by omega)
    (by rw [right]; rfl) rfl
  have b := sweepL (M := Stream.machine) (Stream.q 3) T (S+z+2) n (P := P) (by dsimp [P]; omega) (by
    intro i hl hu; obtain ⟨v,hv⟩ := assn i hl (by omega)
    rw [hv]; cases v <;> rfl)
  have ab : P-1=S+z+2+n := by dsimp [P]; omega
  rw [ab] at a
  have c := keep (M := Stream.machine) (Stream.q 3) (Stream.q 4) (S+z+2) (S+z+1) T .left (P := P)
    (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [sep]; rfl) (by simp [dest])
  have d := sweepL (M := Stream.machine) (Stream.q 4) T S (z+1) (P := P) (by dsimp [P]; omega) (by
    intro i hl hu; rw [reg i hl (by omega)]; rfl)
  have e := keep (M := Stream.machine) (Stream.q 4) (Stream.q 5) S (S-1) T .left (P := P)
    (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [eof]; rfl) rfl
  have f := sweepL (M := Stream.machine) (Stream.q 5) T (p-2) (S-p+1) (P := P) (by dsimp [P]; omega) (by
    intro i hl hu
    have occ : ∃ b, T i=some b := by
      by_cases hi : i=p-1
      · exact ⟨true,hi ▸ marker⟩
      · exact source i (by omega) (by omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> rfl)
  have ef : p-2+(S-p+1)=S-1 := by omega
  rw [ef] at f
  have g := keep (M := Stream.machine) (Stream.q 5) (Stream.q 6) (p-2) (p-1) T .right (P := P)
    (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [hole]; rfl) (by simp [dest]; omega)
  have h := keep (M := Stream.machine) (Stream.q 6) (Stream.q 7) (p-1) p T .right (P := P)
    (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [marker]; rfl) (by simp [dest]; omega)
  have eqD : S+(z+1)=S+z+1 := by omega
  rw [eqD] at d
  convert ((((((a.append b).append c).append d).append e).append f).append g).append h using 1; omega


/-- Generic physical-or-virtual read and a complete return frame. -/
private theorem stream_read_path (T : Nat → Option Bool) (p S z n : Nat) (hp : 2 ≤ p) (hps : p ≤ S)
    (hole : T (p-2)=none) (marker : T (p-1)=some true)
    (source : ∀ i, p ≤ i → i < S → ∃ b, T i=some b)
    (eof : T S=none)
    (reg : ∀ i, S < i → i < S+z+2 → T i=some false)
    (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b)
    (right : T (S+z+n+3)=none) :
    ∃ mode : Fin 3,
      (mode.val=2 ↔ p=S) ∧ (p<S → T p=some (InputRead.result mode)) ∧
      Path (M := Stream.machine) (S+z+n+3) (InputRead.readClock n z (S-p))
        ⟨Stream.q 2,S+z+n+3,T⟩ ⟨Stream.unpaid mode,S+z+n+3,put T p none⟩ := by
  have seek := stream_seek_path T p S z n hp hps hole marker source eof reg sep assn right
  by_cases hlt : p<S
  · obtain ⟨b,hb⟩ := source p le_rfl hlt
    let U := put T p none
    have one := hop (M := Stream.machine) (Stream.q 7) (Stream.q (8+8*(InputRead.modeOf b).val)) p (p+1) T none .right
      (P := S+z+n+3) (by omega) (by omega) (by rw [hb]; cases b <;> rfl) rfl
    have rows := stream_return_rows (InputRead.modeOf b)
    have a := sweepR (M := Stream.machine) (Stream.q (8+8*(InputRead.modeOf b).val)) U (p+1) (S-p-1)
      (P := S+z+n+3) (by omega) (by
        intro i hl hu; obtain ⟨v,hv⟩ := source i (by omega) (by omega)
        have hvU : U i=some v := by simp [U,put,show i≠p by omega,hv]
        rw [hvU]; exact rows.1 v)
    have eqS : p+1+(S-p-1)=S := by omega
    rw [eqS] at a
    have ue : U S=none := by simp [U,put,show S≠p by omega,eof]
    have c := keep (M := Stream.machine) (Stream.q (8+8*(InputRead.modeOf b).val)) (Stream.q (9+8*(InputRead.modeOf b).val)) S (S+1) U .right
      (P := S+z+n+3) (by omega) (by omega) (by rw [ue]; exact rows.2.1) rfl
    have ret := stream_return_path U S z n (InputRead.modeOf b)
      (by intro i hl hu; simp [U,put,show i≠p by omega,reg i hl hu])
      (by simp [U,put,show S+z+2≠p by omega,sep])
      (by intro i hl hu; obtain ⟨v,hv⟩ := assn i hl hu; exact ⟨v,by simp [U,put,show i≠p by omega,hv]⟩)
      (by simp [U,put,show S+z+n+3≠p by omega,right])
    refine ⟨InputRead.modeOf b,by cases b <;> simp [InputRead.modeOf] <;> omega,?_,?_⟩
    · intro _; cases b <;> simpa [InputRead.result,InputRead.modeOf] using hb
    · convert (((seek.append one).append a).append c).append ret using 1; dsimp [InputRead.readClock]; omega
  · have eq : p=S := by omega
    have one := keep (M := Stream.machine) (Stream.q 7) (Stream.q 25) S (S+1) T .right
      (P := S+z+n+3) (by omega) (by omega) (by rw [eof]; rfl) rfl
    have ret := stream_return_path T S z n ⟨2,by decide⟩ reg sep assn right
    have unchanged : put T p none=T := by rw [eq,← eof,put_same]
    refine ⟨⟨2,by decide⟩,by simp [eq],by omega,?_⟩
    rw [unchanged]
    rw [eq] at seek
    convert (seek.append one).append ret using 1; simp [InputRead.readClock]; omega


end SmallOrbit
namespace SmallOrbit
open Pnp3.Complexity.Uniform.V1
attribute [local irreducible] UniformTM.run
private structure Frame (T : Nat → Option Bool) (S z n A F : Nat) : Prop where
  full : 2≤A ∧ A≤S
  room : S+z+n+3<F
  source : ∀ i, A≤ i → i<S → ∃ b, T i=some b
  eof : T S=none
  reg : ∀ i, S< i → i<S+z+2 → T i=some false
  sep : T (S+z+2)=none
  marks : ∀ i, S+z+2< i → i<S+z+n+3 → T i=some true
  right : T (S+z+n+3)=none
  scratch : ∀ i, S+z+n+3< i → i<F → T i=none
  fence : T F=some false
  hole : T (A-2)=none
  marker : T (A-1)=some true
private theorem read_mode (U : Nat → Option Bool) (p S : Nat) (hp : p≤S) (mode : Fin 3)
    (virtual : mode.val=2 ↔ p=S) (bit : p<S → U p=some (InputRead.result mode)) :
    mode=Stream.Target.mode U p S := by
  apply Fin.ext
  by_cases h : p=S
  · have hm := virtual.mpr h
    simp [Stream.Target.mode,h,hm]
  · have hb := bit (by omega)
    have hm : mode.val≠2 := by intro he; exact h (virtual.mp he)
    fin_cases mode <;> simp_all [Stream.Target.mode,InputRead.result]
private theorem image_zero (U : Nat → Option Bool) (S z n A : Nat) (full : A≤S)
    (digits : ∀ i, S+z+2< i → i<S+z+n+3 → U i=some false) (eof : U S=none) :
    Stream.Target.image U S z n A 0 0 true=put U A none := by
  have cursor : Stream.Target.cursor A S 0=A := by
    simp only [Stream.Target.cursor,Nat.add_zero,Nat.min_eq_left full]
  funext i
  by_cases inside : S+z+2< i ∧ i<S+z+n+3
  · have index : S+z+n+3-1-i<n := by omega
    simp only [Stream.Target.image,show S+z+2+n+1=S+z+n+3 by omega,if_pos inside,
      Body.iterBits,List.getElem!_eq_getElem?_getD,List.getElem?_replicate,if_pos index,
      Option.getD_some,put,if_neg (show i≠A by omega),digits i inside.1 inside.2]
  · simp only [Stream.Target.image,show S+z+2+n+1=S+z+n+3 by omega,if_neg inside,
      show ¬ (S+z+n+3< i ∧ i≤S+z+n+3+0) by omega,if_false,cursor,put]
    by_cases h : i=A
    · subst i; by_cases hs : A=S
      · simp [hs,eof]
      · simp [show A<S by omega]
    · simp [h]
private theorem install_read {N B S z n A F : Nat} (T : Nat → Option Bool)
    (frame : Frame T S z n A F) (fit : F<tapeLength N B) :
    let H := S+z+n+3
    let U := Body.clear T (S+z+3) n
    ∀ hL : S+z+2<tapeLength N B,
    Stream.machine.run (n+2+InputRead.readClock n z (S-A))
        ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i => T i.val⟩ =
      ⟨Stream.unpaid (Stream.Target.mode U A S),⟨H,frame.room.trans fit⟩,
        fun i => Stream.Target.image U S z n A 0 0 true i.val⟩ := by
  dsimp only
  let L := S+z+2
  let H := S+z+n+3
  let U := Body.clear T (S+z+3) n
  intro hL
  have low (i : Nat) (hi : i≤L) : U i=T i := by
    unfold U Body.clear; rw [if_neg (by dsimp [L] at hi; omega)]
  have high (i : Nat) (hi : H≤ i) : U i=T i := by
    unfold U Body.clear; rw [if_neg (by dsimp [H] at hi; omega)]
  have digits (i : Nat) (lo : L< i) (hi : i<H) : U i=some false := by
    unfold U Body.clear; rw [if_pos (by dsimp [L,H] at *; omega)]
  have src (i : Nat) (lo : A≤ i) (hi : i<S) : ∃ b, U i=some b := by
    rw [low i (by dsimp [L]; omega)]; exact frame.source i lo hi
  have eof : U S=none := by rw [low S (by dsimp [L]; omega)]; exact frame.eof
  have reg (i : Nat) (lo : S< i) (hi : i<L) : U i=some false := by
    rw [low i (by omega)]; exact frame.reg i lo hi
  have sep : U L=none := by rw [low L le_rfl]; exact frame.sep
  have right : U H=none := by rw [high H le_rfl]; exact frame.right
  have hole : U (A-2)=none := by rw [low _ (by have := frame.full.2; dsimp [L]; omega)]; exact frame.hole
  have marker : U (A-1)=some true := by rw [low _ (by have := frame.full.2; dsimp [L]; omega)]; exact frame.marker
  obtain ⟨mode,virtual,bit,path⟩ := stream_read_path U A S z n frame.full.1 frame.full.2 hole marker src eof reg sep
    (by intro i lo hi; exact ⟨false,digits i lo hi⟩) right
  have modeEq := read_mode U A S frame.full.2 mode virtual bit
  have hH : H<tapeLength N B := frame.room.trans fit
  have assoc : L+n+1=H := by dsimp [L,H]; omega
  have htime : L+1=S+z+3 := rfl
  have installed := (stream_install_path T L n frame.sep
    (by intro i lo hi; rw [assoc] at hi; exact frame.marks i lo hi)
    (by rw [assoc]; exact frame.right)).execute (N := N) (B := B)
    (by rw [assoc]; exact hH)
  have installed' : Stream.machine.run (n+2)
      ⟨Stream.machine.start,⟨L,hL⟩,fun i => T i.val⟩ =
      ⟨Stream.q 2,⟨H,hH⟩,fun i => U i.val⟩ := by
    simpa only [embed,assoc,htime,U] using installed
  have loaded := path.execute (N := N) (B := B) hH
  rw [Stream.machine.run_add,installed']
  refine loaded.trans ?_
  apply Config.ext_parts
  · exact congrArg Stream.unpaid modeEq
  · rfl
  · funext i
    exact (congrFun (image_zero U S z n A frame.full.2 digits eof) i.val).symm
end SmallOrbit
namespace SmallOrbit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding SmallIngress
private theorem region_eq (S z n i : Nat) (hi : S≤ i) :
    (if S< i ∧ i<S+z+2 then some false else if S+z+2< i ∧ i<S+z+n+3 then some true else none) =
    (if i=S then none else if i≤S+1+z then some false else if S+3+z≤ i ∧ i<S+3+z+n then some true else none) := by
  split_ifs <;> first | rfl | omega
set_option linter.unusedSimpArgs false
private theorem small_tape_eq {a m B : Nat} (x : Bitstring a) (w : Bitstring m) (n : Fin 3)
    (full : (if n.val=0 then 9 else 11) ≤ a+m)
    (h8 : FixedContentTagGate.physicalSymbol (Fin.append x w) 8=some (n.val==0)) :
    (fun i : Fin (tapeLength (pairLength a m) B) =>
      seeded (Body.extend (FixedRawLengthFence.fencedContentTape B x w)) (a+m) n.val i.val) =
      prepared B x w (if n.val=0 then 0 else 1) n.val := by
  have low : 9≤a+m := by split_ifs at full <;> omega
  have far : a+m+6 < FixedRawLengthFence.fencePos (pairLength a m) := by
    simp only [FixedRawLengthFence.fencePos,pairLength]; omega
  have bound8 : 8<tapeLength (pairLength a m) B := by
    simp only [tapeLength,pairLength]; omega
  have bound10 (hn0 : n.val≠0) : 10<tapeLength (pairLength a m) B := by
    have hf : 11≤a+m := by simpa only [if_neg hn0] using full
    simp only [tapeLength,pairLength]; omega
  funext i
  have base := Body.extend_read (FixedRawLengthFence.fencedContentTape B x w) i
  by_cases hi : i.val<a+m
  · have neqF : i.val≠FixedRawLengthFence.fencePos (pairLength a m) := by omega
    have nr : ¬ a+m< i.val := by omega
    have nr' : ¬ a+m+1≤ i.val := by omega
    by_cases hn0 : n.val=0
    · have walk : FixedGammaTargetPayloadExhaustion.termWalk (a+m) 0=0 := by
        simp [FixedGammaTargetPayloadExhaustion.termWalk,FixedGammaTargetPayloadLoopFoundation.walk]
      have noMark : ¬ a+m+2< i.val := by omega
      have empty : ¬ (8≤ i.val ∧ i.val<8) := by omega
      by_cases h7 : i.val=7
      · simp [seeded,prepared,hn0,h7]
      · by_cases hmark : i.val=8
        · have ieq : i=⟨8,bound8⟩ := Fin.ext hmark
          subst i
          have bit8 : Fin.append x w ⟨8,by omega⟩=true := by
            simpa [FixedContentTagGate.physicalSymbol,show 8<a+m by omega,hn0] using h8
          simp [seeded,prepared,hn0,h7,hmark,base,FixedRawLengthFence.fencedContentTape,
            FixedRawLengthFence.countdownTape,neqF,FixedGammaTargetUnaryCountdown.loopTape,hi,
            FixedGammaTargetPayloadExhaustion.finishTape,walk,nr,nr',noMark,empty,
            FixedPairContentMarkerErase.contentTape,bit8]
        · simp [seeded,prepared,hn0,h7,hmark,base,FixedRawLengthFence.fencedContentTape,
            FixedRawLengthFence.countdownTape,neqF,FixedGammaTargetUnaryCountdown.loopTape,hi,
            FixedGammaTargetPayloadExhaustion.finishTape,walk,nr,nr',noMark,empty,
            FixedPairContentMarkerErase.contentTape]
    · have walk : FixedGammaTargetPayloadExhaustion.termWalk (a+m) 1=1 := by
        unfold FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk
        apply Nat.min_eq_left; have hf : 11≤a+m := by simpa only [if_neg hn0] using full
        omega
      have noMark : ¬ a+m+1+2< i.val := by omega
      by_cases h9 : i.val=9
      · have ieq : i=⟨9,lt_trans (by decide) (bound10 hn0)⟩ := Fin.ext h9
        subst i
        simp [seeded,prepared,hn0,h9]
        simp [FixedRawLengthFence.countdownTape,neqF,FixedGammaTargetUnaryCountdown.loopTape,hi,
          FixedGammaTargetPayloadExhaustion.finishTape,walk,h9]
      · by_cases h10 : i.val=10
        · have ieq : i=⟨10,bound10 hn0⟩ := Fin.ext h10
          subst i
          simp [seeded,prepared,hn0,h9,h10,FixedRawLengthFence.countdownTape,neqF,
            FixedGammaTargetUnaryCountdown.loopTape,hi,FixedGammaTargetPayloadExhaustion.finishTape,walk]
        · have empty : ¬ (9≤ i.val ∧ i.val<10) := by omega
          simp [seeded,prepared,hn0,h9,h10,base,FixedRawLengthFence.fencedContentTape,
            FixedRawLengthFence.countdownTape,neqF,FixedGammaTargetUnaryCountdown.loopTape,hi,
            FixedGammaTargetPayloadExhaustion.finishTape,walk,nr,nr',noMark,empty,
            FixedPairContentMarkerErase.contentTape]
  · have no7 : ¬ (n.val=0 ∧ i.val=7) := by omega
    have no9 : ¬ (n.val≠0 ∧ i.val=9) := by
      rintro ⟨h,h9⟩; have hf : 11≤a+m := by simpa only [if_neg h] using full
      omega
    have no10 : ¬ (n.val≠0 ∧ i.val=10) := by
      rintro ⟨h,h10⟩; have hf : 11≤a+m := by simpa only [if_neg h] using full
      omega
    by_cases hF : i.val=FixedRawLengthFence.fencePos (pairLength a m)
    · have noReg : ¬ (a+m< i.val ∧ i.val<a+m+(if n.val=0 then 0 else 1)+2) := by
        split_ifs <;> first | rfl | omega
      have noMark : ¬ (a+m+(if n.val=0 then 0 else 1)+2< i.val ∧
          i.val<a+m+(if n.val=0 then 0 else 1)+n.val+3) := by
        have := n.isLt; split_ifs <;> omega
      simp only [seeded,prepared,if_neg no7,if_neg no9,if_neg no10,if_neg noReg,if_neg noMark,
        base,FixedRawLengthFence.fencedContentTape,dif_neg hi,if_pos hF,
        FixedRawLengthFence.countdownTape,if_pos hF]
    · simp only [seeded,prepared,if_neg no7,if_neg no9,if_neg no10,base,
        FixedRawLengthFence.fencedContentTape,dif_neg hi,if_neg hF,
        FixedRawLengthFence.countdownTape,FixedGammaTargetUnaryCountdown.loopTape,if_neg hi,
        Nat.zero_testBit]
      exact region_eq (a+m) (if n.val=0 then 0 else 1) n.val i.val (by omega)
end SmallOrbit
namespace SmallOrbit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding SmallIngress
private theorem prepared_frame {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n<FixedRawLengthFence.capacity a m z) (full : 9+2*z≤a+m) (zero : z=0 → n=0) :
    Frame (Body.extend (prepared (FixedRawLengthFence.allocation (pairLength a m)) x w z n))
      (a+m) z n (9+2*z) (FixedRawLengthFence.fencePos (pairLength a m)) := by
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let A := 9+2*z
  let H := S+z+n+3
  let F := FixedRawLengthFence.fencePos R
  let T := Body.extend (prepared B x w z n)
  have resource := (FixedRawLengthFence.resource_bounds R).1
  have cells := FixedRawLengthFence.countdown_success_cells x w gamma resource (Nat.le_of_lt cap)
  obtain ⟨room,_scratch,hF,_fence⟩ := Stream.raw_budget_cells x w gamma cap
  change H<F at room
  change F<tapeLength R B at hF
  have hH : H<tapeLength R B := room.trans hF
  have read (i : Nat) (hi : i<tapeLength R B) : T i=prepared B x w z n ⟨i,hi⟩ := by
    have h : i<tapeLength (pairLength a m) B := hi
    simp only [T,Body.extend,dif_pos h]
  have old (i : Nat) (hi : i<tapeLength R B) (above : 7< i) :
      T i=FixedRawLengthFence.countdownTape B x w z 0 n ⟨i,hi⟩ := by
    rw [read i hi,prepared,if_neg (by change ¬ (n=0 ∧ i=7); omega)]
  have low (i : Nat) (hi : i<S) (above : 7< i) :
      T i=FixedGammaTargetPayloadExhaustion.finishTape B x w z ⟨i,by
        change i<tapeLength R B; omega⟩ := by
    rw [old i (by omega) above]
    exact cells.1 _ hi
  have walk : FixedGammaTargetPayloadExhaustion.termWalk S z=z := by
    unfold FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk
    apply Nat.min_eq_left; dsimp [S] at *; omega
  have src (i : Nat) (lo : A≤ i) (hi : i<S) : ∃ b, T i=some b := by
    rw [old i (by omega) (by dsimp [A] at lo; omega)]
    exact ⟨_,Body.raw_source_after_header x w gamma resource (Nat.le_of_lt cap) _ (by change 8+2*z+1≤ i; dsimp [A] at lo; omega) hi⟩
  have eof : T S=none := by
    rw [old S (by omega) (by dsimp [S]; omega)]
    unfold FixedRawLengthFence.countdownTape
    rw [if_neg (by change S≠F; omega)]
    simp [FixedGammaTargetUnaryCountdown.loopTape,S]
  have reg (i : Nat) (lo : S< i) (hi : i<S+z+2) : T i=some false := by
    rw [old i (by omega) (by dsimp [S] at lo; omega)]
    exact cells.2.1 (i-S-1) (by omega) _ (by dsimp [S]; omega)
  have sep : T (S+z+2)=none := by
    rw [old _ (by omega) (by dsimp [S]; omega)]
    exact cells.2.2.1 _ (by dsimp [S]; omega)
  have marks (i : Nat) (lo : S+z+2< i) (hi : i<H) : T i=some true := by
    rw [old i (by omega) (by dsimp [S] at lo; omega)]
    exact cells.2.2.2.1 _ (by dsimp [S]; omega) (by change i<a+m+3+z+n; dsimp [H,S] at hi; omega)
  have right : T H=none := by
    rw [old H (room.trans hF) (by dsimp [H,S]; omega)]
    exact cells.2.2.2.2.1 _ (by dsimp [H,S]; omega) room
  have scratch (i : Nat) (lo : H< i) (hi : i<F) : T i=none := by
    rw [old i (hi.trans hF) (by dsimp [H,S] at lo; omega)]
    exact cells.2.2.2.2.1 _ (by change a+m+3+z+n≤ i; dsimp [H,S] at lo; omega) hi
  have fence : T F=some false := by
    rw [old F hF (by dsimp [H,S] at room; omega)]
    exact cells.2.2.2.2.2 _ rfl
  have hole : T (A-2)=none := by
    by_cases hz : z=0
    · have hn := zero hz
      rw [read _ (by dsimp [A]; omega)]
      simp [prepared,A,hz,hn]
    · rw [low _ (by dsimp [A,S]; omega) (by dsimp [A]; omega)]
      unfold FixedGammaTargetPayloadExhaustion.finishTape
      rw [walk,if_pos (by dsimp [A]; omega)]
  have marker : T (A-1)=some true := by
    rw [low _ (by dsimp [A,S]; omega) (by dsimp [A]; omega)]
    unfold FixedGammaTargetPayloadExhaustion.finishTape
    rw [walk,if_neg (by dsimp [A]; omega),if_pos (by dsimp [A]; omega)]
  exact ⟨⟨by omega,full⟩,room,src,eof,reg,sep,marks,right,scratch,fence,hole,marker⟩
private theorem clear_extend {N B : Nat} (T : Fin (tapeLength N B) → Option Bool) (L n : Nat)
    (fit : L+n+1<tapeLength N B) :
    Body.clear (Body.extend T) (L+1) n=Body.extend (Body.installedTape T L n) := by
  funext i
  by_cases hi : i<tapeLength N B
  · simp only [Body.clear,Body.extend,dif_pos hi,Body.installedTape]
    by_cases h : L< i ∧ i<L+n+1
    · rw [if_pos h,if_pos (by omega)]
    · rw [if_neg h,if_neg (by omega)]
  · simp only [Body.clear,Body.extend,dif_neg hi,if_neg (show ¬ (L+1≤ i ∧ i<L+1+n) by omega)]
end SmallOrbit
namespace SmallOrbit
open Pnp3.Complexity.Uniform.V1
attribute [local irreducible] UniformTM.run
private theorem stream_orbit {N B S z n A F : Nat} (T : Nat → Option Bool)
    (frame : Frame T S z n A F) (fit : F<tapeLength N B)
    (rows : 2^n≤F-(S+z+n+3)-1)
    (hL : S+z+2<tapeLength N B) (hH : S+z+n+3<tapeLength N B) :
    let U := Body.clear T (S+z+3) n
    let c : Config Stream.machine.stateCount N B :=
      ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i => T i.val⟩
    ∃ tb, tb≤n+2+InputRead.readClock n z (S-A)+64*(F+1)^2 ∧
      (∀ r, r<2^n → ∃ t, t≤tb ∧ Stream.machine.run t c =
        ⟨Stream.paid (Stream.Target.mode U (Stream.Target.cursor A S r) S),⟨S+z+n+3,hH⟩,
          fun i => Stream.Target.image U S z n A r (r+1) true i.val⟩) ∧
      ∃ hp : Stream.Target.cursor A S (2^n)<tapeLength N B,
        Stream.machine.run tb c=
          ⟨Stream.q (if Stream.Target.cursor A S (2^n)=S then 57 else 58),
            ⟨Stream.Target.cursor A S (2^n),hp⟩,
            fun i => Stream.Target.image U S z n A (2^n) (2^n) false i.val⟩ := by
  dsimp only
  let U := Body.clear T (S+z+3) n
  have low (i : Nat) (hi : i≤S+z+2) : U i=T i := by
    unfold U Body.clear; rw [if_neg (by omega)]
  have high (i : Nat) (hi : S+z+n+3≤ i) : U i=T i := by
    unfold U Body.clear; rw [if_neg (by omega)]
  obtain ⟨tb,price,paid,finish⟩ := Stream.kernel N B S z n A F U frame.full.1 frame.full.2 frame.room fit
    (by intro i lo hi; rw [low i (by omega)]; exact frame.source i lo hi)
    (by rw [low S (by omega)]; exact frame.eof)
    (by intro i lo hi; rw [low i (by omega)]; exact frame.reg i lo hi)
    (by rw [low _ le_rfl]; exact frame.sep)
    (by rw [high _ le_rfl]; exact frame.right)
    (by intro i lo hi; rw [high i (by omega)]; exact frame.scratch i lo hi)
    (by rw [high F (by have := frame.room; omega)]; exact frame.fence) hH
  have pre := install_read T frame fit hL
  have replay (t : Nat) : Stream.machine.run (n+2+InputRead.readClock n z (S-A)+t)
      ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i => T i.val⟩ =
      Stream.machine.run t ⟨Stream.unpaid (Stream.Target.mode U A S),⟨S+z+n+3,hH⟩,
        fun i => Stream.Target.image U S z n A 0 0 true i.val⟩ := by
    rw [Stream.machine.run_add,pre]
  refine ⟨n+2+InputRead.readClock n z (S-A)+tb,by omega,?_,?_⟩
  · intro r hr
    obtain ⟨t,ht,run⟩ := paid r (by rw [Nat.min_eq_left rows]; exact hr)
    exact ⟨n+2+InputRead.readClock n z (S-A)+t,by omega,by rw [replay,run]⟩
  · rw [if_pos rows] at finish
    obtain ⟨hp,run⟩ := finish
    exact ⟨hp,by rw [replay,run]⟩
end SmallOrbit
namespace SmallOrbit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding SmallIngress
attribute [local irreducible] UniformTM.run
private theorem raw_orbit {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n<FixedRawLengthFence.capacity a m z) (full : 9+2*z≤a+m) (zero : z=0 → n=0)
    (rows : 2^n≤FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (handoff : ∃ (tp : Nat) (hL : a+m+z+2<tapeLength (pairLength a m)
        (FixedRawLengthFence.allocation (pairLength a m))),
      tp≤144*(pairLength a m+1)^2 ∧ ∀ s,
        machine.run (tp+s) (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
          producer.seqEmbedRight Stream.machine
            (Stream.machine.run s ⟨Stream.machine.start,⟨a+m+z+2,hL⟩,
              prepared (FixedRawLengthFence.allocation (pairLength a m)) x w z n⟩)) :
    ∃ (T : Nat) (hH : a+m+z+n+3<tapeLength (pairLength a m)
        (FixedRawLengthFence.allocation (pairLength a m))),
        T ≤ 4096*(pairLength a m+1)^2 ∧
        let U := Body.extend (Body.installedTape (prepared
          (FixedRawLengthFence.allocation (pairLength a m)) x w z n) (a+m+z+2) n)
        (∀ r, r<2^n → ∃ t, t ≤ T ∧
          machine.run t (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.paid (Stream.Target.mode U (Stream.Target.cursor (9+2*z) (a+m) r) (a+m)),⟨a+m+z+n+3,hH⟩,
                fun i => Stream.Target.image U (a+m) z n (9+2*z) r (r+1) true i.val⟩) ∧
        ∃ hp : Stream.Target.cursor (9+2*z) (a+m) (2^n) <
          tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          machine.run T (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.q (if Stream.Target.cursor (9+2*z) (a+m) (2^n)=a+m then 57 else 58),
                ⟨Stream.Target.cursor (9+2*z) (a+m) (2^n),hp⟩,
                fun i => Stream.Target.image U (a+m) z n (9+2*z) (2^n) (2^n) false i.val⟩ := by
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let S := a+m
  let A := 9+2*z
  let F := FixedRawLengthFence.fencePos R
  let T0 := Body.extend (prepared B x w z n)
  let U := Body.extend (Body.installedTape (prepared B x w z n) (S+z+2) n)
  have frame := prepared_frame x w gamma cap full zero
  obtain ⟨_room,_scratch,hF,_fence⟩ := Stream.raw_budget_cells x w gamma cap
  have hH : S+z+n+3<tapeLength R B := frame.room.trans hF
  obtain ⟨tp,hL,prePrice,hand⟩ := handoff
  obtain ⟨tb,bodyPrice,paid,finish⟩ := stream_orbit T0 frame hF rows hL hH
  have Ueq : Body.clear T0 (S+z+3) n=U := by
    have hf : S+z+2+n+1<tapeLength R B := by omega
    exact clear_extend (prepared B x w z n) (S+z+2) n hf
  rw [Ueq] at paid finish
  have entry : (⟨Stream.machine.start,⟨S+z+2,hL⟩,prepared B x w z n⟩ : Config 64 R B)=
      ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i => T0 i.val⟩ := by
    apply Config.ext_parts
    · rfl
    · rfl
    · funext i; exact (Body.extend_read _ i).symm
  have replay (s : Nat) : machine.run (tp+s) (initialConfig machine B (encodePair x w)) =
      producer.seqEmbedRight Stream.machine
        (Stream.machine.run s ⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i => T0 i.val⟩) := by
    rw [←entry]; exact hand s
  have price : tp+tb≤4096*(R+1)^2 := by
    have pair : S≤R := by dsimp [S,R,pairLength]; omega
    have gammaBound := ((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
    have nz : n≤3*R := by
      dsimp only [FixedRawLengthFence.capacity,FixedRawLengthFence.fencePos] at cap
      change n<(3*R+2)-(a+m+3+z) at cap
      omega
    have zz : z≤R := by dsimp [S] at pair; omega
    have dist : S-A≤R := (Nat.sub_le _ _).trans pair
    have square : R+1≤(R+1)^2 := by
      simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (R+1) (show 1≤R+1 by omega)
    change tp≤144*(R+1)^2 at prePrice
    change tb≤n+2+InputRead.readClock n z (S-A)+64*(F+1)^2 at bodyPrice
    dsimp only [InputRead.readClock,F,FixedRawLengthFence.fencePos] at bodyPrice
    nlinarith only [prePrice,bodyPrice,nz,zz,dist,square]
  refine ⟨tp+tb,hH,price,?_,?_⟩
  · intro r hr
    obtain ⟨t,ht,run⟩ := paid r hr
    exact ⟨tp+t,by omega,by rw [replay,run]⟩
  · obtain ⟨hp,run⟩ := finish
    exact ⟨hp,by rw [replay,run]⟩
end SmallOrbit
namespace SmallOrbit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding SmallIngress
attribute [local irreducible] UniformTM.run
/-- All paid assignments and the restored next-field Config on the SAME raw machine. -/
theorem accepted_small (k : Nat) : Target.SmallAcceptedOrbit k := by
  intro a m x w accepted pr parsed small
  have semantic := (accepted_facts k x w accepted).2
  have table := AcceptedBody.table_support k (Fin.append x w) parsed semantic
  obtain ⟨gamma,full,h8,h9,h10⟩ := small_header_physical k x w accepted parsed small
  let z := if pr.2.n=0 then 0 else 1
  have tag : FixedContentTagGate.tagMatches (Fin.append x w)=true := by
    have h := fixedTag_semantic_factorization.1 (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)
    rw [semantic] at h; simpa using h.symm
  have width : pr.2.n≤a+m := by
    have h := Nat.lt_two_pow_self (n := pr.2.n)
    change 2^pr.2.n≤a+m at table; omega
  have cap := AcceptedBody.strict_capacity x w gamma width
  have allRows := Stream.accepted_rows_fit k x w accepted parsed gamma
  have full' : 9+2*z≤a+m := by dsimp [z]; split_ifs at full ⊢ <;> omega
  have zero : z=0 → pr.2.n=0 := by
    intro hz; dsimp [z] at hz; split_ifs at hz with h
    · exact h
  obtain ⟨tp,hL,price,run⟩ := raw_small_physical x w ⟨pr.2.n,small⟩ tag full h8 h9 h10
  have tapeEq := small_tape_eq (B := FixedRawLengthFence.allocation (pairLength a m)) x w ⟨pr.2.n,small⟩ full h8
  rw [tapeEq] at run
  obtain ⟨T,hH,cost,paid,finish⟩ := raw_orbit x w gamma cap full' zero allRows
    ⟨tp,hL,by omega,run⟩
  exact ⟨table,z,T,hH,gamma,cost,paid,finish⟩
end SmallOrbit
namespace SmallOrbit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding SmallIngress
attribute [local irreducible] UniformTM.run
private theorem normal_handoff (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true) (normal : 3≤pr.2.n) :
    ∃ z, 2≤z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n<FixedRawLengthFence.capacity a m z →
        ∃ (tp : Nat) (hL : a+m+z+2<tapeLength (pairLength a m)
            (FixedRawLengthFence.allocation (pairLength a m))),
          tp≤144*(pairLength a m+1)^2 ∧ ∀ s,
          machine.run (tp+s) (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              (Stream.machine.run s ⟨Stream.machine.start,⟨a+m+z+2,hL⟩,
                prepared (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n⟩)) := by
  obtain ⟨_,z,C,qp,hS,hz,gamma,_header,_C,_first,success,_reject⟩ :=
    raw_fenced_countdown_parsed_target k x w parsed tag normal
  refine ⟨z,hz,gamma,?_⟩
  intro cap
  obtain ⟨price,oldRun⟩ := success (Nat.le_of_lt cap)
  let R := pairLength a m
  let B := FixedRawLengthFence.allocation R
  let time := FixedRawLengthFence.countdownSuccessClock a m z C
    (FixedGammaTargetRegisterDecrement.borrow x w z) pr.2.n
  have safe : (FixedRawLengthFence.prefixed.run time
      (initialConfig FixedRawLengthFence.prefixed B (encodePair x w))).state≠FixedRawLengthFence.prefixed.reject := by
    rw [oldRun]; exact FixedRawLengthFence.prefixed.accept_ne_reject
  have transferred := SmallIngress.preserves_nonreject (initialConfig FixedRawLengthFence.prefixed B (encodePair x w)) time safe
  have initial : liftOld (initialConfig FixedRawLengthFence.prefixed B (encodePair x w))=
      initialConfig producer B (encodePair x w) := rfl
  rw [initial,oldRun] at transferred
  change a+m+2+z<tapeLength R B at hS
  have hL : a+m+z+2<tapeLength R B := by omega
  have endpoint : producer.run time (initialConfig producer B (encodePair x w))=
      ⟨producer.accept,⟨a+m+z+2,hL⟩,prepared B x w z pr.2.n⟩ := by
    refine transferred.trans ?_
    apply Config.ext_parts
    · rfl
    · apply Fin.ext
      change a+m+2+z=a+m+z+2
      omega
    · funext i
      change FixedRawLengthFence.countdownTape B x w z 0 pr.2.n i=prepared B x w z pr.2.n i
      rw [prepared,if_neg (by omega)]
  obtain ⟨tp,ht,first,arrived⟩ := Body.first_accept_whole producer (initialConfig producer B (encodePair x w)) _ _ endpoint rfl
  change time≤128*(R+1)^2 at price
  refine ⟨tp,hL,by change tp≤144*(R+1)^2; omega,?_⟩
  intro s
  have hand := producer.seq_handoff Stream.machine (initialConfig producer B (encodePair x w)) first (by rw [arrived]) s
  have initialSeq : producer.seqEmbedRouted Stream.machine (initialConfig producer B (encodePair x w))=
      initialConfig machine B (encodePair x w) := rfl
  rw [initialSeq,arrived] at hand
  exact hand
/-- Full all-arity accepted raw orbit on the same 352-state machine and allocation. -/
theorem accepted_raw (k : Nat) : Target.AcceptedOrbit k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,table,_⟩ := AcceptedBody.exact k x w accepted
  refine ⟨pr,parsed,table,?_⟩
  by_cases small : pr.2.n<3
  · obtain ⟨_table,z,T,hH,gamma,price,paid,finish⟩ := accepted_small k x w accepted pr parsed small
    exact ⟨z,T,hH,gamma,price,paid,finish⟩
  · have normal : 3≤pr.2.n := by omega
    have semantic := (accepted_facts k x w accepted).2
    have tag : FixedContentTagGate.tagMatches (Fin.append x w)=true := by
      have h := fixedTag_semantic_factorization.1 (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)
      rw [semantic] at h; simpa using h.symm
    obtain ⟨z,hz,gamma,run⟩ := normal_handoff k x w parsed tag normal
    have width : pr.2.n≤a+m := by
      have h := Nat.lt_two_pow_self (n := pr.2.n)
      change 2^pr.2.n≤a+m at table; omega
    have cap := AcceptedBody.strict_capacity x w gamma width
    have full := GammaSupport.exact k x w parsed semantic normal z gamma
    have rows := Stream.accepted_rows_fit k x w accepted parsed gamma
    obtain ⟨T,hH,price,paid,finish⟩ := raw_orbit x w gamma cap full (by intro h; omega) rows (run cap)
    exact ⟨z,T,hH,gamma,price,paid,finish⟩
/-- Direct discharge of the unchanged immutable predecessor's original target. -/
theorem original_accepted_raw (k : Nat) : SmallIngress.Target.AcceptedOrbit k := accepted_raw k
end SmallOrbit

namespace SmallOrbit.Audit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding SmallIngress
def pin_AcceptedOrbit (k : Nat) : Prop := @SmallOrbit.Target.AcceptedOrbit k
def pin_SmallAcceptedOrbit (k : Nat) : Prop := @SmallOrbit.Target.SmallAcceptedOrbit k
theorem check_small_header_physical (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : (Sigma fun r : Nat => PrefixInput (treeMCSPSearchProblem (thresholdPoly k) (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k)))) (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r))}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (small : pr.2.n<3) :
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some (if pr.2.n=0 then 0 else 1) ∧
    (if pr.2.n=0 then 9 else 11) ≤ a+m ∧
    FixedContentTagGate.physicalSymbol (Fin.append x w) 8=some (pr.2.n==0) ∧
    (pr.2.n≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 9=some true) ∧
    (pr.2.n≠0 → FixedContentTagGate.physicalSymbol (Fin.append x w) 10=some (pr.2.n==2)) := @SmallOrbit.small_header_physical k a m x w accepted pr parsed small
theorem check_accepted_small (k : Nat) :
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∀ (pr : (Sigma fun r : Nat => PrefixInput (treeMCSPSearchProblem (thresholdPoly k) (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k)))) (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r))),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
      pr.2.n < 3 →
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      ∃ (z T : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        T ≤ 4096*(pairLength a m+1)^2 ∧
        let U := Body.extend (Body.installedTape (prepared
          (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) (a+m+z+2) pr.2.n)
        (∀ r, r<2^pr.2.n → ∃ t, t ≤ T ∧
          machine.run t (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.paid (Stream.Target.mode U (Stream.Target.cursor (9+2*z) (a+m) r) (a+m)),⟨a+m+z+pr.2.n+3,hH⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) r (r+1) true i.val⟩) ∧
        ∃ hp : Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n) <
          tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          machine.run T (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.q (if Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m then 57 else 58),
                ⟨Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n),hp⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false i.val⟩ := @SmallOrbit.accepted_small k
theorem check_accepted_raw (k : Nat) :
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun r : Nat => PrefixInput (treeMCSPSearchProblem (thresholdPoly k) (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k)))) (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      ∃ (z T : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        T ≤ 4096*(pairLength a m+1)^2 ∧
        let U := Body.extend (Body.installedTape (prepared
          (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) (a+m+z+2) pr.2.n)
        (∀ r, r<2^pr.2.n → ∃ t, t ≤ T ∧
          machine.run t (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.paid (Stream.Target.mode U (Stream.Target.cursor (9+2*z) (a+m) r) (a+m)),⟨a+m+z+pr.2.n+3,hH⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) r (r+1) true i.val⟩) ∧
        ∃ hp : Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n) <
          tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          machine.run T (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.q (if Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m then 57 else 58),
                ⟨Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n),hp⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false i.val⟩ := @SmallOrbit.accepted_raw k
theorem check_original_accepted_raw (k : Nat) :
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun r : Nat => PrefixInput (treeMCSPSearchProblem (thresholdPoly k) (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k)))) (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      ∃ (z T : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        T ≤ 4096*(pairLength a m+1)^2 ∧
        let U := Body.extend (Body.installedTape (prepared
          (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) (a+m+z+2) pr.2.n)
        (∀ r, r<2^pr.2.n → ∃ t, t ≤ T ∧
          machine.run t (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.paid (Stream.Target.mode U (Stream.Target.cursor (9+2*z) (a+m) r) (a+m)),⟨a+m+z+pr.2.n+3,hH⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) r (r+1) true i.val⟩) ∧
        ∃ hp : Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n) <
          tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
          machine.run T (initialConfig machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            producer.seqEmbedRight Stream.machine
              ⟨Stream.q (if Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n)=a+m then 57 else 58),
                ⟨Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n),hp⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false i.val⟩ := @SmallOrbit.original_accepted_raw k
/-- Independent full mirror of the public unfolding equation generated by this consumer. -/
theorem check_prepared_eq_1 {a m : Nat} (B : Nat) (x : Bitstring a) (w : Bitstring m) (z n : Nat)
    (i : Fin (tapeLength (pairLength a m) B)) :
    SmallIngress.prepared B x w z n i=
      if n=0 ∧ i.val=7 then none else FixedRawLengthFence.countdownTape B x w z 0 n i :=
  @SmallIngress.prepared.eq_1 a m B x w z n i
/-- Independent full mirror of the actual same-table image equation. -/
theorem check_image_eq_1 (U : Nat → Option Bool) (S z n A r marks : Nat) (lift : Bool) (i : Nat) :
    Stream.Target.image U S z n A r marks lift i=
      let L := S+z+2
      let H := L+n+1
      if L < i ∧ i < H then some ((Body.iterBits (List.replicate n false) r)[H-1-i]!)
      else if H < i ∧ i ≤ H+marks then some true
      else if lift ∧ i=Stream.Target.cursor A S r ∧ i < S then none else U i :=
  @Stream.Target.image.eq_1 U S z n A r marks lift i
end SmallOrbit.Audit
#print axioms SmallOrbit.Target.AcceptedOrbit
#print axioms SmallOrbit.Audit.pin_AcceptedOrbit
#print axioms SmallOrbit.Target.SmallAcceptedOrbit
#print axioms SmallOrbit.Audit.pin_SmallAcceptedOrbit
#print axioms SmallOrbit.small_header_physical
#print axioms SmallOrbit.Audit.check_small_header_physical
#print axioms SmallOrbit.accepted_small
#print axioms SmallOrbit.Audit.check_accepted_small
#print axioms SmallOrbit.accepted_raw
#print axioms SmallOrbit.Audit.check_accepted_raw
#print axioms SmallOrbit.original_accepted_raw
#print axioms SmallOrbit.Audit.check_original_accepted_raw
#print axioms SmallIngress.prepared.eq_1
#print axioms SmallOrbit.Audit.check_prepared_eq_1
#print axioms Stream.Target.image.eq_1
#print axioms SmallOrbit.Audit.check_image_eq_1
open Lean in
run_cmd do
  let e ← getEnv
  for (n, _) in e.constants.toList do
    if n.toString.startsWith "SmallOrbit." then logInfo m!"surface|{n}"
    if (e.getModuleIdxFor? n).isNone && !n.toString.startsWith "_private." then logInfo m!"owned|{n}"
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
