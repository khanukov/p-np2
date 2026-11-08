import Attempt.Prefix
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth

namespace Research.SolverToDag.Parser
open Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit
open Pnp4.Frontier.ContractExpansion

/-- One layer stores every bounded start/end cursor and both evaluation bits. -/
private def layerWidth (W : Nat) : Nat := (W + 1) * (W + 1) * 2

private def cellIndex (W nodes start stop : Nat) (value : Bool) : Nat :=
  (((nodes * (W + 1) + start) * (W + 1) + stop) * 2) + (if value then 1 else 0)

private theorem cellIndex_coords (W nodes start stop : Nat) (value : Bool)
    (ha : start ≤ W) (hb : stop ≤ W) :
    let i := cellIndex W nodes start stop value
    i / 2 / (W + 1) / (W + 1) = nodes ∧
    (i / 2 / (W + 1)) % (W + 1) = start ∧
    (i / 2) % (W + 1) = stop ∧ decide (i % 2 = 1) = value := by
  have hv : (if value then 1 else 0 : Nat) < 2 := by cases value <;> decide
  have hhalf : cellIndex W nodes start stop value / 2 =
      (nodes * (W + 1) + start) * (W + 1) + stop := by
    apply Nat.div_eq_of_lt_le <;> dsimp [cellIndex] <;> omega
  have hquarter : cellIndex W nodes start stop value / 2 / (W + 1) =
      nodes * (W + 1) + start := by
    rw [hhalf]
    apply Nat.div_eq_of_lt_le <;> nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hquarter]
    apply Nat.div_eq_of_lt_le <;> nlinarith
  · rw [hquarter, Nat.mul_add_mod_of_lt (by omega : start < W + 1)]
  · rw [hhalf, Nat.mul_add_mod_of_lt (by omega : stop < W + 1)]
  · cases value <;> simp [cellIndex, Nat.add_mod]

private theorem cellIndex_inverse (W i : Nat) :
    cellIndex W (i / 2 / (W + 1) / (W + 1))
      ((i / 2 / (W + 1)) % (W + 1)) ((i / 2) % (W + 1))
      (decide (i % 2 = 1)) = i := by
  have hb : (if decide (i % 2 = 1) then 1 else 0 : Nat) = i % 2 := by
    have h := Nat.mod_lt i (by decide : 0 < 2)
    by_cases he : i % 2 = 1
    · simp [he]
    · simp [he]
      omega
  simp only [cellIndex, hb]
  rw [Nat.div_add_mod', Nat.div_add_mod', Nat.div_add_mod']

private theorem cellIndex_lower (W m a b : Nat) (v : Bool) :
    m * layerWidth W ≤ cellIndex W m a b v := by
  calc
    m * layerWidth W ≤ m * layerWidth W + (a * (W + 1) + b) * 2 +
        (if v then 1 else 0) := by omega
    _ = cellIndex W m a b v := by unfold layerWidth cellIndex; ring

private theorem cellIndex_upper (W m a b : Nat) (v : Bool) (ha : a ≤ W) (hb : b ≤ W) :
    cellIndex W m a b v < (m + 1) * layerWidth W := by
  have h1 : m * (W + 1) + a + 1 ≤ (m + 1) * (W + 1) := by nlinarith
  have h2 : (m * (W + 1) + a) * (W + 1) + b + 1 ≤
      ((m + 1) * (W + 1)) * (W + 1) := by
    calc
      _ ≤ (m * (W + 1) + a) * (W + 1) + (W + 1) := by omega
      _ = (m * (W + 1) + a + 1) * (W + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right (W + 1) h1
  have hv : (if v then 1 else 0 : Nat) ≤ 1 := by cases v <;> decide
  unfold cellIndex layerWidth
  nlinarith

/-- Literal native prefix grammar, with the returned cursor made explicit.
This is a relation on actual tree formulas, not a verifier-existence contract. -/
private inductive Parsed {n W : Nat} (width : Nat) (hw : n ≤ 2 ^ width) (bits : Bitstring W) :
    Nat → Nat → Pnp3.Models.Circuit n → Prop where
  | input (a : Nat) (i : Fin n)
      (h : Prefix.fits bits a (encodeCircuit width hw (.input i))) :
      Parsed width hw bits a (a + 3 + width) (.input i)
  | const (a : Nat) (b : Bool) (h : Prefix.fits bits a [false, false, true, b]) :
      Parsed width hw bits a (a + 4) (.const b)
  | not (a z : Nat) (c : Pnp3.Models.Circuit n)
      (h : Prefix.fits bits a [false, true, false])
      (child : Parsed width hw bits (a + 3) z c) : Parsed width hw bits a z (.not c)
  | and (a middle z : Nat) (c d : Pnp3.Models.Circuit n)
      (h : Prefix.fits bits a [false, true, true])
      (left : Parsed width hw bits (a + 3) middle c)
      (right : Parsed width hw bits middle z d) : Parsed width hw bits a z (.and c d)
  | or (a middle z : Nat) (c d : Pnp3.Models.Circuit n)
      (h : Prefix.fits bits a [true, false, false])
      (left : Parsed width hw bits (a + 3) middle c)
      (right : Parsed width hw bits middle z d) : Parsed width hw bits a z (.or c d)

private theorem Parsed.native_word {n W width : Nat} {hw : n ≤ 2 ^ width}
    {bits : Bitstring W} {a z : Nat} {c : Pnp3.Models.Circuit n}
    (h : Parsed width hw bits a z c) :
    Prefix.fits bits a (encodeCircuit width hw c) ∧
      z = a + (encodeCircuit width hw c).length := by
  induction h with
  | input a i h =>
    refine ⟨h, ?_⟩
    simp only [encodeCircuit, toTree,
      Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeCircuitTree, List.length_append,
      List.length_cons, List.length_nil,
      Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeFin_length]
    omega
  | const a b h => exact ⟨h, rfl⟩
  | not a z c h child ih =>
    change Prefix.fits bits a ([false, true, false] ++ encodeCircuit width hw c) ∧ _
    rw [Prefix.fits_append]
    refine ⟨⟨h, by simpa using ih.1⟩, ?_⟩
    have hl : (encodeCircuit width hw (.not c)).length = 3 + (encodeCircuit width hw c).length := by
      simp only [encodeCircuit, toTree, Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeCircuitTree,
        List.length_append, List.length_cons, List.length_nil]
    rw [hl]
    omega
  | and a m z c d h left right ihc ihd =>
    change Prefix.fits bits a ([false, true, true] ++
      (encodeCircuit width hw c ++ encodeCircuit width hw d)) ∧ _
    rw [Prefix.fits_append, Prefix.fits_append]
    refine ⟨⟨h, ihc.1, ?_⟩, ?_⟩
    · simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, ← ihc.2] using ihd.1
    · have hl : (encodeCircuit width hw (.and c d)).length =
          3 + ((encodeCircuit width hw c).length + (encodeCircuit width hw d).length) := by
        simp only [encodeCircuit, toTree, Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeCircuitTree,
          List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hl]
      omega
  | or a m z c d h left right ihc ihd =>
    change Prefix.fits bits a ([true, false, false] ++
      (encodeCircuit width hw c ++ encodeCircuit width hw d)) ∧ _
    rw [Prefix.fits_append, Prefix.fits_append]
    refine ⟨⟨h, ihc.1, ?_⟩, ?_⟩
    · simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, ← ihc.2] using ihd.1
    · have hl : (encodeCircuit width hw (.or c d)).length =
          3 + ((encodeCircuit width hw c).length + (encodeCircuit width hw d).length) := by
        simp only [encodeCircuit, toTree, Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeCircuitTree,
          List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hl]
      omega

private theorem Parsed.bounds {n W width : Nat} {hw : n ≤ 2 ^ width}
    {bits : Bitstring W} {a z : Nat} {c : Pnp3.Models.Circuit n}
    (h : Parsed width hw bits a z c) : a < z ∧ z ≤ W := by
  obtain ⟨hf, hz⟩ := h.native_word
  have hc : 1 ≤ c.size := by cases c <;> simp only [Pnp3.Models.Circuit.size] <;> omega
  have hl := length_encodeCircuit_ge width hw c
  have hp := hf ⟨(encodeCircuit width hw c).length - 1, by omega⟩
  obtain ⟨hp, _⟩ := hp
  change a + ((encodeCircuit width hw c).length - 1) < W at hp
  omega

/-- Only prior register wires are read. Invalid cursors/zero-node cells reject. -/
private def prior (W r nodes start stop : Nat) (value : Bool) : DagCircuit (W + r) :=
  if h : 0 < nodes ∧ start ≤ W ∧ stop ≤ W ∧ cellIndex W nodes start stop value < r then
    withOutput (constCircuit (W + r) false)
      (.input (Fin.natAdd W ⟨cellIndex W nodes start stop value, h.2.2.2⟩))
  else constCircuit (W + r) false

private theorem eval_prior (W r nodes start stop : Nat) (value : Bool) (inputs : Bitstring (W + r)) :
    eval (prior W r nodes start stop value) inputs =
      if h : 0 < nodes ∧ start ≤ W ∧ stop ≤ W ∧ cellIndex W nodes start stop value < r then
        inputs (Fin.natAdd W ⟨cellIndex W nodes start stop value, h.2.2.2⟩) else false := by
  by_cases h : 0 < nodes ∧ start ≤ W ∧ stop ≤ W ∧ cellIndex W nodes start stop value < r
  · simp only [prior, dif_pos h, eval_withOutput_input]
  · simp only [prior, dif_neg h, eval_constCircuit]

@[simp] private theorem prior_gates (W r nodes start stop : Nat) (value : Bool) :
    (prior W r nodes start stop value).gates = 1 := by
  unfold prior
  split_ifs <;> rfl

private def both {q : Nat} (a b : DagCircuit q) : DagCircuit q :=
  substInputs andCircuit ![a, b]

private def guarded {q : Nat} (enabled : Bool) (c : DagCircuit q) : DagCircuit q :=
  both (constCircuit q enabled) c

private def word (W r start : Nat) (pattern : List Bool) : DagCircuit (W + r) :=
  relabelInputs (Fin.castAdd r) (Prefix.wordCircuit W start pattern)

/-- Actual grammar productions; binary right entry is the LEFT return cursor. -/
private def row (n width W r : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (nodes start stop : Nat) (value : Bool) : DagCircuit (W + r) :=
  if nodes = 0 then constCircuit (W + r) false else
  bigOrCircuit (
    [guarded (decide (nodes = 1 ∧ stop = start + 4) && !value)
       (word W r start [false, false, true, false]),
     guarded (decide (nodes = 1 ∧ stop = start + 4) && value)
       (word W r start [false, false, true, true]),
     both (word W r start [false, true, false])
       (prior W r (nodes - 1) (start + 3) stop (!value))] ++
    (List.finRange n).map (fun i =>
      guarded (decide (nodes = 1 ∧ stop = start + 3 + width) && (x i == value))
        (word W r start (encodeCircuit width hw (.input i)))) ++
    [false, true].map (fun isOr =>
      both (word W r start (if isOr then [true, false, false] else [false, true, true]))
        (bigOrCircuit ((List.finRange nodes).flatMap (fun left =>
          (List.finRange (W + 1)).flatMap (fun middle =>
            [false, true].flatMap (fun a => [false, true].map (fun b =>
              guarded ((if isOr then a || b else a && b) == value)
                (both (prior W r left.val (start + 3) middle.val a)
                  (prior W r (nodes - 1 - left.val) middle.val stop b))))))))))

@[simp] private theorem eval_both {q : Nat} (a b : DagCircuit q) (bits : Bitstring q) :
    eval (both a b) bits = (eval a bits && eval b bits) := by simp [both]

@[simp] private theorem eval_guarded {q : Nat} (enabled : Bool) (c : DagCircuit q)
    (bits : Bitstring q) : eval (guarded enabled c) bits = (enabled && eval c bits) := by
  simp [guarded, both]

@[simp] private theorem eval_word (W r start : Nat) (pattern : List Bool)
    (bits : Bitstring W) (values : Bitstring r) :
    eval (word W r start pattern) (Fin.addCases bits values) = true ↔
      Prefix.fits bits start pattern := by
  simpa [word] using Prefix.wordCircuit_iff W start pattern bits

private def Meaning {n W : Nat} (width : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (bits : Bitstring W) (nodes start stop : Nat) (value : Bool) : Prop :=
  ∃ c : Pnp3.Models.Circuit n, Parsed width hw bits start stop c ∧
    c.size = nodes ∧ c.eval x = value

private theorem row_sound (n width W r : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (bits : Bitstring W) (values : Bitstring r)
    (nodes start stop : Nat) (value : Bool)
    (hp : ∀ m a b v,
      eval (prior W r m a b v) (Fin.addCases bits values) = true →
        Meaning width hw x bits m a b v)
    (h : eval (row n width W r hw x nodes start stop value)
      (Fin.addCases bits values) = true) : Meaning width hw x bits nodes start stop value := by
  by_cases hz : nodes = 0
  · simp [row, hz] at h
  simp [row, hz, List.any_eq_true] at h
  rcases h with h | h | h | h | h | h
  · rcases h with ⟨⟨⟨rfl, rfl⟩, rfl⟩, hf⟩
    exact ⟨.const false, Parsed.const start false hf, rfl, rfl⟩
  · rcases h with ⟨⟨⟨rfl, rfl⟩, rfl⟩, hf⟩
    exact ⟨.const true, Parsed.const start true hf, rfl, rfl⟩
  · rcases h with ⟨hf, hchild⟩
    obtain ⟨c, hc, hs, hv⟩ := hp _ _ _ _ hchild
    refine ⟨.not c, Parsed.not start stop c hf hc, ?_, ?_⟩
    · change c.size + 1 = nodes
      omega
    · change (!(c.eval x)) = value
      rw [hv]
      simp
  · rcases h with ⟨i, ⟨⟨rfl, rfl⟩, hv⟩, hf⟩
    exact ⟨.input i, Parsed.input start i hf, rfl, hv⟩
  · rcases h with ⟨hf, i, middle, cases⟩
    rcases cases with ⟨hv, hl, hr⟩ | ⟨hv, hl, hr⟩ | ⟨hv, hl, hr⟩ | ⟨hv, hl, hr⟩
    all_goals
      obtain ⟨c, hc, hs, hcv⟩ := hp _ _ _ _ hl
      obtain ⟨d, hd, ht, hdv⟩ := hp _ _ _ _ hr
      refine ⟨.and c d, Parsed.and start middle.val stop c d hf hc hd, ?_, ?_⟩
      · change c.size + d.size + 1 = nodes
        have hi := i.isLt
        omega
      · change (c.eval x && d.eval x) = value
        simpa only [hcv, hdv] using hv.symm
  · rcases h with ⟨hf, i, middle, cases⟩
    rcases cases with ⟨hv, hl, hr⟩ | ⟨hv, hl, hr⟩ | ⟨hv, hl, hr⟩ | ⟨hv, hl, hr⟩
    all_goals
      obtain ⟨c, hc, hs, hcv⟩ := hp _ _ _ _ hl
      obtain ⟨d, hd, ht, hdv⟩ := hp _ _ _ _ hr
      refine ⟨.or c d, Parsed.or start middle.val stop c d hf hc hd, ?_, ?_⟩
      · change c.size + d.size + 1 = nodes
        have hi := i.isLt
        omega
      · change (c.eval x || d.eval x) = value
        simpa only [hcv, hdv] using hv.symm

private theorem row_complete (n width W r : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (bits : Bitstring W) (values : Bitstring r)
    (nodes start stop : Nat) (value : Bool)
    (hp : ∀ m a b v, m < nodes → Meaning width hw x bits m a b v →
      eval (prior W r m a b v) (Fin.addCases bits values) = true)
    (h : Meaning width hw x bits nodes start stop value) :
    eval (row n width W r hw x nodes start stop value) (Fin.addCases bits values) = true := by
  obtain ⟨c, hparsed, rfl, rfl⟩ := h
  cases hparsed with
  | const a b hf => cases b <;> simp [row, hf, Pnp3.Models.Circuit.size, Pnp3.Models.Circuit.eval]
  | input a i hf =>
    simp [row, Pnp3.Models.Circuit.size, Pnp3.Models.Circuit.eval, List.any_eq_true]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl, hf⟩)))
  | not a z c hf child =>
    have hc := hp c.size (start + 3) stop (c.eval x) (by simp [Pnp3.Models.Circuit.size])
      ⟨c, child, rfl, rfl⟩
    have hcs : c.size ≠ 0 := by
      have hh : 1 ≤ c.size := by cases c <;> simp only [Pnp3.Models.Circuit.size] <;> omega
      omega
    simp [row, Pnp3.Models.Circuit.size, Pnp3.Models.Circuit.eval, hcs, List.any_eq_true]
    exact Or.inl ⟨hf, hc⟩
  | and a middle z c d hf left right =>
    have hl := hp c.size (start + 3) middle (c.eval x)
      (by change c.size < c.size + d.size + 1; omega) ⟨c, left, rfl, rfl⟩
    have hr := hp d.size middle stop (d.eval x)
      (by change d.size < c.size + d.size + 1; omega) ⟨d, right, rfl, rfl⟩
    have hcs : c.size ≠ 0 := by
      have hh : 1 ≤ c.size := by cases c <;> simp only [Pnp3.Models.Circuit.size] <;> omega
      omega
    have hds : d.size ≠ 0 := by
      have hh : 1 ≤ d.size := by cases d <;> simp only [Pnp3.Models.Circuit.size] <;> omega
      omega
    simp [row, Pnp3.Models.Circuit.size, Pnp3.Models.Circuit.eval, hcs, hds, List.any_eq_true]
    refine Or.inr (Or.inl ⟨hf, ⟨c.size, by omega⟩,
      ⟨middle, by have hb := left.bounds; omega⟩, ?_⟩)
    simp only [Nat.add_sub_cancel_left]
    cases ha : c.eval x <;> cases hb : d.eval x <;> simp_all
  | or a middle z c d hf left right =>
    have hl := hp c.size (start + 3) middle (c.eval x)
      (by change c.size < c.size + d.size + 1; omega) ⟨c, left, rfl, rfl⟩
    have hr := hp d.size middle stop (d.eval x)
      (by change d.size < c.size + d.size + 1; omega) ⟨d, right, rfl, rfl⟩
    have hcs : c.size ≠ 0 := by
      have hh : 1 ≤ c.size := by cases c <;> simp only [Pnp3.Models.Circuit.size] <;> omega
      omega
    have hds : d.size ≠ 0 := by
      have hh : 1 ≤ d.size := by cases d <;> simp only [Pnp3.Models.Circuit.size] <;> omega
      omega
    simp [row, Pnp3.Models.Circuit.size, Pnp3.Models.Circuit.eval, hcs, hds, List.any_eq_true]
    refine Or.inr (Or.inr ⟨hf, ⟨c.size, by omega⟩,
      ⟨middle, by have hb := left.bounds; omega⟩, ?_⟩)
    simp only [Nat.add_sub_cancel_left]
    cases ha : c.eval x <;> cases hb : d.eval x <;> simp_all
@[simp] private theorem both_gates {q : Nat} (a b : DagCircuit q) :
    (both a b).gates = a.gates + b.gates + 1 := by
  have h : size (both a b) = a.gates + b.gates + 2 := by
    simp [both, size_substInputs, bundleOfFamily_gates]
  change (both a b).gates + 1 = _ at h
  omega

@[simp] private theorem guarded_gates {q : Nat} (enabled : Bool) (c : DagCircuit q) :
    (guarded enabled c).gates = c.gates + 2 := by
  simp [guarded, constCircuit, Nat.add_comm]
  omega

@[simp] private theorem word_gates (W r start : Nat) (pattern : List Bool) :
    (word W r start pattern).gates = 2 * pattern.length + 2 :=
  Prefix.wordCircuit_gates W start pattern

@[simp] private theorem input_word_length (n width : Nat) (hw : n ≤ 2 ^ width) (i : Fin n) :
    (encodeCircuit width hw (.input i)).length = 3 + width := by
  simp only [encodeCircuit, toTree, Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeCircuitTree,
    List.length_append, List.length_cons, List.length_nil,
    Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeFin_length]

private theorem sum_flatMap_nat {α : Type} (xs : List α) (f : α → List Nat) :
    (xs.flatMap f).sum = (xs.map (fun a => (f a).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.flatMap_cons, ih]

private theorem row_gates_le (n width W r : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (nodes start stop : Nat) (value : Bool) :
    (row n width W r hw x nodes start stop value).gates ≤
      60 + n * (2 * width + 11) + 48 * nodes * (W + 1) := by
  by_cases hz : nodes = 0
  · simp [row, hz, constCircuit]
    omega
  simp [row, hz, bigOrCircuit_gates, List.map_map, Function.comp_def,
    List.map_flatMap, sum_flatMap_nat]
  ring_nf
  omega

/-- Mixed-radix coordinates of the next physical register, ordered by node count. -/
private def step (n width W : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (r : Nat) : DagCircuit (W + r) :=
  row n width W r hw x (r / 2 / (W + 1) / (W + 1))
    ((r / 2 / (W + 1)) % (W + 1))
    ((r / 2) % (W + 1)) (decide (r % 2 = 1))

private theorem step_gates_le (n width W r : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n) :
    (step n width W hw x r).gates ≤ 60 + n * (2 * width + 11) + 48 * r * (W + 1) := by
  apply (row_gates_le n width W r hw x _ _ _ _).trans
  have hd : r / 2 / (W + 1) / (W + 1) ≤ r :=
    (Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans (Nat.div_le_self _ _))
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (W + 1) (Nat.mul_le_mul_left 48 hd)) _

/-- Every cell graph is appended once; dependencies remain shared wires. -/
private def table (n width W : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n) :
    (r : Nat) → DagBundle W r
  | 0 => emptyBundle W
  | r + 1 => snocBundleSubst (table n width W hw x r) (step n width W hw x r)

private theorem table_gates_succ (n width W : Nat) (hw : n ≤ 2 ^ width)
    (x : Pnp3.Core.BitVec n) (r : Nat) :
    (table n width W hw x (r + 1)).gates =
      (table n width W hw x r).gates + (step n width W hw x r).gates := by
  simp [table]

/-- No semantic premise about a supplied head: every accepted register has an
actual native grammar tree of its indexed size and computed output bit. -/
private theorem table_sound (n width W : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (bits : Bitstring W) (r : Nat) :
    ∀ i : Fin r, (table n width W hw x r).evalOutput i bits = true →
      Meaning width hw x bits (i.val / 2 / (W + 1) / (W + 1))
        ((i.val / 2 / (W + 1)) % (W + 1)) ((i.val / 2) % (W + 1))
        (decide (i.val % 2 = 1)) := by
  induction r with
  | zero => intro i; exact Fin.elim0 i
  | succ r ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro h
      have hs : eval (step n width W hw x r)
          (Fin.addCases bits (fun j => (table n width W hw x r).evalOutput j bits)) = true := by
        change (snocBundleSubst (table n width W hw x r) (step n width W hw x r)).evalOutput
          (Fin.natAdd r (0 : Fin 1)) bits = true at h
        rw [evalOutput_snocBundleSubst_new] at h
        have hf : (fun j => (passthroughBundle (table n width W hw x r)).evalOutput j bits) =
            Fin.addCases bits (fun j => (table n width W hw x r).evalOutput j bits) := by
          funext j
          refine Fin.addCases ?_ ?_ j <;> intro k <;> simp
        rwa [hf] at h
      apply row_sound n width W r hw x bits _ _ _ _ _ ?_ hs
      intro m a b v hre
      by_cases hv : 0 < m ∧ a ≤ W ∧ b ≤ W ∧ cellIndex W m a b v < r
      · have he : (table n width W hw x r).evalOutput ⟨cellIndex W m a b v, hv.2.2.2⟩ bits = true := by
          simpa only [eval_prior, dif_pos hv, Fin.addCases_right] using hre
        have hm := ih ⟨cellIndex W m a b v, hv.2.2.2⟩ he
        obtain ⟨hn, ha, hb, hvv⟩ := cellIndex_coords W m a b v hv.2.1 hv.2.2.1
        simpa only [hn, ha, hb, hvv] using hm
      · simp [eval_prior, hv] at hre
    · intro h
      apply ih j
      change (snocBundleSubst (table n width W hw x r) (step n width W hw x r)).evalOutput
        (Fin.castAdd 1 j) bits = true at h
      simpa only [evalOutput_snocBundleSubst_old] using h

private theorem table_complete (n width W : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (bits : Bitstring W) (r : Nat) :
    ∀ i : Fin r, Meaning width hw x bits (i.val / 2 / (W + 1) / (W + 1))
        ((i.val / 2 / (W + 1)) % (W + 1)) ((i.val / 2) % (W + 1))
        (decide (i.val % 2 = 1)) → (table n width W hw x r).evalOutput i bits = true := by
  induction r with
  | zero => intro i; exact Fin.elim0 i
  | succ r ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro h
      change (snocBundleSubst (table n width W hw x r) (step n width W hw x r)).evalOutput
        (Fin.natAdd r (0 : Fin 1)) bits = true
      rw [evalOutput_snocBundleSubst_new]
      have hf : (fun j => (passthroughBundle (table n width W hw x r)).evalOutput j bits) =
          Fin.addCases bits (fun j => (table n width W hw x r).evalOutput j bits) := by
        funext j
        refine Fin.addCases ?_ ?_ j <;> intro k <;> simp
      rw [hf]
      apply row_complete n width W r hw x bits _ _ _ _ _ ?_ h
      intro m a b v hm hmean
      change m < r / 2 / (W + 1) / (W + 1) at hm
      obtain ⟨c, hc, hs, he⟩ := hmean
      have hb := hc.bounds
      have hp : 0 < m := by
        have hh : 1 ≤ c.size := by cases c <;> simp only [Pnp3.Models.Circuit.size] <;> omega
        omega
      have ha : a ≤ W := by omega
      have hz : b ≤ W := hb.2
      have hidx : cellIndex W m a b v < r := by
        have hl := cellIndex_lower W (r / 2 / (W + 1) / (W + 1))
          ((r / 2 / (W + 1)) % (W + 1)) ((r / 2) % (W + 1)) (decide (r % 2 = 1))
        rw [cellIndex_inverse] at hl
        calc
          cellIndex W m a b v < (m + 1) * layerWidth W := cellIndex_upper W m a b v ha hz
          _ ≤ (r / 2 / (W + 1) / (W + 1)) * layerWidth W :=
            Nat.mul_le_mul_right (layerWidth W) (by omega)
          _ ≤ r := hl
      have hvalid : 0 < m ∧ a ≤ W ∧ b ≤ W ∧ cellIndex W m a b v < r := ⟨hp, ha, hz, hidx⟩
      simp only [eval_prior, dif_pos hvalid, Fin.addCases_right]
      apply ih ⟨cellIndex W m a b v, hidx⟩
      obtain ⟨hn, has, hbs, hvs⟩ := cellIndex_coords W m a b v ha hz
      simpa only [hn, has, hbs, hvs] using
        (show Meaning width hw x bits m a b v from ⟨c, hc, hs, he⟩)
    · intro h
      change (snocBundleSubst (table n width W hw x r) (step n width W hw x r)).evalOutput
        (Fin.castAdd 1 j) bits = true
      rw [evalOutput_snocBundleSubst_old]
      exact ih j h

/-- Closed arbitrary-bit-string semantics for every stored grammar cell. -/
private theorem table_iff (n width W : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (bits : Bitstring W) (r : Nat) (i : Fin r) :
    (table n width W hw x r).evalOutput i bits = true ↔
      ∃ c : Pnp3.Models.Circuit n,
        Parsed width hw bits ((i.val / 2 / (W + 1)) % (W + 1)) ((i.val / 2) % (W + 1)) c ∧
        c.size = i.val / 2 / (W + 1) / (W + 1) ∧ c.eval x = decide (i.val % 2 = 1) :=
  ⟨table_sound n width W hw x bits r i, table_complete n width W hw x bits r i⟩

private theorem parsed_of_word {n W width : Nat} (hw : n ≤ 2 ^ width) (bits : Bitstring W)
    (a : Nat) (c : Pnp3.Models.Circuit n) (h : Prefix.fits bits a (encodeCircuit width hw c)) :
    Parsed width hw bits a (a + (encodeCircuit width hw c).length) c := by
  induction c generalizing a with
  | input i =>
    convert Parsed.input a i h using 1
    simp only [encodeCircuit, toTree, Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeCircuitTree,
      List.length_append, List.length_cons, List.length_nil,
      Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeFin_length]
    omega
  | const b => exact Parsed.const a b h
  | not c ih =>
    change Prefix.fits bits a ([false, true, false] ++ encodeCircuit width hw c) at h
    obtain ⟨ht, hc⟩ := (Prefix.fits_append _ _ _ _).mp h
    have hp := Parsed.not a (a + 3 + (encodeCircuit width hw c).length) c ht
      (ih (a + 3) (by simpa using hc))
    convert hp using 1
    simp only [encodeCircuit, toTree, Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeCircuitTree,
      List.length_append, List.length_cons, List.length_nil]
    omega
  | and c d ihc ihd =>
    change Prefix.fits bits a ([false, true, true] ++
      (encodeCircuit width hw c ++ encodeCircuit width hw d)) at h
    obtain ⟨ht, hc, hd⟩ := (Prefix.fits_append _ _ _ _).mp h |>.imp_right
      ((Prefix.fits_append _ _ _ _).mp)
    have hp := Parsed.and a (a + 3 + (encodeCircuit width hw c).length)
      (a + 3 + (encodeCircuit width hw c).length + (encodeCircuit width hw d).length) c d ht
      (ihc (a + 3) (by simpa using hc))
      (ihd _ (by simpa using hd))
    convert hp using 1
    simp only [encodeCircuit, toTree, Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeCircuitTree,
      List.length_append, List.length_cons, List.length_nil]
    omega
  | or c d ihc ihd =>
    change Prefix.fits bits a ([true, false, false] ++
      (encodeCircuit width hw c ++ encodeCircuit width hw d)) at h
    obtain ⟨ht, hc, hd⟩ := (Prefix.fits_append _ _ _ _).mp h |>.imp_right
      ((Prefix.fits_append _ _ _ _).mp)
    have hp := Parsed.or a (a + 3 + (encodeCircuit width hw c).length)
      (a + 3 + (encodeCircuit width hw c).length + (encodeCircuit width hw d).length) c d ht
      (ihc (a + 3) (by simpa using hc))
      (ihd _ (by simpa using hd))
    convert hp using 1
    simp only [encodeCircuit, toTree, Pnp3.Internal.PsubsetPpoly.TM.Encoding.encodeCircuitTree,
      List.length_append, List.length_cons, List.length_nil]
    omega

/-- Full bounded grammar parser/evaluator DAG, for one specified assignment.
Both evaluation-bit cells share the same memoized state construction. -/
def acceptCircuit (n width W T : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (value : Bool) : DagCircuit W :=
  let R := (T + 1) * layerWidth W
  let outputs : List (DagCircuit R) := (List.finRange (T + 1)).flatMap (fun m =>
    (List.finRange (W + 1)).map (fun z =>
      inputProj ⟨cellIndex W m.val 0 z.val value, lt_of_lt_of_le
        (cellIndex_upper W m.val 0 z.val value (by omega) (by omega))
        (Nat.mul_le_mul_right (layerWidth W) (by omega))⟩))
  substInputsWithBundle (bigOrCircuit outputs) (table n width W hw x R)

theorem acceptCircuit_iff (n width W T : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (value : Bool) (bits : Bitstring W) :
    eval (acceptCircuit n width W T hw x value) bits = true ↔
      ∃ c : Pnp3.Models.Circuit n, c.size ≤ T ∧
        Prefix.fits bits 0 (encodeCircuit width hw c) ∧ c.eval x = value := by
  simp only [acceptCircuit, eval_substInputsWithBundle, eval_bigOrCircuit]
  simp only [List.any_flatMap, List.any_map]
  simp only [List.any_eq_true, List.mem_finRange, true_and]
  constructor
  · rintro ⟨m, z, h⟩
    have hm := table_sound n width W hw x bits ((T + 1) * layerWidth W) _ h
    obtain ⟨hn, ha, hb, hv⟩ := cellIndex_coords W m.val 0 z.val value (by omega) (by omega)
    simp only [hn, ha, hb, hv] at hm
    obtain ⟨c, hc, hs, he⟩ := hm
    exact ⟨c, by omega, hc.native_word.1, he⟩
  · rintro ⟨c, hs, hf, hv⟩
    have hp := parsed_of_word hw bits 0 c hf
    have hb := hp.bounds
    refine ⟨⟨c.size, by omega⟩, ⟨(encodeCircuit width hw c).length, by omega⟩, ?_⟩
    apply table_complete n width W hw x bits ((T + 1) * layerWidth W)
    obtain ⟨hn, ha, hz, hvv⟩ := cellIndex_coords W c.size 0 (encodeCircuit width hw c).length
      value (by omega) (by omega)
    simpa only [hn, ha, hz, hvv, Nat.zero_add] using
      (show Meaning width hw x bits c.size 0 (encodeCircuit width hw c).length value from
        ⟨c, by simpa only [Nat.zero_add] using hp, rfl, hv⟩)

/-- All appended registers share their predecessors; no dependency is recopied. -/
private theorem table_gates_le (n width W r : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n) :
    (table n width W hw x r).gates ≤
      r * (60 + n * (2 * width + 11) + 48 * r * (W + 1)) := by
  induction r with
  | zero => simp [table, emptyBundle]
  | succ r ih =>
    rw [table_gates_succ]
    have hm : 60 + n * (2 * width + 11) + 48 * r * (W + 1) ≤
        60 + n * (2 * width + 11) + 48 * (r + 1) * (W + 1) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ r))) _
    calc
      _ ≤ r * (60 + n * (2 * width + 11) + 48 * r * (W + 1)) +
          (60 + n * (2 * width + 11) + 48 * r * (W + 1)) := Nat.add_le_add ih (step_gates_le ..)
      _ ≤ r * (60 + n * (2 * width + 11) + 48 * (r + 1) * (W + 1)) +
          (60 + n * (2 * width + 11) + 48 * (r + 1) * (W + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left r hm) hm
      _ = _ := by ring

def gateBudget (n width W T : Nat) : Nat :=
  let r := (T + 1) * layerWidth W
  r * (60 + n * (2 * width + 11) + 48 * r * (W + 1)) + (T + 1) * (W + 1) + 2

theorem acceptCircuit_size (n width W T : Nat) (hw : n ≤ 2 ^ width) (x : Pnp3.Core.BitVec n)
    (value : Bool) : size (acceptCircuit n width W T hw x value) ≤ gateBudget n width W T := by
  have ht := table_gates_le n width W ((T + 1) * layerWidth W) hw x
  unfold acceptCircuit
  rw [size_substInputsWithBundle]
  simp [bigOrCircuit_gates, List.map_flatMap, List.map_map, Function.comp_def,
    inputProj, sum_flatMap_nat, gateBudget]
  omega

/-- The concrete metadata price is polynomial in N=2^n for every fixed k. -/
theorem gateBudget_polynomial (k : Nat) :
    PolyBoundedInTable (fun n => gateBudget n (bitLength n)
      ((bitLength n + 4) * thresholdPoly k n) (thresholdPoly k n)) := by
  have ht := polyBoundedInTable_thresholdPoly k
  have hw := (polyBoundedInTable_bitLength.add (PolyBoundedInTable.const 4)).mul ht
  have hr := (ht.add (PolyBoundedInTable.const 1)).mul
    (((hw.add (PolyBoundedInTable.const 1)).pow 2).mul (PolyBoundedInTable.const 2))
  have hb := (PolyBoundedInTable.const 60).add
    (polyBoundedInTable_id.mul (((PolyBoundedInTable.const 2).mul polyBoundedInTable_bitLength).add
      (PolyBoundedInTable.const 11)))
  have hp := (((hr.mul (hb.add (((PolyBoundedInTable.const 48).mul hr).mul
    (hw.add (PolyBoundedInTable.const 1))))).add
    ((ht.add (PolyBoundedInTable.const 1)).mul (hw.add (PolyBoundedInTable.const 1)))).add
    (PolyBoundedInTable.const 2))
  simpa only [gateBudget, layerWidth, pow_two, Nat.mul_assoc] using hp

end Research.SolverToDag.Parser
