import Complexity.Uniform.V1.CircuitEncoding

/-!
# Uniform V1 direct configuration-encoding surface tests

Definition pins and explicit full-proposition wrappers for P1b-1.  Axiom roots
live only in the central `Tests/AxiomsAudit.lean`.
-/

namespace Pnp3.Tests.UniformV1CircuitEncoding

open Pnp3.Complexity.Uniform.V1.Circuit
open Pnp3.Complexity.Uniform.V1
open Pnp3.ComplexityInterfaces.DagCircuit

#check symbolPresent
#check symbolValue
#check decodeSymbol
#check symbolRails_injective
#check symbolRails_cases
#check configIndex_layout
#check configWidth
#check stateIndex
#check headIndex
#check tapePresentIndex
#check tapeValueIndex
#check encodeConfig
#check encodeConfig_state_unique
#check Spec_tape_not_malformed
#check EncodedConfig
#check Spec
#check DagBundle.mk
#check initialBundle_spec
#check initialBundle
#check initialBundle_blank_distinction

#synth DecidableEq (Option Bool)

theorem check_symbolRails_cases :
    (symbolPresent none, symbolValue none) = (false, false) ∧
    (symbolPresent (some false), symbolValue (some false)) = (true, false) ∧
    (symbolPresent (some true), symbolValue (some true)) = (true, true) :=
  symbolRails_cases

theorem check_decodeSymbol_roundtrip (symbol : Option Bool) :
    decodeSymbol (symbolPresent symbol) (symbolValue symbol) = symbol :=
  decodeSymbol_roundtrip symbol

theorem check_symbolRails_injective :
    Function.Injective (fun symbol => (symbolPresent symbol, symbolValue symbol)) :=
  symbolRails_injective

theorem check_symbolRails_not_malformed (symbol : Option Bool) :
    ¬ (symbolPresent symbol = false ∧ symbolValue symbol = true) :=
  symbolRails_not_malformed symbol

theorem check_configIndex_layout (M : UniformTM) (n budget : Nat)
    (q : Fin M.stateCount) (i : Fin (tapeLength n budget)) :
    (stateIndex M n budget q).val = q.val ∧
    (headIndex M n budget i).val = M.stateCount + i.val ∧
    (tapePresentIndex M n budget i).val =
      M.stateCount + tapeLength n budget + i.val ∧
    (tapeValueIndex M n budget i).val =
      M.stateCount + 2 * tapeLength n budget + i.val :=
  configIndex_layout M n budget q i

theorem check_configIndex_ranges (M : UniformTM) (n budget : Nat)
    (q : Fin M.stateCount) (i : Fin (tapeLength n budget)) :
    (stateIndex M n budget q).val < M.stateCount ∧
    (M.stateCount ≤ (headIndex M n budget i).val ∧
      (headIndex M n budget i).val < M.stateCount + tapeLength n budget) ∧
    (M.stateCount + tapeLength n budget ≤
        (tapePresentIndex M n budget i).val ∧
      (tapePresentIndex M n budget i).val <
        M.stateCount + 2 * tapeLength n budget) ∧
    (M.stateCount + 2 * tapeLength n budget ≤
        (tapeValueIndex M n budget i).val ∧
      (tapeValueIndex M n budget i).val < configWidth M n budget) :=
  configIndex_ranges M n budget q i

theorem check_configIndex_injective (M : UniformTM) (n budget : Nat) :
    Function.Injective (stateIndex M n budget) ∧
    Function.Injective (headIndex M n budget) ∧
    Function.Injective (tapePresentIndex M n budget) ∧
    Function.Injective (tapeValueIndex M n budget) :=
  configIndex_injective M n budget

theorem check_configIndex_disjoint (M : UniformTM) (n budget : Nat)
    (q : Fin M.stateCount) (i j : Fin (tapeLength n budget)) :
    stateIndex M n budget q ≠ headIndex M n budget i ∧
    stateIndex M n budget q ≠ tapePresentIndex M n budget i ∧
    stateIndex M n budget q ≠ tapeValueIndex M n budget i ∧
    headIndex M n budget i ≠ tapePresentIndex M n budget j ∧
    headIndex M n budget i ≠ tapeValueIndex M n budget j ∧
    tapePresentIndex M n budget i ≠ tapeValueIndex M n budget j :=
  configIndex_disjoint M n budget q i j

theorem check_encodeConfig_state (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (q : Fin M.stateCount) :
    encodeConfig M c (stateIndex M n budget q) = decide (q = c.state) :=
  encodeConfig_state M c q

theorem check_encodeConfig_head (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    encodeConfig M c (headIndex M n budget i) = decide (i = c.head) :=
  encodeConfig_head M c i

theorem check_encodeConfig_tapePresent (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    encodeConfig M c (tapePresentIndex M n budget i) =
      symbolPresent (c.tape i) :=
  encodeConfig_tapePresent M c i

theorem check_encodeConfig_tapeValue (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    encodeConfig M c (tapeValueIndex M n budget i) =
      symbolValue (c.tape i) :=
  encodeConfig_tapeValue M c i

theorem check_encodeConfig_tape_decode (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    decodeSymbol
      (encodeConfig M c (tapePresentIndex M n budget i))
      (encodeConfig M c (tapeValueIndex M n budget i)) = c.tape i :=
  encodeConfig_tape_decode M c i

theorem check_encodeConfig_state_unique (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    ∃! q : Fin M.stateCount,
      encodeConfig M c (stateIndex M n budget q) = true :=
  encodeConfig_state_unique M c

theorem check_encodeConfig_head_unique (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    ∃! i : Fin (tapeLength n budget),
      encodeConfig M c (headIndex M n budget i) = true :=
  encodeConfig_head_unique M c

theorem check_Spec_tape_decode {M : UniformTM} {n budget : Nat}
    {B : EncodedConfig M n budget}
    {f : Bitstring n → Config M.stateCount n budget} (h : Spec B f)
    (x : Bitstring n) (i : Fin (tapeLength n budget)) :
    decodeSymbol
      (B.evalOutput (tapePresentIndex M n budget i) x)
      (B.evalOutput (tapeValueIndex M n budget i) x) = (f x).tape i :=
  Spec_tape_decode h x i

theorem check_Spec_tape_not_malformed {M : UniformTM} {n budget : Nat}
    {B : EncodedConfig M n budget}
    {f : Bitstring n → Config M.stateCount n budget} (h : Spec B f)
    (x : Bitstring n) (i : Fin (tapeLength n budget)) :
    ¬ (B.evalOutput (tapePresentIndex M n budget i) x = false ∧
      B.evalOutput (tapeValueIndex M n budget i) x = true) :=
  Spec_tape_not_malformed h x i

theorem check_initialBundle_gates (M : UniformTM) (n budget : Nat) :
    (initialBundle M n budget).gates = 2 :=
  initialBundle_gates M n budget

theorem check_initialBundle_spec (M : UniformTM) (n budget : Nat) :
    Spec (initialBundle M n budget) (fun x => initialConfig M budget x) :=
  initialBundle_spec M n budget

theorem check_initialBundle_asCircuit_size (M : UniformTM) (n budget : Nat)
    (o : Fin (configWidth M n budget)) :
    size ((initialBundle M n budget).asCircuit o) =
      (initialBundle M n budget).gates + 1 :=
  initialBundle_asCircuit_size M n budget o

theorem check_initialBundle_output_size (M : UniformTM) (n budget : Nat)
    (o : Fin (configWidth M n budget)) :
    size ((initialBundle M n budget).asCircuit o) = 3 :=
  initialBundle_output_size M n budget o

theorem check_initialBundle_blank_distinction (M : UniformTM) :
    let x : Bitstring 1 := fun _ => false
    let cell0 : Fin (tapeLength 1 0) := ⟨0, by simp [tapeLength]⟩
    let cell1 : Fin (tapeLength 1 0) := ⟨1, by simp [tapeLength]⟩
    (initialBundle M 1 0).evalOutput (stateIndex M 1 0 M.start) x = true ∧
    (initialBundle M 1 0).evalOutput (headIndex M 1 0 cell0) x = true ∧
    (initialBundle M 1 0).evalOutput (tapePresentIndex M 1 0 cell0) x = true ∧
    (initialBundle M 1 0).evalOutput (tapeValueIndex M 1 0 cell0) x = false ∧
    (initialBundle M 1 0).evalOutput (tapePresentIndex M 1 0 cell1) x = false ∧
    (initialBundle M 1 0).evalOutput (tapeValueIndex M 1 0 cell1) x = false :=
  initialBundle_blank_distinction M

end Pnp3.Tests.UniformV1CircuitEncoding
