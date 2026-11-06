import Complexity.PrivateInterfaceLookupResolvedFinish
import FullIngressClosure.CounterFront
import FullIngressClosure.SourceScan
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateFinish.bindings `FullIngressClosure.PhysicalFrame
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated finish-frame identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private theorem canonical_corridor (S z n : Nat) (T : Nat → Option Bool) (beta : Fin n → Bool)
    (eof : T S=none) (register : ∀ i,S < i → i < S+z+2 → T i=some false)
    (separator : T (S+z+2)=none) (headBlank : T (S+z+2+n+1)=none)
    (assignment : ∀ j:Fin n,T (S+z+2+n+1-1-j.val)=some (beta j)) :
    Corridor T S (S+z+2) (S+z+2+n+1) := by
  refine corridorMk ⟨by omega,by omega⟩ eof separator headBlank register ?_
  intro i lower upper
  let j : Fin n:=⟨S+z+2+n+1-1-i,by dsimp; omega⟩
  have digit:=assignment j
  have address : S+z+2+n+1-1-j.val=i:=by dsimp only [j]; omega
  rw [address] at digit
  exact ⟨beta j,digit⟩
private theorem six_from_values (F r n : Nat) (T : Nat → Option Bool) (g ell W : Nat)
    (blank : ∀ j,j ≤ 6 → T (SerializedBody.delimiter F r n j)=none)
    (unary : ∀ j,j < 6 → BankUnary (SerializedBody.delimiter F r n) T j (initialValues g ell W j))
    (fresh : ∀ i,SerializedBody.delimiter F r n 6 < i → i ≤ SerializedBody.delimiter F r n 12 → T i=none) :
    Six T F r n := by
  refine sixMk blank ?_ fresh
  intro j i hj il iu
  exact ⟨decide (i-SerializedBody.delimiter F r n j ≤ initialValues g ell W j),unary j hj i il iu⟩
private theorem initial_fields (F r n : Nat) (T : Nat → Option Bool) (g ell W : Nat)
    (bank0 : ∀ i,SerializedBody.delimiter F r n 0 < i → i < SerializedBody.delimiter F r n 1 →
      T i=some (decide (i-SerializedBody.delimiter F r n 0 ≤ g)))
    (bank1 : ∀ i,SerializedBody.delimiter F r n 1 < i → i < SerializedBody.delimiter F r n 2 → T i=some false)
    (bank2 : ∀ i,SerializedBody.delimiter F r n 2 < i → i < SerializedBody.delimiter F r n 3 →
      T i=some (decide (i-SerializedBody.delimiter F r n 2 ≤ ell)))
    (bank34 : ∀ i,SerializedBody.delimiter F r n 3 < i → i < SerializedBody.delimiter F r n 5 →
      i ≠ SerializedBody.delimiter F r n 4 → T i=some false)
    (bank5 : ∀ i,SerializedBody.delimiter F r n 5 < i → i < SerializedBody.delimiter F r n 6 →
      T i=some (decide (i-SerializedBody.delimiter F r n 5 ≤ W))) :
    ∀ j,j < 6 → BankUnary (SerializedBody.delimiter F r n) T j (initialValues g ell W j) := by
  intro j hj i lower upper
  interval_cases j
  · exact bank0 i lower upper
  · change T i=some (decide (i-SerializedBody.delimiter F r n 1 ≤ 0))
    rw [decide_eq_false (by omega)]
    exact bank1 i lower upper
  · exact bank2 i lower upper
  · change i < SerializedBody.delimiter F r n 4 at upper
    change T i=some (decide (i-SerializedBody.delimiter F r n 3 ≤ 0))
    rw [decide_eq_false (by omega)]
    apply bank34 i lower ?_ (by omega)
    have span : SerializedBody.delimiter F r n 4 < SerializedBody.delimiter F r n 5:=by
      dsimp only [SerializedBody.delimiter]; omega
    omega
  · change T i=some (decide (i-SerializedBody.delimiter F r n 4 ≤ 0))
    rw [decide_eq_false (by omega)]
    apply bank34 i ?_ upper (by omega)
    have span : SerializedBody.delimiter F r n 3 < SerializedBody.delimiter F r n 4:=by
      dsimp only [SerializedBody.delimiter]; omega
    omega
  · exact bank5 i lower upper
private structure PhysicalFrame (T : Nat → Option Bool) (S L H F r n Q g ell W : Nat) : Prop where
  six : Six T F r n
  fields : ∀ j,j < 6 → BankUnary (SerializedBody.delimiter F r n) T j (initialValues g ell W j)
  corridor : Corridor T S L H
  arena : Arena T H F Q
end FullIngressClosure
