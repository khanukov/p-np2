import NormalFinalClosure.Target2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
private def D (F r n j : Nat) : Nat :=
  if j ≤ 12 then SerializedBody.delimiter F r n j else SerializedBody.delimiter F r n 12+6
/-- Static tape facts only. No run, future result, AST, validity or correctness
field is present. r is operationally the physical width of bank4. -/
private structure GuardFrame (S z n F r W : Nat) (source : Fin S → Bool)
    (T : Nat → Option Bool) : Prop where
  rSource : r ≤ S
  positive : 0 < W
  windowRoom : W ≤ r
  headBefore : S+z+2+n+1 < F
  sourceCells : ∀ i,S-r ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩)
  eof : T S=none
  registers : ∀ i,S < i → i < S+z+2 → T i=some false
  left : T (S+z+2)=none
  assignment : ∀ i,S+z+2 < i → i < S+z+2+n+1 → ∃ b,T i=some b
  right : T (S+z+2+n+1)=none
  paid : T (S+z+2+n+2)=some true
  gap : ∀ i,S+z+2+n+2 < i → i < F → T i=none
  fence : T F=some false
  delimiters : ∀ j,j ≤ 13 → T (D F r n j)=none
  occupied : ∀ j i,j < 13 → D F r n j < i → i < D F r n (j+1) → ∃ b,T i=some b
  window : ∀ i,D F r n 3 < i → i < D F r n 4 → T i=some (decide (i-D F r n 3 ≤ W))
  freeStack : ∀ i,D F r n 10 < i → i < D F r n 11 → T i=some true
private def PrefixAt {S : Nat} (source : Fin S → Bool) (p W : Nat) : Prop :=
  ∃ i,readNatBE (padWord source (p+bitLength W+W)) p (bitLength W)=some i ∧ i ≤ W ∧
    (∀ j,j < i → padRead source (p+bitLength W+j)=padRead source (p+bitLength W+W+j)) ∧
    (∀ j,i ≤ j → j < W → padRead source (p+bitLength W+j)=false)
/-- Single shared native invariant, at subroutine boundaries. It stores only
proof ghosts for current scalar counters, raw buffer codes and current source
hole. The actual machine constructor receives none of these parameters. -/
private def repImage (T : Nat → Option Bool) (F r n S cursor a b c index : Nat)
    (records : List Nat) : Nat → Option Bool := fun i=>
  if i=cursor ∧ cursor < S then none
  else if D F r n 4 < i ∧ i < D F r n 5 then some (decide (i-D F r n 4 ≤ a))
  else if D F r n 5 < i ∧ i < D F r n 6 then some (decide (i-D F r n 5 ≤ b))
  else if D F r n 6 < i ∧ i < D F r n 7 then some (decide (i-D F r n 6 ≤ c))
  else if D F r n 11 < i ∧ i < D F r n 12 then some (decide (i-D F r n 11 ≤ index))
  else if D F r n 10 < i ∧ i < D F r n 11 then
    let off:=i-D F r n 10-1
    if off/3 < records.length then some (Nat.testBit (records[off/3]!) (2-off%3)) else some true
  else T i
/-- Complete internal physical guard goal. This is an intermediate dependency of
Target2.Raw, never an accepted/raw completion claim on its own. -/
private def GuardBody (k : Nat) : Prop :=
  ∀ (N B S z n F r W : Nat) (source : Fin S → Bool) (T : Nat → Option Bool),
    GuardFrame S z n F r W source T →
    ∀ _fit:D F r n 13 < tapeLength N B,
    ∀ hH:S+z+2+n+1 < tapeLength N B,
    let initial : Config (machine2 k).stateCount N B:=
      ⟨old2 k (RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)),⟨S+z+2+n+1,hH⟩,fun i=>T i.val⟩
    ∃ t, t ≤ 1048576*(r+1)^4*(D F r n 13+1)^2 ∧
      (∀ u,u < t → ((machine2 k).run u initial).state≠(machine2 k).accept ∧
        ((machine2 k).run u initial).state≠(machine2 k).reject) ∧
      (∀ u,u ≤ t → ((machine2 k).run u initial).head.val ≤ D F r n 13 ∧
        ∀ i:Fin (tapeLength N B),D F r n 13 < i.val → ((machine2 k).run u initial).tape i=T i.val) ∧
      ∃ answer : Bool,(answer=true ↔ PrefixAt source (S-r) W) ∧
      (machine2 k).run t initial=
        ⟨if answer then (machine2 k).accept else (machine2 k).reject,⟨S+z+2+n+1,hH⟩,
          Target.cleared (fun i:Fin (tapeLength N B)=>T i.val) F r n⟩
end NormalFinalClosure
