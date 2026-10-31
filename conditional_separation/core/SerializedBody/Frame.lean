import SerializedBody.Machine
namespace SerializedBody
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
/-- Proof/specification addresses; the machine locates fields by literal scans. -/
def delimiter (F r n j : Nat) : Nat :=
  match j with
  | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
  | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | 6 => F+5*r+n+7
  | 7 => F+6*r+n+8 | 8 => F+7*r+n+9 | 9 => F+7*r+2*n+10
  | 10 => F+9*r+2*n+11 | 11 => F+12*r+2*n+15 | _ => F+13*r+2*n+16
/-- Complete endpoint tape image. All twelve field interiors are occupied;
stack free sentinel is111, never blank. Outside the workspace T is preserved. -/
def image (T : Nat → Option Bool) (F r n g W anchor nodes consumed remaining quota : Nat) : Nat → Option Bool := fun i =>
  if i < (delimiter F r n 0) ∨ (delimiter F r n 12) < i then T i else
  if (List.range 13).any (fun j => i==delimiter F r n j) then none else
  if i<delimiter F r n 1 then some (decide (i-delimiter F r n 0≤g)) else
  if i<delimiter F r n 2 then some false else
  if i<delimiter F r n 3 then some (decide (i-delimiter F r n 2≤bitLength n)) else
  if i<delimiter F r n 4 then some (decide (i-delimiter F r n 3≤W)) else
  if i<delimiter F r n 5 then some (decide (i-delimiter F r n 4≤remaining)) else
  if i<delimiter F r n 6 then some (decide (i-delimiter F r n 5≤nodes)) else
  if i<delimiter F r n 7 then some (decide (i-delimiter F r n 6≤quota)) else
  if i<delimiter F r n 8 then some (decide (i-delimiter F r n 7≤anchor)) else
  if i<delimiter F r n 10 then some false else
  if i<delimiter F r n 11 then some true else
  some (decide (i-delimiter F r n 11≤consumed))
/-- Prepared ABI: actual lifted source bit; EOF has no physical source hole. -/
def prepared (T : Nat → Option Bool) (S M F r n g W : Nat) : Nat → Option Bool := fun i =>
  if i=M ∧ i<S then none else image T F r n g W (S-min M S) 0 0 W g i
/-- Specification of the carried bit/control; never called by rawStep. -/
def sourceMode {S : Nat} (source : Fin S → Bool) (M : Nat) : Fin 3 :=
  if h : M<S then if source ⟨M,h⟩ then ⟨1,by decide⟩ else ⟨0,by decide⟩ else ⟨2,by decide⟩
/-- Logical finite witness window, including virtual false only within W. -/
def window {S : Nat} (source : Fin S → Bool) (M W : Nat) : List Bool :=
  List.ofFn (fun i : Fin W => padRead source (M+i.val))
end SerializedBody
