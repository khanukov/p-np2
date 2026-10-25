import CertificateGuardClosure.Semantic
namespace CertificateGuardClosure
open Pnp3.Complexity.Uniform.V1
private def q (o : Bool) (p : Fin 32) : Fin 67 :=
  ⟨(if o then 32 else 0)+p.val, by split <;> omega⟩
private def qa : Fin 67 := ⟨65,by decide⟩
private def qr : Fin 67 := ⟨66,by decide⟩
/-- A fixed source-restoring unary length comparator. The saved origin bit and
one lifted certificate bit are finite-control data, never input indices. -/
private def raw (s : Fin 67) (b : Option Bool) : Fin 67 × Option Bool × Move :=
  if s.val=64 then
    match b with
    | none => (qr,none,.stay)
    | some o => (q o 0,none,.right)
  else if s.val < 64 then
    let o := decide (32 ≤ s.val)
    let go (p : Fin 32) (v : Option Bool) (d : Move) := (q o p,v,d)
    match s.val % 32,b with
    | 0,some v => go 0 (some v) .right
    | 0,none => go 1 none .right
    | 1,none => if o then go 3 (some true) .left else go 2 (some true) .right
    | 2,none => go 3 (some true) .left
    | 3,some v => go 3 (some v) .left
    | 3,none => go 4 none .left
    | 4,some v => go 4 (some v) .left
    | 4,none => go (if o then 10 else 5) none .right
    | 5,some v => go 6 (some v) .right
    | 6,some false => go 7 none .right
    | 6,some true => go 10 (some true) .right
    | 7,some v => go 7 (some v) .right
    | 7,none => go 8 none .right
    | 8,some v => go 8 (some v) .right
    | 8,none => go 9 (some true) .left
    | 9,some v => go 9 (some v) .left
    | 9,none => go 11 none .left
    | 11,some v => go 11 (some v) .left
    | 11,none => go 5 (some false) .right
    | 10,some false => go 12 none .right
    | 10,some true => go 13 none .right
    | 10,none => go 28 none .right
    | 12,some v => go 12 (some v) .right
    | 13,some v => go 13 (some v) .right
    | 12,none => go 14 none .right
    | 13,none => go 15 none .right
    | 14,some false => go 14 (some false) .right
    | 15,some false => go 15 (some false) .right
    | 14,some true => go 16 (some false) .left
    | 15,some true => go 17 (some false) .left
    | 14,none => go 20 none .left
    | 15,none => go 21 none .left
    | 16,some v => go 16 (some v) .left
    | 17,some v => go 17 (some v) .left
    | 16,none => go 18 none .left
    | 17,none => go 19 none .left
    | 18,some v => go 18 (some v) .left
    | 19,some v => go 19 (some v) .left
    | 18,none => go 10 (some false) .right
    | 19,none => go 10 (some true) .right
    | 20,some v => go 20 (some v) .left
    | 21,some v => go 21 (some v) .left
    | 20,none => go 22 none .left
    | 21,none => go 23 none .left
    | 22,some v => go 22 (some v) .left
    | 23,some v => go 23 (some v) .left
    | 22,none => go 24 (some false) .right
    | 23,none => go 24 (some true) .right
    | 24,some v => go 24 (some v) .right
    | 24,none => go 25 none .right
    | 25,some v => go 25 (some v) .right
    | 25,none => go 26 none .left
    | 26,some _ => go 26 none .left
    | 26,none => go 27 none .left
    | 27,some v => go 27 (some v) .left
    | 27,none => (qr,some o,.stay)
    | 28,some false => go 28 (some false) .right
    | 28,some true => go 25 (some true) .right
    | 28,none => go 30 none .left
    | 30,some _ => go 30 none .left
    | 30,none => go 31 none .left
    | 31,some v => go 31 (some v) .left
    | 31,none => (qa,some o,.stay)
    | _,_ => (qr,b,.stay)
  else if s.val=65 then (qa,b,.stay) else (qr,b,.stay)
/-- Sixty-four phase controls, entry, and two literal verdicts; no input data in
its constructor. The caller first runs the verified physical pair parser. -/
def guard : UniformTM where
  stateCount := 67
  start := ⟨64,by decide⟩
  accept := qa
  reject := qr
  accept_ne_reject := by decide
  rawStep := raw
/-- Physical parsing, exact query/certificate comparison, then the complete
sealed all-input ingress. Every component shares the original tape allocation. -/
def machine (k : Nat) : UniformTM :=
  FixedPairParser.machine.seq (guard.seq (TotalIngressClosure.machine k))
/-- Injective inclusion of the entire sealed ingress, including its terminals. -/
def old (k : Nat) (s : Fin (TotalIngressClosure.machine k).stateCount) : Fin (machine k).stateCount :=
  FixedPairParser.machine.seqRight (guard.seq (TotalIngressClosure.machine k))
    (guard.seqRight (TotalIngressClosure.machine k) s)
/-- Full same-allocation state inclusion; tape and head remain literal. -/
def config (k : Nat) {N B : Nat} (c : Config (TotalIngressClosure.machine k).stateCount N B) :
    Config (machine k).stateCount N B :=
  FixedPairParser.machine.seqEmbedRight (guard.seq (TotalIngressClosure.machine k))
    (guard.seqEmbedRight (TotalIngressClosure.machine k) c)
/-- Exact predecessor allocation, unchanged. -/
def allocation (k N : Nat) : Nat := TotalIngressClosure.allocation k N
/-- Local guard plus ingress clock, not a full verifier clock. -/
def deadline (k N : Nat) : Nat := 137438953472*(k+1)*(N+1)^6
end CertificateGuardClosure
