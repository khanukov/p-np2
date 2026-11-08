import FullBodyClosure.Representation
namespace FullBodyClosure
open Pnp3.Internal.PsubsetPpoly.TM.Encoding
open Pnp4.Frontier Pnp4.Frontier.ContractExpansion
/-- Proof specification of the grammar and shared quota, never an executable machine instruction. -/
private def evalSpec {n : Nat} (beta : Fin n → Bool) (width : Nat) :
    Nat → Nat → List Bool → Option ((Nat × Bool) × List Bool)
  | 0,_,_ => none
  | _+1,0,_ => none
  | _+1,_+1,false::false::false::rest =>
      if rest.length < width then none else
        (decodeFin width (rest.take width)).bind (fun i=>
          if h : i.val < n then some ((1,beta ⟨i.val,h⟩),rest.drop width) else none)
  | _+1,_+1,false::false::true::b::rest => some ((1,b),rest)
  | d+1,q+1,false::true::false::rest =>
      (evalSpec beta width d q rest).bind (fun p=>some ((p.1.1+1,!p.1.2),p.2))
  | d+1,q+1,false::true::true::rest =>
      (evalSpec beta width d q rest).bind (fun p=>
        (evalSpec beta width d (q-p.1.1) p.2).bind (fun p'=>
          some ((p.1.1+p'.1.1+1,p.1.2 && p'.1.2),p'.2)))
  | d+1,q+1,true::false::false::rest =>
      (evalSpec beta width d q rest).bind (fun p=>
        (evalSpec beta width d (q-p.1.1) p.2).bind (fun p'=>
          some ((p.1.1+p'.1.1+1,p.1.2 || p'.1.2),p'.2)))
  | _+1,_+1,_ => none
private def capTree {n : Nat} (beta : Fin n → Bool) (q : Nat) :
    Option (CircuitTree n × List Bool) → Option ((Nat × Bool) × List Bool)
  | none => none
  | some (c,tail) => if c.size≤q then some ((c.size,Pnp3.Models.Circuit.eval (fromTree c) beta),tail) else none
private theorem tree_size_pos {n : Nat} (c : CircuitTree n) : 0<c.size := by
  cases c <;> simp only [CircuitTree.size] <;> omega
private theorem capTree_zero {n : Nat} (beta : Fin n → Bool) (x : Option (CircuitTree n × List Bool)) :
    capTree beta 0 x=none := by
  cases x with
  | none => rfl
  | some p =>
    rcases p with ⟨c,tail⟩
    have no : ¬c.size≤0 := by have :=tree_size_pos c;omega
    exact if_neg no
private theorem fromTree_size {n : Nat} (c : CircuitTree n) : (fromTree c).size=c.size := by
  rw [←size_toTree (fromTree c),toTree_fromTree]
private theorem capTree_not {n : Nat} (beta : Fin n → Bool) (q : Nat)
    (x : Option (CircuitTree n × List Bool)) :
    capTree beta (q+1) (x.map (fun p=>(CircuitTree.not p.1,p.2)))=
      (capTree beta q x).bind (fun p=>some ((p.1.1+1,!p.1.2),p.2)) := by
  cases x with
  | none => rfl
  | some p =>
    rcases p with ⟨c,tail⟩
    by_cases fit : c.size≤q
    · have fit' : c.size+1≤q+1 := by omega
      simp only [capTree,Option.map_some,CircuitTree.size,fit,fit',↓reduceIte,Option.bind_some,
        fromTree,Pnp3.Models.Circuit.eval]
    · have fit' : ¬c.size+1≤q+1 := by omega
      simp only [capTree,Option.map_some,CircuitTree.size,fit,fit',↓reduceIte,Option.bind_none]
private theorem capTree_binary {n : Nat} (beta : Fin n → Bool) (q : Nat) (isOr : Bool)
    (x : Option (CircuitTree n × List Bool))
    (next : List Bool → Option (CircuitTree n × List Bool)) :
    capTree beta (q+1) (x.bind (fun p=>(next p.2).map (fun p'=>
      ((if isOr then CircuitTree.or p.1 p'.1 else CircuitTree.and p.1 p'.1),p'.2))))=
      (capTree beta q x).bind (fun p=>(capTree beta (q-p.1.1) (next p.2)).bind (fun p'=>
        some ((p.1.1+p'.1.1+1,if isOr then p.1.2 || p'.1.2 else p.1.2 && p'.1.2),p'.2))) := by
  cases x with
  | none => rfl
  | some p =>
    rcases p with ⟨a,tail⟩
    cases hn : next tail with
    | none =>
      by_cases fit : a.size≤q
      · simp only [Option.bind_some,hn,Option.map_none,capTree,if_pos fit,Option.bind_none]
      · simp only [Option.bind_some,hn,Option.map_none,capTree,if_neg fit,Option.bind_none]
    | some p =>
      rcases p with ⟨b,tail'⟩
      let C:=if isOr then CircuitTree.or a b else CircuitTree.and a b
      have sz : C.size=a.size+b.size+1 := by dsimp only [C];cases isOr <;> rfl
      have ev : Pnp3.Models.Circuit.eval (fromTree C) beta=
        if isOr then Pnp3.Models.Circuit.eval (fromTree a) beta || Pnp3.Models.Circuit.eval (fromTree b) beta
        else Pnp3.Models.Circuit.eval (fromTree a) beta && Pnp3.Models.Circuit.eval (fromTree b) beta := by
        dsimp only [C];cases isOr <;> rfl
      rw [Option.bind_some,hn,Option.map_some]
      change (if C.size≤q+1 then some ((C.size,Pnp3.Models.Circuit.eval (fromTree C) beta),tail') else none)=_
      rw [sz,ev]
      by_cases ha : a.size≤q
      · by_cases hb : b.size≤q-a.size
        · have total : a.size+b.size+1≤q+1 := by omega
          rw [if_pos total]
          change _=(if a.size≤q then some ((a.size,Pnp3.Models.Circuit.eval (fromTree a) beta),tail) else none).bind _
          rw [if_pos ha,Option.bind_some]
          dsimp only
          rw [hn]
          change _=(if b.size≤q-a.size then some ((b.size,Pnp3.Models.Circuit.eval (fromTree b) beta),tail') else none).bind _
          rw [if_pos hb,Option.bind_some]
        · have total : ¬a.size+b.size+1≤q+1 := by omega
          rw [if_neg total]
          change _=(if a.size≤q then some ((a.size,Pnp3.Models.Circuit.eval (fromTree a) beta),tail) else none).bind _
          rw [if_pos ha,Option.bind_some]
          dsimp only
          rw [hn]
          change _=(if b.size≤q-a.size then some ((b.size,Pnp3.Models.Circuit.eval (fromTree b) beta),tail') else none).bind _
          rw [if_neg hb,Option.bind_none]
      · have total : ¬a.size+b.size+1≤q+1 := by omega
        rw [if_neg total]
        change _=(if a.size≤q then some ((a.size,Pnp3.Models.Circuit.eval (fromTree a) beta),tail) else none).bind _
        rw [if_neg ha,Option.bind_none]
private theorem evalSpec_eq {n : Nat} (beta : Fin n → Bool) (width : Nat) :
    ∀ fuel q bits,evalSpec beta width fuel q bits=
      capTree beta q (decodeCircuitTreeAtDepth n width fuel bits) := by
  intro fuel
  induction fuel with
  | zero => intro q bits;rfl
  | succ fuel ih =>
    intro q bits
    cases q with
    | zero => rw [evalSpec,capTree_zero]
    | succ q =>
      cases bits with
      | nil => rfl
      | cons b0 bits =>
        cases bits with
        | nil => cases b0 <;> rfl
        | cons b1 bits =>
          cases bits with
          | nil => cases b0 <;> cases b1 <;> rfl
          | cons b2 rest =>
            cases b0 <;> cases b1 <;> cases b2
            · simp only [evalSpec,decodeCircuitTreeAtDepth]
              by_cases short : rest.length < width
              · simp only [short,↓reduceIte,↓reduceDIte,capTree]
              · simp only [short,↓reduceIte,↓reduceDIte]
                cases decoded : decodeFin width (rest.take width) with
                | none => rfl
                | some index =>
                  by_cases inside : index.val < n
                  · simp only [Option.bind_some,inside,↓reduceDIte,capTree,CircuitTree.size,fromTree,
                      Pnp3.Models.Circuit.eval,show 1≤q+1 by omega,↓reduceIte]
                  · simp only [Option.bind_some,inside,↓reduceDIte,capTree]
            · cases rest with
              | nil => rfl
              | cons b tail =>
                simp only [evalSpec,decodeCircuitTreeAtDepth,capTree,CircuitTree.size,fromTree,
                  Pnp3.Models.Circuit.eval,show 1≤q+1 by omega,↓reduceIte]
            · simp only [evalSpec,decodeCircuitTreeAtDepth,ih]
              cases h : decodeCircuitTreeAtDepth n width fuel rest with
              | none => rfl
              | some p =>
                rcases p with ⟨c,tail⟩
                exact (capTree_not beta q (some (c,tail))).symm
            · simp only [evalSpec,decodeCircuitTreeAtDepth,ih]
              cases h : decodeCircuitTreeAtDepth n width fuel rest with
              | none => rfl
              | some p =>
                rcases p with ⟨c,tail⟩
                cases hn : decodeCircuitTreeAtDepth n width fuel tail with
                | none =>
                  have law:=capTree_binary beta q false (some (c,tail)) (decodeCircuitTreeAtDepth n width fuel)
                  simpa only [Option.bind_some,hn,Option.map_none,Bool.false_eq_true,↓reduceIte] using law.symm
                | some p =>
                  rcases p with ⟨c',tail'⟩
                  have law:=capTree_binary beta q false (some (c,tail)) (decodeCircuitTreeAtDepth n width fuel)
                  simpa only [Option.bind_some,hn,Option.map_some,Bool.false_eq_true,↓reduceIte] using law.symm
            · simp only [evalSpec,decodeCircuitTreeAtDepth,ih]
              cases h : decodeCircuitTreeAtDepth n width fuel rest with
              | none => rfl
              | some p =>
                rcases p with ⟨c,tail⟩
                cases hn : decodeCircuitTreeAtDepth n width fuel tail with
                | none =>
                  have law:=capTree_binary beta q true (some (c,tail)) (decodeCircuitTreeAtDepth n width fuel)
                  simpa only [Option.bind_some,hn,Option.map_none,↓reduceIte] using law.symm
                | some p =>
                  rcases p with ⟨c',tail'⟩
                  have law:=capTree_binary beta q true (some (c,tail)) (decodeCircuitTreeAtDepth n width fuel)
                  simpa only [Option.bind_some,hn,Option.map_some,↓reduceIte] using law.symm
            · rfl
            · rfl
            · rfl
private theorem evalSpec_full {n : Nat} (beta : Fin n → Bool) (bits : List Bool) (g : Nat) :
    evalSpec beta (bitLength n) bits.length g bits=
      (decodeCircuitFull n (bitLength n) bits).bind (fun p=>
          if p.1.size≤g then some ((p.1.size,Pnp3.Models.Circuit.eval p.1 beta),p.2) else none) := by
  rw [evalSpec_eq]
  unfold decodeCircuitFull decodeCircuit
  cases decoded : decodeCircuitTreeAtDepth n (bitLength n) bits.length bits with
  | none => rfl
  | some p =>
    rcases p with ⟨c,tail⟩
    simp only [Option.map_some,Option.bind_some,capTree,fromTree_size]
end FullBodyClosure
