import SerializedBodyCompletion.Case
namespace SerializedBodyCompletion
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open SerializedBody
-- Independent complete proposition annotations: no inferred-type aliases or Target aliases.
theorem abort_cleanup_mirror (D : Nat → Nat) (T : Nat → Option Bool) (S L H Q F c N B P : Nat)
    (source : Fin S → Bool) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) (hH : H < tapeLength N B)
    (ts : T S=none) (tl : T L=none) (th : T H=none) (tf : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b) (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hole : c < S → T c=none) (src : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    let clearedTape : Nat → Option Bool:=fun i=>if D 10 < i ∧ i < D 11 then some true else
      if [1,4,5,6,8,9,11].any (fun j=>decide (D j < i ∧ i < D (j+1))) then some false else T i
    let initial : Config 7500 N B:=⟨SerializedBodyRefinement.getAbort (SerializedBody.sourceMode source c),⟨D 0,h0⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 512*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>if c < S then if i.val=c then
        some (Pnp4.Frontier.ContractExpansion.padRead source c) else clearedTape i.val else clearedTape i.val⟩ ∧
      ∀ u,u < t → 4 ≤ (SerializedBody.machine.run u initial).state.val := abort_cleanup D T S L H Q F c N B P source sl lh positive arena anchor rise mono blank cells room fit h0 hH ts tl th tf reg ass marks gap hole src
#print axioms SerializedBodyCompletion.abort_cleanup
#print axioms SerializedBodyCompletion.abort_cleanup_mirror
theorem zero_quota_native_mirror (D : Nat → Nat) (T : Nat → Option Bool) (S L H Q F c N B P : Nat)
    (source : Fin S → Bool) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (hH : H < tapeLength N B)
    (quota : ∀ i,D 6 < i → i < D 7 → T i=some false)
    (ts : T S=none) (tl : T L=none) (th : T H=none) (tf : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b) (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hole : c < S → T c=none) (src : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    let clearedTape : Nat → Option Bool:=fun i=>if D 10 < i ∧ i < D 11 then some true else
      if [1,4,5,6,8,9,11].any (fun j=>decide (D j < i ∧ i < D (j+1))) then some false else T i
    let initial : Config 7500 N B:=⟨SerializedBody.entry (SerializedBody.sourceMode source c),⟨H,hH⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 1024*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>if c < S then if i.val=c then
        some (Pnp4.Frontier.ContractExpansion.padRead source c) else clearedTape i.val else clearedTape i.val⟩ ∧
      ∀ u,u < t → 4 ≤ (SerializedBody.machine.run u initial).state.val := zero_quota_native D T S L H Q F c N B P source sl lh positive arena anchor rise mono blank cells room fit hH quota ts tl th tf reg ass marks gap hole src
#print axioms SerializedBodyCompletion.zero_quota_native
#print axioms SerializedBodyCompletion.zero_quota_native_mirror
theorem entry_need_mirror (mode : Fin 3) (T : Nat → Option Bool) (H Q F N B P : Nat)
    (positive : 0 < Q) (arena : H+Q < F) (room : F+1 ≤ P) (fit : P < tapeLength N B)
    (hH : H < tapeLength N B) (h0 : F+1 < tapeLength N B) (th : T H=none) (tf : T F=some false)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none) :
    let initial : Config 7500 N B:=⟨SerializedBody.entry mode,⟨H,hH⟩,fun i=>T i.val⟩
    SerializedBody.machine.run (F+2-H) initial=⟨needEntry mode,⟨F+1,h0⟩,fun i=>T i.val⟩ ∧
      ∀ u,u ≤ F+2-H → 4 ≤ (SerializedBody.machine.run u initial).state.val := entry_need mode T H Q F N B P positive arena room fit hH h0 th tf marks gap
#print axioms SerializedBodyCompletion.entry_need
#print axioms SerializedBodyCompletion.entry_need_mirror
theorem need_get_mirror (mode : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool) (r q v N B P : Nat)
    (rise : ∀ j,j < 12 → D j < D (j+1)) (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B)
    (positive : 0 < q) (bound : q+v ≤ r) (len5 : D 6=D 5+r+1) (len6 : D 7=D 6+r+1)
    (quota : ∀ i,D 6 < i → i < D 7 → T i=some (decide (i-D 6 ≤ q)))
    (nodes : ∀ i,D 5 < i → i < D 6 → T i=some (decide (i-D 5 ≤ v))) :
    let ticks:=1+(2*(D 6-D 0+6)+2*q+4)+(2*(D 5-D 0+5)+2*v+4)+1
    let initial : Config 7500 N B:=⟨needEntry mode,⟨D 0,h0⟩,fun i=>T i.val⟩
    ticks ≤ 128*(P+1) ∧ SerializedBody.machine.run ticks initial=
      ⟨SerializedBodyRefinement.getEntry ⟨0,by decide⟩ mode,⟨D 0,h0⟩,
        fun i=>if i.val=D 5+v+1 then some true else if i.val=D 6+q then some false else T i.val⟩ ∧
      ∀ u,u ≤ ticks → 4 ≤ (SerializedBody.machine.run u initial).state.val := need_get mode D T r q v N B P rise mono blank cells room fit h0 positive bound len5 len6 quota nodes
#print axioms SerializedBodyCompletion.need_get
#print axioms SerializedBodyCompletion.need_get_mirror
theorem exhausted_consumer_mirror (site : Fin 9) (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F r used c N B P : Nat) (source : Fin S → Bool)
    (bounded : used ≤ r) (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (len4 : D 5=D 4+r+1) (len11 : D 12=D 11+r+1)
    (remaining : ∀ i,D 4 < i → i < D 5 → T i=some false)
    (consumed : ∀ i,D 11 < i → i < D 12 → T i=some (decide (i-D 11 ≤ used)))
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (h0 : D 0 < tapeLength N B) (hH : H < tapeLength N B)
    (ts : T S=none) (tl : T L=none) (th : T H=none) (tf : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b) (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (hole : c < S → T c=none) (src : ∀ i,c < i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    let clearedTape : Nat → Option Bool:=fun i=>if D 10 < i ∧ i < D 11 then some true else
      if [1,4,5,6,8,9,11].any (fun j=>decide (D j < i ∧ i < D (j+1))) then some false else T i
    let initial : Config 7500 N B:=⟨SerializedBodyRefinement.getEntry site (SerializedBody.sourceMode source c),⟨D 0,h0⟩,fun i=>T i.val⟩
    ∃ t,t ≤ 1024*(P+1) ∧ SerializedBody.machine.run t initial=
      ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>if c < S then if i.val=c then
        some (Pnp4.Frontier.ContractExpansion.padRead source c) else clearedTape i.val else clearedTape i.val⟩ ∧
      ∀ u,u < t → 4 ≤ (SerializedBody.machine.run u initial).state.val := exhausted_consumer site D T S L H Q F r used c N B P source bounded sl lh positive arena anchor rise mono blank cells len4 len11 remaining consumed room fit h0 hH ts tl th tf reg ass marks gap hole src
#print axioms SerializedBodyCompletion.exhausted_consumer
#print axioms SerializedBodyCompletion.exhausted_consumer_mirror
theorem zero_quota_body_mirror :
  ∀ (R S z n r W M Q : Nat) (source : Fin S → Bool) (beta : Fin n → Bool)
    (T : Nat → Option Bool),
    r ≤ S → S ≤ R → 0 ≤ r → W ≤ r → bitLength n ≤ r → S-min M S ≤ r →
    let B:=FixedRawLengthFence.allocation R
    let L:=S+z+2; let H:=L+n+1; let F:=FixedRawLengthFence.fencePos R
    0 < Q → H+Q < F →
    (∀ i, M ≤ i → ∀ hi : i < S, T i=some (source ⟨i,hi⟩)) →
    T S=none →
    (∀ i, S < i → i < L → T i=some false) → T L=none →
    (∀ j : Fin n, T (H-1-j.val)=some (beta j)) → T H=none →
    (∀ i, H < i → i ≤ H+Q → T i=some true) →
    (∀ i, H+Q < i → i < F → T i=none) → T F=some false →
    ∀ _fit : delimiter F r n 12 < tapeLength R B,
    ∀ hH : H < tapeLength R B,
    let bits:=window source M W
    let initial : Config machine.stateCount R B :=
      ⟨entry (sourceMode source M),⟨H,hH⟩,fun i => prepared T S M F r n 0 W i.val⟩
    let semantics:=do
      let (c,tail) ← decodeCircuitFull n (bitLength n) bits
      if c.size ≤ 0 then some ((c.size,Pnp3.Models.Circuit.eval c beta),tail) else none
    ∃ t, t ≤ 1073741824*(R+1)^6 ∧
      (∀ u, u ≤ t → ((machine.run u initial).state≠machine.accept)) ∧
      (∀ u, u < t → (machine.run u initial).state≠machine.reject ∧
        (machine.run u initial).state≠done false ∧ (machine.run u initial).state≠done true) ∧
      match semantics with
      | none => machine.run t initial=
          ⟨machine.reject,⟨H,hH⟩,fun i => image T F r n 0 W (S-min M S) 0 0 0 0 i.val⟩
      | some ((size,b),tail) => ∃ consumed,
          consumed ≤ W ∧ tail=bits.drop consumed ∧
          machine.run t initial=
            ⟨done b,⟨H,hH⟩,fun i => image T F r n 0 W (S-min M S) size consumed (W-consumed) 0 i.val⟩ := zero_quota_body
#print axioms SerializedBodyCompletion.zero_quota_body
#print axioms SerializedBodyCompletion.zero_quota_body_mirror
theorem zero_window_body_mirror :
  ∀ (R S z n r g M Q : Nat) (source : Fin S → Bool) (beta : Fin n → Bool)
    (T : Nat → Option Bool),
    r ≤ S → S ≤ R → g ≤ r → 0 ≤ r → bitLength n ≤ r → S-min M S ≤ r →
    let B:=FixedRawLengthFence.allocation R
    let L:=S+z+2; let H:=L+n+1; let F:=FixedRawLengthFence.fencePos R
    0 < Q → H+Q < F →
    (∀ i, M ≤ i → ∀ hi : i < S, T i=some (source ⟨i,hi⟩)) →
    T S=none →
    (∀ i, S < i → i < L → T i=some false) → T L=none →
    (∀ j : Fin n, T (H-1-j.val)=some (beta j)) → T H=none →
    (∀ i, H < i → i ≤ H+Q → T i=some true) →
    (∀ i, H+Q < i → i < F → T i=none) → T F=some false →
    ∀ _fit : delimiter F r n 12 < tapeLength R B,
    ∀ hH : H < tapeLength R B,
    let bits:=window source M 0
    let initial : Config machine.stateCount R B :=
      ⟨entry (sourceMode source M),⟨H,hH⟩,fun i => prepared T S M F r n g 0 i.val⟩
    let semantics:=do
      let (c,tail) ← decodeCircuitFull n (bitLength n) bits
      if c.size ≤ g then some ((c.size,Pnp3.Models.Circuit.eval c beta),tail) else none
    ∃ t, t ≤ 1073741824*(R+1)^6 ∧
      (∀ u, u ≤ t → ((machine.run u initial).state≠machine.accept)) ∧
      (∀ u, u < t → (machine.run u initial).state≠machine.reject ∧
        (machine.run u initial).state≠done false ∧ (machine.run u initial).state≠done true) ∧
      match semantics with
      | none => machine.run t initial=
          ⟨machine.reject,⟨H,hH⟩,fun i => image T F r n g 0 (S-min M S) 0 0 0 0 i.val⟩
      | some ((size,b),tail) => ∃ consumed,
          consumed ≤ 0 ∧ tail=bits.drop consumed ∧
          machine.run t initial=
            ⟨done b,⟨H,hH⟩,fun i => image T F r n g 0 (S-min M S) size consumed (0-consumed) 0 i.val⟩ := zero_window_body
#print axioms SerializedBodyCompletion.zero_window_body
#print axioms SerializedBodyCompletion.zero_window_body_mirror
theorem image_equation_mirror (T : Nat → Option Bool)
    (F r n g W anchor nodes consumed remaining quota i : Nat) :
    SerializedBody.image T F r n g W anchor nodes consumed remaining quota i =
      if i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i then T i else
      if (List.range 13).any (fun j=>i==SerializedBody.delimiter F r n j) then none else
      if i < SerializedBody.delimiter F r n 1 then some (decide (i-SerializedBody.delimiter F r n 0 ≤ g)) else
      if i < SerializedBody.delimiter F r n 2 then some false else
      if i < SerializedBody.delimiter F r n 3 then some (decide (i-SerializedBody.delimiter F r n 2 ≤ bitLength n)) else
      if i < SerializedBody.delimiter F r n 4 then some (decide (i-SerializedBody.delimiter F r n 3 ≤ W)) else
      if i < SerializedBody.delimiter F r n 5 then some (decide (i-SerializedBody.delimiter F r n 4 ≤ remaining)) else
      if i < SerializedBody.delimiter F r n 6 then some (decide (i-SerializedBody.delimiter F r n 5 ≤ nodes)) else
      if i < SerializedBody.delimiter F r n 7 then some (decide (i-SerializedBody.delimiter F r n 6 ≤ quota)) else
      if i < SerializedBody.delimiter F r n 8 then some (decide (i-SerializedBody.delimiter F r n 7 ≤ anchor)) else
      if i < SerializedBody.delimiter F r n 10 then some false else
      if i < SerializedBody.delimiter F r n 11 then some true else
      some (decide (i-SerializedBody.delimiter F r n 11 ≤ consumed)) :=
  SerializedBody.image.eq_1 T F r n g W anchor nodes consumed remaining quota i
theorem prepared_equation_mirror (T : Nat → Option Bool) (S M F r n g W i : Nat) :
    SerializedBody.prepared T S M F r n g W i =
      if i=M ∧ i < S then none else SerializedBody.image T F r n g W (S-min M S) 0 0 W g i :=
  SerializedBody.prepared.eq_1 T S M F r n g W i
#print axioms SerializedBody.image.eq_1
#print axioms SerializedBodyCompletion.image_equation_mirror
#print axioms SerializedBody.prepared.eq_1
#print axioms SerializedBodyCompletion.prepared_equation_mirror
end SerializedBodyCompletion

open Lean in
run_cmd do
  let e ← getEnv
  for n in e.header.moduleNames do logInfo m!"current-imported|{n}"
  for (n,ci) in e.constants.toList do
    let owner := match e.getModuleIdxFor? n with
      | some i => e.header.moduleNames[i]!
      | none => e.mainModule
    if owner.toString.startsWith "SerializedBodyCompletion." then
      let s:=n.toString
      let kind:=if s.startsWith "_private." then "private" else if n.isInternal ||
        (s.splitOn ".").any (fun c => "_".isPrefixOf c || "match_".isPrefixOf c)
        then "internal" else "public"
      let ck:=match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiomatic" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor" | .quotInfo _ => "quotient"
      logInfo m!"current-owner|{kind}|{owner}|{n}|{ck}"
      logInfo m!"current-owner-type|{n}|{ci.type}"
      logInfo m!"current-owner-axioms|{n}|{← Lean.collectAxioms n}"
  logInfo m!"registered-option|maxHeartbeats|{Lean.maxHeartbeats.get (← getOptions)}"
  logInfo m!"registered-option|maxRecDepth|{Lean.maxRecDepth.get (← getOptions)}"
