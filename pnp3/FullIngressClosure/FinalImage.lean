import FullIngressClosure.SourceImage
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","put","put"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid","Grid"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Grid.blank","gridBlank"),
      ("SerializedBodyRefinement.Proof","SerializedBodyRefinement","Unary","BankUnary"),
      ("FullIngressClosure.SourceImage","FullIngressClosure","lifted","lifted") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique exact final image proof {mod}/{key}: {found.map Prod.fst}"
private def endpointValues (r n g W anchor j : Nat) : Nat :=
  if j=0 ∨ j=6 then g else if j=2 then bitLength n else if j=3 ∨ j=4 then W
  else if j=7 then anchor else if j=10 then 3*r+3 else 0
private theorem complete_image (F r n g W anchor : Nat) (original current : Nat → Option Bool)
    (grid : Grid (SerializedBody.delimiter F r n) current)
    (values : ∀ j,j < 12 → BankUnary (SerializedBody.delimiter F r n) current j (endpointValues r n g W anchor j))
    (outside : ∀ i,i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i → current i=original i) :
    current=SerializedBody.image original F r n g W anchor 0 0 W g := by
  let D:=SerializedBody.delimiter F r n
  funext i
  dsimp only [SerializedBody.image]
  change current i=(if i < D 0 ∨ D 12 < i then original i else
    if (List.range 13).any (fun j=>i==D j) then none else
    if i < D 1 then some (decide (i-D 0 ≤ g)) else
    if i < D 2 then some false else
    if i < D 3 then some (decide (i-D 2 ≤ bitLength n)) else
    if i < D 4 then some (decide (i-D 3 ≤ W)) else
    if i < D 5 then some (decide (i-D 4 ≤ W)) else
    if i < D 6 then some (decide (i-D 5 ≤ 0)) else
    if i < D 7 then some (decide (i-D 6 ≤ g)) else
    if i < D 8 then some (decide (i-D 7 ≤ anchor)) else
    if i < D 10 then some false else
    if i < D 11 then some true else some (decide (i-D 11 ≤ 0)))
  by_cases ext : i < D 0 ∨ D 12 < i
  · rw [if_pos ext]
    exact outside i ext
  · rw [if_neg ext]
    by_cases delim : ∃ j,j ≤ 12 ∧ i=D j
    · obtain ⟨j,hj,eq⟩:=delim
      have hit : (List.range 13).any (fun j=>i==D j)=true:=by
        apply List.any_eq_true.mpr
        refine ⟨j,List.mem_range.mpr (by omega),?_⟩
        simpa only [beq_iff_eq] using eq
      rw [if_pos hit,eq]
      exact gridBlank grid j hj
    · have ne (j : Nat) (hj : j ≤ 12) : i ≠ D j:=by intro h; exact delim ⟨j,hj,h⟩
      have miss : ¬(List.range 13).any (fun j=>i==D j)=true:=by
        intro h
        obtain ⟨j,hj,eq⟩:=List.any_eq_true.mp h
        have bound : j < 13:=List.mem_range.mp hj
        apply ne j (by omega)
        simpa only [beq_iff_eq] using eq
      rw [if_neg miss]
      have start : D 0 < i:=by have h:=ne 0 (by decide); omega
      have last : i < D 12:=by have h:=ne 12 le_rfl; omega
      by_cases h1 : i < D 1
      · rw [if_pos h1]
        exact values 0 (by decide) i start h1
      · rw [if_neg h1]
        have l1 : D 1 < i:=by have h:=ne 1 (by decide); omega
        by_cases h2 : i < D 2
        · rw [if_pos h2,values 1 (by decide) i l1 h2]
          change some (decide (i-D 1 ≤ 0))=some false
          rw [decide_eq_false (by omega)]
        · rw [if_neg h2]
          have l2 : D 2 < i:=by have h:=ne 2 (by decide); omega
          by_cases h3 : i < D 3
          · rw [if_pos h3]
            exact values 2 (by decide) i l2 h3
          · rw [if_neg h3]
            have l3 : D 3 < i:=by have h:=ne 3 (by decide); omega
            by_cases h4 : i < D 4
            · rw [if_pos h4]
              exact values 3 (by decide) i l3 h4
            · rw [if_neg h4]
              have l4 : D 4 < i:=by have h:=ne 4 (by decide); omega
              by_cases h5 : i < D 5
              · rw [if_pos h5]
                exact values 4 (by decide) i l4 h5
              · rw [if_neg h5]
                have l5 : D 5 < i:=by have h:=ne 5 (by decide); omega
                by_cases h6 : i < D 6
                · rw [if_pos h6]
                  exact values 5 (by decide) i l5 h6
                · rw [if_neg h6]
                  have l6 : D 6 < i:=by have h:=ne 6 (by decide); omega
                  by_cases h7 : i < D 7
                  · rw [if_pos h7]
                    exact values 6 (by decide) i l6 h7
                  · rw [if_neg h7]
                    have l7 : D 7 < i:=by have h:=ne 7 (by decide); omega
                    by_cases h8 : i < D 8
                    · rw [if_pos h8]
                      exact values 7 (by decide) i l7 h8
                    · rw [if_neg h8]
                      have l8 : D 8 < i:=by have h:=ne 8 (by decide); omega
                      by_cases h10 : i < D 10
                      · rw [if_pos h10]
                        by_cases h9 : i < D 9
                        · rw [values 8 (by decide) i l8 h9]
                          change some (decide (i-D 8 ≤ 0))=some false
                          rw [decide_eq_false (by omega)]
                        · have l9 : D 9 < i:=by have h:=ne 9 (by decide); omega
                          rw [values 9 (by decide) i l9 h10]
                          change some (decide (i-D 9 ≤ 0))=some false
                          rw [decide_eq_false (by omega)]
                      · rw [if_neg h10]
                        have l10 : D 10 < i:=by have h:=ne 10 (by decide); omega
                        by_cases h11 : i < D 11
                        · rw [if_pos h11,values 10 (by decide) i l10 h11]
                          change some (decide (i-D 10 ≤ 3*r+3))=some true
                          have span : D 11=D 10+(3*r+3)+1:=by dsimp only [D,SerializedBody.delimiter]; omega
                          rw [decide_eq_true (by omega)]
                        · rw [if_neg h11]
                          have l11 : D 11 < i:=by have h:=ne 11 (by decide); omega
                          exact values 11 (by decide) i l11 last
private theorem lifted_prepared (T : Nat → Option Bool) (S M F r n g W : Nat) :
    lifted (SerializedBody.image T F r n g W (S-min M S) 0 0 W g) S (min M S)=
      SerializedBody.prepared T S M F r n g W := by
  funext i
  by_cases physical : M < S
  · have minEq : min M S=M:=Nat.min_eq_left (by omega)
    dsimp only [lifted,SerializedBody.prepared]
    rw [minEq,if_pos physical]
    dsimp only [put]
    by_cases hit : i=M
    · rw [if_pos hit,if_pos ⟨hit,by omega⟩]
    · rw [if_neg hit,if_neg (by omega)]
  · have minEq : min M S=S:=Nat.min_eq_right (by omega)
    dsimp only [lifted,SerializedBody.prepared]
    rw [minEq,if_neg (by omega)]
    rw [if_neg (by omega)]
end FullIngressClosure
