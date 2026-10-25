import SerializedPositiveBody.Operands
namespace SerializedPositiveBody
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion
private def V (T : Nat → Option Bool) (D : Nat → Nat) (S M W u i : Nat) : Option Bool :=
  if i=M+u ∧ i < S then none else if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W-u)) else
  if D 11 < i ∧ i < D 12 then some (decide (i-D 11 ≤ u)) else T i
private theorem not_between (D : Nat → Nat) (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    (j k : Nat) (hj : j ≤ 12) (hk : k < 12) : ¬(D k < D j ∧ D j < D (k+1)) := by
  by_cases order : j ≤ k
  · have :=mono j k order (by omega);omega
  · have :=mono (k+1) j (by omega) hj;omega
private theorem separated (D : Nat → Nat) (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b)
    {i j k : Nat} (hj : j < 12) (hk : k < 12) (ne : j≠k) (inside : D j < i ∧ i < D (j+1)) :
    ¬(D k < i ∧ i < D (k+1)) := by
  by_cases order : j < k
  · have :=mono (j+1) k (by omega) (by omega);omega
  · have :=mono (k+1) j (by omega) (by omega);omega
private theorem compose {N B t s : Nat} {a b : Config 7500 N B}
    (run : SerializedBody.machine.run t a=b)
    (before : ∀ u,u ≤ t → 4 ≤ (SerializedBody.machine.run u a).state.val)
    (later : ∀ u,u ≤ s → 4 ≤ (SerializedBody.machine.run u b).state.val) :
    ∀ u,u ≤ t+s → 4 ≤ (SerializedBody.machine.run u a).state.val := by
  intro u hu
  by_cases early : u ≤ t
  · exact before u early
  · rw [show u=t+(u-t) by omega,SerializedBody.machine.run_add,run]
    exact later (u-t) (by omega)
/-- One complete positive node-opening phase: real H entry, paid node/quota update and all three original tag bits. -/
theorem open_node (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H Q F r M W u quota nodes N B P : Nat) (source : Fin S → Bool)
    (paid : 0 < quota) (bounded : quota+nodes ≤ r) (enough : u+3 ≤ W) (hw : W ≤ r)
    (sl : S < L) (lh : L < H) (positive : 0 < Q) (arena : H+Q < F)
    (anchor : D 0=F+1) (rise : ∀ j,j < 12 → D j < D (j+1))
    (mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) (blank : ∀ j,j ≤ 12 → T (D j)=none)
    (cells : ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b)
    (len4 : D 5=D 4+r+1) (len5 : D 6=D 5+r+1) (len6 : D 7=D 6+r+1) (len11 : D 12=D 11+r+1)
    (quotaField : ∀ i,D 6 < i → i < D 7 → T i=some (decide (i-D 6 ≤ quota)))
    (nodesField : ∀ i,D 5 < i → i < D 6 → T i=some (decide (i-D 5 ≤ nodes)))
    (eof : T S=none) (left : T L=none) (right : T H=none) (fence : T F=some false)
    (reg : ∀ i,S < i → i < L → ∃ b,T i=some b) (ass : ∀ i,L < i → i < H → ∃ b,T i=some b)
    (marks : ∀ i,H < i → i ≤ H+Q → T i=some true) (gap : ∀ i,H+Q < i → i < F → T i=none)
    (sourceCells : ∀ i,M ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩))
    (room : D 12 ≤ P) (fit : P < tapeLength N B) (hH : H < tapeLength N B) (h0 : D 0 < tapeLength N B) :
    let X:=fun base v i=>if i=M+v ∧ i < S then none else
      if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W-v)) else
      if D 11 < i ∧ i < D 12 then some (decide (i-D 11 ≤ v)) else base i
    let U : Nat → Option Bool:=fun i=>if i=D 5+nodes+1 then some true else if i=D 6+quota then some false else T i
    let b0:=padRead source (M+u); let b1:=padRead source (M+(u+1)); let b2:=padRead source (M+(u+2))
    let site : Fin 9:=if b0 then if b1 then 6 else 5 else if b1 then 4 else 3
    let initial : Config 7500 N B:=⟨SerializedBody.entry (SerializedBody.sourceMode source (M+u)),⟨H,hH⟩,fun i=>X T u i.val⟩
    ∃ t,t ≤ 512*(P+1) ∧ quota-1+(nodes+1)=quota+nodes ∧
      SerializedBody.machine.run t initial=
        ⟨SerializedBodyRefinement.getExit site b2 (SerializedBody.sourceMode source (M+(u+3))),⟨D 0,h0⟩,fun i=>X U (u+3) i.val⟩ ∧
      ∀ j,j ≤ t → 4 ≤ (SerializedBody.machine.run j initial).state.val := by
  dsimp only
  let memory:=V T D S M W u
  have before : S < D 0 := by omega
  have lower (j : Nat) (hj : j ≤ 12) : D 0 ≤ D j :=mono 0 j (by omega) hj
  have work (i : Nat) (lo : D 0 ≤ i) : memory i=
      (if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W-u)) else
      if D 11 < i ∧ i < D 12 then some (decide (i-D 11 ≤ u)) else T i) := by
    simp only [memory,V,if_neg (by omega : ¬(i=M+u ∧ i < S))]
  have header (i : Nat) (lo : S ≤ i) (hi : i < D 0) : memory i=T i := by
    have a:=lower 4 (by decide);have b:=lower 11 (by decide)
    simp only [memory,V,if_neg (by omega : ¬(i=M+u ∧ i < S)),
      if_neg (by omega : ¬(D 4 < i ∧ i < D 5)),if_neg (by omega : ¬(D 11 < i ∧ i < D 12))]
  have mb (j : Nat) (hj : j ≤ 12) : memory (D j)=none := by
    rw [work _ (lower j hj),if_neg (not_between D mono j 4 hj (by decide)),if_neg (not_between D mono j 11 hj (by decide))]
    exact blank j hj
  have mc (j i : Nat) (hj : j < 12) (lo : D j < i) (hi : i < D (j+1)) : ∃ b,memory i=some b := by
    rw [work i (by have :=lower j (by omega);omega)]
    by_cases a : D 4 < i ∧ i < D 5
    · exact ⟨_,if_pos a⟩
    rw [if_neg a]
    by_cases b : D 11 < i ∧ i < D 12
    · exact ⟨_,if_pos b⟩
    rw [if_neg b];exact cells j i hj lo hi
  have field (j i : Nat) (hj : j < 12) (not4 : j≠4) (not11 : j≠11) (lo : D j < i) (hi : i < D (j+1)) : memory i=T i := by
    rw [work i (by have :=lower j (by omega);omega),if_neg (separated D mono hj (by decide) not4 ⟨lo,hi⟩),if_neg (separated D mono hj (by decide) not11 ⟨lo,hi⟩)]
  have rootRoom : F+1 ≤ P := by rw [←anchor];exact le_trans (lower 12 (by decide)) room
  obtain ⟨entryRun,entryPrefix⟩:=SerializedBodyCompletion.entry_need (SerializedBody.sourceMode source (M+u)) memory H Q F N B P positive arena rootRoom fit hH (by simpa only [anchor] using h0)
    (by rw [header H (by omega) (by omega)];exact right)
    (by rw [header F (by omega) (by omega)];exact fence)
    (by intro i lo hi;rw [header i (by omega) (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [header i (by omega) (by omega)];exact gap i lo hi)
  obtain ⟨needPrice,needRun,needPrefix⟩:=SerializedBodyCompletion.need_get (SerializedBody.sourceMode source (M+u)) D memory r quota nodes N B P rise mono mb mc room fit h0 paid bounded len5 len6
    (by intro i lo hi;rw [field 6 i (by decide) (by decide) (by decide) lo hi];exact quotaField i lo hi)
    (by intro i lo hi;rw [field 5 i (by decide) (by decide) (by decide) lo hi];exact nodesField i lo hi)
  let U : Nat → Option Bool:=fun i=>if i=D 5+nodes+1 then some true else if i=D 6+quota then some false else T i
  have ip : D 5 < D 5+nodes+1 ∧ D 5+nodes+1 < D 6 := by omega
  have dp : D 6 < D 6+quota ∧ D 6+quota < D 7 := by omega
  have usame (i : Nat) (a : i≠D 5+nodes+1) (b : i≠D 6+quota) : U i=T i := by simp only [U,if_neg a,if_neg b]
  have ublank (j : Nat) (hj : j ≤ 12) : U (D j)=none := by
    have neq (k i : Nat) (hk : k < 12) (inside : D k < i ∧ i < D (k+1)) : D j≠i := by
      intro eq;rw [←eq] at inside;exact not_between D mono j k hj hk inside
    rw [usame _ (neq 5 _ (by decide) ip) (neq 6 _ (by decide) dp)]
    exact blank j hj
  have ucells (j i : Nat) (hj : j < 12) (lo : D j < i) (hi : i < D (j+1)) : ∃ b,U i=some b := by
    by_cases a : i=D 5+nodes+1
    · exact ⟨true,by simp only [U,if_pos a]⟩
    by_cases b : i=D 6+quota
    · exact ⟨false,by simp only [U,if_neg a,if_pos b]⟩
    rw [usame i a b];exact cells j i hj lo hi
  have low (i : Nat) (hi : i < D 0) : U i=T i := by
    have a:=lower 5 (by decide);have b:=lower 6 (by decide)
    exact usame i (by omega) (by omega)
  have atSource (i : Nat) (mi : M ≤ i) (hi : i < S) : U i=some (source ⟨i,hi⟩) := by rw [low i (by omega)];exact sourceCells i mi hi
  have updated : (fun i=>if i=D 5+nodes+1 then some true else if i=D 6+quota then some false else memory i)=V U D S M W u := by
    funext i
    have outside (j : Nat) (hj : j < 12) (nj : j≠4) (nj' : j≠11) (pos : D j < i ∧ i < D (j+1)) :
        ¬(i=M+u ∧ i < S) ∧ ¬(D 4 < i ∧ i < D 5) ∧ ¬(D 11 < i ∧ i < D 12) := by
      have :=lower j (by omega)
      exact ⟨by omega,separated D mono hj (by decide) nj pos,separated D mono hj (by decide) nj' pos⟩
    by_cases a : i=D 5+nodes+1
    · have out:=outside 5 (by decide) (by decide) (by decide) (by simpa only [a] using ip)
      simp only [if_pos a,V,if_neg out.1,if_neg out.2.1,if_neg out.2.2,U]
    by_cases b : i=D 6+quota
    · have out:=outside 6 (by decide) (by decide) (by decide) (by simpa only [b] using dp)
      simp only [if_neg a,if_pos b,V,if_neg out.1,if_neg out.2.1,if_neg out.2.2,U]
    simp only [if_neg a,if_neg b,memory,V,usame i a b]
  have finiteUpdated:=congrArg (fun f : Nat → Option Bool=>fun i : Fin (tapeLength N B)=>f i.val) updated
  dsimp only at finiteUpdated
  rw [finiteUpdated] at needRun
  obtain ⟨_,tagTime,tagPrice,tagRun,tagPrefix⟩:=tag_reader D U S L H Q F r M W u N B P source enough hw sl lh positive arena anchor rise mono ublank ucells len4 len11
    (by rw [low S before];exact eof)
    (by rw [low L (by omega)];exact left)
    (by rw [low H (by omega)];exact right)
    (by rw [low F (by omega)];exact fence)
    (by intro i lo hi;rw [low i (by omega)];exact reg i lo hi)
    (by intro i lo hi;rw [low i (by omega)];exact ass i lo hi)
    (by intro i lo hi;rw [low i (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [low i (by omega)];exact gap i lo hi) atSource room fit h0
  let steps:=1+(2*(D 6-D 0+6)+2*quota+4)+(2*(D 5-D 0+5)+2*nodes+4)+1
  replace entryRun : SerializedBody.machine.run (F+2-H)
      (⟨SerializedBody.entry (SerializedBody.sourceMode source (M+u)),⟨H,hH⟩,fun i=>memory i.val⟩ : Config 7500 N B)=
      ⟨SerializedBodyCompletion.needEntry (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,fun i=>memory i.val⟩ := by
    apply entryRun.trans
    apply Config.ext_parts
    · rfl
    · exact Fin.ext anchor.symm
    · rfl
  let A : Config 7500 N B:=⟨SerializedBody.entry (SerializedBody.sourceMode source (M+u)),⟨H,hH⟩,fun i=>memory i.val⟩
  have middle : SerializedBody.machine.run (F+2-H+steps) A=
      ⟨SerializedBodyRefinement.getEntry 0 (SerializedBody.sourceMode source (M+u)),⟨D 0,h0⟩,fun i=>V U D S M W u i.val⟩ := by
    rw [SerializedBody.machine.run_add]
    exact (congrArg (SerializedBody.machine.run steps) entryRun).trans needRun
  have total : SerializedBody.machine.run (F+2-H+steps+tagTime) A=
      ⟨SerializedBodyRefinement.getExit (if padRead source (M+u) then if padRead source (M+(u+1)) then 6 else 5 else if padRead source (M+(u+1)) then 4 else 3)
        (padRead source (M+(u+2))) (SerializedBody.sourceMode source (M+(u+3))),⟨D 0,h0⟩,fun i=>V U D S M W (u+3) i.val⟩ := by
    rw [SerializedBody.machine.run_add]
    exact (congrArg (SerializedBody.machine.run tagTime) middle).trans tagRun
  have f1:=compose entryRun entryPrefix needPrefix
  have f2:=compose middle f1 tagPrefix
  have bound0 : F+2-H ≤ 2*(P+1) := by omega
  refine ⟨F+2-H+steps+tagTime,?_,by omega,total,f2⟩
  change steps ≤ 128*(P+1) at needPrice
  omega
private abbrev d (F r n : Nat) :=SerializedBody.delimiter F r n
private theorem dm (F r n : Nat) : ∀ a b,a ≤ b → b ≤ 12 → d F r n a ≤ d F r n b := by
  intro a b
  induction b generalizing a with
  | zero =>
    intro h _
    have eq : a=0 := by omega
    subst a
    exact le_rfl
  | succ b ih =>
    intro h hb
    by_cases eq : a=b+1
    · subst a;exact le_rfl
    · have step : d F r n b < d F r n (b+1) := by
        have hb' : b < 12 := by omega
        interval_cases b <;> dsimp only [d,SerializedBody.delimiter] <;> omega
      exact le_trans (ih a (by omega) (by omega)) (Nat.le_of_lt step)
private theorem im_out (T : Nat → Option Bool) (F r n g W a i : Nat) (out : i < d F r n 0) :
    SerializedBody.image T F r n g W a 0 0 W g i=T i := by
  simp only [SerializedBody.image,if_pos (Or.inl out)]
private theorem im_blank (T : Nat → Option Bool) (F r n g W a j : Nat) (hj : j ≤ 12) :
    SerializedBody.image T F r n g W a 0 0 W g (d F r n j)=none := by
  have lower:=dm F r n 0 j (by omega) hj
  have upper:=dm F r n j 12 hj (by decide)
  have inside : ¬(d F r n j < d F r n 0 ∨ d F r n 12 < d F r n j) := by omega
  have mask : (List.range 13).any (fun k=>d F r n j==d F r n k)=true :=
    List.any_eq_true.mpr ⟨j,by simp only [List.mem_range];omega,by simp⟩
  simp only [SerializedBody.image,if_neg inside,mask,↓reduceIte]
private theorem im_middle (T : Nat → Option Bool) (F r n g W a j i : Nat)
    (hj : j < 12) (lo : d F r n j < i) (hi : i < d F r n (j+1)) :
    SerializedBody.image T F r n g W a 0 0 W g i=
      (if i < d F r n 1 then some (decide (i-d F r n 0 ≤ g)) else
      if i < d F r n 2 then some false else
      if i < d F r n 3 then some (decide (i-d F r n 2 ≤ bitLength n)) else
      if i < d F r n 4 then some (decide (i-d F r n 3 ≤ W)) else
      if i < d F r n 5 then some (decide (i-d F r n 4 ≤ W)) else
      if i < d F r n 6 then some (decide (i-d F r n 5 ≤ 0)) else
      if i < d F r n 7 then some (decide (i-d F r n 6 ≤ g)) else
      if i < d F r n 8 then some (decide (i-d F r n 7 ≤ a)) else
      if i < d F r n 10 then some false else if i < d F r n 11 then some true else
      some (decide (i-d F r n 11 ≤ 0))) := by
  have lower:=dm F r n 0 j (by omega) (by omega)
  have upper:=dm F r n (j+1) 12 (by omega) (by omega)
  have out : ¬(i < d F r n 0 ∨ d F r n 12 < i) := by omega
  have mask : (List.range 13).any (fun k=>i==d F r n k)=false := by
    cases eq : (List.range 13).any (fun k=>i==d F r n k) with
    | false => rfl
    | true =>
      obtain ⟨k,hk,yes⟩:=List.any_eq_true.mp eq
      have kb : k ≤ 12 := by have :=List.mem_range.mp hk;omega
      have same : i=d F r n k := by simpa only [beq_iff_eq] using yes
      by_cases order : k ≤ j
      · have :=dm F r n k j order (by omega);omega
      · have :=dm F r n (j+1) k (by omega) kb;omega
  simp only [SerializedBody.image,if_neg out,mask,Bool.false_eq_true,↓reduceIte]
private theorem im_field (T : Nat → Option Bool) (F r n g W a j i : Nat)
    (mem : j∈[4,5,6,11]) (lo : d F r n j < i) (hi : i < d F r n (j+1)) :
    SerializedBody.image T F r n g W a 0 0 W g i=
      some (decide (i-d F r n j ≤ if j=4 then W else if j=6 then g else 0)) := by
  have hj : j < 12 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at mem;omega
  rw [im_middle T F r n g W a j i hj lo hi]
  have no (k : Nat) (hk : k ≤ j) : ¬i < d F r n k := by have :=dm F r n k j hk (by omega);omega
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl
  · simp only [if_neg (no 1 (by decide)),if_neg (no 2 (by decide)),if_neg (no 3 (by decide)),if_neg (no 4 (by decide)),if_pos hi,↓reduceIte]
  · simp only [if_neg (no 1 (by decide)),if_neg (no 2 (by decide)),if_neg (no 3 (by decide)),if_neg (no 4 (by decide)),if_neg (no 5 (by decide)),if_pos hi,if_neg (by decide : (5:Nat)≠4),if_neg (by decide : (5:Nat)≠6)]
  · simp only [if_neg (no 1 (by decide)),if_neg (no 2 (by decide)),if_neg (no 3 (by decide)),if_neg (no 4 (by decide)),if_neg (no 5 (by decide)),if_neg (no 6 (by decide)),if_pos hi,if_neg (by decide : (6:Nat)≠4),↓reduceIte]
  · simp only [if_neg (no 1 (by decide)),if_neg (no 2 (by decide)),if_neg (no 3 (by decide)),if_neg (no 4 (by decide)),if_neg (no 5 (by decide)),if_neg (no 6 (by decide)),if_neg (no 7 (by decide)),if_neg (no 8 (by decide)),if_neg (no 10 (by decide)),if_neg (no 11 (by decide)),if_neg (by decide : (11:Nat)≠4),if_neg (by decide : (11:Nat)≠6)]
private theorem im_occupied (T : Nat → Option Bool) (F r n g W a j i : Nat)
    (hj : j < 12) (lo : d F r n j < i) (hi : i < d F r n (j+1)) :
    ∃ b,SerializedBody.image T F r n g W a 0 0 W g i=some b := by
  rw [im_middle T F r n g W a j i hj lo hi]
  by_cases b1 : i < d F r n 1
  · rw [if_pos b1];exact ⟨_,rfl⟩
  rw [if_neg b1]
  by_cases b2 : i < d F r n 2
  · rw [if_pos b2];exact ⟨_,rfl⟩
  rw [if_neg b2]
  by_cases b3 : i < d F r n 3
  · rw [if_pos b3];exact ⟨_,rfl⟩
  rw [if_neg b3]
  by_cases b4 : i < d F r n 4
  · rw [if_pos b4];exact ⟨_,rfl⟩
  rw [if_neg b4]
  by_cases b5 : i < d F r n 5
  · rw [if_pos b5];exact ⟨_,rfl⟩
  rw [if_neg b5]
  by_cases b6 : i < d F r n 6
  · rw [if_pos b6];exact ⟨_,rfl⟩
  rw [if_neg b6]
  by_cases b7 : i < d F r n 7
  · rw [if_pos b7];exact ⟨_,rfl⟩
  rw [if_neg b7]
  by_cases b8 : i < d F r n 8
  · rw [if_pos b8];exact ⟨_,rfl⟩
  rw [if_neg b8]
  by_cases b10 : i < d F r n 10
  · rw [if_pos b10];exact ⟨_,rfl⟩
  rw [if_neg b10]
  by_cases b11 : i < d F r n 11
  · rw [if_pos b11];exact ⟨_,rfl⟩
  rw [if_neg b11]
  exact ⟨_,rfl⟩
private theorem initial_view (T : Nat → Option Bool) (S M F r n g W : Nat) :
    V (SerializedBody.image T F r n g W (S-min M S) 0 0 W g) (d F r n) S M W 0=
      SerializedBody.prepared T S M F r n g W := by
  funext i
  dsimp only [V,SerializedBody.prepared]
  rw [Nat.add_zero]
  by_cases hole : i=M ∧ i < S
  · rw [if_pos hole,if_pos hole]
  rw [if_neg hole,if_neg hole]
  by_cases a : d F r n 4 < i ∧ i < d F r n 5
  · rw [if_pos a,im_field T F r n g W (S-min M S) 4 i (by simp) a.1 a.2]
    rfl
  rw [if_neg a]
  by_cases b : d F r n 11 < i ∧ i < d F r n 12
  · rw [if_pos b,im_field T F r n g W (S-min M S) 11 i (by simp) b.1 b.2]
    rfl
  · rw [if_neg b]
/-- Original BODY H frame, positive quota/window domain: actual node-opening and tag handoff, not completed evaluation. -/
theorem initialized_node :
    ∀ (R S z n r g W M Q : Nat) (source : Fin S → Bool) (beta : Fin n → Bool) (T : Nat → Option Bool),
    r ≤ S → S ≤ R → g ≤ r → W ≤ r → bitLength n ≤ r → S-min M S ≤ r →
    0 < g → 3 ≤ W →
    let B:=FixedRawLengthFence.allocation R
    let L:=S+z+2; let H:=L+n+1; let F:=FixedRawLengthFence.fencePos R
    0 < Q → H+Q < F →
    (∀ i,M ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) → T S=none →
    (∀ i,S < i → i < L → T i=some false) → T L=none →
    (∀ j : Fin n,T (H-1-j.val)=some (beta j)) → T H=none →
    (∀ i,H < i → i ≤ H+Q → T i=some true) → (∀ i,H+Q < i → i < F → T i=none) → T F=some false →
    ∀ _fit : SerializedBody.delimiter F r n 12 < tapeLength R B,∀ hH : H < tapeLength R B,
    let D : Nat → Nat:=SerializedBody.delimiter F r n
    let base : Nat → Option Bool:=SerializedBody.image T F r n g W (S-min M S) 0 0 W g
    let U : Nat → Option Bool:=fun i=>if i=D 5+1 then some true else if i=D 6+g then some false else base i
    let C : Nat → Option Bool:=fun i=>if i=M+3 ∧ i < S then none else if D 4 < i ∧ i < D 5 then some (decide (i-D 4 ≤ W-3)) else
      if D 11 < i ∧ i < D 12 then some (decide (i-D 11 ≤ 3)) else U i
    let site : Fin 9:=if padRead source M then if padRead source (M+1) then 6 else 5 else if padRead source (M+1) then 4 else 3
    ∃ (t : Nat) (h0 : D 0 < tapeLength R B),t ≤ 1073741824*(R+1)^6 ∧
      SerializedBody.machine.run t (⟨SerializedBody.entry (SerializedBody.sourceMode source M),⟨H,hH⟩,fun i=>SerializedBody.prepared T S M F r n g W i.val⟩ : Config 7500 R B)=
      ⟨SerializedBodyRefinement.getExit site (padRead source (M+2)) (SerializedBody.sourceMode source (M+3)),⟨D 0,h0⟩,fun i=>C i.val⟩ ∧
      ∀ u,u ≤ t → 4 ≤ (SerializedBody.machine.run u (⟨SerializedBody.entry (SerializedBody.sourceMode source M),⟨H,hH⟩,fun i=>SerializedBody.prepared T S M F r n g W i.val⟩ : Config 7500 R B)).state.val := by
  intro R S z n r g W M Q source beta T hr hs hg hw _hell _ha paid enough
  dsimp only
  intro hq arena src ts reg tl betaCells th marks gap tf fit hH
  let F:=FixedRawLengthFence.fencePos R
  let L:=S+z+2
  let H:=L+n+1
  let D:=d F r n
  let base:=SerializedBody.image T F r n g W (S-min M S) 0 0 W g
  have mono : ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b :=dm F r n
  have rise : ∀ j,j < 12 → D j < D (j+1) := by
    intro j hj;interval_cases j <;> dsimp only [D,d,SerializedBody.delimiter] <;> omega
  have before : S < D 0 := by change S < F+1;omega
  have h0 : D 0 < tapeLength R (FixedRawLengthFence.allocation R) :=lt_of_le_of_lt (mono 0 12 (by decide) (by decide)) fit
  have same (i : Nat) (hi : i < D 0) : base i=T i :=im_out T F r n g W (S-min M S) i hi
  have blanks : ∀ j,j ≤ 12 → base (D j)=none :=im_blank T F r n g W (S-min M S)
  have occupied (j i : Nat) (hj : j < 12) (lo : D j < i) (hi : i < D (j+1)) : ∃ b,base i=some b :=
    im_occupied T F r n g W (S-min M S) j i hj lo hi
  have original : V base D S M W 0=SerializedBody.prepared T S M F r n g W :=initial_view T S M F r n g W
  have ass (i : Nat) (lo : L < i) (hi : i < H) : ∃ b,base i=some b := by
    have geometry : H=L+n+1 := rfl
    let j : Fin n:=⟨H-1-i,by omega⟩
    have eq : H-1-j.val=i := by dsimp only [j];omega
    rw [same i (by change i < F+1;omega),←eq]
    exact ⟨beta j,betaCells j⟩
  obtain ⟨t,price,_,run,prefixBound⟩:=open_node D base S L H Q F r M W 0 g 0 R (FixedRawLengthFence.allocation R) (D 12) source paid (by omega) (by omega) hw (by dsimp only [L];omega) (by dsimp only [H];omega) hq arena rfl rise mono blanks occupied
    (by dsimp only [D,d,SerializedBody.delimiter];omega) (by dsimp only [D,d,SerializedBody.delimiter];omega)
    (by dsimp only [D,d,SerializedBody.delimiter];omega) (by dsimp only [D,d,SerializedBody.delimiter];omega)
    (by intro i lo hi;exact im_field T F r n g W (S-min M S) 6 i (by simp) lo hi)
    (by intro i lo hi;exact im_field T F r n g W (S-min M S) 5 i (by simp) lo hi)
    (by rw [same S before];exact ts) (by rw [same L (by change L < F+1;omega)];exact tl)
    (by rw [same H (by change H < F+1;omega)];exact th) (by rw [same F (by change F < F+1;omega)];exact tf)
    (by intro i lo hi;rw [same i (by change i < F+1;omega)];exact ⟨false,reg i lo hi⟩) ass
    (by intro i lo hi;rw [same i (by change i < F+1;omega)];exact marks i lo hi)
    (by intro i lo hi;rw [same i (by change i < F+1;omega)];exact gap i lo hi)
    (by intro i mi hi;rw [same i (by omega)];exact src i mi hi) le_rfl fit hH h0
  have initialTape : (fun i : Fin (tapeLength R (FixedRawLengthFence.allocation R))=>V base D S M W 0 i.val)=
      (fun i=>SerializedBody.prepared T S M F r n g W i.val) :=congrArg (fun f : Nat → Option Bool=>fun i : Fin (tapeLength R (FixedRawLengthFence.allocation R))=>f i.val) original
  dsimp only at run prefixBound
  change SerializedBody.machine.run t ⟨SerializedBody.entry (SerializedBody.sourceMode source (M+0)),⟨H,hH⟩,fun i=>V base D S M W 0 i.val⟩=_ at run
  change ∀ u,u ≤ t → 4 ≤ (SerializedBody.machine.run u ⟨SerializedBody.entry (SerializedBody.sourceMode source (M+0)),⟨H,hH⟩,fun i=>V base D S M W 0 i.val⟩).state.val at prefixBound
  rw [initialTape] at run prefixBound
  refine ⟨t,h0,?_,by simpa only [Nat.add_zero,Nat.zero_add] using run,by simpa only [Nat.add_zero] using prefixBound⟩
  have rn : n ≤ 3*R := by change S+z+2+n+1+Q < 3*R+2 at arena;omega
  have extent : D 12+1 ≤ 22*(R+1) := by change 3*R+2+13*r+2*n+16+1 ≤ 22*(R+1);omega
  have power : R+1 ≤ (R+1)^6 :=Nat.le_pow (by decide : 0 < 6)
  omega
end SerializedPositiveBody
