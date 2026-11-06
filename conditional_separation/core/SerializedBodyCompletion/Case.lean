import SerializedBodyCompletion.Consumer
namespace SerializedBodyCompletion
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open SerializedBody
private abbrev D (F r n : Nat) : Nat → Nat := SerializedBody.delimiter F r n
private theorem d_rise (F r n : Nat) : ∀ j,j < 12 → D F r n j < D F r n (j+1) := by
  intro j hj
  interval_cases j <;> dsimp only [D,SerializedBody.delimiter] <;> omega
private theorem d_mono (F r n : Nat) : ∀ a b,a ≤ b → b ≤ 12 → D F r n a ≤ D F r n b := by
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
    · exact le_trans (ih a (by omega) (by omega)) (Nat.le_of_lt (d_rise F r n b (by omega)))
private theorem no_delimiter {F r n j i} (hj : j < 12)
    (lo : D F r n j < i) (hi : i < D F r n (j+1)) :
    (List.range 13).any (fun k => i==D F r n k)=false := by
  have no : (List.range 13).any (fun k => i==D F r n k)=true → False := by
    intro yes
    obtain ⟨k,hk,eq⟩:=List.any_eq_true.mp yes
    have bound : k ≤ 12 := by
      have hk' : k < 13 := List.mem_range.mp hk
      omega
    have eq' : i=D F r n k := by simpa only [beq_iff_eq] using eq
    by_cases before : k ≤ j
    · have order:=d_mono F r n k j before (by omega);omega
    · have order:=d_mono F r n (j+1) k (by omega) bound;omega
  cases h : (List.range 13).any (fun k => i==D F r n k) with
  | false => rfl
  | true => exact False.elim (no h)
private theorem image_blank (T : Nat → Option Bool) (F r n g W a v u rem quota j : Nat)
    (hj : j ≤ 12) : SerializedBody.image T F r n g W a v u rem quota (D F r n j)=none := by
  have lower:=d_mono F r n 0 j (by omega) hj
  have upper:=d_mono F r n j 12 hj (by decide)
  have inside : ¬(D F r n j < D F r n 0 ∨ D F r n 12 < D F r n j) := by omega
  have mask : (List.range 13).any (fun k => D F r n j==D F r n k)=true := by
    exact List.any_eq_true.mpr ⟨j,by simp only [List.mem_range];omega,by simp⟩
  simp only [SerializedBody.image,if_neg inside,mask,↓reduceIte]
private def cellValue (F r n g W a v u rem quota j i : Nat) : Bool :=
  match j with
  | 0 => decide (i-D F r n 0 ≤ g) | 1 => false
  | 2 => decide (i-D F r n 2 ≤ bitLength n) | 3 => decide (i-D F r n 3 ≤ W)
  | 4 => decide (i-D F r n 4 ≤ rem) | 5 => decide (i-D F r n 5 ≤ v)
  | 6 => decide (i-D F r n 6 ≤ quota) | 7 => decide (i-D F r n 7 ≤ a)
  | 10 => true | 11 => decide (i-D F r n 11 ≤ u) | _ => false
private def contents (d : Nat → Nat) (ell g W a nodes used remaining quota i : Nat) : Option Bool :=
  if i < d 1 then some (decide (i-d 0 ≤ g)) else
  if i < d 2 then some false else if i < d 3 then some (decide (i-d 2 ≤ ell)) else
  if i < d 4 then some (decide (i-d 3 ≤ W)) else if i < d 5 then some (decide (i-d 4 ≤ remaining)) else
  if i < d 6 then some (decide (i-d 5 ≤ nodes)) else if i < d 7 then some (decide (i-d 6 ≤ quota)) else
  if i < d 8 then some (decide (i-d 7 ≤ a)) else if i < d 10 then some false else
  if i < d 11 then some true else some (decide (i-d 11 ≤ used))
private def value (d : Nat → Nat) (ell g W a nodes used remaining quota j i : Nat) : Bool :=
  match j with
  | 0 => decide (i-d 0 ≤ g) | 1 => false | 2 => decide (i-d 2 ≤ ell)
  | 3 => decide (i-d 3 ≤ W) | 4 => decide (i-d 4 ≤ remaining) | 5 => decide (i-d 5 ≤ nodes)
  | 6 => decide (i-d 6 ≤ quota) | 7 => decide (i-d 7 ≤ a) | 10 => true
  | 11 => decide (i-d 11 ≤ used) | _ => false
private theorem contents_at (d : Nat → Nat) (ell g W a nodes used remaining quota j i : Nat)
    (mono : ∀ a b,a ≤ b → b ≤ 12 → d a ≤ d b)
    (hj : j < 12) (lo : d j < i) (hi : i < d (j+1)) :
    contents d ell g W a nodes used remaining quota i=some (value d ell g W a nodes used remaining quota j i) := by
  have before (k : Nat) (hk : k ≤ j) : ¬i < d k := by
    have :=mono k j hk (by omega)
    omega
  have after (k : Nat) (hk : j+1 ≤ k) (ku : k ≤ 12) : i < d k := lt_of_lt_of_le hi (mono (j+1) k hk ku)
  interval_cases j
  · unfold contents
    rw [if_pos (after 1 (by decide) (by decide))]
    rfl
  · unfold contents
    rw [if_neg (before 1 (by decide)), if_pos (after 2 (by decide) (by decide))]
    rfl
  · unfold contents
    rw [if_neg (before 1 (by decide)), if_neg (before 2 (by decide)), if_pos (after 3 (by decide) (by decide))]
    rfl
  · unfold contents
    rw [if_neg (before 1 (by decide)), if_neg (before 2 (by decide)), if_neg (before 3 (by decide)), if_pos (after 4 (by decide) (by decide))]
    rfl
  · unfold contents
    rw [if_neg (before 1 (by decide)), if_neg (before 2 (by decide)), if_neg (before 3 (by decide)), if_neg (before 4 (by decide)), if_pos (after 5 (by decide) (by decide))]
    rfl
  · unfold contents
    rw [if_neg (before 1 (by decide)), if_neg (before 2 (by decide)), if_neg (before 3 (by decide)), if_neg (before 4 (by decide)), if_neg (before 5 (by decide)), if_pos (after 6 (by decide) (by decide))]
    rfl
  · unfold contents
    rw [if_neg (before 1 (by decide)), if_neg (before 2 (by decide)), if_neg (before 3 (by decide)), if_neg (before 4 (by decide)), if_neg (before 5 (by decide)), if_neg (before 6 (by decide)), if_pos (after 7 (by decide) (by decide))]
    rfl
  · unfold contents
    rw [if_neg (before 1 (by decide)), if_neg (before 2 (by decide)), if_neg (before 3 (by decide)), if_neg (before 4 (by decide)), if_neg (before 5 (by decide)), if_neg (before 6 (by decide)), if_neg (before 7 (by decide)), if_pos (after 8 (by decide) (by decide))]
    rfl
  · unfold contents
    rw [if_neg (before 1 (by decide)), if_neg (before 2 (by decide)), if_neg (before 3 (by decide)), if_neg (before 4 (by decide)), if_neg (before 5 (by decide)), if_neg (before 6 (by decide)), if_neg (before 7 (by decide)), if_neg (before 8 (by decide)), if_pos (after 10 (by decide) (by decide))]
    rfl
  · unfold contents
    rw [if_neg (before 1 (by decide)), if_neg (before 2 (by decide)), if_neg (before 3 (by decide)), if_neg (before 4 (by decide)), if_neg (before 5 (by decide)), if_neg (before 6 (by decide)), if_neg (before 7 (by decide)), if_neg (before 8 (by decide)), if_pos (after 10 (by decide) (by decide))]
    rfl
  · unfold contents
    rw [if_neg (before 1 (by decide)), if_neg (before 2 (by decide)), if_neg (before 3 (by decide)), if_neg (before 4 (by decide)), if_neg (before 5 (by decide)), if_neg (before 6 (by decide)), if_neg (before 7 (by decide)), if_neg (before 8 (by decide)), if_neg (before 10 (by decide)), if_pos (after 11 (by decide) (by decide))]
    rfl
  · unfold contents
    rw [if_neg (before 1 (by decide)), if_neg (before 2 (by decide)), if_neg (before 3 (by decide)), if_neg (before 4 (by decide)), if_neg (before 5 (by decide)), if_neg (before 6 (by decide)), if_neg (before 7 (by decide)), if_neg (before 8 (by decide)), if_neg (before 10 (by decide)), if_neg (before 11 (by decide))]
    rfl
private theorem image_value (T : Nat → Option Bool) (F r n g W a v u rem quota j i : Nat)
    (hj : j < 12) (lo : D F r n j < i) (hi : i < D F r n (j+1)) :
    SerializedBody.image T F r n g W a v u rem quota i=some (cellValue F r n g W a v u rem quota j i) := by
  have lower:=d_mono F r n 0 j (by omega) (by omega)
  have upper:=d_mono F r n (j+1) 12 (by omega) (by omega)
  have outside : ¬(i < D F r n 0 ∨ D F r n 12 < i) := by omega
  have mask:=no_delimiter hj lo hi
  dsimp only [SerializedBody.image]
  rw [if_neg outside,mask]
  change contents (D F r n) (bitLength n) g W a v u rem quota i=_
  have result:=contents_at (D F r n) (bitLength n) g W a v u rem quota j i (d_mono F r n) hj lo hi
  convert result using 1
private theorem image_outside (T : Nat → Option Bool) (F r n g W a v u rem quota i : Nat)
    (out : i < D F r n 0 ∨ D F r n 12 < i) :
    SerializedBody.image T F r n g W a v u rem quota i=T i := by
  simp only [SerializedBody.image,if_pos out]
private theorem prep_work (T : Nat → Option Bool) (S M F r n g W i : Nat)
    (source : S < D F r n 0) (lo : D F r n 0 ≤ i) :
    SerializedBody.prepared T S M F r n g W i=SerializedBody.image T F r n g W (S-min M S) 0 0 W g i := by
  have no : ¬(i=M ∧ i < S) := by omega
  simp only [SerializedBody.prepared,if_neg no]
private theorem prep_below (T : Nat → Option Bool) (S M F r n g W i : Nat)
    (lo : i < D F r n 0) :
    SerializedBody.prepared T S M F r n g W i=(if i=M ∧ i < S then none else T i) := by
  simp only [SerializedBody.prepared,image_outside T F r n g W (S-min M S) 0 0 W g i (Or.inl lo)]
private theorem quota_zero (T : Nat → Option Bool) (S M F r n W : Nat)
    (source : S < D F r n 0) :
    ∀ i,D F r n 6 < i → i < D F r n 7 → SerializedBody.prepared T S M F r n 0 W i=some false := by
  intro i lo hi
  have lower:=d_mono F r n 0 6 (by decide) (by decide)
  rw [prep_work T S M F r n 0 W i source (by omega)]
  rw [image_value T F r n 0 W (S-min M S) 0 0 W 0 6 i (by decide) lo hi]
  simp only [cellValue,show ¬i-D F r n 6 ≤ 0 by omega,decide_false]
private theorem circuit_positive {n : Nat} (c : Pnp3.Models.Circuit n) : 0 < c.size := by
  cases c <;> simp only [Pnp3.Models.Circuit.size] <;> omega
private theorem zero_semantics (n : Nat) (bits : List Bool) (beta : Fin n → Bool) :
    (do let (c,tail) ← decodeCircuitFull n (bitLength n) bits
        if c.size ≤ 0 then some ((c.size,Pnp3.Models.Circuit.eval c beta),tail) else none)=none := by
  cases h : decodeCircuitFull n (bitLength n) bits with
  | none => rfl
  | some p =>
    rcases p with ⟨c,tail⟩
    have no : ¬c.size ≤ 0 := by have :=circuit_positive c;omega
    change (if c.size ≤ 0 then some ((c.size,c.eval beta),tail) else none)=none
    rw [if_neg no]
private abbrev clearView (T : Nat → Option Bool) (d : Nat → Nat) : Nat → Option Bool := fun i=>
  if d 10 < i ∧ i < d 11 then some true else
  if [1,4,5,6,8,9,11].any (fun j=>decide (d j < i ∧ i < d (j+1))) then some false else T i
private abbrev restored {S : Nat} (T : Nat → Option Bool) (d : Nat → Nat) (source : Fin S → Bool) (c : Nat) : Nat → Option Bool := fun i=>
  if c < S then if i=c then some (padRead source c) else clearView T d i else clearView T d i
private theorem any_false {l : List Nat} {p : Nat → Bool} (h : ∀ k,k∈l → p k≠true) : l.any p=false := by
  cases v : l.any p with
  | false => rfl
  | true =>
    obtain ⟨k,hk,yes⟩:=List.any_eq_true.mp v
    exact False.elim (h k hk yes)
private theorem disjoint {d : Nat → Nat} (mono : ∀ a b,a ≤ b → b ≤ 12 → d a ≤ d b)
    {i j k : Nat} (hj : j < 12) (hk : k < 12) (ne : j≠k)
    (inside : d j < i ∧ i < d (j+1)) : ¬(d k < i ∧ i < d (k+1)) := by
  by_cases order : j < k
  · have :=mono (j+1) k (by omega) (by omega);omega
  · have :=mono (k+1) j (by omega) (by omega);omega
private theorem false_field_bound (j : Nat) (mem : j∈[1,4,5,6,8,9,11]) : j < 12 ∧ j≠10 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem clear_field {d : Nat → Nat} (mono : ∀ a b,a ≤ b → b ≤ 12 → d a ≤ d b)
    (T : Nat → Option Bool) (j i : Nat) (hj : j < 12) (lo : d j < i) (hi : i < d (j+1)) :
    clearView T d i=(if j=10 then some true else if j∈[1,4,5,6,8,9,11] then some false else T i) := by
  by_cases eq : j=10
  · subst j
    have inside : d 10 < i ∧ i < d 11 := ⟨lo,hi⟩
    simp only [clearView,if_pos inside,↓reduceIte]
  · have notTen:=disjoint mono hj (by decide) eq ⟨lo,hi⟩
    by_cases mem : j∈[1,4,5,6,8,9,11]
    · have yes : [1,4,5,6,8,9,11].any (fun k=>decide (d k < i ∧ i < d (k+1)))=true :=
        List.any_eq_true.mpr ⟨j,mem,by simp only [lo,hi,and_self,decide_true]⟩
      simp only [clearView,if_neg notTen,yes,if_neg eq,if_pos mem,↓reduceIte]
    · have no : [1,4,5,6,8,9,11].any (fun k=>decide (d k < i ∧ i < d (k+1)))=false := by
        apply any_false
        intro k hk yes
        have inside : d k < i ∧ i < d (k+1) := of_decide_eq_true yes
        have kn : j≠k := by intro e;subst k;exact mem hk
        exact disjoint mono hj (false_field_bound k hk).1 kn ⟨lo,hi⟩ inside
      simp only [clearView,if_neg notTen,no,if_neg eq,if_neg mem,Bool.false_eq_true,↓reduceIte]
private theorem clear_separator {d : Nat → Nat} (mono : ∀ a b,a ≤ b → b ≤ 12 → d a ≤ d b)
    (T : Nat → Option Bool) (j : Nat) (hj : j ≤ 12) : clearView T d (d j)=T (d j) := by
  have notInside (k : Nat) (hk : k < 12) : ¬(d k < d j ∧ d j < d (k+1)) := by
    by_cases order : j ≤ k
    · have :=mono j k order (by omega);omega
    · have :=mono (k+1) j (by omega) hj;omega
  have mask : [1,4,5,6,8,9,11].any (fun k=>decide (d k < d j ∧ d j < d (k+1)))=false := by
    apply any_false
    intro k hk yes
    exact notInside k (false_field_bound k hk).1 (of_decide_eq_true yes)
  simp only [clearView,if_neg (notInside 10 (by decide)),mask,Bool.false_eq_true,↓reduceIte]
private theorem clear_outside {d : Nat → Nat} (mono : ∀ a b,a ≤ b → b ≤ 12 → d a ≤ d b)
    (T : Nat → Option Bool) (i : Nat) (out : i < d 0 ∨ d 12 < i) : clearView T d i=T i := by
  have notInside (k : Nat) (hk : k < 12) : ¬(d k < i ∧ i < d (k+1)) := by
    have l:=mono 0 k (by omega) (by omega)
    have u:=mono (k+1) 12 (by omega) (by omega)
    omega
  have mask : [1,4,5,6,8,9,11].any (fun k=>decide (d k < i ∧ i < d (k+1)))=false := by
    apply any_false
    intro k hk yes
    exact notInside k (false_field_bound k hk).1 (of_decide_eq_true yes)
  simp only [clearView,if_neg (notInside 10 (by decide)),mask,Bool.false_eq_true,↓reduceIte]
private theorem locate (d : Nat → Nat) (m : Nat) : ∀ i,d 0 < i → i < d m →
    (∀ k,k ≤ m → i≠d k) → ∃ j,j < m ∧ d j < i ∧ i < d (j+1) := by
  induction m with
  | zero => intro i lo hi _;omega
  | succ m ih =>
    intro i lo hi ne
    by_cases before : i < d m
    · obtain ⟨j,hj,a,b⟩:=ih i lo before (by intro k hk;exact ne k (by omega))
      exact ⟨j,by omega,a,b⟩
    · exact ⟨m,by omega,by have :=ne m (by omega);omega,hi⟩
private theorem immutable_field (j : Nat) (hj : j < 12) (notTen : j≠10)
    (notFalse : j∉[1,4,5,6,8,9,11]) : j∈[0,2,3,7] := by
  interval_cases j <;> simp_all
private theorem false_value (F r n g W a j i : Nat) (mem : j∈[1,4,5,6,8,9,11])
    (lo : D F r n j < i) : cellValue F r n g W a 0 0 0 0 j i=false := by
  have no (k : Nat) (h : D F r n k < i) : ¬i-D F r n k ≤ 0 := by omega
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [cellValue] <;> first | rfl | simp only [no _ lo,decide_false]
private theorem restored_image (base T : Nat → Option Bool) (S F r n g W a c : Nat) (source : Fin S → Bool)
    (before : S < D F r n 0) (atCursor : c < S → base c=some (padRead source c))
    (outside : ∀ i,i < D F r n 0 ∨ D F r n 12 < i → T i=(if c < S ∧ i=c then none else base i))
    (blank : ∀ j,j ≤ 12 → T (D F r n j)=none)
    (fixed : ∀ j,j∈[0,2,3,7] → ∀ i,D F r n j < i → i < D F r n (j+1) →
      T i=some (cellValue F r n g W a 0 0 0 0 j i)) :
    restored T (D F r n) source c=SerializedBody.image base F r n g W a 0 0 0 0 := by
  funext i
  by_cases current : c < S ∧ i=c
  · rcases current with ⟨physical,eq⟩
    subst i
    rw [image_outside base F r n g W a 0 0 0 0 c (Or.inl (by omega))]
    simp only [restored,if_pos physical,atCursor physical,↓reduceIte]
  · have noPatch : restored T (D F r n) source c i=clearView T (D F r n) i := by
      by_cases physical : c < S
      · have ne : i≠c := by omega
        simp only [restored,if_pos physical,if_neg ne]
      · simp only [restored,if_neg physical]
    rw [noPatch]
    by_cases out : i < D F r n 0 ∨ D F r n 12 < i
    · rw [clear_outside (d_mono F r n) T i out,outside i out,if_neg current,image_outside base F r n g W a 0 0 0 0 i out]
    · by_cases sep : ∃ j,j ≤ 12 ∧ i=D F r n j
      · obtain ⟨j,hj,rfl⟩:=sep
        rw [clear_separator (d_mono F r n) T j hj,blank j hj,image_blank base F r n g W a 0 0 0 0 j hj]
      · have noSep : ∀ k,k ≤ 12 → i≠D F r n k := by intro k hk eq;exact sep ⟨k,hk,eq⟩
        have lo : D F r n 0 < i := by have :=noSep 0 (by decide);omega
        have hi : i < D F r n 12 := by have :=noSep 12 (by decide);omega
        obtain ⟨j,hj,lo,hi⟩:=locate (D F r n) 12 i lo hi noSep
        rw [clear_field (d_mono F r n) T j i hj lo hi,image_value base F r n g W a 0 0 0 0 j i hj lo hi]
        by_cases ten : j=10
        · subst j;simp only [↓reduceIte,cellValue]
        · by_cases mem : j∈[1,4,5,6,8,9,11]
          · rw [if_neg ten,if_pos mem,false_value F r n g W a j i mem lo]
          · rw [if_neg ten,if_neg mem]
            exact fixed j (immutable_field j hj ten mem) i lo hi
private theorem phase_clock (R S z n r Q t : Nat) (hr : r ≤ S) (hs : S ≤ R) (hq : 0 < Q)
    (arena : S+z+n+3+Q < FixedRawLengthFence.fencePos R)
    (price : t ≤ 2048*(D (FixedRawLengthFence.fencePos R) r n 12+1)) :
    t ≤ 1073741824*(R+1)^6 := by
  have roomy : S+z+n+3+Q < 3*R+2 := arena
  have width : n ≤ 3*R := by omega
  have ext : D (FixedRawLengthFence.fencePos R) r n 12+1 ≤ 22*(R+1) := by
    change 3*R+2+13*r+2*n+16+1 ≤ 22*(R+1)
    omega
  have pow : R+1 ≤ (R+1)^6 := Nat.le_pow (by decide : 0 < 6)
  omega
private theorem prep_blank (T : Nat → Option Bool) (S M F r n g W : Nat)
    (before : S < D F r n 0) : ∀ j,j ≤ 12 → SerializedBody.prepared T S M F r n g W (D F r n j)=none := by
  intro j hj
  have lo:=d_mono F r n 0 j (by omega) hj
  rw [prep_work T S M F r n g W _ before lo,image_blank]
  exact hj
private theorem prep_cells (T : Nat → Option Bool) (S M F r n g W : Nat)
    (before : S < D F r n 0) :
    ∀ j i,j < 12 → D F r n j < i → i < D F r n (j+1) → ∃ b,SerializedBody.prepared T S M F r n g W i=some b := by
  intro j i hj lo hi
  have l:=d_mono F r n 0 j (by omega) (by omega)
  refine ⟨cellValue F r n g W (S-min M S) 0 0 W g j i,?_⟩
  rw [prep_work T S M F r n g W i before (by omega),image_value T F r n g W (S-min M S) 0 0 W g j i hj lo hi]
private theorem fixed_bound (j : Nat) (mem : j∈[0,2,3,7]) : j < 12 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl <;> decide
private theorem fixed_value (F r n g W a j i : Nat) (mem : j∈[0,2,3,7]) :
    cellValue F r n g W a 0 0 W g j i=cellValue F r n g W a 0 0 0 0 j i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl <;> rfl
private theorem prep_fixed (T : Nat → Option Bool) (S M F r n g W : Nat)
    (before : S < D F r n 0) : ∀ j,j∈[0,2,3,7] → ∀ i,D F r n j < i → i < D F r n (j+1) →
      SerializedBody.prepared T S M F r n g W i=some (cellValue F r n g W (S-min M S) 0 0 0 0 j i) := by
  intro j mem i lo hi
  have hj:=fixed_bound j mem
  have l:=d_mono F r n 0 j (by omega) (by omega)
  rw [prep_work T S M F r n g W i before (by omega),image_value T F r n g W (S-min M S) 0 0 W g j i hj lo hi,fixed_value F r n g W (S-min M S) j i mem]
private theorem prep_exterior (T : Nat → Option Bool) (S M F r n g W : Nat) :
    ∀ i,i < D F r n 0 ∨ D F r n 12 < i →
      SerializedBody.prepared T S M F r n g W i=(if M < S ∧ i=M then none else T i) := by
  intro i out
  have eq : (i=M ∧ i < S) ↔ (M < S ∧ i=M) := by omega
  simp only [SerializedBody.prepared,image_outside T F r n g W (S-min M S) 0 0 W g i out,eq]
private theorem prep_header (T : Nat → Option Bool) (S M F r n g W i : Nat)
    (lo : S ≤ i) (hi : i < D F r n 0) : SerializedBody.prepared T S M F r n g W i=T i := by
  rw [prep_below T S M F r n g W i hi,if_neg (by omega : ¬(i=M ∧ i < S))]
private theorem beta_occupied {n L H : Nat} (T : Nat → Option Bool) (beta : Fin n → Bool)
    (hH : H=L+n+1) (installed : ∀ j : Fin n,T (H-1-j.val)=some (beta j)) :
    ∀ i,L < i → i < H → ∃ b,T i=some b := by
  intro i lo hi
  let j : Fin n:=⟨H-1-i,by omega⟩
  have cell:=installed j
  have pos : H-1-j.val=i := by dsimp only [j];omega
  rw [pos] at cell
  exact ⟨beta j,cell⟩
private theorem prefix_join {N B t s : Nat} {a b : Config 7500 N B}
    (eq : SerializedBody.machine.run t a=b)
    (first : ∀ u,u ≤ t → 4 ≤ (SerializedBody.machine.run u a).state.val)
    (second : ∀ u,u < s → 4 ≤ (SerializedBody.machine.run u b).state.val) :
    ∀ u,u < t+s → 4 ≤ (SerializedBody.machine.run u a).state.val := by
  intro u hu
  by_cases early : u ≤ t
  · exact first u early
  · have endEq : u=t+(u-t) := by omega
    rw [endEq,SerializedBody.machine.run_add,eq]
    exact second (u-t) (by omega)
private theorem terminal_prefix {N B t : Nat} (a : Config 7500 N B)
    (last : (SerializedBody.machine.run t a).state=SerializedBody.machine.reject)
    (first : ∀ u,u < t → 4 ≤ (SerializedBody.machine.run u a).state.val) :
    (∀ u,u ≤ t → (SerializedBody.machine.run u a).state≠SerializedBody.machine.accept) ∧
    (∀ u,u < t → (SerializedBody.machine.run u a).state≠SerializedBody.machine.reject ∧
      (SerializedBody.machine.run u a).state≠SerializedBody.done false ∧
      (SerializedBody.machine.run u a).state≠SerializedBody.done true) := by
  have before (u : Nat) (hu : u < t) (v : Fin 7500) (small : v.val < 4) : (SerializedBody.machine.run u a).state≠v := by
    intro eq
    have order:=first u hu
    rw [eq] at order;omega
  constructor
  · intro u hu
    by_cases eq : u=t
    · subst u;rw [last];exact SerializedBody.machine.accept_ne_reject.symm
    · exact before u (by omega) _ (by decide)
  · intro u hu
    exact ⟨before u hu _ (by decide),before u hu _ (by decide),before u hu _ (by decide)⟩
theorem zero_quota_body :
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
            ⟨done b,⟨H,hH⟩,fun i => image T F r n 0 W (S-min M S) size consumed (W-consumed) 0 i.val⟩ := by
  intro R S z n r W M Q source beta T hr hs _hg _hW _hell _ha
  dsimp only
  intro hq arena sourceCells ts reg tl installed th marks gap tf fit hH
  rw [zero_semantics]
  let F:=FixedRawLengthFence.fencePos R
  let L:=S+z+2
  let H:=L+n+1
  let P:=D F r n 12
  let B:=FixedRawLengthFence.allocation R
  let memory:=SerializedBody.prepared T S M F r n 0 W
  have sl : S < L := by dsimp only [L];omega
  have lh : L < H := by dsimp only [H];omega
  have ar : H+Q < F := arena
  have before : S < D F r n 0 := by change S < F+1;omega
  have same (i : Nat) (lo : S ≤ i) (hi : i < D F r n 0) : memory i=T i := prep_header T S M F r n 0 W i lo hi
  have installedSome:=beta_occupied T beta (show H=L+n+1 from rfl) installed
  obtain ⟨t,price,run,first⟩:=zero_quota_native (D F r n) memory S L H Q F M R B P source sl lh hq ar rfl
    (d_rise F r n) (d_mono F r n) (prep_blank T S M F r n 0 W before)
    (prep_cells T S M F r n 0 W before) le_rfl fit hH (quota_zero T S M F r n W before)
    (by rw [same S le_rfl before];exact ts)
    (by rw [same L (by omega) (by change L < F+1;omega)];exact tl)
    (by rw [same H (by omega) (by change H < F+1;omega)];exact th)
    (by rw [same F (by omega) (by change F < F+1;omega)];exact tf)
    (by intro i lo hi;rw [same i (by omega) (by change i < F+1;omega)];exact ⟨false,reg i lo hi⟩)
    (by intro i lo hi;rw [same i (by omega) (by change i < F+1;omega)];exact installedSome i lo hi)
    (by intro i lo hi;rw [same i (by omega) (by change i < F+1;omega)];exact marks i lo hi)
    (by intro i lo hi;rw [same i (by omega) (by change i < F+1;omega)];exact gap i lo hi)
    (by intro phys;simp only [memory,SerializedBody.prepared,phys,and_self,ite_true])
    (by intro i lo hi;change SerializedBody.prepared T S M F r n 0 W i=some (source ⟨i,hi⟩);rw [prep_below T S M F r n 0 W i (by change i < F+1;omega),if_neg (by omega : ¬(i=M ∧ i < S))];exact sourceCells i (by omega) hi)
  have atCursor : M < S → T M=some (padRead source M) := by
    intro phys
    simpa only [padRead,phys,↓reduceDIte] using sourceCells M le_rfl phys
  have post:=restored_image T memory S F r n 0 W (S-min M S) M source before atCursor
    (prep_exterior T S M F r n 0 W) (prep_blank T S M F r n 0 W before) (prep_fixed T S M F r n 0 W before)
  have finitePost : (fun i : Fin (tapeLength R B)=>restored memory (D F r n) source M i.val)=
      (fun i : Fin (tapeLength R B)=>SerializedBody.image T F r n 0 W (S-min M S) 0 0 0 0 i.val) := by
    funext i;exact congrFun post i.val
  change SerializedBody.machine.run t _=⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>restored memory (D F r n) source M i.val⟩ at run
  rw [finitePost] at run
  have last : (SerializedBody.machine.run t _).state=SerializedBody.machine.reject := congrArg Config.state run
  obtain ⟨noAccept,noEarly⟩:=terminal_prefix _ last first
  refine ⟨t,?_,noAccept,noEarly,run⟩
  apply phase_clock R S z n r Q t hr hs hq (by omega)
  change t ≤ 2048*(P+1)
  omega
private theorem empty_semantics (n g : Nat) (source : Fin S → Bool) (M : Nat) (beta : Fin n → Bool) :
    (do let (c,tail) ← decodeCircuitFull n (bitLength n) (SerializedBody.window source M 0)
        if c.size ≤ g then some ((c.size,c.eval beta),tail) else none)=none := by
  rfl
theorem zero_window_body :
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
            ⟨done b,⟨H,hH⟩,fun i => image T F r n g 0 (S-min M S) size consumed (0-consumed) 0 i.val⟩ := by
  intro R S z n r g M Q source beta T hr hs hg _hW hell ha
  dsimp only
  intro hq arena sourceCells ts reg tl installed th marks gap tf fit hH
  rw [empty_semantics]
  let F:=FixedRawLengthFence.fencePos R
  let L:=S+z+2
  let H:=L+n+1
  let d:=D F r n
  let P:=d 12
  let B:=FixedRawLengthFence.allocation R
  let memory:=SerializedBody.prepared T S M F r n g 0
  have sl : S < L := by dsimp only [L];omega
  have lh : L < H := by dsimp only [H];omega
  have ar : H+Q < F := arena
  have before : S < d 0 := by change S < F+1;omega
  have same (i : Nat) (lo : S ≤ i) (hi : i < d 0) : memory i=T i := prep_header T S M F r n g 0 i lo hi
  have lower : d 0 ≤ P := d_mono F r n 0 12 (by decide) (by decide)
  have h0 : d 0 < tapeLength R B := lt_of_le_of_lt lower fit
  by_cases zero : g=0
  · subst g
    exact zero_quota_body R S z n r 0 M Q source beta T hr hs hg _hW hell ha hq arena sourceCells ts reg tl installed th marks gap tf fit hH
  have positive : 0 < g := by omega
  have dr : ∀ j,j < 12 → d j < d (j+1) := d_rise F r n
  have dm : ∀ a b,a ≤ b → b ≤ 12 → d a ≤ d b := d_mono F r n
  have db:=prep_blank T S M F r n g 0 before
  have dc:=prep_cells T S M F r n g 0 before
  have quota (i : Nat) (lo : d 6 < i) (hi : i < d 7) : memory i=some (decide (i-d 6 ≤ g)) := by
    have dl:=dm 0 6 (by decide) (by decide)
    change SerializedBody.prepared T S M F r n g 0 i=_
    rw [prep_work T S M F r n g 0 i before (by change d 0 ≤ i;omega),image_value T F r n g 0 (S-min M S) 0 0 0 g 6 i (by decide) lo hi]
    rfl
  have nodes (i : Nat) (lo : d 5 < i) (hi : i < d 6) : memory i=some (decide (i-d 5 ≤ 0)) := by
    have dl:=dm 0 5 (by decide) (by decide)
    change SerializedBody.prepared T S M F r n g 0 i=_
    rw [prep_work T S M F r n g 0 i before (by change d 0 ≤ i;omega),image_value T F r n g 0 (S-min M S) 0 0 0 g 5 i (by decide) lo hi]
    rfl
  obtain ⟨entryRun,entryPrefix⟩:=entry_need (SerializedBody.sourceMode source M) memory H Q F R B P hq ar lower fit hH h0
    (by rw [same H (by omega) (by change H < F+1;omega)];exact th)
    (by rw [same F (by omega) (by change F < F+1;omega)];exact tf)
    (by intro i lo hi;rw [same i (by omega) (by change i < F+1;omega)];exact marks i lo hi)
    (by intro i lo hi;rw [same i (by omega) (by change i < F+1;omega)];exact gap i lo hi)
  obtain ⟨needPrice,needRun,needPrefix⟩:=need_get (SerializedBody.sourceMode source M) d memory r g 0 R B P dr dm db dc le_rfl fit h0 positive (by omega)
    (by dsimp only [d,D,SerializedBody.delimiter];omega) (by dsimp only [d,D,SerializedBody.delimiter];omega) quota nodes
  change SerializedBody.machine.run (F+2-H) _=⟨needEntry (SerializedBody.sourceMode source M),⟨d 0,h0⟩,fun i=>memory i.val⟩ at entryRun
  let ticks:=1+(2*(d 6-d 0+6)+2*g+4)+(2*(d 5-d 0+5)+2*0+4)+1
  let U : Nat → Option Bool:=fun i=>if i=d 5+0+1 then some true else if i=d 6+g then some false else memory i
  have p5 : d 5 < d 5+0+1 ∧ d 5+0+1 < d 6 := by
    have width : d 6=d 5+r+1 := by dsimp only [d,D,SerializedBody.delimiter];omega
    omega
  have p6 : d 6 < d 6+g ∧ d 6+g < d 7 := by
    have width : d 7=d 6+r+1 := by dsimp only [d,D,SerializedBody.delimiter];omega
    omega
  have unchanged (i : Nat) (a : ¬(d 5 < i ∧ i < d 6)) (b : ¬(d 6 < i ∧ i < d 7)) : U i=memory i := by
    have ne5 : i≠d 5+0+1 := by intro e;subst i;exact a p5
    have ne6 : i≠d 6+g := by intro e;subst i;exact b p6
    simp only [U,if_neg ne5,if_neg ne6]
  have uf (j i : Nat) (hj : j < 12) (j5 : j≠5) (j6 : j≠6) (lo : d j < i) (hi : i < d (j+1)) : U i=memory i :=
    unchanged i (disjoint dm hj (by decide) j5 ⟨lo,hi⟩) (disjoint dm hj (by decide) j6 ⟨lo,hi⟩)
  have lowSame (i : Nat) (hi : i < d 0) : U i=memory i := by
    have d5:=dm 0 5 (by decide) (by decide)
    have d6:=dm 0 6 (by decide) (by decide)
    apply unchanged i <;> omega
  have ub (j : Nat) (hj : j ≤ 12) : U (d j)=none := by
    have neq (k : Nat) (hk : k < 12) (i : Nat) (inside : d k < i ∧ i < d (k+1)) : d j≠i := by
      by_cases order : j ≤ k
      · have :=dm j k order (by omega);omega
      · have :=dm (k+1) j (by omega) hj;omega
    rw [show U (d j)=memory (d j) by simp only [U,if_neg (neq 5 (by decide) _ p5),if_neg (neq 6 (by decide) _ p6)]]
    exact db j hj
  have uc (j i : Nat) (hj : j < 12) (lo : d j < i) (hi : i < d (j+1)) : ∃ b,U i=some b := by
    by_cases eq5 : i=d 5+0+1
    · exact ⟨true,by simp only [U,if_pos eq5]⟩
    by_cases eq6 : i=d 6+g
    · exact ⟨false,by simp only [U,if_neg eq5,if_pos eq6]⟩
    obtain ⟨b,eq⟩:=dc j i hj lo hi
    exact ⟨b,by simp only [U,if_neg eq5,if_neg eq6];exact eq⟩
  have uHeader (i : Nat) (lo : S ≤ i) (hi : i < d 0) : U i=T i := by rw [lowSame i hi,same i lo hi]
  have remaining (i : Nat) (lo : d 4 < i) (hi : i < d 5) : U i=some false := by
    rw [uf 4 i (by decide) (by decide) (by decide) lo hi]
    have dl:=dm 0 4 (by decide) (by decide)
    change SerializedBody.prepared T S M F r n g 0 i=_
    rw [prep_work T S M F r n g 0 i before (by change d 0 ≤ i;omega),image_value T F r n g 0 (S-min M S) 0 0 0 g 4 i (by decide) lo hi]
    change some (decide (i-d 4 ≤ 0))=some false
    simp only [show ¬i-d 4 ≤ 0 by omega,decide_false]
  have consumed (i : Nat) (lo : d 11 < i) (hi : i < d 12) : U i=some (decide (i-d 11 ≤ 0)) := by
    rw [uf 11 i (by decide) (by decide) (by decide) lo hi]
    have dl:=dm 0 11 (by decide) (by decide)
    change SerializedBody.prepared T S M F r n g 0 i=_
    rw [prep_work T S M F r n g 0 i before (by change d 0 ≤ i;omega),image_value T F r n g 0 (S-min M S) 0 0 0 g 11 i (by decide) lo hi]
    rfl
  have installedSome:=beta_occupied T beta (show H=L+n+1 from rfl) installed
  obtain ⟨cleanTime,cleanPrice,cleanRun,cleanPrefix⟩:=exhausted_consumer ⟨0,by decide⟩ d U S L H Q F r 0 M R B P source (by omega) sl lh hq ar rfl dr dm ub uc
    (by dsimp only [d,D,SerializedBody.delimiter];omega) (by dsimp only [d,D,SerializedBody.delimiter];omega) remaining consumed le_rfl fit h0 hH
    (by rw [uHeader S le_rfl before];exact ts)
    (by rw [uHeader L (by omega) (by change L < F+1;omega)];exact tl)
    (by rw [uHeader H (by omega) (by change H < F+1;omega)];exact th)
    (by rw [uHeader F (by omega) (by change F < F+1;omega)];exact tf)
    (by intro i lo hi;rw [uHeader i (by omega) (by change i < F+1;omega)];exact ⟨false,reg i lo hi⟩)
    (by intro i lo hi;rw [uHeader i (by omega) (by change i < F+1;omega)];exact installedSome i lo hi)
    (by intro i lo hi;rw [uHeader i (by omega) (by change i < F+1;omega)];exact marks i lo hi)
    (by intro i lo hi;rw [uHeader i (by omega) (by change i < F+1;omega)];exact gap i lo hi)
    (by intro phys;rw [lowSame M (by omega)];simp only [memory,SerializedBody.prepared,phys,and_self,ite_true])
    (by intro i lo hi;rw [lowSame i (by omega)];change SerializedBody.prepared T S M F r n g 0 i=some (source ⟨i,hi⟩);rw [prep_below T S M F r n g 0 i (by change i < d 0;omega),if_neg (by omega : ¬(i=M ∧ i < S))];exact sourceCells i (by omega) hi)
  have atCursor : M < S → T M=some (padRead source M) := by
    intro phys
    simpa only [padRead,phys,↓reduceDIte] using sourceCells M le_rfl phys
  have outside (i : Nat) (out : i < d 0 ∨ d 12 < i) : U i=(if M < S ∧ i=M then none else T i) := by
    have d5:=dm 0 5 (by decide) (by decide)
    have d6:=dm 0 6 (by decide) (by decide)
    have e6:=dm 6 12 (by decide) (by decide)
    have e7:=dm 7 12 (by decide) (by decide)
    rw [unchanged i (by omega) (by omega)]
    exact prep_exterior T S M F r n g 0 i out
  have fixed (j : Nat) (mem : j∈[0,2,3,7]) (i : Nat) (lo : d j < i) (hi : i < d (j+1)) :
      U i=some (cellValue F r n g 0 (S-min M S) 0 0 0 0 j i) := by
    have not5 : j≠5 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at mem;omega
    have not6 : j≠6 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at mem;omega
    rw [uf j i (fixed_bound j mem) not5 not6 lo hi]
    exact prep_fixed T S M F r n g 0 before j mem i lo hi
  have post:=restored_image T U S F r n g 0 (S-min M S) M source before atCursor outside ub fixed
  have finitePost : (fun i : Fin (tapeLength R B)=>restored U d source M i.val)=
      (fun i : Fin (tapeLength R B)=>SerializedBody.image T F r n g 0 (S-min M S) 0 0 0 0 i.val) := by
    funext i;exact congrFun post i.val
  change SerializedBody.machine.run cleanTime _=⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>restored U d source M i.val⟩ at cleanRun
  rw [finitePost] at cleanRun
  have combined : SerializedBody.machine.run (F+2-H+ticks+cleanTime)
      (⟨SerializedBody.entry (SerializedBody.sourceMode source M),⟨H,hH⟩,fun i=>memory i.val⟩ : Config 7500 R B)=
      ⟨SerializedBody.machine.reject,⟨H,hH⟩,fun i=>SerializedBody.image T F r n g 0 (S-min M S) 0 0 0 0 i.val⟩ := by
    rw [SerializedBody.machine.run_add,SerializedBody.machine.run_add,entryRun]
    dsimp only [ticks]
    rw [needRun]
    exact cleanRun
  have afterEntry:=prefix_join needRun needPrefix cleanPrefix
  have first:=prefix_join entryRun entryPrefix afterEntry
  have allTime : F+2-H+(ticks+cleanTime)=F+2-H+ticks+cleanTime := by omega
  rw [allTime] at first
  obtain ⟨noAccept,noEarly⟩:=terminal_prefix _ (congrArg Config.state combined) first
  refine ⟨F+2-H+ticks+cleanTime,?_,noAccept,noEarly,combined⟩
  apply phase_clock R S z n r Q _ hr hs hq (by omega)
  change F+2-H+ticks+cleanTime ≤ 2048*(P+1)
  have fRoom : F+1 ≤ P := lower
  have entryPrice : F+2-H ≤ 2*(P+1) := by omega
  change ticks ≤ 128*(P+1) at needPrice
  omega
end SerializedBodyCompletion
