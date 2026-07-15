import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.OnlineCanonicalCutExtraction

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Information barrier for exact canonical-cut output

The trajectory-side canonicalizer ultimately returns one leftmost-minimum
offset for every full spatial bucket.  This file isolates an information
obstruction that is stronger than the earlier left-inverse bound for the
literal vector of all crossing counters: even the **decoded cut-offset
vector itself** can carry linearly many independent bits.

For a seed of `r` bits, use horizon `T = 6 * r` and bucket width `b = 2`.
In each of the first `r` buckets, one boundary has crossing count four and
the other has crossing count two.  Which boundary has the larger count is
the corresponding seed bit.  The canonical leftmost minimum is therefore
the opposite boundary and recovers that bit.  All later boundaries have
count zero.  Every profile has total crossing mass exactly `T`, all counts
are even, and below we also exhibit a legal nearest-neighbour boundary word
realizing it.

Consequently any finite terminal state from which all canonical offsets are
decoded exactly on this family has at least `2^r` states.  This does not rule
out a componentwise/unambiguous construction which guesses the offsets, a
streaming construction which emits information before the terminal state,
or a PRG/HSG which fools the aggregate without computing the offsets.  It
does rule out the proposed generic shortcut "retain a small terminal
sufficient statistic and then recover every exact canonical cut".
-/

/-! ## The explicit paired crossing profiles -/

/-- Encode one bit as the boundary in a two-boundary bucket which receives
the two extra crossings. -/
def pairedSelectedOffset (bit : Bool) : Fin 2 :=
  if bit then 1 else 0

/-- The other boundary is the unique minimum in the paired profile. -/
def pairedMinimumOffset (bit : Bool) : Fin 2 :=
  if bit then 0 else 1

/-- One two-boundary bucket: the selected coordinate has count four and the
other coordinate has count two. -/
def pairedBucketCrossingCount {r : Nat} (seed : Fin r -> Bool)
    (bucket : Fin r) (offset : Fin 2) : Nat :=
  if offset = pairedSelectedOffset (seed bucket) then 4 else 2

/-- Extend the paired profiles to every boundary below `T = 6*r`.  The first
`2*r` boundaries form the `r` informative buckets; the remaining coordinates
are zero. -/
def pairedCrossingProfile {r : Nat} (seed : Fin r -> Bool) :
    Fin (6 * r) -> Nat :=
  fun boundary =>
    if hbucket : boundary.val / 2 < r then
      pairedBucketCrossingCount seed
        ⟨boundary.val / 2, hbucket⟩
        ⟨boundary.val % 2, Nat.mod_lt _ (by omega)⟩
    else 0

/-- Embed one informative bucket into the full family of buckets at horizon
`6*r` and width two. -/
def pairedFullBucket {r : Nat} (bucket : Fin r) : Fin ((6 * r) / 2) :=
  ⟨bucket.val, by omega⟩

@[simp]
theorem pairedBucketCrossingCount_zero {r : Nat}
    (seed : Fin r -> Bool) (bucket : Fin r) :
    pairedBucketCrossingCount seed bucket 0 =
      if seed bucket then 2 else 4 := by
  cases h : seed bucket <;>
    simp [pairedBucketCrossingCount, pairedSelectedOffset, h]

@[simp]
theorem pairedBucketCrossingCount_one {r : Nat}
    (seed : Fin r -> Bool) (bucket : Fin r) :
    pairedBucketCrossingCount seed bucket 1 =
      if seed bucket then 4 else 2 := by
  cases h : seed bucket <;>
    simp [pairedBucketCrossingCount, pairedSelectedOffset, h]

/-- On the embedded informative bucket, the global profile is exactly the
two-coordinate paired profile. -/
theorem pairedCrossingProfile_fullBucket {r : Nat}
    (seed : Fin r -> Bool) (bucket : Fin r) (offset : Fin 2) :
    pairedCrossingProfile seed
        (fullBucketBoundary (pairedFullBucket bucket) offset) =
      pairedBucketCrossingCount seed bucket offset := by
  have hval :
      (fullBucketBoundary (pairedFullBucket bucket) offset).val =
        bucket.val * 2 + offset.val := by
    simp [pairedFullBucket, fullBucketBoundary]
  have hdiv : (bucket.val * 2 + offset.val) / 2 = bucket.val := by
    have hoffset := offset.isLt
    omega
  have hmod : (bucket.val * 2 + offset.val) % 2 = offset.val := by
    have hoffset := offset.isLt
    omega
  unfold pairedCrossingProfile
  rw [dif_pos]
  · congr 2
  · change (bucket.val * 2 + offset.val) / 2 < r
    rw [hdiv]
    exact bucket.isLt

/-- The exact leftmost canonical minimum in an informative bucket is the
coordinate opposite the encoded bit. -/
theorem canonicalBoundaryOffset_pairedCrossingProfile {r : Nat}
    (seed : Fin r -> Bool) (bucket : Fin r) :
    canonicalBoundaryOffset (by omega : 0 < 2) (pairedCrossingProfile seed)
        (pairedFullBucket bucket) =
      pairedMinimumOffset (seed bucket) := by
  symm
  apply
    (advertisedCutOffsetIsLeftmostMinimum_iff_eq_canonicalBoundaryOffset
      (by omega : 0 < 2) (pairedCrossingProfile seed)
      (pairedFullBucket bucket) (pairedMinimumOffset (seed bucket))).1
  constructor
  · intro candidate
    fin_cases candidate <;> cases h : seed bucket <;>
      simp [pairedMinimumOffset, h, pairedCrossingProfile_fullBucket]
  · intro candidate htie
    fin_cases candidate <;> cases h : seed bucket <;>
      simp [pairedMinimumOffset, h, pairedCrossingProfile_fullBucket] at htie ⊢

/-- The complete canonical cut vector associated to the explicit profile. -/
noncomputable def pairedCanonicalCutOffsets {r : Nat} (seed : Fin r -> Bool) :
    CanonicalCutOffsets (6 * r) 2 :=
  fun bucket =>
    canonicalBoundaryOffset (by omega : 0 < 2)
      (pairedCrossingProfile seed) bucket

/-- The informative projection of the canonical cut vector recovers the
opposite of every seed bit. -/
@[simp]
theorem pairedCanonicalCutOffsets_informative {r : Nat}
    (seed : Fin r -> Bool) (bucket : Fin r) :
    pairedCanonicalCutOffsets seed (pairedFullBucket bucket) =
      pairedMinimumOffset (seed bucket) :=
  canonicalBoundaryOffset_pairedCrossingProfile seed bucket

/-- The two possible minimum offsets distinguish the two Boolean values. -/
theorem pairedMinimumOffset_injective :
    Function.Injective pairedMinimumOffset := by
  intro left right h
  cases left <;> cases right <;> simp [pairedMinimumOffset] at h ⊢

/-- Hence the exact canonical cut vectors contain all `r` seed bits. -/
theorem pairedCanonicalCutOffsets_injective (r : Nat) :
    Function.Injective
      (pairedCanonicalCutOffsets : (Fin r -> Bool) ->
        CanonicalCutOffsets (6 * r) 2) := by
  intro left right hOffsets
  funext bucket
  apply pairedMinimumOffset_injective
  rw [← pairedCanonicalCutOffsets_informative left bucket,
    ← pairedCanonicalCutOffsets_informative right bucket, hOffsets]

/-! ## Terminal-state lower bounds -/

/-- Any exact finite encoding of these canonical cut vectors needs at least
`2^r` terminal states.  The decoder is required to work only on the explicit
paired family, not on arbitrary counter vectors. -/
theorem two_pow_le_card_of_recovers_pairedCanonicalCutOffsets
    (r : Nat) (State : Type) [Fintype State]
    (encode : (Fin r -> Bool) -> State)
    (decode : State -> CanonicalCutOffsets (6 * r) 2)
    (hdecode : ∀ seed, decode (encode seed) = pairedCanonicalCutOffsets seed) :
    2 ^ r ≤ Fintype.card State := by
  have hInjective : Function.Injective encode := by
    intro left right hState
    apply pairedCanonicalCutOffsets_injective r
    rw [← hdecode left, ← hdecode right, hState]
  simpa using Fintype.card_le_of_injective encode hInjective

/-- A left-inverse formulation when the terminal state is intended to decode
the seed itself. -/
theorem two_pow_le_card_of_recovers_pairedSeed
    (r : Nat) (State : Type) [Fintype State]
    (encode : (Fin r -> Bool) -> State)
    (decode : State -> (Fin r -> Bool))
    (hleft : Function.LeftInverse decode encode) :
    2 ^ r ≤ Fintype.card State := by
  simpa using Fintype.card_le_of_injective encode hleft.injective

/-! ## Realization by legal nearest-neighbour work-head moves -/

/-- `LegalBoundaryWord start word stop` means that a nearest-neighbour head
starting at `start` can cross the listed boundaries, in order, and finish at
`stop`.  Crossing boundary `j` means moving between cells `j` and `j+1`.
Thus the relation records exactly the information counted by
`CrossesWorkBoundary`, while forgetting tape symbols and control states. -/
inductive LegalBoundaryWord : Nat -> List Nat -> Nat -> Prop where
  | nil (head : Nat) : LegalBoundaryWord head [] head
  | right {head stop : Nat} {tail : List Nat}
      (hTail : LegalBoundaryWord (head + 1) tail stop) :
      LegalBoundaryWord head (head :: tail) stop
  | left {boundary stop : Nat} {tail : List Nat}
      (hTail : LegalBoundaryWord boundary tail stop) :
      LegalBoundaryWord (boundary + 1) (boundary :: tail) stop

/-- Legal boundary words compose chronologically. -/
theorem LegalBoundaryWord.append
    {start middle stop : Nat} {firstWord secondWord : List Nat}
    (hPrefix : LegalBoundaryWord start firstWord middle)
    (hSuffix : LegalBoundaryWord middle secondWord stop) :
    LegalBoundaryWord start (firstWord ++ secondWord) stop := by
  induction hPrefix with
  | nil => simpa using hSuffix
  | right hTail ih => exact .right (ih hSuffix)
  | left hTail ih => exact .left (ih hSuffix)

/-- The increasing word `0,1,...,n-1` is the monotone walk from zero to `n`. -/
theorem legalBoundaryWord_range (n : Nat) :
    LegalBoundaryWord 0 (List.range n) n := by
  induction n with
  | zero => exact .nil 0
  | succ n ih =>
      rw [List.range_succ]
      exact ih.append (.right (.nil (n + 1)))

/-- Four crossings which descend across the two-boundary bucket `bucket`.
If `bit` is false the lower boundary is crossed three times; if it is true
the upper boundary is crossed three times.  The other boundary is crossed
once. -/
def pairedDescentChunk (bit : Bool) (bucket : Nat) : List Nat :=
  let lower := 2 * bucket
  if bit then
    [lower + 1, lower + 1, lower + 1, lower]
  else
    [lower + 1, lower, lower, lower]

@[simp]
theorem length_pairedDescentChunk (bit : Bool) (bucket : Nat) :
    (pairedDescentChunk bit bucket).length = 4 := by
  cases bit <;> rfl

/-- Each paired chunk is a legal walk from the right edge of its bucket to
the left edge. -/
theorem legalBoundaryWord_pairedDescentChunk (bit : Bool) (bucket : Nat) :
    LegalBoundaryWord (2 * (bucket + 1))
      (pairedDescentChunk bit bucket) (2 * bucket) := by
  let lower := 2 * bucket
  have hFalse :
      LegalBoundaryWord ((lower + 1) + 1)
        [lower + 1, lower + 1, lower + 1, lower] lower :=
    .left (.right (.left (.left (.nil lower))))
  have hTrue :
      LegalBoundaryWord ((lower + 1) + 1)
        [lower + 1, lower, lower, lower] lower :=
    .left (.left (.right (.left (.nil lower))))
  cases bit
  · simpa [pairedDescentChunk, lower] using hTrue
  · simpa [pairedDescentChunk, lower] using hFalse

/-- Process paired buckets from right to left. -/
def pairedDescentBoundaryWord (bits : Nat -> Bool) : Nat -> List Nat
  | 0 => []
  | bucketCount + 1 =>
      pairedDescentChunk (bits bucketCount) bucketCount ++
        pairedDescentBoundaryWord bits bucketCount

@[simp]
theorem length_pairedDescentBoundaryWord (bits : Nat -> Bool) (r : Nat) :
    (pairedDescentBoundaryWord bits r).length = 4 * r := by
  induction r with
  | zero => simp [pairedDescentBoundaryWord]
  | succ r ih =>
      simp [pairedDescentBoundaryWord, ih]
      omega

/-- The full descending word is a legal return from cell `2*r` to zero. -/
theorem legalBoundaryWord_pairedDescentBoundaryWord
    (bits : Nat -> Bool) (r : Nat) :
    LegalBoundaryWord (2 * r) (pairedDescentBoundaryWord bits r) 0 := by
  induction r with
  | zero => exact .nil 0
  | succ r ih =>
      exact (legalBoundaryWord_pairedDescentChunk (bits r) r).append ih

/-- Read a finite seed as a total function, using `false` only outside its
typed domain. -/
def pairedSeedBitAt {r : Nat} (seed : Fin r -> Bool) (index : Nat) : Bool :=
  if h : index < r then seed ⟨index, h⟩ else false

@[simp]
theorem pairedSeedBitAt_apply {r : Nat} (seed : Fin r -> Bool)
    (index : Fin r) : pairedSeedBitAt seed index.val = seed index := by
  simp [pairedSeedBitAt, index.isLt]

/-- Ascend across all `2*r` informative boundaries, then execute the paired
bounces while descending. -/
def pairedBounceBoundaryWord {r : Nat} (seed : Fin r -> Bool) : List Nat :=
  List.range (2 * r) ++ pairedDescentBoundaryWord (pairedSeedBitAt seed) r

/-- Every paired word has exactly `T = 6*r` boundary crossings. -/
@[simp]
theorem length_pairedBounceBoundaryWord {r : Nat} (seed : Fin r -> Bool) :
    (pairedBounceBoundaryWord seed).length = 6 * r := by
  simp [pairedBounceBoundaryWord]
  omega

/-- The paired word is an actual closed nearest-neighbour head trajectory. -/
theorem legalBoundaryWord_pairedBounceBoundaryWord {r : Nat}
    (seed : Fin r -> Bool) :
    LegalBoundaryWord 0 (pairedBounceBoundaryWord seed) 0 := by
  exact (legalBoundaryWord_range (2 * r)).append
    (legalBoundaryWord_pairedDescentBoundaryWord (pairedSeedBitAt seed) r)

/-! The remaining lemmas identify occurrence counts in this legal word with
the paired profile used above. -/

/-- Every boundary mentioned during the descending phase belongs to one of
the first `r` two-boundary buckets. -/
theorem mem_pairedDescentBoundaryWord_lt
    (bits : Nat -> Bool) (r boundary : Nat)
    (hmem : boundary ∈ pairedDescentBoundaryWord bits r) :
    boundary < 2 * r := by
  induction r with
  | zero => simp [pairedDescentBoundaryWord] at hmem
  | succ r ih =>
      simp only [pairedDescentBoundaryWord, List.mem_append] at hmem
      rcases hmem with hchunk | htail
      · cases h : bits r <;>
          simp [pairedDescentChunk, h] at hchunk <;> omega
      · exact (ih htail).trans_le (by omega)

/-- Exact occurrence count of either boundary inside its own four-crossing
chunk. -/
theorem count_pairedDescentChunk (bit : Bool) (bucket : Nat)
    (offset : Fin 2) :
    List.count (2 * bucket + offset.val) (pairedDescentChunk bit bucket) =
      if offset = pairedSelectedOffset bit then 3 else 1 := by
  cases bit <;> fin_cases offset <;>
    simp [pairedDescentChunk, pairedSelectedOffset]

/-- A boundary belonging to bucket `bucket < r` occurs only in that bucket's
descending chunk, with the exact count above. -/
theorem count_pairedDescentBoundaryWord_at
    (bits : Nat -> Bool) {bucket r : Nat} (hbucket : bucket < r)
    (offset : Fin 2) :
    List.count (2 * bucket + offset.val)
        (pairedDescentBoundaryWord bits r) =
      if offset = pairedSelectedOffset (bits bucket) then 3 else 1 := by
  induction r with
  | zero => omega
  | succ r ih =>
      simp only [pairedDescentBoundaryWord, List.count_append]
      by_cases htop : bucket = r
      · subst bucket
        rw [count_pairedDescentChunk]
        have hzero :
            List.count (2 * r + offset.val)
                (pairedDescentBoundaryWord bits r) = 0 := by
          apply List.count_eq_zero.2
          intro hmem
          have hlt := mem_pairedDescentBoundaryWord_lt bits r
            (2 * r + offset.val) hmem
          omega
        rw [hzero]
        omega
      · have hlt : bucket < r := by omega
        have htopZero :
            List.count (2 * bucket + offset.val)
                (pairedDescentChunk (bits r) r) = 0 := by
          apply List.count_eq_zero.2
          intro hmem
          cases hbit : bits r <;>
            simp [pairedDescentChunk, hbit] at hmem <;>
            have hoffset := offset.isLt <;> omega
        rw [htopZero, ih hlt]
        simp

/-- Every boundary in the complete ascent-and-descent word is informative:
it lies below `2*r`. -/
theorem mem_pairedBounceBoundaryWord_lt {r : Nat}
    (seed : Fin r -> Bool) (boundary : Nat)
    (hmem : boundary ∈ pairedBounceBoundaryWord seed) :
    boundary < 2 * r := by
  simp only [pairedBounceBoundaryWord, List.mem_append] at hmem
  rcases hmem with hrange | hdescent
  · simpa using (List.mem_range.mp hrange)
  · exact mem_pairedDescentBoundaryWord_lt
      (pairedSeedBitAt seed) r boundary hdescent

/-- In the legal word, the two physical boundaries of every informative
bucket have exactly the counts specified by `pairedBucketCrossingCount`. -/
theorem count_pairedBounceBoundaryWord_fullBucket {r : Nat}
    (seed : Fin r -> Bool) (bucket : Fin r) (offset : Fin 2) :
    List.count (2 * bucket.val + offset.val)
        (pairedBounceBoundaryWord seed) =
      pairedBucketCrossingCount seed bucket offset := by
  rw [pairedBounceBoundaryWord, List.count_append]
  have hmemRange : 2 * bucket.val + offset.val ∈ List.range (2 * r) := by
    rw [List.mem_range]
    have hoffset := offset.isLt
    have hbucket := bucket.isLt
    omega
  have hRange :
      List.count (2 * bucket.val + offset.val) (List.range (2 * r)) = 1 :=
    List.count_eq_one_of_mem List.nodup_range hmemRange
  rw [hRange,
    count_pairedDescentBoundaryWord_at (pairedSeedBitAt seed) bucket.isLt]
  rw [pairedSeedBitAt_apply]
  cases hbit : seed bucket <;> fin_cases offset <;>
    simp [pairedBucketCrossingCount, pairedSelectedOffset, hbit]

/-- The occurrence profile of the exhibited legal word is extensionally the
synthetic profile used by the canonical-cut lower bound. -/
theorem count_pairedBounceBoundaryWord_eq_pairedCrossingProfile {r : Nat}
    (seed : Fin r -> Bool) (boundary : Fin (6 * r)) :
    List.count boundary.val (pairedBounceBoundaryWord seed) =
      pairedCrossingProfile seed boundary := by
  unfold pairedCrossingProfile
  split_ifs with hbucket
  · let bucket : Fin r := ⟨boundary.val / 2, hbucket⟩
    let offset : Fin 2 :=
      ⟨boundary.val % 2, Nat.mod_lt _ (by omega)⟩
    have hdecomp : boundary.val = 2 * bucket.val + offset.val := by
      dsimp only [bucket, offset]
      omega
    have hcount :
        List.count boundary.val (pairedBounceBoundaryWord seed) =
          pairedBucketCrossingCount seed bucket offset := by
      rw [hdecomp]
      exact count_pairedBounceBoundaryWord_fullBucket seed bucket offset
    simpa [bucket, offset] using hcount
  · have hge : 2 * r ≤ boundary.val := by
      have hmod := Nat.mod_lt boundary.val (by omega : 0 < 2)
      omega
    apply List.count_eq_zero.2
    intro hmem
    exact (Nat.not_lt_of_ge hge)
      (mem_pairedBounceBoundaryWord_lt seed boundary.val hmem)

/-- Decode canonical offsets directly from the crossing multiplicities of a
boundary word. -/
noncomputable def canonicalCutOffsetsOfBoundaryWord {T b : Nat}
    (hb : 0 < b) (word : List Nat) : CanonicalCutOffsets T b :=
  fun bucket =>
    canonicalBoundaryOffset hb
      (fun boundary : Fin T => List.count boundary.val word) bucket

/-- On the explicit legal words, direct decoding from word multiplicities is
exactly the paired canonical vector used in the injectivity proof. -/
theorem canonicalCutOffsetsOfBoundaryWord_pairedBounce {r : Nat}
    (seed : Fin r -> Bool) :
    canonicalCutOffsetsOfBoundaryWord (by omega : 0 < 2)
        (pairedBounceBoundaryWord seed) =
      pairedCanonicalCutOffsets seed := by
  have hProfile :
      (fun boundary : Fin (6 * r) =>
        List.count boundary.val (pairedBounceBoundaryWord seed)) =
        pairedCrossingProfile seed := by
    funext boundary
    exact count_pairedBounceBoundaryWord_eq_pairedCrossingProfile seed boundary
  unfold canonicalCutOffsetsOfBoundaryWord pairedCanonicalCutOffsets
  rw [hProfile]

/-- **Exact-output information barrier on legal trajectories.**  A finite
terminal state which exactly recovers every canonical cut vector even on the
explicit closed nearest-neighbour family has at least `2^r` states. -/
theorem two_pow_le_card_of_recovers_legal_pairedBoundaryWords
    (r : Nat) (State : Type) [Fintype State]
    (encode : (Fin r -> Bool) -> State)
    (decode : State -> CanonicalCutOffsets (6 * r) 2)
    (hdecode : ∀ seed,
      decode (encode seed) =
        canonicalCutOffsetsOfBoundaryWord (by omega : 0 < 2)
          (pairedBounceBoundaryWord seed)) :
    2 ^ r ≤ Fintype.card State := by
  apply two_pow_le_card_of_recovers_pairedCanonicalCutOffsets
    r State encode decode
  intro seed
  rw [hdecode, canonicalCutOffsetsOfBoundaryWord_pairedBounce]

/-- If the terminal carrier is explicitly `s` bits, exact recovery on the
legal paired family forces at least `r` bits.  Since the common horizon is
`T = 6*r`, this is a linear-in-time terminal-memory lower bound. -/
theorem bitBudget_of_recovers_legal_pairedBoundaryWords
    (r s : Nat)
    (encode : (Fin r -> Bool) -> Fin (2 ^ s))
    (decode : Fin (2 ^ s) -> CanonicalCutOffsets (6 * r) 2)
    (hdecode : ∀ seed,
      decode (encode seed) =
        canonicalCutOffsetsOfBoundaryWord (by omega : 0 < 2)
          (pairedBounceBoundaryWord seed)) :
    r ≤ s := by
  have hCard := two_pow_le_card_of_recovers_legal_pairedBoundaryWords
    r (Fin (2 ^ s)) encode decode hdecode
  simp only [Fintype.card_fin] at hCard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 hCard

/-- The same bit-budget conclusion for an arbitrary finite carrier whose
cardinality is bounded by `2^s`. -/
theorem bitBudget_of_card_le_two_pow_of_recovers_legal_pairedBoundaryWords
    (r s : Nat) (State : Type) [Fintype State]
    (hStateCard : Fintype.card State ≤ 2 ^ s)
    (encode : (Fin r -> Bool) -> State)
    (decode : State -> CanonicalCutOffsets (6 * r) 2)
    (hdecode : ∀ seed,
      decode (encode seed) =
        canonicalCutOffsetsOfBoundaryWord (by omega : 0 < 2)
          (pairedBounceBoundaryWord seed)) :
    r ≤ s := by
  have hLower := two_pow_le_card_of_recovers_legal_pairedBoundaryWords
    r State encode decode hdecode
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1
    (hLower.trans hStateCard)

end OneTapeMagnification
end Frontier
end Pnp4
