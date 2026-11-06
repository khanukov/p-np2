import Pnp4.Frontier.ContractExpansion.PrefixParserConvention

/-!
# Cap-aware natural arithmetic for virtual content parsing

Addition and multiplication guard before constructing their results. `checkedPow`
uses one recursive call at exponent `e / 2`; it does not recurse through every
predecessor. These are source-level exactness contracts, not machine-cost claims.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

/-! ## Primitive cap-aware arithmetic -/
/-- Return `x` exactly when it is at most `B`. -/
def checkedNat (B x : Nat) : Option Nat :=
  if _h : x ≤ B then some x else none
@[simp] theorem checkedNat_eq_some_iff (B x y : Nat) :
    checkedNat B x = some y ↔ y = x ∧ x ≤ B := by
  unfold checkedNat
  by_cases h : x ≤ B <;> simp [h, eq_comm]
@[simp] theorem checkedNat_eq_none_iff (B x : Nat) :
    checkedNat B x = none ↔ B < x := by
  unfold checkedNat
  by_cases h : x ≤ B
  · simp [h]
  · simp [h]
    omega
/--
Checked addition.  The sum is constructed only after the subtraction guard
has established that it fits.
-/
def checkedAdd (B a b : Nat) : Option Nat :=
  if _h : a ≤ B ∧ b ≤ B - a then some (a + b) else none
@[simp] theorem checkedAdd_eq_some_iff (B a b c : Nat) :
    checkedAdd B a b = some c ↔ c = a + b ∧ a + b ≤ B := by
  unfold checkedAdd
  by_cases h : a ≤ B ∧ b ≤ B - a
  · have hab : a + b ≤ B := by omega
    simp [h, hab, eq_comm]
  · have hab : ¬ a + b ≤ B := by
      intro hab
      apply h
      omega
    simp [h, hab]
@[simp] theorem checkedAdd_eq_none_iff (B a b : Nat) :
    checkedAdd B a b = none ↔ B < a + b := by
  unfold checkedAdd
  by_cases h : a ≤ B ∧ b ≤ B - a
  · have hab : a + b ≤ B := by omega
    simp [h, hab]
  · have hab : ¬ a + b ≤ B := by
      intro hab
      apply h
      omega
    have hover : B < a + b := Nat.lt_of_not_ge hab
    simp [h, hover]
private theorem mul_le_cap_iff_le_div
    {B a b : Nat} (ha : a ≠ 0) :
    a * b ≤ B ↔ b ≤ B / a := by
  have hapos : 0 < a := Nat.pos_of_ne_zero ha
  rw [Nat.le_div_iff_mul_le hapos]
  simp [Nat.mul_comm]
/-- Zero-safe multiplication, guarded by division before product construction. -/
def checkedMul (B a b : Nat) : Option Nat :=
  if _ha : a = 0 then
    some 0
  else if _hb : b = 0 then
    some 0
  else if _h : b ≤ B / a then
    some (a * b)
  else
    none
@[simp] theorem checkedMul_eq_some_iff (B a b c : Nat) :
    checkedMul B a b = some c ↔ c = a * b ∧ a * b ≤ B := by
  unfold checkedMul
  by_cases ha : a = 0
  · subst a
    simp [eq_comm]
  · by_cases hb : b = 0
    · subst b
      simp [ha, eq_comm]
    · have hguard := mul_le_cap_iff_le_div (B := B) (a := a) (b := b) ha
      by_cases hle : b ≤ B / a
      · have hp : a * b ≤ B := hguard.mpr hle
        simp [ha, hb, hle, hp, eq_comm]
      · have hp : ¬ a * b ≤ B := by
          intro hp
          exact hle (hguard.mp hp)
        simp [ha, hb, hle, hp]
@[simp] theorem checkedMul_eq_none_iff (B a b : Nat) :
    checkedMul B a b = none ↔ B < a * b := by
  unfold checkedMul
  by_cases ha : a = 0
  · subst a
    simp
  · by_cases hb : b = 0
    · subst b
      simp [ha]
    · have hguard := mul_le_cap_iff_le_div (B := B) (a := a) (b := b) ha
      by_cases hle : b ≤ B / a
      · have hp : a * b ≤ B := hguard.mpr hle
        simp [ha, hb, hle, hp]
      · have hp : ¬ a * b ≤ B := by
          intro hp
          exact hle (hguard.mp hp)
        have hover : B < a * b := Nat.lt_of_not_ge hp
        simp [ha, hb, hle, hover]
private theorem pow_eq_half_square_of_mod_two_eq_zero
    (a e : Nat) (heven : e % 2 = 0) :
    a ^ e = a ^ (e / 2) * a ^ (e / 2) := by
  have hdiv : e % 2 + 2 * (e / 2) = e := Nat.mod_add_div e 2
  have hexp : e = e / 2 + e / 2 := by omega
  calc
    a ^ e = a ^ (e / 2 + e / 2) :=
      congrArg (fun t : Nat => a ^ t) hexp
    _ = a ^ (e / 2) * a ^ (e / 2) :=
      pow_add a (e / 2) (e / 2)
private theorem pow_eq_half_square_mul_of_mod_two_ne_zero
    (a e : Nat) (hodd : e % 2 ≠ 0) :
    a ^ e = (a ^ (e / 2) * a ^ (e / 2)) * a := by
  have hdiv : e % 2 + 2 * (e / 2) = e := Nat.mod_add_div e 2
  have hmodlt : e % 2 < 2 := Nat.mod_lt e (by omega)
  have hexp : e = (e / 2 + e / 2) + 1 := by omega
  calc
    a ^ e = a ^ ((e / 2 + e / 2) + 1) :=
      congrArg (fun t : Nat => a ^ t) hexp
    _ = a ^ (e / 2 + e / 2) * a ^ 1 :=
      pow_add a (e / 2 + e / 2) 1
    _ = (a ^ (e / 2) * a ^ (e / 2)) * a ^ 1 :=
      congrArg (fun x : Nat => x * a ^ 1)
        (pow_add a (e / 2) (e / 2))
    _ = (a ^ (e / 2) * a ^ (e / 2)) * a :=
      congrArg (fun x : Nat =>
        (a ^ (e / 2) * a ^ (e / 2)) * x) (pow_one a)
/--
Cap-aware exponentiation by squaring.  The only recursive call is at `e / 2`;
there is no recursion through all predecessors of `e`.
-/
def checkedPow (B a e : Nat) : Option Nat :=
  if _he : e = 0 then
    checkedNat B 1
  else if _ha : a = 0 then
    some 0
  else
    match checkedPow B a (e / 2) with
    | none => none
    | some half =>
        match checkedMul B half half with
        | none => none
        | some square =>
            if _hEven : e % 2 = 0 then
              some square
            else
              checkedMul B square a
termination_by e
decreasing_by omega
/-- The recursive exponent is strictly smaller in every recursive branch. -/
theorem checkedPow_recursiveArgument_lt {e : Nat} (he : e ≠ 0) :
    e / 2 < e := by
  omega
@[simp] theorem checkedPow_eq_some_iff (B a e r : Nat) :
    checkedPow B a e = some r ↔ r = a ^ e ∧ a ^ e ≤ B := by
  induction e using Nat.strong_induction_on generalizing r with
  | h e ih =>
      by_cases he : e = 0
      · subst e
        rw [checkedPow]
        simp
      by_cases ha : a = 0
      · unfold checkedPow
        simp [he, ha, eq_comm]
      rw [checkedPow]
      simp only [he, ha, ↓reduceDIte]
      have hlt : e / 2 < e := checkedPow_recursiveArgument_lt he
      have hbase : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
      have hhalf_le : a ^ (e / 2) ≤ a ^ e :=
        Nat.pow_le_pow_right hbase (by omega)
      cases hrec : checkedPow B a (e / 2) with
      | none =>
          have hhalf_not : ¬ a ^ (e / 2) ≤ B := by
            intro hcap
            have hs := (ih (e / 2) hlt (a ^ (e / 2))).mpr
              ⟨rfl, hcap⟩
            rw [hrec] at hs
            contradiction
          have hpow_not : ¬ a ^ e ≤ B := by
            intro hcap
            exact hhalf_not (le_trans hhalf_le hcap)
          simp [hpow_not]
      | some half =>
          have hhalf := (ih (e / 2) hlt half).mp hrec
          rcases hhalf with ⟨rfl, hhalf_cap⟩
          simp only
          cases hsquare : checkedMul B (a ^ (e / 2)) (a ^ (e / 2)) with
          | none =>
              have hover : B < a ^ (e / 2) * a ^ (e / 2) :=
                (checkedMul_eq_none_iff
                  B (a ^ (e / 2)) (a ^ (e / 2))).mp hsquare
              by_cases hparity : e % 2 = 0
              · have hpow :=
                  pow_eq_half_square_of_mod_two_eq_zero a e hparity
                have hpow_not : ¬ a ^ e ≤ B := by omega
                simp [hpow_not]
              · have hpow :=
                  pow_eq_half_square_mul_of_mod_two_ne_zero a e hparity
                have hsquare_le_pow :
                    a ^ (e / 2) * a ^ (e / 2) ≤ a ^ e := by
                  rw [hpow]
                  calc
                    a ^ (e / 2) * a ^ (e / 2) =
                        (a ^ (e / 2) * a ^ (e / 2)) * 1 := by simp
                    _ ≤ (a ^ (e / 2) * a ^ (e / 2)) * a :=
                      Nat.mul_le_mul_left _ hbase
                have hpow_not : ¬ a ^ e ≤ B := by
                  intro hcap
                  omega
                simp [hpow_not]
          | some square =>
              have hsquare_spec :=
                (checkedMul_eq_some_iff
                  B (a ^ (e / 2)) (a ^ (e / 2)) square).mp hsquare
              rcases hsquare_spec with ⟨rfl, hsquare_cap⟩
              by_cases hparity : e % 2 = 0
              · have hpow :=
                  pow_eq_half_square_of_mod_two_eq_zero a e hparity
                simp [hparity.symm, hpow, hsquare_cap, eq_comm]
              · have hpow :=
                  pow_eq_half_square_mul_of_mod_two_ne_zero a e hparity
                simp only [hparity, ↓reduceDIte]
                simp [hpow]
@[simp] theorem checkedPow_eq_none_iff (B a e : Nat) :
    checkedPow B a e = none ↔ B < a ^ e := by
  constructor
  · intro hnone
    by_contra hnot
    have hcap : a ^ e ≤ B := Nat.le_of_not_gt hnot
    have hsome := (checkedPow_eq_some_iff B a e (a ^ e)).mpr
      ⟨rfl, hcap⟩
    rw [hnone] at hsome
    contradiction
  · intro hover
    cases hrun : checkedPow B a e with
    | none => rfl
    | some r =>
        have hspec := (checkedPow_eq_some_iff B a e r).mp hrun
        exact False.elim ((Nat.not_le_of_lt hover) hspec.2)
/-- Cap-aware binary length.  No operation-cost theorem is asserted here. -/
def checkedBitLength (B n : Nat) : Option Nat :=
  checkedNat B (bitLength n)
@[simp] theorem checkedBitLength_eq_some_iff (B n width : Nat) :
    checkedBitLength B n = some width ↔
      width = bitLength n ∧ bitLength n ≤ B := by
  simp [checkedBitLength]
@[simp] theorem checkedBitLength_eq_none_iff (B n : Nat) :
    checkedBitLength B n = none ↔ B < bitLength n := by
  simp [checkedBitLength]

end ContractExpansion
end Frontier
end Pnp4
