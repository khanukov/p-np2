import Mathlib.Data.Nat.Log
import Core.BooleanBasics
import Core.ShrinkageWitness
import AC0.Formulas

/-!
  pnp3/ThirdPartyFacts/AC0Witness.lean

  This module factors out the bookkeeping needed to talk about partial
  shrinkage certificates for AC⁰ families.  The original implementation lived
  directly inside `Facts_Switching.lean`; we keep the very same API but split it
  out so that higher-level files (most notably `Core/ShrinkageAC0`) can depend on
  these declarations without triggering circular imports.

  The definitions in this file are purely combinatorial: we introduce the data
  structures that package the outcome of the multi-switching lemma and basic
  lemmas for accessing the underlying partial certificates.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Core
open Classical

/-- Parameters for AC⁰ families used across the shrinkage interface. -/
structure AC0Parameters where
  n : Nat
  M : Nat
  d : Nat
  depthBudget_ge_n :
    n ≤ Nat.pow (Nat.log2 (M + 2)) (d + 1)
  deriving Repr

/--
  Стандартная квазиполиномиальная оценка глубины для shrinkage-свидетеля.
  Выделяем её в отдельное обозначение, чтобы не таскать развёрнутое выражение
  по всему коду и чтобы проще было применять численные леммы.
-/
@[simp] def AC0Parameters.depthBudget (params : AC0Parameters) : Nat :=
  Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)

@[simp] lemma AC0Parameters.depthBudget_le
    (params : AC0Parameters) :
    params.n ≤ params.depthBudget :=
  params.depthBudget_ge_n

/-- Удобное обозначение: линейное расширение параметров по размеру и глубине. -/
lemma AC0Parameters.depthBudget_mono_M
    (params : AC0Parameters) {M' : Nat}
    (hM : params.M ≤ M') :
    params.depthBudget
      ≤ Nat.pow (Nat.log2 (M' + 2)) (params.d + 1) := by
  have hle : params.M + 2 ≤ M' + 2 := Nat.add_le_add_right hM 2
  have hpos : 1 ≤ params.M + 2 := by
    have htwo : 2 ≤ params.M + 2 := Nat.le_add_left 2 params.M
    exact Nat.le_trans (by decide : 1 ≤ 2) htwo
  have hne : params.M + 2 ≠ 0 := by simp
  have hne' : M' + 2 ≠ 0 := by simp
  have hpow := Nat.log2_self_le (h := hne)
  have hle' := Nat.le_trans hpow hle
  have hlog := (Nat.le_log2 (h := hne')).mpr hle'
  have hpow := Nat.pow_le_pow_left hlog (params.d + 1)
  exact hpow

lemma AC0Parameters.depthBudget_mono
    (params : AC0Parameters) {M' d' : Nat}
    (hM : params.M ≤ M') (hd : params.d ≤ d') :
    params.depthBudget
      ≤ Nat.pow (Nat.log2 (M' + 2)) (d' + 1) := by
  have hmonoM := params.depthBudget_mono_M (hM := hM)
  have hpos₁ : 1 ≤ Nat.log2 (M' + 2) := by
    have htwo : 2 ≤ M' + 2 := Nat.le_add_left 2 M'
    have hpow_eq : Nat.pow 2 1 = 2 := by simp
    have hpow : Nat.pow 2 1 ≤ M' + 2 := by
      simpa [hpow_eq]
        using htwo
    have hne : M' + 2 ≠ 0 := by simp
    exact (Nat.le_log2 (h := hne)).mpr hpow
  have hpos : 0 < Nat.log2 (M' + 2) := Nat.lt_of_lt_of_le (Nat.succ_pos 0) hpos₁
  have hpow := Nat.pow_le_pow_right hpos (Nat.succ_le_succ hd)
  exact hmonoM.trans hpow

def AC0Parameters.withBounds (params : AC0Parameters)
    {M d : Nat} (hM : params.M ≤ M) (hd : params.d ≤ d) :
    AC0Parameters :=
  { n := params.n
    M := M
    d := d
    depthBudget_ge_n :=
      (params.depthBudget_le).trans
        (params.depthBudget_mono (hM := hM) (hd := hd)) }

/-- Parameters for "local" circuits.  These are needed by the locality bridge
and remain here so that the surrounding API keeps compiling. -/
structure LocalCircuitParameters where
  n      : Nat
  M      : Nat
  ℓ      : Nat
  depth  : Nat
  deriving Repr

/-- Explicit bounds returned by shrinkage theorems.  We only need the depth and
error estimates and hence keep the structure extremely small. -/
structure ShrinkageBounds where
  depthBound : Nat
  errorBound : Q
  deriving Repr

/--
`AC0PartialWitness` collects the combinatorial data produced by the
multi-switching lemma: a partial PDT together with the quantitative bounds we
care about.  The field names match the usage in `Facts_Switching.lean` so that
no downstream file has to change after the refactor.
-/
structure AC0PartialWitness
    (params : AC0Parameters) (F : Family params.n) where
  level          : Nat
  certificate    : Core.PartialCertificate params.n level F
  level_le_log   : level ≤ Nat.log2 (params.M + 2)
  depth_le       : certificate.depthBound + level
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)
  epsilon_nonneg : (0 : Core.Q) ≤ certificate.epsilon
  epsilon_le_inv : certificate.epsilon ≤ (1 : Core.Q) / (params.n + 2)

/--
Having a partial witness is expressed through a typeclass so that the rest of
the development can simply assume `[HasAC0PartialWitness params F]` and pick up
all accompanying bounds via projection lemmas.
-/
class HasAC0PartialWitness
    (params : AC0Parameters) (F : Family params.n) : Type where
  witness : AC0PartialWitness params F

section WitnessInterface

variable (params : AC0Parameters) (F : Family params.n)

/-- Extract the witness stored in the typeclass. -/
noncomputable def ac0PartialWitness
    [w : HasAC0PartialWitness params F] :
    AC0PartialWitness params F :=
  w.witness

/--
Convenience wrapper: expose the level bound coming from the witness in a form
that is easy to `simp` with. -/
noncomputable def partialCertificate_level_from_AC0
    [HasAC0PartialWitness params F] : Nat :=
  (ac0PartialWitness params F).level

/-- Recover the partial certificate itself from the witness. -/
noncomputable def partialCertificate_from_AC0
    [HasAC0PartialWitness params F] :
    Core.PartialCertificate params.n
      (partialCertificate_level_from_AC0 params F) F :=
  (ac0PartialWitness params F).certificate

lemma partialCertificate_level_from_AC0_le
    [HasAC0PartialWitness params F] :
    partialCertificate_level_from_AC0 params F ≤ Nat.log2 (params.M + 2) :=
  (ac0PartialWitness params F).level_le_log

/-- The trunk depth bound transported from the witness. -/
lemma partialCertificate_depthBound_add_level_le
    [HasAC0PartialWitness params F] :
    (partialCertificate_from_AC0 params F).depthBound
        + partialCertificate_level_from_AC0 params F
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) :=
  (ac0PartialWitness params F).depth_le

/-- The witness always delivers a nonnegative error parameter. -/
lemma partialCertificate_epsilon_nonneg
    [HasAC0PartialWitness params F] :
    (0 : Core.Q) ≤ (partialCertificate_from_AC0 params F).epsilon :=
  (ac0PartialWitness params F).epsilon_nonneg

/-- The quantitative error bound packaged with the witness. -/
lemma partialCertificate_epsilon_le_inv
    [HasAC0PartialWitness params F] :
    (partialCertificate_from_AC0 params F).epsilon
      ≤ (1 : Core.Q) / (params.n + 2) :=
  (ac0PartialWitness params F).epsilon_le_inv

end WitnessInterface

namespace AC0PartialWitness

open Nat

variable {params : AC0Parameters} {F : Family params.n}

/--
  Помощник: `log₂` монотонна на натуральных числах `≥ 1`, поэтому увеличение
  допустимого размера формулы с `M` до `M'` автоматически ослабляет верхнюю
  границу на высоту ствола.
-/
lemma level_log_bound_mono {M' : Nat}
    (W : AC0PartialWitness params F) (hM : params.M ≤ M') :
    W.level ≤ Nat.log2 (M' + 2) := by
  have hle : params.M + 2 ≤ M' + 2 := by exact Nat.add_le_add_right hM 2
  have hpos : 1 ≤ params.M + 2 := by
    have htwo : 2 ≤ params.M + 2 := Nat.le_add_left 2 params.M
    exact Nat.le_trans (by decide : 1 ≤ 2) htwo
  have hne : params.M + 2 ≠ 0 := by simp
  have hne' : M' + 2 ≠ 0 := by simp
  have hpow := Nat.log2_self_le (h := hne)
  have hle' := Nat.le_trans hpow hle
  have hlog := (Nat.le_log2 (h := hne')).mpr hle'
  exact W.level_le_log.trans hlog

/--
  Первая часть монотонности: если увеличить параметр `M`, то величина
  `(log₂ (M+2))^{d+1}` не убывает.  Это следует из монотонности `Nat.pow`
  по основанию.
-/
lemma depth_bound_mono_M {M' : Nat}
    (W : AC0PartialWitness params F) (hM : params.M ≤ M') :
    W.certificate.depthBound + W.level
      ≤ Nat.pow (Nat.log2 (M' + 2)) (params.d + 1) := by
  have hbase : Nat.log2 (params.M + 2) ≤ Nat.log2 (M' + 2) := by
    have hle : params.M + 2 ≤ M' + 2 := Nat.add_le_add_right hM 2
    have hpos : 1 ≤ params.M + 2 := by
      have htwo : 2 ≤ params.M + 2 := Nat.le_add_left 2 params.M
      exact Nat.le_trans (by decide : 1 ≤ 2) htwo
    have hne : params.M + 2 ≠ 0 := by simp
    have hne' : M' + 2 ≠ 0 := by simp
    have hpow := Nat.log2_self_le (h := hne)
    have hle' := Nat.le_trans hpow hle
    exact (Nat.le_log2 (h := hne')).mpr hle'
  have hpowMono : ∀ {a b e : Nat}, a ≤ b → Nat.pow a e ≤ Nat.pow b e := by
    intro a b e h
    induction e with
    | zero => simp
    | succ e ih =>
        have := Nat.mul_le_mul ih h
        simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have hpow :
      Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)
        ≤ Nat.pow (Nat.log2 (M' + 2)) (params.d + 1) :=
    hpowMono hbase
  exact W.depth_le.trans hpow

/--
  Помощник: если основание `≥ 1`, то рост показателя степени только увеличивает
  значение степени.  Это позволит расширять глубину схем `d`.
-/
lemma pow_le_pow_succ {a e₁ e₂ : Nat}
    (ha : 1 ≤ a) (h : e₁ ≤ e₂) : Nat.pow a e₁ ≤ Nat.pow a e₂ := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  subst hk
  have pow_ge_one : ∀ t, 1 ≤ Nat.pow a t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have hx : 1 * 1 ≤ Nat.pow a t * a := Nat.mul_le_mul ih ha
        simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hx
  have hpow_pos : 1 ≤ Nat.pow a k := pow_ge_one k
  have hmul_le : Nat.pow a e₁ ≤ Nat.pow a e₁ * Nat.pow a k := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (Nat.pow a e₁) hpow_pos
  have : Nat.pow a e₁ ≤ Nat.pow a (e₁ + k) := by
    simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hmul_le
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

/--
  Совмещаем рост по `M` и `d`: получаем свидетель для параметров с тем же
  числом переменных, но более крупными оценками размера и глубины.
-/
def upgrade (W : AC0PartialWitness params F)
    {M' d' : Nat}
    (hM : params.M ≤ M') (hd : params.d ≤ d') :
    AC0PartialWitness
      (AC0Parameters.withBounds params (hM := hM) (hd := hd)) F :=
  { level := W.level
    certificate := W.certificate
    level_le_log := level_log_bound_mono (params := params) (F := F)
      (W := W) hM
    depth_le := by
      have hmonoM := depth_bound_mono_M (params := params) (F := F)
        (W := W) hM
      have hpos : 1 ≤ Nat.log2 (M' + 2) := by
        have htwo : 2 ≤ M' + 2 := Nat.le_add_left 2 M'
        have hne : M' + 2 ≠ 0 := by simp
        have hpow : 2 ^ 1 ≤ M' + 2 := by simpa using htwo
        exact (Nat.le_log2 (h := hne)).mpr hpow
      have hpow := pow_le_pow_succ (a := Nat.log2 (M' + 2))
        (e₁ := params.d + 1) (e₂ := d' + 1) hpos
        (Nat.succ_le_succ hd)
      exact hmonoM.trans hpow
    epsilon_nonneg := W.epsilon_nonneg
    epsilon_le_inv := by
      have := W.epsilon_le_inv
      simpa [AC0Parameters.withBounds, hM, hd] using this }

/--
  Монотонность параметров оформляем как отдельный экземпляр `HasAC0PartialWitness`.
-/
noncomputable def upgradeInstance
    {M' d' : Nat}
    (hM : params.M ≤ M') (hd : params.d ≤ d')
    [HasAC0PartialWitness params F] :
    HasAC0PartialWitness
      (AC0Parameters.withBounds params (hM := hM) (hd := hd)) F :=
  ⟨upgrade (params := params) (F := F)
      (W := ac0PartialWitness params F) hM hd⟩

end AC0PartialWitness

section DefaultWitness

open AC0

variable (params : AC0Parameters) (F : Family params.n)

/--
  Тривиальный shrinkage-сертификат: берём полное PDT глубины `n`, построенное
  в `AC0.Formulas`, и упаковываем его в структуру `AC0PartialWitness`.  Благодаря
  полю `depthBudget_ge_n` в `AC0Parameters` требуемая оценка глубины выполняется
  автоматически.
-/
noncomputable def defaultAC0Witness : AC0PartialWitness params F :=
  { level := 0
    certificate := AC0.perfectCertificate F
    level_le_log := by exact Nat.zero_le _
    depth_le := by
      have hbound := params.depthBudget_le
      have hdepth : (AC0.perfectCertificate F).depthBound = params.n := by simp
      have hsum : (AC0.perfectCertificate F).depthBound + 0 = params.n := by
        simpa [Nat.zero_add] using hdepth
      simpa [hsum]
        using hbound
    epsilon_nonneg := by simp
    epsilon_le_inv := by
      have hnonneg : (0 : Q) ≤ (1 : Q) / (params.n + 2) := by
        have hnum : (0 : Q) ≤ (1 : Q) := by norm_num
        have hden : (0 : Q) ≤ (params.n + 2 : Q) := by
          exact_mod_cast Nat.zero_le (params.n + 2)
        exact div_nonneg hnum hden
      have heps : (AC0.perfectCertificate F).epsilon = 0 := by simp
      simpa [heps]
        using hnonneg
  }

/--
  Базовый экземпляр `HasAC0PartialWitness`, доступный без дополнительных
  допущений.  Он опирается на полный PDT и пригоден как безопасная заглушка
  до тех пор, пока не подключено более сильное shrinkage-доказательство.
-/
noncomputable instance instHasAC0PartialWitness
    (params : AC0Parameters) (F : Family params.n) :
    HasAC0PartialWitness params F :=
  ⟨defaultAC0Witness (params := params) (F := F)⟩

end DefaultWitness

end ThirdPartyFacts
end Pnp3
