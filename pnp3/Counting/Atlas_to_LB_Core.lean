namespace Pnp3
namespace Counting

/-- TODO: верхняя оценка на количество объединений ≤ k подкубов из словаря размера D. -/
axiom num_unions (D k : ℕ) : ℕ

/-- TODO: лемма об ограничении «покрывающей мощности» словаря с ошибкой ε. -/
axiom covering_power (D k : ℕ) (ε : ℚ) : ℚ

/-- TODO: критерий несовместимости параметров YES/NO. -/
axiom incompatibility : Prop

end Counting
end Pnp3
