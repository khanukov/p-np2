import Std.Data.Finset

open Classical
open Finset

namespace Utils

/-- `card_filter_lt_card` states that if a finset `s` contains an element which
fails the predicate `p`, then the filtered set is strictly smaller. -/
lemma card_filter_lt_card {α} [DecidableEq α] {s : Finset α} {p : α → Bool}
    (h : ∃ a, a ∈ s ∧ p a = false) :
    (s.filter p).card < s.card := by
  classical
  obtain ⟨a, ha, hpa⟩ := h
  have : a ∉ s.filter p := by
    simpa [Finset.mem_filter, ha, hpa]
  exact Finset.card_filter_lt_card this

end Utils
