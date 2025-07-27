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

/-!  If `s` is a strict subset of `t`, then the cardinality of `s` is
strictly smaller than that of `t`.  This wrapper around `Finset.card_lt_card`
makes the statement available in the `Utils` namespace. -/
lemma card_lt_of_ssSubset {α} [DecidableEq α] {s t : Finset α}
    (h : s ⊂ t) :
    s.card < t.card := by
  classical
  simpa using Finset.card_lt_card h

end Utils
