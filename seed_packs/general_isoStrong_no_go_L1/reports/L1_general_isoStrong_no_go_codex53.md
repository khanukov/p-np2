Task: general iso-strong no-go L1
Handle: codex53
Branch: main

## 1. Executive verdict
YELLOW_PARTIAL_GENERAL_L1

## 2. What landed
- `exists_label_not_in_trace_image_of_card_lt`
- `generalIsoStrong_L1_partial_status`

## 3. Does this generalize canonical RED?
no

## 4. Remaining blockers
- `exists_valid_agreeing_not_yes_under_general_slack` is not landed.
- Missing bridge from image-not-containing-label to
  `¬ encodePartial (diagonalPartialTable ...) ∈ (gapSliceOfParams p).Yes` in a
  fully general (`sYES`-agnostic) form.
- Full assembly theorem
  `isoStrong_conclusion_negative_general` remains open.

## 5. Next action
open_general_isoStrong_no_go_L1_session_2
