// Apply_wrong_label prints the function type with typecore's type_expr
// (Error_message_utils.type_expr), which normalizes it, and the outcome
// printer's line breaks are not indented by the enclosing box.
@obj
external make: (
  ~localeMatcher: @string [#lookup | @as("best fit") #best_fit]=?,
  ~weekday: [#narrow | #short | #long]=?,
  ~era: [#narrow | #short | #long]=?,
  ~timeZoneName: [#short | #long | #shortOffset]=?,
  unit,
) => int = ""

let x = make(~weekdays=#long, ())
