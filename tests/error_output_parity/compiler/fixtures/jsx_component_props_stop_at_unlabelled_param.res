// transform_params_for_make stops at the first unlabelled parameter, while returned_expression keeps every labelled pattern.
include {
  @react.component
  let make = (~x, y, ~x, ~y) => React.null
}
