// error-output-parity: Builtin_attributes.error_of_extension reports nested %%error sub-errors.
%%error(
  "main"
  %%error("sub")
)
