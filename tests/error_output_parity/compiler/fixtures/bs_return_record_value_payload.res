// error-output-parity: @return rejects config fields with explicit values.
@return({nullable: false}) @val external f: unit => option<int> = "f"
