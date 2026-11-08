// error-output-parity: Typedecl.Rebind_wrong_type wider than the margin
type extensibleTypeWithAVeryLongNameNumberOne = ..
type extensibleTypeWithAVeryLongNameNumberTwo = ..

type extensibleTypeWithAVeryLongNameNumberOne += A(int)
type extensibleTypeWithAVeryLongNameNumberTwo += B = A
