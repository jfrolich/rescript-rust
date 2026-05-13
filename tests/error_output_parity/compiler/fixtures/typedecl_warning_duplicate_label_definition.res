// error-output-parity: Typedecl warns for duplicate record labels across type definitions.
@@warning("-32-34")

type rec first = {shared: int}
and second = {shared: string}
