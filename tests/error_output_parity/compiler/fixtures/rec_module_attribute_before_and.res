module type S = {let x: int}
module rec A: S = {let x = 1}
@attr and B: S = {let x = 1}
