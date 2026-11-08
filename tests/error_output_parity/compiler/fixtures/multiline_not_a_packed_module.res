// error-output-parity: Typemod.Not_a_packed_module with a multi-line type
let x: [#alphaAlphaAlpha | #betaBetaBetaBeta | #gammaGammaGamma | #deltaDeltaDelta | #epsilonEpsilon] = #alphaAlphaAlpha

module M = unpack(x)
