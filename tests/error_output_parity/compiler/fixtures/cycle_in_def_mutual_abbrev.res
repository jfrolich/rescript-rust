// error-output-parity: Typedecl.Cycle_in_def through a mutually recursive abbreviation
type rec t<'a> = u<'a>
and u<'a> = t<[#alphaAlphaAlpha | #betaBetaBetaBeta | #gammaGammaGamma | #deltaDeltaDelta | #epsilonEpsilon]>
