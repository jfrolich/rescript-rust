// error-output-parity: Typedecl.Constraint_failed with a multi-line type
type rec t<'a> = {x: 'a} constraint 'a = [#alphaAlphaAlpha | #betaBetaBetaBeta | #gammaGammaGamma | #deltaDeltaDelta | #epsilonEpsilon]
and u = t<int>
