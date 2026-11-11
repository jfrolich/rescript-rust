// error-output-parity: Typetexp.Not_an_object with a multi-line type
type a<'x> = option<'x>

type b = {...a<[#alphaAlphaAlpha | #betaBetaBetaBeta | #gammaGammaGamma | #deltaDeltaDelta | #epsilonEpsilon]>, "x": int}
