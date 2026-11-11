// error-output-parity: Typecore.Wrong_name of a record field with a multi-line expected type
type a<'p> = {x: 'p}
type b = {y: int}
let _ = (({x: #alphaAlphaAlpha, y: 2}: a<[#alphaAlphaAlpha | #betaBetaBetaBeta | #gammaGammaGamma | #deltaDeltaDelta | #epsilonEpsilon]>))
