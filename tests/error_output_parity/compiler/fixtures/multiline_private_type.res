// error-output-parity: Typecore.Private_type with a multi-line type
module P: {
  type t<'a> = private {value: 'a}
} = {
  type t<'a> = {value: 'a}
}

let _item: P.t<[#alphaAlphaAlpha | #betaBetaBetaBeta | #gammaGammaGamma | #deltaDeltaDelta | #epsilonEpsilon]> = {value: #alphaAlphaAlpha}
