// Error size counts heap words, not text: long names alone do not elide
// the enclosing module types (includemod.ml is_big).
module M: {
  type aVeryLongTypeNameThatHasTheSameShapeAsAShortOne = {aVeryLongFieldNameThatGoesOnAndOnAndOn0: int, aVeryLongFieldNameThatGoesOnAndOnAndOn1: int}
  let v: string
} = {
  type aVeryLongTypeNameThatHasTheSameShapeAsAShortOne = {aVeryLongFieldNameThatGoesOnAndOnAndOn0: int, aVeryLongFieldNameThatGoesOnAndOnAndOn1: int}
  let v = 1
}
