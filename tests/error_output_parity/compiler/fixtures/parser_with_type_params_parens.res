module type S = {
  type t<'a>
}
module type T = S with type t('a) = int
