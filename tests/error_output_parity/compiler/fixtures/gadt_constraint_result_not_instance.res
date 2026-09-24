type rec t<'a> =
  | Int(int): t<int>
  | Bool(bool): t<_> constraint 'a = int
