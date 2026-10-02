// Pattern_type_clash goes through super_report_unification_error, which
// breaks long types onto their own line.
let rec r: (string, ~wrongLabelName: int=?) => 'a = (_s, ~_s: string=3) => {
  assert(false)
}
