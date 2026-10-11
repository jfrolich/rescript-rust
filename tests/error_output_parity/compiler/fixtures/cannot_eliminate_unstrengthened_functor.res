module Make=(S:{type elt})=>{open S
  type t<'a>
  @get_index external unsafe_get:(t<elt>,int)=> elt = ""
}
module Int_arr = Make({
  type elt = private int
})