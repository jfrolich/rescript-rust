// The pattern constraint's type variables are globalized by the pattern
// force after the whole pattern is typed; the occurs check is reported there
// as Typetexp.Type_mismatch at the variable.
type rec vlist<'a> = [#Nil | #Cons('a, vlist<'a>)]

let rec map = (f): (vlist<'a> => vlist<'b>) =>
  x =>
    switch x {
    | #Nil => #Nil
    | #Cons(l: option<'a>, a) => #Cons(f(a), map(f)(l))
    }
