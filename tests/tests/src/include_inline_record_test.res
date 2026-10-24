// An inline-record constructor brought into scope by `include` keeps its
// record argument, so its fields are found through the constructor.
module Gen = {
  type fit = [#Cover | #Letterbox]
  type style = Regular | Full({fit: fit})
}

include Gen

let style: style = Full({fit: #Cover})

module Name = {
  include Gen

  let styles: array<style> = [Regular, Full({fit: #Cover}), Full({fit: #Letterbox})]

  let fit = style =>
    switch style {
    | Regular => None
    | Full({fit}) => Some(fit)
    }
}
