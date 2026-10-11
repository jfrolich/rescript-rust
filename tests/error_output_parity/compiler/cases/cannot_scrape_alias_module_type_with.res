// error-output-parity: Typemod.Cannot_scrape_alias
module type T = (module type of A.M) with type t = int
