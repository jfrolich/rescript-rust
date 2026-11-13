/*** Items that other files declare. */

/** The items of another file's interface. */
include DocExtraction2

/** A record that spreads another file's record. */
type online = {
  ...DocExtractionRes.t,
  /** When it went online. */
  since: float,
}

/** Another file under a new name. */
module User = ModC

module Local = {
  /** A record within this file. */
  type base = {
    /** The name of the base. */
    name: string,
  }

  /** A record that spreads one of this file. */
  type extended = {...base, extra: int}
}
