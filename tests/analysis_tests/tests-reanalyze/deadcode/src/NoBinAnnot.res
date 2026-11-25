// A file compiled without binary annotations has no `.cmt`, so it is not
// analyzed: its dead value is not reported.
@@config({flags: ["-bs-no-bin-annot"]})

let neverUsed = 1
