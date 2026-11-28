type status = Idle | Loading | Failed | Done | GaveUp
type request = {status: status, attempts: int}
type event = Send | Succeed | Fail | Retry

let update = (request, event) =>
  switch (request.status, event) {
  | (Idle, Send) => {status: Loading, attempts: 1}
  | (Loading, Succeed) => {...request, status: Done}
  | (Loading, Fail) => {...request, status: request.attempts >= 3 ? GaveUp : Failed}
  // The attempt is not counted.
  | (Failed, Retry) => {...request, status: Loading}
  | _ => request
  }

@spec
let settles: Spec.t<request, event> = {
  init: {status: Idle, attempts: 0},
  step: update,
  always: request => request.attempts <= 3,
  eventually: request => request.status == Done || request.status == GaveUp,
}
