type status = Idle | Loading | Failed | Done | GaveUp
type request = {status: status, attempts: int}
type event = Send | Succeed | Fail | Retry

// A request that is sent again after a failure, three times at most.
let update = (request, event) =>
  switch (request.status, event) {
  | (Idle, Send) => {status: Loading, attempts: 1}
  | (Loading, Succeed) => {...request, status: Done}
  | (Loading, Fail) => {...request, status: request.attempts >= 3 ? GaveUp : Failed}
  | (Failed, Retry) => {status: Loading, attempts: request.attempts + 1}
  | _ => request
  }

@spec
let request: Spec.t<request, event> = {
  init: {status: Idle, attempts: 0},
  step: update,
  always: request => request.attempts <= 3,
  sometimes: request => request.status == GaveUp,
}
