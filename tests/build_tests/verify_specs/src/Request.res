// A request that is sent again after a failure, three times at most.
type status = Idle | Loading | Failed | Done | GaveUp
type request = {status: status, attempts: int}
type event = Send | Succeed | Fail | Retry

let update = (request, event) =>
  switch (request.status, event) {
  | (Idle, Send) => {status: Loading, attempts: 1}
  | (Loading, Succeed) => {...request, status: Done}
  | (Loading, Fail) => {...request, status: request.attempts >= 3 ? GaveUp : Failed}
  | (Failed, Retry) => {status: Loading, attempts: request.attempts + 1}
  | _ => request
  }

let settled = request => request.status == Done || request.status == GaveUp

@spec
let request: Spec.t<request, event> = {
  init: {status: Idle, attempts: 0},
  step: update,
  always: request => request.attempts <= 3,
  sometimes: request => request.status == GaveUp,
  reachable: settled,
  eventually: settled,
}

// The same, but a retry is not counted.
let updateForever = (request, event) =>
  switch (request.status, event) {
  | (Failed, Retry) => {...request, status: Loading}
  | _ => update(request, event)
  }

@spec
let retriesForever: Spec.t<request, event> = {
  init: {status: Idle, attempts: 0},
  step: updateForever,
  always: request => request.attempts <= 3,
  reachable: settled,
  eventually: settled,
}

// Nothing ever gives up here.
@spec
let neverGivesUp: Spec.t<request, event> = {
  init: {status: Idle, attempts: 0},
  step: updateForever,
  sometimes: request => request.status == GaveUp,
}
