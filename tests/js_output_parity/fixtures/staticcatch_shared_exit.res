type result = Initial | Success(option<string>) | Failed

type phase = Pending | Processing | Complete

let shouldContinue = (status, progress, phase, state, enabled, medium) =>
  switch status {
  | None => true
  | Some(_) =>
    switch progress {
    | Some(value) if value < 100 => true
    | _ =>
      switch phase {
      | Some(Pending | Processing) => true
      | _ =>
        switch state {
        | Initial | Success(None) =>
          if enabled == Some(false) {
            false
          } else {
            medium != "SoundEffect"
          }
        | Success(Some(_)) | Failed => false
        }
      }
    }
  }
