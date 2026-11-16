module M = {
  exception E(int)
}

exception A = M.E
