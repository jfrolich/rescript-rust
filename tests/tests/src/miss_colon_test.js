let +:;

+: = (f, g) => {
  let match = [f, g];
  let tuple = match;
  let ctor = tuple[0];
  let ifres;
  if (ctor.TAG === "Int") {
    let n = ctor._0;
    let ctor = tuple[1];
    let ifres;
    if (ctor.TAG === "Int") {
      let m = ctor._0;
      ifres = {TAG: "Int", _0: n + m};
    } else {
      let tuple = match;
      let ctor = tuple[0];
      let ifres;
      if (ctor.TAG === "Int") {
        let ifres;
        if (ctor._0 === 0) {
          let e = tuple[1];
          ifres = e;
        } else {
          let tuple = match;
          let e = tuple[0];
          let ctor = tuple[1];
          let ifres;
          if (ctor.TAG === "Int") {
            let ifres;
            if (ctor._0 === 0) {
              ifres = e;
            } else {
              let tuple = match;
              let f = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Add") {
                let g = ctor._0;
                let h = ctor._1;
                ifres = +:(+:(f, g), h);
              } else {
                let tuple = match;
                let f = tuple[0];
                let g = tuple[1];
                ifres = {TAG: "Add", _0: f, _1: g};
              }
              ifres = ifres;
            }
            ifres = ifres;
          } else {
            let tuple = match;
            let f = tuple[0];
            let ctor = tuple[1];
            let ifres;
            if (ctor.TAG === "Add") {
              let g = ctor._0;
              let h = ctor._1;
              ifres = +:(+:(f, g), h);
            } else {
              let tuple = match;
              let f = tuple[0];
              let g = tuple[1];
              ifres = {TAG: "Add", _0: f, _1: g};
            }
            ifres = ifres;
          }
          ifres = ifres;
        }
        ifres = ifres;
      } else {
        let tuple = match;
        let e = tuple[0];
        let ctor = tuple[1];
        let ifres;
        if (ctor.TAG === "Int") {
          let ifres;
          if (ctor._0 === 0) {
            ifres = e;
          } else {
            let tuple = match;
            let f = tuple[0];
            let ctor = tuple[1];
            let ifres;
            if (ctor.TAG === "Add") {
              let g = ctor._0;
              let h = ctor._1;
              ifres = +:(+:(f, g), h);
            } else {
              let tuple = match;
              let f = tuple[0];
              let g = tuple[1];
              ifres = {TAG: "Add", _0: f, _1: g};
            }
            ifres = ifres;
          }
          ifres = ifres;
        } else {
          let tuple = match;
          let f = tuple[0];
          let ctor = tuple[1];
          let ifres;
          if (ctor.TAG === "Add") {
            let g = ctor._0;
            let h = ctor._1;
            ifres = +:(+:(f, g), h);
          } else {
            let tuple = match;
            let f = tuple[0];
            let g = tuple[1];
            ifres = {TAG: "Add", _0: f, _1: g};
          }
          ifres = ifres;
        }
        ifres = ifres;
      }
      ifres = ifres;
    }
    ifres = ifres;
  } else {
    let tuple = match;
    let ctor = tuple[0];
    let ifres;
    if (ctor.TAG === "Int") {
      let ifres;
      if (ctor._0 === 0) {
        let e = tuple[1];
        ifres = e;
      } else {
        let tuple = match;
        let e = tuple[0];
        let ctor = tuple[1];
        let ifres;
        if (ctor.TAG === "Int") {
          let ifres;
          if (ctor._0 === 0) {
            ifres = e;
          } else {
            let tuple = match;
            let f = tuple[0];
            let ctor = tuple[1];
            let ifres;
            if (ctor.TAG === "Add") {
              let g = ctor._0;
              let h = ctor._1;
              ifres = +:(+:(f, g), h);
            } else {
              let tuple = match;
              let f = tuple[0];
              let g = tuple[1];
              ifres = {TAG: "Add", _0: f, _1: g};
            }
            ifres = ifres;
          }
          ifres = ifres;
        } else {
          let tuple = match;
          let f = tuple[0];
          let ctor = tuple[1];
          let ifres;
          if (ctor.TAG === "Add") {
            let g = ctor._0;
            let h = ctor._1;
            ifres = +:(+:(f, g), h);
          } else {
            let tuple = match;
            let f = tuple[0];
            let g = tuple[1];
            ifres = {TAG: "Add", _0: f, _1: g};
          }
          ifres = ifres;
        }
        ifres = ifres;
      }
      ifres = ifres;
    } else {
      let tuple = match;
      let e = tuple[0];
      let ctor = tuple[1];
      let ifres;
      if (ctor.TAG === "Int") {
        let ifres;
        if (ctor._0 === 0) {
          ifres = e;
        } else {
          let tuple = match;
          let f = tuple[0];
          let ctor = tuple[1];
          let ifres;
          if (ctor.TAG === "Add") {
            let g = ctor._0;
            let h = ctor._1;
            ifres = +:(+:(f, g), h);
          } else {
            let tuple = match;
            let f = tuple[0];
            let g = tuple[1];
            ifres = {TAG: "Add", _0: f, _1: g};
          }
          ifres = ifres;
        }
        ifres = ifres;
      } else {
        let tuple = match;
        let f = tuple[0];
        let ctor = tuple[1];
        let ifres;
        if (ctor.TAG === "Add") {
          let g = ctor._0;
          let h = ctor._1;
          ifres = +:(+:(f, g), h);
        } else {
          let tuple = match;
          let f = tuple[0];
          let g = tuple[1];
          ifres = {TAG: "Add", _0: f, _1: g};
        }
        ifres = ifres;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};

let *:;

*: = (f, g) => {
  let match = [f, g];
  let tuple = match;
  let ctor = tuple[0];
  let ifres;
  if (ctor.TAG === "Int") {
    let n = ctor._0;
    let ctor = tuple[1];
    let ifres;
    if (ctor.TAG === "Int") {
      let m = ctor._0;
      ifres = {TAG: "Int", _0: n * m};
    } else {
      let tuple = match;
      let ctor = tuple[0];
      let ifres;
      if (ctor.TAG === "Int") {
        let ifres;
        if (ctor._0 === 0) {
          ifres = {TAG: "Int", _0: 0};
        } else {
          let tuple = match;
          let ctor = tuple[1];
          let ifres;
          if (ctor.TAG === "Int") {
            let ifres;
            if (ctor._0 === 0) {
              ifres = {TAG: "Int", _0: 0};
            } else {
              let tuple = match;
              let ctor = tuple[0];
              let ifres;
              if (ctor.TAG === "Int") {
                let ifres;
                if (ctor._0 === 1) {
                  let e = tuple[1];
                  ifres = e;
                } else {
                  let tuple = match;
                  let e = tuple[0];
                  let ctor = tuple[1];
                  let ifres;
                  if (ctor.TAG === "Int") {
                    let ifres;
                    if (ctor._0 === 1) {
                      ifres = e;
                    } else {
                      let tuple = match;
                      let f = tuple[0];
                      let ctor = tuple[1];
                      let ifres;
                      if (ctor.TAG === "Mul") {
                        let g = ctor._0;
                        let h = ctor._1;
                        ifres = *:(*:(f, g), h);
                      } else {
                        let tuple = match;
                        let f = tuple[0];
                        let g = tuple[1];
                        ifres = {TAG: "Mul", _0: f, _1: g};
                      }
                      ifres = ifres;
                    }
                    ifres = ifres;
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let ctor = tuple[1];
                    let ifres;
                    if (ctor.TAG === "Mul") {
                      let g = ctor._0;
                      let h = ctor._1;
                      ifres = *:(*:(f, g), h);
                    } else {
                      let tuple = match;
                      let f = tuple[0];
                      let g = tuple[1];
                      ifres = {TAG: "Mul", _0: f, _1: g};
                    }
                    ifres = ifres;
                  }
                  ifres = ifres;
                }
                ifres = ifres;
              } else {
                let tuple = match;
                let e = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Int") {
                  let ifres;
                  if (ctor._0 === 1) {
                    ifres = e;
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let ctor = tuple[1];
                    let ifres;
                    if (ctor.TAG === "Mul") {
                      let g = ctor._0;
                      let h = ctor._1;
                      ifres = *:(*:(f, g), h);
                    } else {
                      let tuple = match;
                      let f = tuple[0];
                      let g = tuple[1];
                      ifres = {TAG: "Mul", _0: f, _1: g};
                    }
                    ifres = ifres;
                  }
                  ifres = ifres;
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let ctor = tuple[1];
                  let ifres;
                  if (ctor.TAG === "Mul") {
                    let g = ctor._0;
                    let h = ctor._1;
                    ifres = *:(*:(f, g), h);
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let g = tuple[1];
                    ifres = {TAG: "Mul", _0: f, _1: g};
                  }
                  ifres = ifres;
                }
                ifres = ifres;
              }
              ifres = ifres;
            }
            ifres = ifres;
          } else {
            let tuple = match;
            let ctor = tuple[0];
            let ifres;
            if (ctor.TAG === "Int") {
              let ifres;
              if (ctor._0 === 1) {
                let e = tuple[1];
                ifres = e;
              } else {
                let tuple = match;
                let e = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Int") {
                  let ifres;
                  if (ctor._0 === 1) {
                    ifres = e;
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let ctor = tuple[1];
                    let ifres;
                    if (ctor.TAG === "Mul") {
                      let g = ctor._0;
                      let h = ctor._1;
                      ifres = *:(*:(f, g), h);
                    } else {
                      let tuple = match;
                      let f = tuple[0];
                      let g = tuple[1];
                      ifres = {TAG: "Mul", _0: f, _1: g};
                    }
                    ifres = ifres;
                  }
                  ifres = ifres;
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let ctor = tuple[1];
                  let ifres;
                  if (ctor.TAG === "Mul") {
                    let g = ctor._0;
                    let h = ctor._1;
                    ifres = *:(*:(f, g), h);
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let g = tuple[1];
                    ifres = {TAG: "Mul", _0: f, _1: g};
                  }
                  ifres = ifres;
                }
                ifres = ifres;
              }
              ifres = ifres;
            } else {
              let tuple = match;
              let e = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Int") {
                let ifres;
                if (ctor._0 === 1) {
                  ifres = e;
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let ctor = tuple[1];
                  let ifres;
                  if (ctor.TAG === "Mul") {
                    let g = ctor._0;
                    let h = ctor._1;
                    ifres = *:(*:(f, g), h);
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let g = tuple[1];
                    ifres = {TAG: "Mul", _0: f, _1: g};
                  }
                  ifres = ifres;
                }
                ifres = ifres;
              } else {
                let tuple = match;
                let f = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Mul") {
                  let g = ctor._0;
                  let h = ctor._1;
                  ifres = *:(*:(f, g), h);
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let g = tuple[1];
                  ifres = {TAG: "Mul", _0: f, _1: g};
                }
                ifres = ifres;
              }
              ifres = ifres;
            }
            ifres = ifres;
          }
          ifres = ifres;
        }
        ifres = ifres;
      } else {
        let tuple = match;
        let ctor = tuple[1];
        let ifres;
        if (ctor.TAG === "Int") {
          let ifres;
          if (ctor._0 === 0) {
            ifres = {TAG: "Int", _0: 0};
          } else {
            let tuple = match;
            let ctor = tuple[0];
            let ifres;
            if (ctor.TAG === "Int") {
              let ifres;
              if (ctor._0 === 1) {
                let e = tuple[1];
                ifres = e;
              } else {
                let tuple = match;
                let e = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Int") {
                  let ifres;
                  if (ctor._0 === 1) {
                    ifres = e;
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let ctor = tuple[1];
                    let ifres;
                    if (ctor.TAG === "Mul") {
                      let g = ctor._0;
                      let h = ctor._1;
                      ifres = *:(*:(f, g), h);
                    } else {
                      let tuple = match;
                      let f = tuple[0];
                      let g = tuple[1];
                      ifres = {TAG: "Mul", _0: f, _1: g};
                    }
                    ifres = ifres;
                  }
                  ifres = ifres;
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let ctor = tuple[1];
                  let ifres;
                  if (ctor.TAG === "Mul") {
                    let g = ctor._0;
                    let h = ctor._1;
                    ifres = *:(*:(f, g), h);
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let g = tuple[1];
                    ifres = {TAG: "Mul", _0: f, _1: g};
                  }
                  ifres = ifres;
                }
                ifres = ifres;
              }
              ifres = ifres;
            } else {
              let tuple = match;
              let e = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Int") {
                let ifres;
                if (ctor._0 === 1) {
                  ifres = e;
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let ctor = tuple[1];
                  let ifres;
                  if (ctor.TAG === "Mul") {
                    let g = ctor._0;
                    let h = ctor._1;
                    ifres = *:(*:(f, g), h);
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let g = tuple[1];
                    ifres = {TAG: "Mul", _0: f, _1: g};
                  }
                  ifres = ifres;
                }
                ifres = ifres;
              } else {
                let tuple = match;
                let f = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Mul") {
                  let g = ctor._0;
                  let h = ctor._1;
                  ifres = *:(*:(f, g), h);
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let g = tuple[1];
                  ifres = {TAG: "Mul", _0: f, _1: g};
                }
                ifres = ifres;
              }
              ifres = ifres;
            }
            ifres = ifres;
          }
          ifres = ifres;
        } else {
          let tuple = match;
          let ctor = tuple[0];
          let ifres;
          if (ctor.TAG === "Int") {
            let ifres;
            if (ctor._0 === 1) {
              let e = tuple[1];
              ifres = e;
            } else {
              let tuple = match;
              let e = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Int") {
                let ifres;
                if (ctor._0 === 1) {
                  ifres = e;
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let ctor = tuple[1];
                  let ifres;
                  if (ctor.TAG === "Mul") {
                    let g = ctor._0;
                    let h = ctor._1;
                    ifres = *:(*:(f, g), h);
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let g = tuple[1];
                    ifres = {TAG: "Mul", _0: f, _1: g};
                  }
                  ifres = ifres;
                }
                ifres = ifres;
              } else {
                let tuple = match;
                let f = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Mul") {
                  let g = ctor._0;
                  let h = ctor._1;
                  ifres = *:(*:(f, g), h);
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let g = tuple[1];
                  ifres = {TAG: "Mul", _0: f, _1: g};
                }
                ifres = ifres;
              }
              ifres = ifres;
            }
            ifres = ifres;
          } else {
            let tuple = match;
            let e = tuple[0];
            let ctor = tuple[1];
            let ifres;
            if (ctor.TAG === "Int") {
              let ifres;
              if (ctor._0 === 1) {
                ifres = e;
              } else {
                let tuple = match;
                let f = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Mul") {
                  let g = ctor._0;
                  let h = ctor._1;
                  ifres = *:(*:(f, g), h);
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let g = tuple[1];
                  ifres = {TAG: "Mul", _0: f, _1: g};
                }
                ifres = ifres;
              }
              ifres = ifres;
            } else {
              let tuple = match;
              let f = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Mul") {
                let g = ctor._0;
                let h = ctor._1;
                ifres = *:(*:(f, g), h);
              } else {
                let tuple = match;
                let f = tuple[0];
                let g = tuple[1];
                ifres = {TAG: "Mul", _0: f, _1: g};
              }
              ifres = ifres;
            }
            ifres = ifres;
          }
          ifres = ifres;
        }
        ifres = ifres;
      }
      ifres = ifres;
    }
    ifres = ifres;
  } else {
    let tuple = match;
    let ctor = tuple[0];
    let ifres;
    if (ctor.TAG === "Int") {
      let ifres;
      if (ctor._0 === 0) {
        ifres = {TAG: "Int", _0: 0};
      } else {
        let tuple = match;
        let ctor = tuple[1];
        let ifres;
        if (ctor.TAG === "Int") {
          let ifres;
          if (ctor._0 === 0) {
            ifres = {TAG: "Int", _0: 0};
          } else {
            let tuple = match;
            let ctor = tuple[0];
            let ifres;
            if (ctor.TAG === "Int") {
              let ifres;
              if (ctor._0 === 1) {
                let e = tuple[1];
                ifres = e;
              } else {
                let tuple = match;
                let e = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Int") {
                  let ifres;
                  if (ctor._0 === 1) {
                    ifres = e;
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let ctor = tuple[1];
                    let ifres;
                    if (ctor.TAG === "Mul") {
                      let g = ctor._0;
                      let h = ctor._1;
                      ifres = *:(*:(f, g), h);
                    } else {
                      let tuple = match;
                      let f = tuple[0];
                      let g = tuple[1];
                      ifres = {TAG: "Mul", _0: f, _1: g};
                    }
                    ifres = ifres;
                  }
                  ifres = ifres;
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let ctor = tuple[1];
                  let ifres;
                  if (ctor.TAG === "Mul") {
                    let g = ctor._0;
                    let h = ctor._1;
                    ifres = *:(*:(f, g), h);
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let g = tuple[1];
                    ifres = {TAG: "Mul", _0: f, _1: g};
                  }
                  ifres = ifres;
                }
                ifres = ifres;
              }
              ifres = ifres;
            } else {
              let tuple = match;
              let e = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Int") {
                let ifres;
                if (ctor._0 === 1) {
                  ifres = e;
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let ctor = tuple[1];
                  let ifres;
                  if (ctor.TAG === "Mul") {
                    let g = ctor._0;
                    let h = ctor._1;
                    ifres = *:(*:(f, g), h);
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let g = tuple[1];
                    ifres = {TAG: "Mul", _0: f, _1: g};
                  }
                  ifres = ifres;
                }
                ifres = ifres;
              } else {
                let tuple = match;
                let f = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Mul") {
                  let g = ctor._0;
                  let h = ctor._1;
                  ifres = *:(*:(f, g), h);
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let g = tuple[1];
                  ifres = {TAG: "Mul", _0: f, _1: g};
                }
                ifres = ifres;
              }
              ifres = ifres;
            }
            ifres = ifres;
          }
          ifres = ifres;
        } else {
          let tuple = match;
          let ctor = tuple[0];
          let ifres;
          if (ctor.TAG === "Int") {
            let ifres;
            if (ctor._0 === 1) {
              let e = tuple[1];
              ifres = e;
            } else {
              let tuple = match;
              let e = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Int") {
                let ifres;
                if (ctor._0 === 1) {
                  ifres = e;
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let ctor = tuple[1];
                  let ifres;
                  if (ctor.TAG === "Mul") {
                    let g = ctor._0;
                    let h = ctor._1;
                    ifres = *:(*:(f, g), h);
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let g = tuple[1];
                    ifres = {TAG: "Mul", _0: f, _1: g};
                  }
                  ifres = ifres;
                }
                ifres = ifres;
              } else {
                let tuple = match;
                let f = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Mul") {
                  let g = ctor._0;
                  let h = ctor._1;
                  ifres = *:(*:(f, g), h);
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let g = tuple[1];
                  ifres = {TAG: "Mul", _0: f, _1: g};
                }
                ifres = ifres;
              }
              ifres = ifres;
            }
            ifres = ifres;
          } else {
            let tuple = match;
            let e = tuple[0];
            let ctor = tuple[1];
            let ifres;
            if (ctor.TAG === "Int") {
              let ifres;
              if (ctor._0 === 1) {
                ifres = e;
              } else {
                let tuple = match;
                let f = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Mul") {
                  let g = ctor._0;
                  let h = ctor._1;
                  ifres = *:(*:(f, g), h);
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let g = tuple[1];
                  ifres = {TAG: "Mul", _0: f, _1: g};
                }
                ifres = ifres;
              }
              ifres = ifres;
            } else {
              let tuple = match;
              let f = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Mul") {
                let g = ctor._0;
                let h = ctor._1;
                ifres = *:(*:(f, g), h);
              } else {
                let tuple = match;
                let f = tuple[0];
                let g = tuple[1];
                ifres = {TAG: "Mul", _0: f, _1: g};
              }
              ifres = ifres;
            }
            ifres = ifres;
          }
          ifres = ifres;
        }
        ifres = ifres;
      }
      ifres = ifres;
    } else {
      let tuple = match;
      let ctor = tuple[1];
      let ifres;
      if (ctor.TAG === "Int") {
        let ifres;
        if (ctor._0 === 0) {
          ifres = {TAG: "Int", _0: 0};
        } else {
          let tuple = match;
          let ctor = tuple[0];
          let ifres;
          if (ctor.TAG === "Int") {
            let ifres;
            if (ctor._0 === 1) {
              let e = tuple[1];
              ifres = e;
            } else {
              let tuple = match;
              let e = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Int") {
                let ifres;
                if (ctor._0 === 1) {
                  ifres = e;
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let ctor = tuple[1];
                  let ifres;
                  if (ctor.TAG === "Mul") {
                    let g = ctor._0;
                    let h = ctor._1;
                    ifres = *:(*:(f, g), h);
                  } else {
                    let tuple = match;
                    let f = tuple[0];
                    let g = tuple[1];
                    ifres = {TAG: "Mul", _0: f, _1: g};
                  }
                  ifres = ifres;
                }
                ifres = ifres;
              } else {
                let tuple = match;
                let f = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Mul") {
                  let g = ctor._0;
                  let h = ctor._1;
                  ifres = *:(*:(f, g), h);
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let g = tuple[1];
                  ifres = {TAG: "Mul", _0: f, _1: g};
                }
                ifres = ifres;
              }
              ifres = ifres;
            }
            ifres = ifres;
          } else {
            let tuple = match;
            let e = tuple[0];
            let ctor = tuple[1];
            let ifres;
            if (ctor.TAG === "Int") {
              let ifres;
              if (ctor._0 === 1) {
                ifres = e;
              } else {
                let tuple = match;
                let f = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Mul") {
                  let g = ctor._0;
                  let h = ctor._1;
                  ifres = *:(*:(f, g), h);
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let g = tuple[1];
                  ifres = {TAG: "Mul", _0: f, _1: g};
                }
                ifres = ifres;
              }
              ifres = ifres;
            } else {
              let tuple = match;
              let f = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Mul") {
                let g = ctor._0;
                let h = ctor._1;
                ifres = *:(*:(f, g), h);
              } else {
                let tuple = match;
                let f = tuple[0];
                let g = tuple[1];
                ifres = {TAG: "Mul", _0: f, _1: g};
              }
              ifres = ifres;
            }
            ifres = ifres;
          }
          ifres = ifres;
        }
        ifres = ifres;
      } else {
        let tuple = match;
        let ctor = tuple[0];
        let ifres;
        if (ctor.TAG === "Int") {
          let ifres;
          if (ctor._0 === 1) {
            let e = tuple[1];
            ifres = e;
          } else {
            let tuple = match;
            let e = tuple[0];
            let ctor = tuple[1];
            let ifres;
            if (ctor.TAG === "Int") {
              let ifres;
              if (ctor._0 === 1) {
                ifres = e;
              } else {
                let tuple = match;
                let f = tuple[0];
                let ctor = tuple[1];
                let ifres;
                if (ctor.TAG === "Mul") {
                  let g = ctor._0;
                  let h = ctor._1;
                  ifres = *:(*:(f, g), h);
                } else {
                  let tuple = match;
                  let f = tuple[0];
                  let g = tuple[1];
                  ifres = {TAG: "Mul", _0: f, _1: g};
                }
                ifres = ifres;
              }
              ifres = ifres;
            } else {
              let tuple = match;
              let f = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Mul") {
                let g = ctor._0;
                let h = ctor._1;
                ifres = *:(*:(f, g), h);
              } else {
                let tuple = match;
                let f = tuple[0];
                let g = tuple[1];
                ifres = {TAG: "Mul", _0: f, _1: g};
              }
              ifres = ifres;
            }
            ifres = ifres;
          }
          ifres = ifres;
        } else {
          let tuple = match;
          let e = tuple[0];
          let ctor = tuple[1];
          let ifres;
          if (ctor.TAG === "Int") {
            let ifres;
            if (ctor._0 === 1) {
              ifres = e;
            } else {
              let tuple = match;
              let f = tuple[0];
              let ctor = tuple[1];
              let ifres;
              if (ctor.TAG === "Mul") {
                let g = ctor._0;
                let h = ctor._1;
                ifres = *:(*:(f, g), h);
              } else {
                let tuple = match;
                let f = tuple[0];
                let g = tuple[1];
                ifres = {TAG: "Mul", _0: f, _1: g};
              }
              ifres = ifres;
            }
            ifres = ifres;
          } else {
            let tuple = match;
            let f = tuple[0];
            let ctor = tuple[1];
            let ifres;
            if (ctor.TAG === "Mul") {
              let g = ctor._0;
              let h = ctor._1;
              ifres = *:(*:(f, g), h);
            } else {
              let tuple = match;
              let f = tuple[0];
              let g = tuple[1];
              ifres = {TAG: "Mul", _0: f, _1: g};
            }
            ifres = ifres;
          }
          ifres = ifres;
        }
        ifres = ifres;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};

let simplify;

simplify = x => {
  let f = x;
  let ctor = x;
  let ifres;
  if (ctor.TAG === "Int") {
    ifres = f;
  } else {
    let ctor = x;
    let ifres;
    if (ctor.TAG === "Var") {
      ifres = f;
    } else {
      let ctor = x;
      let ifres;
      if (ctor.TAG === "Add") {
        let f = ctor._0;
        let g = ctor._1;
        ifres = +:(simplify(f), simplify(g));
      } else {
        let ctor = x;
        let ifres;
        if (ctor.TAG === "Mul") {
          let f = ctor._0;
          let g = ctor._1;
          ifres = *:(simplify(f), simplify(g));
        } else {
          ifres = undefined;
        }
        ifres = ifres;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};