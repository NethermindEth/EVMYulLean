unsafe def unsafePerformIO {τ} [Inhabited τ] (io : IO τ) : τ :=
  match unsafeIO io with
    | Except.ok    a => a
    | Except.error e => panic! s!"unsafePerformIO was a not great idea after all: {e}"

@[implemented_by unsafePerformIO]
def totallySafePerformIO {τ} [Inhabited τ] (io : IO τ) : τ := Inhabited.default
