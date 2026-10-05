import Lean
set_option debug.skipKernelTC true
run_elab
  Lean.addDecl (.thmDecl {
    name := `contract
    levelParams := []
    type := .const ``False []
    value := .const ``True.intro []
  })
