import Mugda.Core

/-- Standalone CLI entry point (`lake exe mugda <file.ma>` or `./mugda <file.ma>`). -/
def main (args : List String) : IO UInt32 := do
  IO.println "***** Mugda v1.0 (Constructive Lean 4 Edition) *****"
  match args with
  | [] =>
      IO.eprintln "Usage: mugda <file.ma>"
      pure 1
  | path :: _ =>
      let src ← IO.FS.readFile path
      match MugdaCore.tokenize src >>= MugdaCore.parseTokens with
      | .error err =>
          IO.eprintln ("parse error:\n" ++ err)
          pure 1
      | .ok cdecls =>
          IO.println "--- scope checking ---"
          match MugdaCore.scopeCheck cdecls with
          | .error err =>
              IO.eprintln ("scope check error: " ++ err)
              pure 1
          | .ok adecls =>
              IO.println "--- type checking ---"
              match MugdaCore.runTypeCheck {} (MugdaCore.typeCheckDecls MugdaCore.defaultFuel adecls) with
              | .error err =>
                  IO.println ("error during typechecking:\n" ++ err)
                  pure 1
              | .ok (_, st) =>
                  st.warnings.forM IO.println
                  IO.println "--- evaluating ---"
                  let evalDecls := adecls.filterMap fun d =>
                    match d with
                    | .LetDecl true (.mk n _) e => some (n, e)
                    | _                         => none
                  evalDecls.forM fun (n, e) =>
                    match MugdaCore.runTypeCheck st (MugdaCore.whnf MugdaCore.defaultFuel [] e) with
                    | .ok (v, _) => IO.println (n ++ " evaluates to " ++ MugdaCore.showVal v)
                    | .error err => IO.println ("eval error in " ++ n ++ ": " ++ err)
                  pure (if st.warnings.isEmpty then 0 else 1)
