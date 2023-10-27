def read : String → String := id
def eval : String → String := id
def print : String → String := id

def rep (s: String) : String := print $ eval $ read s

partial def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  let rec repl : IO Unit := do
    stdout.putStr "user> "
    let inp ← stdin.getLine

    if inp != "" then
      stdout.putStr $ rep inp
      repl

  repl
