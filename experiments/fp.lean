import Mathlib.Data.Set.Basic

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

def enumerate : Nat := Id.run do
  let mut x := 0
  while x < 10 do
    x := x - 3
  return x

set_option pp.notation false in

#print enumerate

-- #eval enumerate 10

#check fun x y => x <&&> y

partial def f : IO Unit := do while true do pure ()

def loops : IO Unit := do 
  while h : true do
    pure ()
  return ()

def loops2 : IO Unit := do 
  let mut x := 10
  while x > 0 do
    x := x - 1
    IO.println x
  return ()

#print loops

-- #eval loops

inductive Expression where
  | x : Expression
  | parens : Expression → Expression
  | add : Expression → Expression → Expression
  | mul : Expression → Expression → Expression
deriving Repr

structure Error where
  message : String

-- def parse (s : String) : Sum Expression Error :=
--   let rec parse_expression (s : List Char) : Sum (Expression × List Char) Error := match s with
--     | 'x' :: cs => Sum.inl (Expression.x, cs)
--     | '(' :: cs => do
--       let (innerExpr, cs) ← parse_expression cs
--       let expr := Expression.parens innerExpr
--       return (expr, cs)
--     | _ => none

  -- (parse_expression s.data).map (·.fst)

-- #eval parse "(x)"

