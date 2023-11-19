def tokenize_rule (rule: Char → Bool) (source : List Char) : Option (List Char × List Char) :=
  match source with
    | [] => none
    | c :: cs => do
      if rule c then
        let rest := tokenize_rule rule cs
        match rest with
          | none => some ([c], cs)
          | some (rest_id, rest_tokens) => some (c :: rest_id, rest_tokens)
      else
        none

def tokenize_single (prop : Char → Bool) (source : List Char) : Option (List Char × List Char) :=
  match source with
    | [] => none
    | c :: cs => if prop c then some ([c], cs) else none

def tokenize_punc := tokenize_single ("()[]{}'`~^@".data.contains ·)
def tokenize_id := tokenize_rule
  fun c => 'a' <= c && c <= 'z'
    || 'A' <= c && c <= 'Z'
    || '0' <= c && c <= '9' || "+-/*?=!#.".data.contains c

partial def tokenize_chars (source : List Char) : Option (List String) :=
  let tokenizers := [tokenize_punc, tokenize_id]

  let rec use_tokenizers
    (ts : List (List Char → Option (List Char × List Char))) (cs : List Char)
      : Option (List Char × List Char) :=

    match ts with
      | [] => none
      | t :: ts => (t cs).orElse (fun _ => use_tokenizers ts cs)

  match source with
    | [] => some []
    | ' ' :: rest => tokenize_chars rest
    | '\n' :: rest => tokenize_chars rest
    | ',' :: rest => tokenize_chars rest
    | cs => do
      let (token, rest_chars) ← use_tokenizers tokenizers cs
      let rest_tokens ← tokenize_chars rest_chars
      return String.mk token :: rest_tokens

def tokenize (source : String) : Option (List String) :=
  tokenize_chars (source.data)

inductive AST where
  | atom : String → AST
  | list : List AST → AST
  | vector : List AST → AST
deriving Repr

structure NonemptyList (α : Type) where
  head : α
  rest : List α

notation x "|:" xs => NonemptyList.mk x xs

mutual

partial def read_list (source : List String) : Option (AST × List String) :=
  let rec read_items_until_end (source : List String) : Option (List AST × List String) :=
    match source with
      | [] => none
      | ")" :: ts => some ([], ts)
      | t :: ts => do
          let (first_item, rest_tokens) ← read_form (t :: ts)
          let (rest_items, rest_tokens) ← read_items_until_end rest_tokens
          return (first_item :: rest_items, rest_tokens)

  (read_items_until_end source).map
    fun (items, rest_tokens) => (AST.list items, rest_tokens)

partial def read_vector (source : List String) : Option (AST × List String) :=
  let rec read_items_until_end (source : List String) : Option (List AST × List String) :=
    match source with
      | [] => none
      | "]" :: ts => some ([], ts)
      | t :: ts => do
          let (first_item, rest_tokens) ← read_form (t :: ts)
          let (rest_items, rest_tokens) ← read_items_until_end rest_tokens
          return (first_item :: rest_items, rest_tokens)

  (read_items_until_end source).map
    fun (items, rest_tokens) => (AST.vector items, rest_tokens)

partial def read_atom (source : NonemptyList String) : Option (AST × List String) :=
  some (AST.atom source.head, source.rest)

partial def read_form (source : List String) : Option (AST × List String) :=
  match source with
    | [] => none
    | "(" :: ts => read_list ts
    | "[" :: ts => read_vector ts
    | t :: ts => read_atom (t |: ts)

partial def parse (source : List String) : Option AST :=
  match read_form source with
    | some (ast, []) => some ast
    | _ => none

end

def join_spaces (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: [] => x
  | x :: xs => s!"{x} {join_spaces xs}"

def stringify (ast : AST) : String :=
  let rec map (as : List AST) :=
    match as with
    | [] => []
    | x :: xs => stringify x :: map xs
  match ast with
  | AST.atom x => x
  | AST.list xs =>
    s!"({join_spaces (map xs)})"
  | AST.vector xs =>
    s!"[{join_spaces (map xs)}]"

-- def list_heads (ast : AST) (hnempty : no_empty_lists ast) : List String :=
--   match ast with
--     | .atom _ => []
--     | .list as => match as with
--       | [] => by
--         simp only [no_empty_lists] at *
--         have := hnempty.left
--         contradiction
--       | a :: as =>
--         match a with
--           | .atom label => label :: list_heads_iter as _
--             where list_heads_iter (as : List AST) (h : all_no_empty_lists as) : List String :=
--               match as with
--                 | [] => []
--                 | a :: [] =>
--                   have : all_no_empty_lists (a :: []) = no_empty_lists a := rfl
--                   list_heads a (by assumption)
--                 | a :: as =>
--                   have : all_no_empty_lists (a :: as) = no_empty_lists a ∧ all_no_empty_lists as := by
--                     simp only [all_no_empty_lists] at *
--                   (list_heads a (by admit)) ++ (list_heads_iter as h)

inductive RuntimeValue where
  | nat : Nat → RuntimeValue
  | vector : List RuntimeValue → RuntimeValue
  | fn : List String → AST → RuntimeValue
  | native_fn : String → RuntimeValue

abbrev ReplEnv := List (String × RuntimeValue)
abbrev NativeEnv := List (String × (List RuntimeValue → Option RuntimeValue))

def binary_nat_native (f : Nat → Nat → Nat) : List RuntimeValue → Option RuntimeValue
  | (.nat x) :: (.nat y) :: [] => .some $ .nat (f x y)
  | _ => .none

def cons : List RuntimeValue → Option RuntimeValue
  | x :: (.vector xs) :: [] => .some $ .vector (x :: xs)
  | _ => .none

def car : List RuntimeValue → Option RuntimeValue
  | (.vector xs) :: [] => match xs with
    | [] => .none
    | x :: _ => .some x
  | _ => .none

def cdr : List RuntimeValue → Option RuntimeValue
  | (.vector xs) :: [] => match xs with
    | [] => .none
    | _ :: xs => .some $ .vector xs
  | _ => .none

def len : List RuntimeValue → Option RuntimeValue
  | (.vector xs) :: [] => .some $ .nat xs.length
  | _ => .none

def ns : NativeEnv := [
  ("+", binary_nat_native (HAdd.hAdd)),
  ("-", binary_nat_native (HSub.hSub)),
  ("*", binary_nat_native (HMul.hMul)),
  ("/", binary_nat_native (HDiv.hDiv)),
  ("%", binary_nat_native (HMod.hMod)),
  ("==", binary_nat_native (fun x y => if x = y then 1 else 0)),
  ("cons", cons),
  ("car", car),
  ("cdr", cdr),
  ("len", len)
]

-- def Repeat (n : Nat) (t : Type) : Type := Id.run do
--   let mut tuple := t
--   for _ in List.range (n - 1) do
--     tuple := t × tuple
--   return tuple

-- example : Repeat 5 Nat := (10, 3, 15, 7, 29)
-- example : Repeat 5 Nat := (10, 3, 15, 7, 29, 2)

def binary_first_class (f : Nat → Nat → Nat) : (List RuntimeValue → Option RuntimeValue)
    | .nat x :: .nat y :: [] => some $ .nat $ f x y
    | _ => .none

def List.map_get : List (String × α) → String → Option α
  | [], _ => none
  | (x, a) :: xs, y => if x = y then some a else map_get xs y

partial def eval_ast (ast : AST) (env : ReplEnv) : Option RuntimeValue :=
  let rec eval_all : (xs : List AST) → Option (List RuntimeValue)
    | x :: xs => do
      let x_eval ← eval_ast x env
      let rest ← eval_all xs
      return x_eval :: rest
    | [] => .some []
  match ast with
    | .atom label =>
        if let .some f := env.map_get label then
          f
        else if let .some _ := ns.map_get label then
          .some $ .native_fn label
        else String.toNat? label |>.map (.nat)

    | .vector xs => do
      let elements ← eval_all xs
      return .vector elements

    | .list (.atom "fn*" :: .list params :: expr :: []) => do
        -- the label of each atom in params, or `none` if any are not atoms
        let param_labels ← List.foldl (fun m p_ast => match m, p_ast with
          | .some acc, .atom label => .some (acc ++ [label])
          | _, _ => none
        ) (Option.some []) params

        RuntimeValue.fn param_labels expr

    | .list (.atom "if" :: cond_expr :: if_expr :: else_expr :: []) => do
        let cond ← eval_ast cond_expr env
        match cond with
          | .nat 0 => eval_ast else_expr env
          | _ => eval_ast if_expr env

    | .list (.atom "let*" :: .atom name :: value_expr :: expr :: []) => do
        let value ← eval_ast value_expr env
        let new_env_item := (name, value)
        let new_env := new_env_item :: env
        eval_ast expr new_env

    | .list (.atom "seq*" :: as) => do
        let rec build_seq : List AST → Option AST
          | []      => .none
          | a :: [] => .some a
          | a :: as => match a with
            | .list inside_a => do
              .some $ .list (inside_a ++ [←build_seq as])
            | _ => none
        eval_ast (←build_seq as) env

      /-
         jank "syntactical" comment; evaluates to the value of
         the last element and ignores the rest
      -/
    | .list (.atom "#" :: as) => List.getLast? as >>= (eval_ast · env)

    | .list (f_expr :: xs) => do
        let f ← eval_ast f_expr env
        let rec build_env (env : ReplEnv) (params : List String) (xs : List AST) : Option ReplEnv :=
          match params, xs with
            | p :: ps, x :: xs => do (p, ←(eval_ast x env)) :: (←(build_env env ps xs))
            | [], [] => some env
            | [], _ :: _ |
              _ :: _, [] => .none -- invalid number of paramters!
        match f with
          | .fn params expr =>
            let new_env ← build_env env params xs
            eval_ast expr new_env
          | .native_fn name => do
            let f ← ns.map_get name
            f $ ← eval_all xs
          | .nat _ => .none
          | .vector _ => .none

    | .list [] => .none

-- termination_by eval_ast ast env => sizeOf ast
--                eval_ast.eval_all x => sizeOf x
--                eval_ast.build_env env params xs => sizeOf xs

-- #eval tokenize "[()]"

def read : String → Option AST := (do parse $ ←tokenize ·)
def eval : AST → Option RuntimeValue := (eval_ast · [])
partial def print : RuntimeValue → String
  | .nat n => toString n
  | .vector xs => s!"[{String.intercalate " " (List.map print xs)}]"
  | .fn params _ => s!"fn with {params}"
  | .native_fn name => s!"native fn {name}"
-- termination_by print rv => sizeOf rv

def rep (s : String) : Option String := do print $ ←eval $ ←read s

partial def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  -- let filePath := System.mkFilePath ["test.mal"]

  let rec repl : IO Unit := do
    stdout.putStr "user> "
    let inp := (←stdin.getLine).trim
    -- let inp ← IO.FS.readFile filePath

    if inp != "" then
      let r := rep inp
      stdout.putStrLn $ r.getD "err!"
      repl

  repl
