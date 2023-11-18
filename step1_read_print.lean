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
    || '0' <= c && c <= '9'
    || c == '+' || c == '-' || c == '/'
    || c == '*' || c == '?' || c == '!'
    || c == '='

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
    | cs => do
      let (token, rest_chars) ← use_tokenizers tokenizers cs
      let rest_tokens ← tokenize_chars rest_chars
      return String.mk token :: rest_tokens

def tokenize (source : String) : Option (List String) :=
  tokenize_chars (source.data)

inductive AST where
  | atom : String → AST
  | list : List AST → AST
deriving Repr

structure NonemptyList (α : Type) where
  head : α
  rest : List α

notation x "|:" xs => NonemptyList.mk x xs

mutual

partial def read_list (source : NonemptyList String) : Option (AST × List String) :=
  let rec read_items_until_end (source : List String) : Option (List AST × List String) :=
    match source with
      | [] => none
      | ")" :: ts => some ([], ts)
      | t :: ts => do
          let (first_item, rest_tokens) ← read_form (t :: ts)
          let (rest_items, rest_tokens) ← read_items_until_end rest_tokens
          return (first_item :: rest_items, rest_tokens)

  (read_items_until_end source.rest).map
    fun (items, rest_tokens) => (AST.list items, rest_tokens)

partial def read_atom (source : NonemptyList String) : Option (AST × List String) :=
  some (AST.atom source.head, source.rest)

partial def read_form (source : List String) : Option (AST × List String) :=
  match source with
    | [] => none
    | "(" :: ts => read_list ("(" |: ts)
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

def size (ast : AST) : Nat :=

  let rec asum (as : List AST) : Nat :=
    match as with
    | [] => 0
    | a :: as => size a + asum as

  match ast with
  | AST.atom _ => 1
  | AST.list xs => asum xs + 1

def stringify (ast : AST) : String :=
  match ast with
  | AST.atom x => x
  | AST.list xs =>
    let rec map (as : List AST) :=
      match as with
      | [] => []
      | x :: xs => stringify x :: map xs
    s!"({join_spaces (map xs)})"

mutual

def all_no_empty_lists (as : List AST) :=
  match as with
    | [] => False
    | a :: [] => no_empty_lists a
    | a :: as => no_empty_lists a ∧ all_no_empty_lists as

def no_empty_lists (ast : AST) : Prop :=
  match ast with
    | .atom _ => True
    | .list as => as ≠ [] ∧ all_no_empty_lists as

end

-- there has gotta be a simpler way to do this

inductive ListValidateResult (as : List AST) (α : Type) where
  | success : all_no_empty_lists as → ListValidateResult as α
  | error : α → ListValidateResult as α

inductive ValidateResult (ast : AST) (α : Type) where
  | success : no_empty_lists ast → ValidateResult ast α
  | error : α → ValidateResult ast α

mutual

def validate_ast_list (as : List AST) : ListValidateResult as String :=
  match as with
  | [] => .error "no empty lists."
  | a :: [] =>
    match validate a with
      | .success h => ListValidateResult.success h
      | .error m => .error m
  | a :: as =>
    match validate a with
      | .success h =>
        let rest_validate := validate_ast_list as
        match rest_validate with
          | .success h₂ => .success (by
            have : as ≠ [] := by
              intro empty
              have := Eq.subst empty h₂
              contradiction
            simp only [all_no_empty_lists]
            apply And.intro
            exact h
            exact h₂
          )
          | .error m => .error m
      | .error m => .error m

def validate (ast : AST) : ValidateResult ast String :=
  match ast with
  | AST.atom _ => ValidateResult.success (by simp only [no_empty_lists])
  | AST.list as => match validate_ast_list as with
    | .success h => ValidateResult.success (by
        simp only [no_empty_lists]
        exact And.intro (by
          intro empty
          have := Eq.subst empty h
          contradiction
        ) h
    )
    | .error m => .error m

end

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

inductive RuntimeType where
  | nat : RuntimeType
  | fn : RuntimeType

inductive RuntimeValue where
  | nat : Nat → RuntimeValue
  | fn : List String → AST → RuntimeValue
  | native_fn : String → RuntimeValue

abbrev ReplEnv := List (String × RuntimeValue)
abbrev NativeEnv := List (String × (List RuntimeValue → Option RuntimeValue))

def binary_nat_native (f : Nat → Nat → Nat) : List RuntimeValue → Option RuntimeValue
  | (.nat x) :: (.nat y) :: [] => .some $ .nat (f x y)
  | _ => .none

def fc : NativeEnv := [
  ("+", binary_nat_native (HAdd.hAdd)),
  ("-", binary_nat_native (HSub.hSub)),
  ("*", binary_nat_native (HMul.hMul)),
  ("/", binary_nat_native (HDiv.hDiv)),
  ("%", binary_nat_native (HMod.hMod)),
  ("==", binary_nat_native (fun x y => if x = y then 1 else 0))
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
  match ast with
    | .atom label =>
        if let .some f := env.map_get label then
          f
        else if let .some _ := fc.map_get label then
          .some $ .native_fn label
        else String.toNat? label |>.map (.nat)

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

    | .list (f_expr :: xs) => do
        let f ← eval_ast f_expr env
        let rec build_env (env : ReplEnv) (params : List String) (xs : List AST) : Option ReplEnv :=
          match params, xs with
            | p :: ps, x :: xs => do (p, ←(eval_ast x env)) :: (←(build_env env ps xs))
            | [], [] => some env
            | _, _ => .none -- invalid number of paramters!
        match f with
          | .fn params fast =>
            eval_ast fast (← build_env env params xs)
          | .native_fn name => do
            let f ← fc.map_get name
            let rec eval_all : (xs : List AST) → Option (List RuntimeValue)
              | x :: xs => do
                let x_eval ← eval_ast x env
                let rest ← eval_all xs
                return x_eval :: rest
              | [] => .some []
            f $ ← eval_all xs
          | .nat _ => .none

    | .list [] => .none

-- #eval do
--   let tokens ← tokenize "(+ 1 1)"
--   let ast ← parse tokens
--   let eval ← eval_ast ast repl_env []
--   return eval

def read : String → Option AST := (do parse $ ←tokenize ·)
def eval : AST → Option RuntimeValue := (eval_ast · [])
def print : RuntimeValue → String
  | .nat n => toString n
  | .fn params _ => s!"fn with {params}"
  | .native_fn name => s!"native fn {name}"

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


/-

ideas:

(seq*
  (let x 10)
  (let y (* x 2))
  (+ x y
)

==

(let x 10
(let y (* x 2)
(+ x y)))


(seq*
  (f)
  (g)
  ...
) == (f (g ...))

infix structures:

(+ 1 2) == [1 + 2]

(+ (* 2 3) (* (- 4 1) 5)) == [[2 * 3] + [[4 - 1] * 5]]

(cons x xs) == [x cons xs] == [x :: xs]

-/
