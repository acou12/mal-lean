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
  fun c => 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z'

-- todo: remove partial and prove termination
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
    | cs => do
      let (token, rest_chars) ← use_tokenizers tokenizers cs
      let rest_tokens ← tokenize_chars rest_chars
      return String.mk token :: rest_tokens

def tokenize (source : String) : Option (List String) :=
  tokenize_chars (source.data)

#eval tokenize "(very nice [it appears to {work}])"
#eval tokenize "this is none!"
