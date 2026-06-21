module
public import Lean
public meta section
open Lean Parser Meta Elab Command

def Lean.Parser.ParserTrace.toDebugTrace
  (t : ParserTrace)
  (omitNode : String → Bool)
  (posStr : String.Pos.Raw → String) : CommandElabM Unit
:= do
  match t with
  | .stop => pure ()
  | .parser lhsPrec pos descr fail children =>
    if omitNode descr then
      for child in children do
        toDebugTrace child omitNode posStr
    else
      discard <| Lean.withTraceNode `debug (fun _ => return m!"Running `{descr}` at {posStr pos} with lhsPrec {lhsPrec}") do
        for child in children do
          toDebugTrace child omitNode posStr
        return !fail
  | .cacheHit key entry =>
    trace[debug] m!"Cache hit for {key.parserName} at {posStr key.pos}: {format entry.stx}"
  | .log str => trace[debug] str
  | .error err pos => trace[debug] "Error at {posStr pos}: {err.toString}"
  | .result stx =>
    trace[debug] m!"Syntax: {format stx}"

def Lean.MessageData.intercalate : MessageData → List MessageData → MessageData
:= flip .joinSep

def Lean.Parser.Parser.traceParse
  (p : Parser) (input : String)
  (omits : List Name := [])
  (stxToMsg : Syntax → MessageData := .ofSyntax)
: CommandElabM Unit
:= do
  let omits := omits.map toString
  let omits : Std.HashSet String := .ofList <| omits ++ omits.map (s!"node {·}")
  let ictx := {
    inputString := input
    fileName := "input"
    fileMap := .ofString input
  }
  let posStr pos :=
    let pos := ictx.fileMap.toPosition pos
    s!"input:{pos.line}:{pos.column}"
  let pmctx := {
    env := ← getEnv
    options := ← getOptions
    currNamespace := ← getCurrNamespace
    openDecls := ← getOpenDecls
  }
  let toks := getTokenTable (← getEnv)
  let s := mkParserState input
  let s := { s with traces := #[.stop] }
  let s := (andthenFn whitespace p.fn).run ictx pmctx toks s
  (if s.errorMsg.isNone then logInfo else logError) =<< do
    let mut msg : MessageData := .nil
    match s.errorMsg with
      | none => msg := (msg ++ ·) <|
        (m!"Parser succeeded, had arity {s.stxStack.size} and produced:" ++ ·) <|
        (indentD · ++ "\n") <| .intercalate "\n" <|
          stxToMsg <$> (s.stxStack.extract 0 s.stxStack.size).toList
      | some e => msg := (msg ++ ·) <|
        (m!"Parser failed with arity {s.stxStack.size} and error:" ++ ·) <|
        (indentD m!"{e}") ++ "\n"
    if (String.pos! input s.pos).IsAtEnd then
      msg := msg ++ "Input was consumed completely."
    else
      msg := msg ++
        m!"Parsing ended at {posStr s.pos} and left" ++
        indentD (input.extract (String.pos! input s.pos) input.endPos).quote ++
        "\nunparsed."
    return msg
  withScope (fun scope => { scope with opts := scope.opts.setBool `trace.debug true }) do
    for trace in s.traces do
      trace.toDebugTrace omits.contains posStr

namespace TraceParse

def resolveParser (parserName : Ident) : CommandElabM Parser :=
  withRef parserName do
    let res ← liftCoreM <| Lean.Parser.resolveParserName <| parserName
    if res.isEmpty then throwError "Unknown parser `{parserName}`"
    let [res] := res | throwError "Ambiguous parser name `{parserName}`"
    match res with
      | .category nm => pure (categoryParser nm 0)
      | .parser nm _ => pure { fn := (evalParserConst nm) }
      | .alias val =>
        match val with
        | .const c => pure c
        | _ => throwError "Unexpected parser alias `{parserName}`, must not take parameters"

syntax (name := parse)
  "#parse" (" : " term:max)?
    ppSpace ("+" noWs (&"format" <|> &"repr"))?
    ppSpace ("-" noWs ident)*
    ppSpace str
: command


-- Taken from https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Defining-New-Syntax/#removeSourceInfo-_LPAR_in-Representing-Syntax-as-Constructors_RPAR_
def removeSourceInfo : Syntax → Syntax
  | .atom _ str => .atom .none str
  | .ident _ str x pre => .ident .none str x pre
  | .node _ k children => .node .none k (children.map removeSourceInfo)
  | .missing => .missing

def collectTokensIntoContext (p : Parser) : Parser where
  info := p.info
  fn :=
    -- The following is taken from `evalParserConst`. Without this, when `p` is
    -- an anonymous parser, and defines/uses new keywords/tokens, those do not
    -- get recognized. I do not yet understand the details. But it seems to work
    -- well.
    adaptUncacheableContextFn
      (fun ctx => { ctx with tokens := p.info.collectTokens [] |>.foldl (fun tks tk => tks.insert tk tk) ctx.tokens })
      p.fn

/--
Try to parse a string and display the resulting parser state und a trace.

- `#parse s` tries to parse the string `s` as a term
- `#parse : id s` tries to parse `s` as an `id`, any identifier resolvable by
  `Lean.Parser.resolveParserName`
- `#parse : e s` runs any `e : Lean.Parser.Parser` on `s`
- `#parse +format s` or `#parse +repr s` use `format` or `repr` instead of the
  pretty printer for the resulting `Syntax`
- `#parse -omit₁ -omit₂ … s` omits nodes for `omit₁`, `omit₂`, … from the
  resulting trace, for example `#parse : binderIdent -token -orElse "x"`

The order of argments is exemplified by `#parse : ident +repr -token "x"`.
-/
elab_rules : command
| `(#parse%$tk $[: $parser]? $[+$stxToMsg?]? $[-$omits:ident]* $input:str) => do
  let parser : Parser ← match parser with
    | none => resolveParser <| mkIdent `term
    | some term => withRef term <| match term with
        | `($id:ident) => resolveParser id
        | term => liftTermElabM do
          let τ : Expr := .const ``Parser []
          let e : Expr ← Term.elabTermEnsuringType term τ
          let p ← unsafe evalExpr Parser τ e
          return collectTokensIntoContext p
  let stxToMsg := match stxToMsg? with
    | none => .ofSyntax
    | some tk => .ofFormat ∘ if tk.raw[0].getAtomVal == "format"
      then format else repr ∘ removeSourceInfo
  let omits := omits.toList.map (·.getId)
  let input := input.getString
  withRef tk do
    parser.traceParse input omits stxToMsg
