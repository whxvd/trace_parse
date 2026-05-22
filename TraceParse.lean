import Lean
import Lean.Parser
open Lean Parser Elab Command

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

def Lean.MessageData.intercalate
  (m : MessageData) (l : List MessageData) : MessageData := .joinSep l m

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
  let s := p.fn.run ictx pmctx toks s
  (if s.errorMsg.isNone then logInfo else logWarning) <| ← do
    let mut msg : MessageData := .nil
    match s.errorMsg with
    | none => msg := msg ++ m!"Parser succeeded, "
    | some e => msg := msg ++ m!"Parser failed:" ++ indentD m!"{e}" ++ "\n" ++ "Parser "
    msg := msg ++ m!"had arity {s.stxStack.size} and produced:"
    msg := (msg ++ indentD · ++ "\n") <| .intercalate "\n" <|
      stxToMsg <$> (s.stxStack.extract 0 s.stxStack.size).toList
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

def Lean.traceParse.resolveParserName
  (parserName : Name) (ref? : Option Syntax := none)
: CommandElabM Parser
:=
  (ref?.elim id withRef) do
    let res ← liftCoreM <| Lean.Parser.resolveParserName <| mkIdent parserName
    if res.isEmpty then throwError "Unknown parser `{parserName}`"
    let [res] := res | throwError "Ambiguous parser name `{parserName}`"
    let p ← match res with
      | .category nm => pure (categoryParser nm 0)
      | .parser nm _ => pure { fn := (evalParserConst nm) }
      | .alias val =>
        match val with
        | .const c => pure c
        | _ => throwError "Unexpected parser alias `{parserName}`, must not take parameters"

def Lean.traceParse
  (parserName : Name) (input : String)
  (omits : List Name := [])
  (parserNameRef? : Option Syntax := none)
  (stxToMessageData : Syntax → MessageData := .ofSyntax)
: CommandElabM Unit
:= do
  let p : Parser ← traceParse.resolveParserName parserName parserNameRef?
  p.traceParse input omits stxToMessageData

syntax (name := parse)
  "#parse" (" : " ident)?
    ppSpace ("+" noWs (&"format" <|> &"repr"))?
    ppSpace ("-" noWs ident)*
    ppSpace str
: command

def removeSourceInfo : Syntax → Syntax
  | .atom _ str => .atom .none str
  | .ident _ str x pre => .ident .none str x pre
  | .node _ k children => .node .none k (children.map removeSourceInfo)
  | .missing => .missing

elab_rules : command
| `(#parse%$tk $[: $parserNameStx]? $[+$stxToMsg?]? $[-$omits:ident]* $input:str) =>
  let (parserName, parserNameRef) := match parserNameStx with
    | none => (`term, none)
    | some id => (id.getId, some id)
  let stxToMsg := match stxToMsg? with
    | none => .ofSyntax
    | some tk => .ofFormat ∘ if tk.raw[0].getAtomVal == "format"
      then format else repr ∘ removeSourceInfo
  let omits := omits.toList.map (·.getId)
  let input := input.getString
  withRef tk do
    Lean.traceParse parserName input omits parserNameRef stxToMsg
