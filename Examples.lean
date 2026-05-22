import TraceParse
open Lean Parser

/- Info with final state when parser succeeds -/
/--
info: Parser succeeded, had arity 1 and produced:
  x
Parsing ended at input:1:2 and left
  "x"
unparsed.
-/
#guard_msgs (info) in
#parse : ident "x x"

/- Warning instead of info when parser fails -/
/--
warning: Parser failed:
  expected term
Parser had arity 1 and produced:
  <missing>
Parsing ended at input:1:0 and left
  ":"
unparsed.
-/
#guard_msgs (warning) in
#parse ":"

/- Choice between pp, format, and repr -/
/--
info: Parser succeeded, had arity 1 and produced:
  Lean.Syntax.ident (Lean.SourceInfo.none) "x".toRawSubstring `x []
Input was consumed completely.
---
trace: [debug] Syntax: `x
-/
#guard_msgs in
#parse : ident +repr -token "x"

/- Anonymous parser with custom omit list -/
def myFrequentOmits : List Name := [`token]
/--
info: Parser succeeded, had arity 2 and produced:
  x
  x
Parsing ended at input:1:4 and left
  "x"
unparsed.
---
trace: [debug] Syntax: `x
[debug] Syntax: `x
-/
#guard_msgs in
run_cmd (ident >> ident).traceParse "x x x" myFrequentOmits
