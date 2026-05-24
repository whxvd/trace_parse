import TraceParse
open Lean Parser

-- Info or error with final state when parser succeeds

/--
info: Parser succeeded, had arity 1 and produced:
  x
Parsing ended at input:1:2 and left
  "x"
unparsed.
-/
#guard_msgs (info, drop trace) in
#parse : ident "x x"

/--
error: Parser failed with arity 1 and error:
  expected term
Parsing ended at input:1:0 and left
  ":"
unparsed.
-/
#guard_msgs (error, drop trace) in
#parse ":"

-- Choice between pp, format, and repr for the parse results

/--
info: Parser succeeded, had arity 1 and produced:
  Lean.Syntax.ident (Lean.SourceInfo.none) "x".toRawSubstring `x []
Input was consumed completely.
-/
#guard_msgs (info, drop trace) in
#parse : ident +repr "x"

-- Parsing of arbitraty expressions of type `Parser`

/--
info: Parser succeeded, had arity 2 and produced:
  "a"
  "a"
Input was consumed completely.
-/
#guard_msgs (info, drop trace) in
#parse : ("a" >> "a") +format "a a"

-- Factored-out
--
-- - `Lean.Parser.Parser.traceParse` and
-- - `resolveParser : Ident → CommandElabM Parser`
--
-- for things the `#parse` syntax does not (yet) account for or for custom
-- experiments and exploration.

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
