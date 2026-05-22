import TraceParse
open Lean Parser

#check ParserState
#check Term.app
#check Parser.atomic

syntax:max (name := p) ident ":" ":" : term
-- syntax:max (name := p) atomic(ident ":" ":") : term

set_option pp.rawOnError true
#parse +format -token -withoutPosition -withoutForbidden -orElse -many1 -many "\
(x : X)
"
