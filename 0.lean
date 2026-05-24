import TraceParse
open Lean Parser

-- declare_syntax_cat c
-- syntax (name := a₁) "a" : c
-- syntax (name := a₂) "a" : c

-- #parse : c +repr "a"

#parse : (checkWsBefore >> { fn := whitespace : Parser} >> ":") " :"
#parse : ws " "

#parse
