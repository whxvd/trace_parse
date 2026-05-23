import TraceParse
import Lean.Parser
open Lean Parser

set_option pp.rawOnError true

-- Recall that `syntax p := …` defines a named parser `p`, meaning: `p` now is
-- defined as `…`. But `p` is not registered anywhere; the syntax of Lean is not
-- extended by `p`. Contrast this with `syntax (name := p) … : term`, where `p`
-- is not only defined as a parser but registered to the category parser for
-- `term`, extending the syntax of Lean terms with `p`. Examples:

syntax a   := "a"
syntax ab  := "a" "b"

-- What follows is just a preliminary illustration of relevant parts of the
-- parser state after a parser run. The named parser `a` is run on input "a a".
-- The parser succeeds, but ends before consuming the complete input.

/--
info: Parser succeeded, had arity 1 and produced:
  a
Parsing ended at input:1:2 and left
  "a"
unparsed.
-/
#guard_msgs (info, drop trace) in
#parse : a "a a"

-- Now parser `a` fails on input "b". It consumes no input, because the very
-- first input token already disagrees with the first (and in this case, only)
-- expected token of the parser.

/--
error: Parser failed with arity 1 and error:
  expected 'a'
Parsing ended at input:1:0 and left
  "b"
unparsed.
-/
#guard_msgs (error, drop trace) in
#parse : a "b"

-- When a non-`atomic` parser fails but agrees on some non-empty prefix of the
-- input, the input position is not rewound to where it started.  E.g., the
-- parser `ab` fails on "a a", but the first token remains consumed.

/--
error: Parser failed with arity 1 and error:
  expected 'b'
Parsing ended at input:1:2 and left
  "a"
unparsed.
-/
#guard_msgs (error, drop trace) in
#parse : ab "a a"

-- That means parsers in Lean are non-backtracking by default. Not at all does
-- this mean that backtracking is not possible or does not happen. Some
-- constructs do that implicitly, like category parsers (by means of
-- `longestMatchFn`). But each construct can do it in a way specifically
-- tailored to semantics/heuristics most appropriate in the particular case.
--
-- A canonical and user-facing way of turning a parser into a backtracking
-- parser is `atomic`.  Its definition, `Lean.Parser.atomicFn`, literally does
-- nothing but remembering the initial position, and resetting it when `p`
-- fails.

syntax atomic_ab := atomic(ab)

-- Now the position after failure is rewound to the start of the input:

/--
error: Parser failed with arity 1 and error:
  expected 'b'
Parsing ended at input:1:0 and left
  "a a"
unparsed.
-/
#guard_msgs (error, drop trace) in
#parse : atomic_ab "a a"

-- A note about the *arity* of parsers. Lean parsers essentially are functions
-- `ParserState → ParserState`. A `ParserState` contains a `SyntaxStack` for
-- accumulating parse results. Given a parser `p`, the number of elements it
-- pushes on the stack is called the arity of `p`. That in principle can be a
-- variable number for a given parser. Parser combinators like
--
#check (Lean.Parser.node : SyntaxNodeKind → Parser → Parser)
--
-- run the argument parser, pop all resulting elements from the stack, put them
-- into a new `Syntax` node, and push that single node back on the stack.
--
-- Parsers defined with, e.g., `syntax` or `leading_parser` already do this
-- wrapping into a single node. So most parsers are of arity 1. Here is a parser
-- of arity 2, using the lower level parsing framework:

/--
info: Parser succeeded, had arity 2 and produced:
  "a"
  "a"
Input was consumed completely.
-/
#guard_msgs (info, drop trace) in
#parse : ("a" >> "a") +format "a a"

-- Let `p` and `q` be parsers. When there are no antiquotations and both parsers
-- have arity 1, `p <|> q` (`orelse(p,q)`) has the following semantics:
--
-- The initial `ParserState` is stored (especially including its input
-- position). `p` is run from the initial state. When it fails and has consumed
-- some input, `p <|> q` fails with the failure state of `p`; no backtracking
-- happens in this case. When `p` succeeds, backtracking does happen, and `q`,
-- too, is run from the initial state. When `q` fails, `p <|> q` succeeds with
-- the resulting state of `p`. When both succeed, the longest match wins.
--
-- (This entire file is written by hand.) I wondered about the reason for this
-- peculiar default semantics and asked Claude. Its output seems plausible
-- enough to me: https://claude.ai/share/c1768f94-65bf-4225-b8e0-1299caaf4f6d.

-- Minimal example: `ab <|> a` fails on input "a", because `ab` fails on "a"
-- after consuming a token. `a` is not tried, which also is reflected in the
-- trace.

syntax oe := ab <|> a
/--
error: Parser failed with arity 1 and error:
  unexpected end of input; expected 'b'
Input was consumed completely.
---
trace: [debug] ❌️ Running `node oe` at input:1:0 with lhsPrec 0
  [debug] ❌️ Running `orElse` at input:1:0 with lhsPrec 0
    [debug] ❌️ Running `node ab` at input:1:0 with lhsPrec 0
      [debug] Syntax: "a"
      [debug] Error at input:1:1: unexpected end of input; expected 'b'
      [debug] Syntax: <missing>
-/
#guard_msgs in
#parse : oe -token "a"

-- `atomic(ab) <|> a` on the same input succeeds.

syntax oe' := atomic(ab) <|> a
/--
info: Parser succeeded, had arity 1 and produced:
  a
Parsing ended at input:1:2 and left
  "a"
unparsed.
---
trace: [debug] ✅️ Running `node oe'` at input:1:0 with lhsPrec 0
  [debug] ✅️ Running `orElse` at input:1:0 with lhsPrec 0
    [debug] ❌️ Running `atomic` at input:1:0 with lhsPrec 0
      [debug] ❌️ Running `node ab` at input:1:0 with lhsPrec 0
        [debug] Syntax: "a"
        [debug] Syntax: "a"
        [debug] Error at input:1:2: expected 'b'
        [debug] Syntax: <missing>
    [debug] ✅️ Running `node a` at input:1:0 with lhsPrec 0
      [debug] Syntax: "a"
-/
#guard_msgs in
#parse : oe' -token "a a"

#check ParserInfo.firstTokens

-- Category parsers essentially run all parsers registered for the category from
-- the initial state, i.e., with unconditional backtracking. (There almost
-- certainly is some premiliminary filtering using `ParserInfo.firstTokens`, but
-- that is semantically irrelevant.) The resuling state of each parser is scored
-- with a triple `(position, success, priority)`. `position` is the input
-- position of the resulting state. `success` is 0 on failure and 1 on success.
-- `priority` can be assigned, e.g., by `syntax (priority := …) … : cat`.
--
-- The state with the lexicographicall greatest triple (lexicographically) wins.
-- That means longest matches always win, even when the resulting state is a
-- failure. Success is secondary. This is a heuristic that usually leads to good
-- and very specific error messages. But it can also lead to great confusion
-- when extending the syntax.
--
-- Here is a minimal example exhibiting a category and an input where a
-- successful parser gets rejected because of a failing parser with a longer
-- match.

declare_syntax_cat lm
syntax (name := lm₁) "a" : lm
syntax (name := lm₂) "a" "a" "b" : lm
/--
error: Parser failed with arity 1 and error:
  unexpected end of input; expected 'b'
Input was consumed completely.
---
trace: [debug] ❌️ Running `category lm:0` at input:1:0 with lhsPrec 0
  [debug] Syntax: "a"
  [debug] ❌️ Running `longestMatchFn` at input:1:0 with lhsPrec 0
    [debug] ❌️ Running `node lm₂` at input:1:0 with lhsPrec 1024
      [debug] Syntax: "a"
      [debug] Syntax: "a"
      [debug] Error at input:1:3: unexpected end of input; expected 'b'
      [debug] Syntax: <missing>
    [debug] New parser has score: (3, (0, 1000))
    [debug] ✅️ Running `node lm₁` at input:1:0 with lhsPrec 1024
      [debug] Syntax: "a"
    [debug] New parser has score: (2, (1, 1000))
-/
#guard_msgs (error, trace) in
#parse : lm -token "a a"

-- The same with atomic. Now `lm₁'` gets a lower score than `lm₂'` on the same
-- input as above.

declare_syntax_cat lm'
syntax (name := lm₁') atomic("a" "a" "b") : lm'
syntax (name := lm₂') "a" : lm'

/--
info: Parser succeeded, had arity 1 and produced:
  a
Parsing ended at input:1:2 and left
  "a"
unparsed.
---
trace: [debug] ✅️ Running `category lm':0` at input:1:0 with lhsPrec 0
  [debug] Syntax: "a"
  [debug] ✅️ Running `longestMatchFn` at input:1:0 with lhsPrec 0
    [debug] ✅️ Running `node lm₂'` at input:1:0 with lhsPrec 1024
      [debug] Syntax: "a"
    [debug] New parser has score: (2, (1, 1000))
    [debug] ❌️ Running `node lm₁'` at input:1:0 with lhsPrec 1024
      [debug] ❌️ Running `atomic` at input:1:0 with lhsPrec 1024
        [debug] Syntax: "a"
        [debug] Syntax: "a"
        [debug] Error at input:1:3: unexpected end of input; expected 'b'
        [debug] Syntax: <missing>
    [debug] New parser has score: (0, (0, 1000))
-/
#guard_msgs in
#parse : lm' -token "a a"

-- Now we are able to understand why `syntax ident ":" term "↦" term : term`
-- "breaks" parsing of type ascription. For the sake of short traces we
-- introduce a new category with minimal other parsers.

declare_syntax_cat t
syntax (name := tIdent) ident : t
syntax (name := tFun) ident ":" t "↦" t : t
syntax (name := tTypeAscription) "(" t ":" t ")" : t

/--
error: Parser failed with arity 1 and error:
  expected '↦'
Parsing ended at input:1:6 and left
  ")"
unparsed.
---
trace: [debug] ❌️ Running `category t:0` at input:1:0 with lhsPrec 0
  [debug] Syntax: "("
  [debug] ❌️ Running `longestMatchFn` at input:1:0 with lhsPrec 0
    [debug] ❌️ Running `node tTypeAscription` at input:1:0 with lhsPrec 1024
      [debug] Syntax: "("
      [debug] ❌️ Running `category t:0` at input:1:1 with lhsPrec 1024
        [debug] Syntax: `x
        [debug] ❌️ Running `longestMatchFn` at input:1:1 with lhsPrec 0
          [debug] ❌️ Running `node tFun` at input:1:1 with lhsPrec 1024
            [debug] Syntax: `x
            [debug] Syntax: ":"
            [debug] ✅️ Running `category t:0` at input:1:5 with lhsPrec 1024
              [debug] Syntax: `X
              [debug] ✅️ Running `longestMatchFn` at input:1:5 with lhsPrec 0
                [debug] ❌️ Running `node tFun` at input:1:5 with lhsPrec 1024
                  [debug] Syntax: `X
                  [debug] Syntax: ")"
                  [debug] Error at input:1:6: expected ':'
                  [debug] Syntax: <missing>
                [debug] New parser has score: (6, (0, 1000))
                [debug] ✅️ Running `node tIdent` at input:1:5 with lhsPrec 1024
                  [debug] Syntax: `X
                [debug] New parser has score: (6, (1, 1000))
-/

#parse : t -optional -withoutPosition -withoutForbidden -token -orElse "(x : X)"

#parse : t -optional -withoutPosition -withoutForbidden -token -orElse "(x : X)"
