import TraceParse

syntax a   := "a"
syntax ab  := "a" "b"

-- What follows is just a preliminary illustration of relevant parts of the
-- parser state after a parser is run. The named parser `a` is run on input "a
-- a". The parser succeeds, but ends before consuming the complete input.

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
-- this mean that backtracking is not possible or does not happen in Lean. Some
-- constructs do that implicitly, like category parsers (by means of
-- `longestMatchFn`). But each construct can do it in a way specifically
-- tailored to semantics/heuristics most appropriate in the particular case.
--
-- The canonical and user-facing way of turning a parser into a backtracking
-- parser is `atomic`.  Its definition, `Lean.Parser.atomicFn`, literally does
-- nothing but remembers the initial position, and resets it when `p` fails.

syntax atomic_ab := atomic(ab)

-- Now the position after failure is rewound to the start of the input.

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
--   `Lean.Parser.node : SyntaxNodeKind → Parser → Parser`
--
-- run the argument parser, pop all resulting elements from the stack, put them
-- into a new `Syntax` node, and push that single node back on the stack.
-- Parsers defined with, e.g., `syntax` or `leading_parser` always do this
-- automatically. So in practice most parsers are of arity 1. Here is a parser
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
-- happens in this case, `q` is not tried. When `p` succeeds, backtracking does
-- happen, and `q`, too, is run from the initial state. When `q` fails,
-- `p <|> q` succeeds with the resulting state of `p`. When both succeed, the
-- longest match wins.
--
-- (This entire file is written by hand.) I wondered about the reason for this
-- seemingly peculiar semantics of `orelse` and asked Claude. Its output seems
-- plausible enough to me:
-- https://claude.ai/share/c1768f94-65bf-4225-b8e0-1299caaf4f6d.
--
-- Minimal example: `ab <|> a` fails on input "a", because `ab` fails on "a"
-- after consuming a token. `a` is not tried at all.

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

-- `atomic(ab) <|> a` on the same input succeeds, because the `atomic` makes
-- `atomic(ab)` consume no input on failure any more.

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

-- Category parsers essentially run all parsers registered for the category,
-- each starting from the initial state (which includes the initial position),
-- i.e. with unconditional backtracking. (There almost certainly is some
-- preliminary filtering of parsers using `ParserInfo.firstTokens`, but that is
-- semantically irrelevant.) The resuling state of each parser is scored with a
-- triple `(position, success, priority)`. `position` is the input position of
-- the resulting state (a byte index in a UTF-8 string, so not necessarily
-- coinciding with character counts). `success` is 0 on failure and 1 on
-- success. `priority` can be assigned, e.g., by
-- `syntax (priority := …) … : cat`.

-- The states with the lexicographically greatest triples win (on a tie
-- resulting in a choice node). That means longest matches always win, even when
-- the resulting state is a failure state. Success is secondary. This is a
-- heuristic that usually leads to good and very specific error messages. But it
-- can also lead to great confusion when extending and debugging the syntax.

-- Here is a minimal example exhibiting a category and an input where a
-- successful parser gets rejected because of a failing parser with a longer
-- match. Note the scores in the trace.

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
#guard_msgs in
#parse : lm -token "a a"

-- The same with `atomic`. Now `lm₁'` gets a lower score than `lm₂'` on the same
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

-- `"a" atomic("a" "b")` works, too. In that case both parses end at the same
-- position, and the second element of the triple (success) decides.

declare_syntax_cat lm''
syntax (name := lm₁'') "a" atomic("a" "b") : lm''
syntax (name := lm₂'') "a" : lm''

/--
info: Parser succeeded, had arity 1 and produced:
  a
Parsing ended at input:1:2 and left
  "a"
unparsed.
---
trace: [debug] ✅️ Running `category lm'':0` at input:1:0 with lhsPrec 0
  [debug] Syntax: "a"
  [debug] ✅️ Running `longestMatchFn` at input:1:0 with lhsPrec 0
    [debug] ✅️ Running `node lm₂''` at input:1:0 with lhsPrec 1024
      [debug] Syntax: "a"
    [debug] New parser has score: (2, (1, 1000))
    [debug] ❌️ Running `node lm₁''` at input:1:0 with lhsPrec 1024
      [debug] Syntax: "a"
      [debug] ❌️ Running `atomic` at input:1:2 with lhsPrec 1024
        [debug] Syntax: "a"
        [debug] Error at input:1:3: unexpected end of input; expected 'b'
        [debug] Syntax: <missing>
    [debug] New parser has score: (2, (0, 1000))
-/
#guard_msgs in
#parse : lm'' -token "a a"

-- Now we are fully able to understand
--
-- - why `syntax ident ":" term "↦" term : term` "breaks" parsing of type
--   ascription, e.g. `(x : X)`,
-- - how the "weird" error messages are chosen,
-- - why `syntax atomic(ident ":" term "↦") term : term` fixes the issue, and
-- - why `syntax ident atomic(":" term "↦") term : term` suffices, too.
--
-- I leave that as an exercise to the reader. In part because the traces get
-- very long and unwieldy in `#guard_msgs`. They are better viewed and explored
-- in the InfoView, where folding is available. But mostly because I finished my
-- job of fully understanding the relevant underlying aspects of the Lean
-- parsing framework, and finding and displaying minimal examples to showcase
-- them.
--
-- The solution can be looked up in Thomas Murrills' write-up of the 2026-05-13
-- Meta Café at
-- https://docs.google.com/document/d/1nRIGUMm9S7lnM5GYBYt7I_NtH3xLPZD7WVe_R4l0SPU/edit?tab=t.0.
