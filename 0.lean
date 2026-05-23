import TraceParse
import Lean.Parser
open Lean Parser

syntax a   := "a"
syntax ab  := "a" "b"
syntax aab := "a" "a" "b"

-- The following is just a preliminary illustration of relevant parts of the
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

-- Now parser `a` fails on input "b". Notably, it consumes no input, because the
-- very first input token already disagrees with the first (and in this case,
-- only) expected token of the parser.

/--
error: Parser failed with arity 1 and error:
  expected 'a'
Parsing ended at input:1:0 and left
  "b"
unparsed.
-/
#guard_msgs (error, drop trace) in
#parse : a "b"

-- But when a non-`atomic` parser fails but agrees on some non-empty prefix of
-- the input, the input position is not rewound to where it started: The parser
-- `ab` fails on "a a", but the first token remains consumed.

/--
error: Parser failed with arity 1 and error:
  expected 'b'
Parsing ended at input:1:2 and left
  "a"
unparsed.
-/
#guard_msgs (error, drop trace) in
#parse : ab "a a"

-- That means parsers in Lean are non-backtracking by default. This does not at
-- all mean that backtracking is not possible or does not happen. But
-- backtracking must be explicitly invoked. Some constructs do that
-- automatically, like category parsers (by means of `longestMatchFn`). But each
-- construct can do it in a way specifically tailored to semantics/heuristics
-- most appropriate in the particular case.
--
-- A canonical and user-facing way of turning a parser into a backtracking
-- parser is `atomic`.  Its definitioin, `Lean.Parser.atomicFn`, literally does
-- nothing but remembering the initial position when an `atomic(p)` is run, and
-- resetting it when `p` fails.

syntax atomic_ab := atomic(ab)
/--
error: Parser failed with arity 1 and error:
  expected 'b'
Parsing ended at input:1:0 and left
  "a a"
unparsed.
-/
#guard_msgs (error, drop trace) in
#parse : atomic_ab "a a"

-- `orelse` with atomic. Works, as one would naively expect.
declare_syntax_cat oe
syntax (name := oe) orelse(atomic("a" "b"), "a") : oe
/--
info: Parser succeeded, had arity 1 and produced:
  a
Parsing ended at input:1:2 and left
  "a"
unparsed.
-/
#guard_msgs (info) in
#parse : oe "a a"

-- The same without `atomic`. Fails, because the lhs of `orelse` successfully
-- consumes a token before failing on the second token, and `orelse` does not
-- try the rhs after having consumed tokens on the lhs.
declare_syntax_cat oe'
syntax (name := oe') orelse("a" "b", "a") : oe'
/--
warning: Parser failed:
  expected 'b'
Parser had arity 1 and produced:
  (oe' (group "a" <missing>))
Parsing ended at input:1:2 and left
  "a"
unparsed.
---
trace: [debug] ❌️ Running `category oe':0` at input:1:0 with lhsPrec 0
  [debug] Syntax: "a"
  [debug] ❌️ Running `longestMatchFn` at input:1:0 with lhsPrec 0
    [debug] ❌️ Running `node oe'` at input:1:0 with lhsPrec 1024
      [debug] ❌️ Running `orElse` at input:1:0 with lhsPrec 1024
        [debug] ❌️ Running `node group` at input:1:0 with lhsPrec 1024
          [debug] Syntax: "a"
          [debug] Syntax: "a"
          [debug] Error at input:1:2: expected 'b'
          [debug] Syntax: <missing>
-/
#guard_msgs in
#parse : oe' +format -token "a a"

declare_syntax_cat lm
syntax (name := lm₁) atomic("a" "a" "b") : lm
syntax (name := lm₂) "a" : lm
/--
info: Parser succeeded, had arity 1 and produced:
  a
Parsing ended at input:1:2 and left
  "a"
unparsed.
-/
#guard_msgs (info) in
#parse : lm "a a"

declare_syntax_cat lm'
syntax (name := lm₁') "a" "a" "b" : lm'
syntax (name := lm₂') "a" : lm'

-- Although the `longestMatchFn` in the category parser encounters the
-- succeeding `lm₂'`, `lm₁'` fails later than `lm₂'` succeeds, and the failure
-- gets preferred.
/--
warning: Parser failed:
  unexpected end of input; expected 'b'
Parser had arity 1 and produced:
  (lm₁' "a" "a" <missing>)
Input was consumed completely.
---
trace: [debug] ❌️ Running `category lm':0` at input:1:0 with lhsPrec 0
  [debug] Syntax: "a"
  [debug] ❌️ Running `longestMatchFn` at input:1:0 with lhsPrec 0
    [debug] ✅️ Running `node lm₂'` at input:1:0 with lhsPrec 1024
      [debug] Syntax: "a"
    [debug] New parser has score: (2, (1, 1000))
    [debug] ❌️ Running `node lm₁'` at input:1:0 with lhsPrec 1024
      [debug] Syntax: "a"
      [debug] Syntax: "a"
      [debug] Error at input:2:0: unexpected end of input; expected 'b'
      [debug] Syntax: <missing>
    [debug] New parser has score: (4, (0, 1000))
-/
#guard_msgs in
#parse : lm' +format -token -withoutPosition -withoutForbidden "\
a a
"


declare_syntax_cat lm
syntax lm1* : lm

#parse : lm +format -token -withoutPosition -withoutForbidden -orElse -many1 -many "\
a a
"
