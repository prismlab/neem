
(* The type of tokens. *)

type token = 
  | WITH
  | WHEN
  | VAL
  | USE_LANG_BLOB of (string * string * Lexing.position * FStarC_Sedlexing.snap)
  | UNOPTEQUALITY
  | UNIV_HASH
  | UNFOLDABLE
  | UNFOLD
  | UNDERSCORE
  | UINT8 of (string)
  | UINT64 of (string)
  | UINT32 of (string)
  | UINT16 of (string)
  | TYP_APP_LESS
  | TYP_APP_GREATER
  | TYPE
  | TVAR of (string)
  | TRY
  | TRUE
  | TOTAL
  | TILDE of (string)
  | THEN
  | SYNTH
  | SUB_EFFECT
  | SUBTYPE
  | SUBKIND
  | STRING of (string)
  | SQUIGGLY_RARROW
  | SPLICET
  | SPLICE
  | SIZET of (string)
  | SET_RANGE_OF
  | SEQ_BANG_LBRACK
  | SEMICOLON_OP of (string option)
  | SEMICOLON
  | RPAREN
  | RETURNS_EQ
  | RETURNS
  | REQUIRES
  | REIFY
  | REIFIABLE
  | REFLECTABLE
  | REC
  | REAL of (string)
  | RBRACK
  | RBRACE
  | RARROW
  | RANGE_OF
  | RANGE of (string)
  | QUOTE
  | QMARK_DOT
  | QMARK
  | PRIVATE
  | PRAGMA_SHOW_OPTIONS
  | PRAGMA_SET_OPTIONS
  | PRAGMA_RESTART_SOLVER
  | PRAGMA_RESET_OPTIONS
  | PRAGMA_PUSH_OPTIONS
  | PRAGMA_PRINT_EFFECTS_GRAPH
  | PRAGMA_POP_OPTIONS
  | POLYMONADIC_SUBCOMP
  | POLYMONADIC_BIND
  | PIPE_RIGHT
  | PIPE_LEFT
  | PERCENT_LBRACK
  | OP_MIXFIX_ASSIGNMENT of (string)
  | OP_MIXFIX_ACCESS of (string)
  | OPPREFIX of (string)
  | OPINFIX4 of (string)
  | OPINFIX3 of (string)
  | OPINFIX2 of (string)
  | OPINFIX1 of (string)
  | OPINFIX0d of (string)
  | OPINFIX0c of (string)
  | OPINFIX0b of (string)
  | OPINFIX0a of (string)
  | OPEN
  | OPAQUE
  | OF
  | NOEXTRACT
  | NOEQUALITY
  | NEW_EFFECT
  | NEW
  | NAME of (string)
  | MODULE
  | MINUS
  | MATCH_OP of (string)
  | MATCH
  | LPAREN_RPAREN
  | LPAREN
  | LONG_LEFT_ARROW
  | LOGIC
  | LET_OP of (string)
  | LET of (bool)
  | LENS_PAREN_RIGHT
  | LENS_PAREN_LEFT
  | LBRACK_BAR
  | LBRACK_AT_AT_AT
  | LBRACK_AT_AT
  | LBRACK_AT
  | LBRACK
  | LBRACE_COLON_WELL_FOUNDED
  | LBRACE_COLON_PATTERN
  | LBRACE_BAR
  | LBRACE
  | LAYERED_EFFECT
  | LARROW
  | IRREDUCIBLE
  | INTRO
  | INT8 of (string * bool)
  | INT64 of (string * bool)
  | INT32 of (string * bool)
  | INT16 of (string * bool)
  | INT of (string * bool)
  | INSTANCE
  | INLINE_FOR_EXTRACTION
  | INLINE
  | INCLUDE
  | IN
  | IMPLIES
  | IF_OP of (string)
  | IFF
  | IF
  | IDENT of (string)
  | HASH
  | FUNCTION
  | FUN
  | FRIEND
  | FORALL_OP of (string)
  | FORALL of (bool)
  | FALSE
  | EXISTS_OP of (string)
  | EXISTS of (bool)
  | EXCEPTION
  | EQUALTYPE
  | EQUALS
  | EOF
  | ENSURES
  | END
  | ELSE
  | ELIM
  | EFFECT
  | DOT_LPAREN
  | DOT_LENS_PAREN_LEFT
  | DOT_LBRACK_BAR
  | DOT_LBRACK
  | DOT
  | DOLLAR
  | DISJUNCTION
  | DEFAULT
  | DECREASES
  | CONJUNCTION
  | COMMA
  | COLON_EQUALS
  | COLON_COLON
  | COLON
  | CLASS
  | CHAR of (FStar_Char.char)
  | CALC
  | BY
  | BLOB of (string * string * Lexing.position * FStarC_Sedlexing.snap)
  | BEGIN
  | BAR_RBRACK
  | BAR_RBRACE
  | BAR
  | BANG_LBRACE
  | BACKTICK_PERC
  | BACKTICK_HASH
  | BACKTICK_AT
  | BACKTICK
  | ATTRIBUTES
  | ASSUME
  | ASSERT
  | AS
  | AND_OP of (string)
  | AND
  | AMP

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val warn_error_list: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> ((FStarC_Errors_Codes.error_flag * string) list)

val term: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (FStarC_Parser_AST.typ)

val oneDeclOrEOF: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> ((FStarC_Parser_AST.decl list * FStarC_Sedlexing.snap option) option)

val inputFragment: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (FStarC_Parser_AST.inputFragment)
