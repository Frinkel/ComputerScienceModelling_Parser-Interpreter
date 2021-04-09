// This file implements the types
module GCLTypesAST

type AExpr =
  | Num of int
  | Var of string
  | Array of (string * AExpr)
  | TimesExpr of (AExpr * AExpr)
  | DivExpr of (AExpr * AExpr)
  | PlusExpr of (AExpr * AExpr)
  | MinusExpr of (AExpr * AExpr)
  | PowExpr of (AExpr * AExpr)
  | UPlusExpr of (AExpr)
  | UMinusExpr of (AExpr)


type BExpr = 
  | Bool of bool
  | AndExpr of (BExpr * BExpr) 
  | NotExpr of BExpr 
  | OrExpr of (BExpr * BExpr) 
  | ShortOrExpr of (BExpr * BExpr)
  | ShortAndExpr of (BExpr * BExpr)
  | EqualsExpr of (AExpr * AExpr)
  | NotEqualsExpr of (AExpr * AExpr)
  | GreaterExpr of (AExpr * AExpr)
  | LessExpr of (AExpr * AExpr)
  | GreaterOrEqualExpr of (AExpr * AExpr)
  | LessOrEqualExpr of (AExpr * AExpr)

type Command =
  | Assign of (AExpr * AExpr)
  | Skip
  | SemiColon of (Command * Command)
  | If of (GuardedCommand)
  | Do of (GuardedCommand)
and GuardedCommand =
  | ExecuteIf of (BExpr * Command)
  | Else of (GuardedCommand * GuardedCommand)


type SubTypes =
  | SubB of BExpr
  | SubC of Command

type Signs =
  | Plus
  | Minus
  | Zero
