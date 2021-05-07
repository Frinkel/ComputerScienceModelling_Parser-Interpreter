module MethodChecker


let rec reachOne (edges:(int * SubTypes * int)List) (q:int) nl=
    match edges with
    | (q0,c,q1)::tail  when q = q0 -> reachOne tail q ([(q1,c)]@nl)
    | (q0,c,q1)::tail -> reachOne tail q nl
    |  _  -> nl


let rec avalMethod (a:AExpr) (varList:(AExpr * (int)List) List) =
    match a with
    | Num(x)            -> x
    | Array(var,x)      -> (getArray var (avalMethod x varList) varList)
    | Var(x)            -> (getVariable a varList)
    | TimesExpr(x,y)    -> (avalMethod x varList) * (avalMethod y varList)
    | DivExpr(x,y)      -> (avalMethod x varList) / (avalMethod y varList)
    | PlusExpr(x,y)     -> (avalMethod x varList) + (avalMethod y varList)
    | MinusExpr(x,y)    -> (avalMethod x varList) - (avalMethod y varList)
    | PowExpr(x,y)      -> (pow (avalMethod x varList) (avalMethod y varList))
    | UPlusExpr(x)      -> (avalMethod x varList)
    | UMinusExpr(x)     -> - (avalMethod x varList)
    | _ -> 0

let rec cvalMethod (c:Command) (varList:(AExpr * (int)List) List) =
    match c with
    | Assign(var, x) -> match var with
                        | Var(v)       -> setVariable var (avalMethod x varList) varList []
                        | Array(v1,v2) -> setArray v1 (avalMethod v2 varList) (avalMethod x varList) varList []



let rec bvalMethod b (varList:(AExpr * (int)List) List) =
    match b with
    | Bool(x)                   -> x
    | AndExpr(x,y)              -> (bvalMethod x varList) & (bvalMethod y varList)
    | NotExpr(x)                -> not (bvalMethod x varList)
    | OrExpr(x,y)               -> (bvalMethod x varList) || (bvalMethod y varList)
    | ShortOrExpr(x,y)          -> ((bvalMethod x varList) || (bvalMethod y varList))
    | ShortAndExpr(x,y)         -> ((bvalMethod x varList) && (bvalMethod y varList))
    | EqualsExpr(x,y)           -> (avalMethod x varList) = (avalMethod y varList)
    | NotEqualsExpr(x,y)        -> (avalMethod x varList) <> (avalMethod y varList)
    | GreaterExpr(x,y)          -> (avalMethod x varList) > (avalMethod y varList)
    | LessExpr(x,y)             -> (avalMethod x varList) < (avalMethod y varList)
    | GreaterOrEqualExpr(x,y)   -> (avalMethod x varList) >= (avalMethod y varList)
    | LessOrEqualExpr(x,y)      -> (avalMethod x varList) <= (avalMethod y varList)


let rec checkMethod (visited) (toExplore) (edges) = 

let edgeList = [(0, SubB (GreaterExpr (Var "x", Num 0)), 2); (2, SubC (Assign (Var "a", Num 2)), 1); (0, SubB (LessExpr (Var "x", Num 0)), 3); (3, SubC (Assign (Var "b", Num 2)), 1)]
reachOne edgeList 0 []