module Interpreter

let rec setVariable (a:AExpr) (i:int) (varList:(AExpr * (int)List) List) (nl:(AExpr * (int)List) List) =
    match varList with
    | (a1,l)::tail when a1 = a -> setVariable a i tail ((a1,[i])::nl) 
    | (a1,l)::tail             -> setVariable a i tail ((a1,l)::nl) 
    | _ ->  nl

let rec getVariable (a:AExpr) (varList:(AExpr * (int)List) List) =
    match varList with
    | (a1,l)::tail when a1 = a -> l.[0]
    | (a1,l)::tail             -> getVariable a tail
    | _ ->  printfn "ERROR VARIABLE DOES NOT EXIST!!!!!!!!!!!!!"
            (0)

let rec pow a b =
    if b = 0 then 1
    else if b <> 1 then a * (pow a (b-1))
    else a

let rec aval (a:AExpr) (varList:(AExpr * (int)List) List) =
    match a with
    | Num(x)            -> x
    | Var(x)            -> (getVariable a varList)
    | TimesExpr(x,y)    -> (aval x varList) * (aval y varList)
    | DivExpr(x,y)      -> (aval x varList) / (aval y varList)
    | PlusExpr(x,y)     -> (aval x varList) + (aval y varList)
    | MinusExpr(x,y)    -> (aval x varList) - (aval y varList)
    | PowExpr(x,y)      -> (pow (aval x varList) (aval y varList))
    | UPlusExpr(x)      -> (aval x varList)
    | UMinusExpr(x)     -> - (aval x varList)
    | _ -> 0

let rec cval (c:Command) (varList:(AExpr * (int)List) List) =
    match c with
    | Assign(var, x) -> setVariable var (aval x varList) varList []

let rec bval b (varList:(AExpr * (int)List) List) =
    match b with
    | Bool(x)                   -> x
    | AndExpr(x,y)              -> (bval x varList) & (bval y varList)
    | NotExpr(x)                -> not (bval x varList)
    | OrExpr(x,y)               -> (bval x varList) || (bval y varList)
    | ShortOrExpr(x,y)          -> ((bval x varList) || (bval y varList))
    | ShortAndExpr(x,y)         -> ((bval x varList) && (bval y varList))
    | EqualsExpr(x,y)           -> (aval x varList) = (aval y varList)
    | NotEqualsExpr(x,y)        -> (aval x varList) <> (aval y varList)
    | GreaterExpr(x,y)          -> (aval x varList) > (aval y varList)
    | LessExpr(x,y)             -> (aval x varList) < (aval y varList)
    | GreaterOrEqualExpr(x,y)   -> (aval x varList) >= (aval y varList)
    | LessOrEqualExpr(x,y)      -> (aval x varList) <= (aval y varList)

let rec interpret (edges:(int * SubTypes * int)List) (edgestail:(int * SubTypes * int)List) (varList:(AExpr * (int)List) List) (q:int) =
    match edgestail with
    | (q0,c,q1)::tail  when q = q0 -> match (c) with 
                                    | SubC(x)                      -> printfn "Took path %i to %i" q0 q1
                                                                      interpret edges edges (cval x varList) q1
                                    | SubB(x) when (bval x varList)-> printfn "Took path %i to %i" q0 q1
                                                                      interpret edges edges varList q1
                                    | _                            -> interpret edges tail varList q
    | (q0,e,q1)::tail -> interpret edges tail varList q
    | _ when q = 1    -> printfn "Succes %A" varList 
    | _               -> printfn "Error! %A at node %i " varList q

   