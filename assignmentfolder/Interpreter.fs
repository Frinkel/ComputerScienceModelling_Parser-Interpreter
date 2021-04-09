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
    | _ ->  printfn "ERROR VARIABLE DOES NOT EXIST!"
            (0)

let rec setArray (a:string) (index:int) (i:int) (varList:(AExpr * (int)List) List) (nl:(AExpr * (int)List) List) =
    match varList with
    | (Array(x,y),l)::tail when x = a -> if l.Length <= index 
                                         then printfn "Index %i out of bounds for array %s" index x
                                              failwith ""
                                         else  setArray a index i tail ((Array(x,y),(getElement index i l 0 []))::nl) 
    | (a1,l)::tail             -> setArray a index i tail ((a1,l)::nl) 
    | _ ->  nl
and getElement (index:int) (i:int) (l:(int)List) (j:int) (nl:(int)List)=
    match l with
    | x::tail when j = index -> getElement index i tail (j+1) (nl@[i])
    | x::tail                -> getElement index i tail (j+1) (nl@[x])
    | _ -> nl


let rec getArray (a:string) (index:int) (varList:(AExpr * (int)List) List) =
    match varList with
    | (Array(x,y),l)::tail when x = a -> if l.Length <= index 
                                         then printfn "Index %i out of bounds for array %s" index x
                                              failwith ""
                                         else l.[index]
    | (a1,l)::tail             -> getArray a index tail
    | _ ->  printfn "ERROR VARIABLE DOES NOT EXIST!"
            failwith ""

let rec pow a b =
    if b < 0        then printfn "ERROR CANNOT HAVE NEGATIVE EXPONENT!!"
                         0
    else if b <> 0  then a * (pow a (b-1))
    else                 1

let rec aval (a:AExpr) (varList:(AExpr * (int)List) List) =
    match a with
    | Num(x)            -> x
    | Array(var,x)      -> (getArray var (aval x varList) varList)
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
    | Assign(var, x) -> match var with
                        | Var(v)       -> setVariable var (aval x varList) varList []
                        | Array(v1,v2) -> setArray v1 (aval v2 varList) (aval x varList) varList []



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
    | _ when q = 1    -> printfn "Succes finished at node %i " q
                         varList
    | _               -> printfn "Error! stuck at node %i " q
                         varList

