module SignAnalyzer

open System.Text.RegularExpressions

// From: https://stackoverflow.com/questions/53818476/f-match-many-regex
let (|Regex|_|) pattern input =
    let m = Regex.Match(input, pattern)
    if m.Success then Some(List.tail [ for g in m.Groups -> g.Value ])
    else None

// Check if a string is a sign type
let signChecker s =
    match s with
    | Regex @"(^\+)" [ chr ]    -> Plus
    | Regex @"(^\-)" [ chr ]    -> Minus
    | Regex @"(^0)"  [ chr ]    -> Zero
    | _                         -> printfn "Not a valid sign initialization"
                                   failwith "Not a valid sign initialization"

// Check if a sign array is on the correct form
let signArrayChecker (a:string) =
    match a with
    | Regex @"^\{((\s*[\+ \- 0]+\s*,?\s*)+\s*[\+ \- 0]*\s*)\}" [ num; d ] ->
        num
    | _ ->  printfn "ERROR: Array failed to hold correct syntax of \"{Sign 1, Sign 2, ..., Sign N}\""
            failwith "Array failed to hold correct syntax of \"{Sign 1, Sign 2, ..., Sign N}\""

// Convert a string list to a signs list
let arrayStringToSignList (s:string) =
    let sA = Seq.toList (signArrayChecker s)
    let rec arrayStringToListS (l:char List) (nl:Signs List) =
        match l with
        | [] -> nl
        | (x:char)::[] -> arrayStringToListS [] (nl@[signChecker (string x)])
        | (x:char)::tail when x = ',' -> arrayStringToListS tail (nl)
        | (x:char)::tail -> arrayStringToListS tail (nl@[signChecker (string x)])

    arrayStringToListS sA []


let rec InitializationOfSigns (l: AExpr List) (nl:(AExpr * (Signs)List) List) = 
    match l with
    | [] -> nl
    | a::tail -> match a with
                 | Var(x)       -> InitializationOfSigns tail (nl@getVariableInitializationFromUser x)
                 | Array(x,y)   -> InitializationOfSigns tail (nl@getArrayInitializationFromUser x)
and getVariableInitializationFromUser (x:string) =
    printf "%s =" x
    [Var(x), [signChecker(Console.ReadLine())]]
and getArrayInitializationFromUser (x:string) =
    printfn "Enter all ellements of your array with the syntax \"{Sign 1, Sign 2, ..., Sign N}\""
    printf "%s =" x
    [Array(x,Num(1)), arrayStringToSignList(Console.ReadLine())]







// let rec avalSign (a:AExpr) (varList:(int*(AExpr*(Signs)List)List)List) =
//     match a with
//     | Num(x)            -> x
//     | Array(var,x)      -> (getArray var (aval x varList) varList)
//     | Var(x)            -> (getVariable a varList)
//     | TimesExpr(x,y)    -> (aval x varList) * (aval y varList)
//     | DivExpr(x,y)      -> (aval x varList) / (aval y varList)
//     | PlusExpr(x,y)     -> (aval x varList) + (aval y varList)
//     | MinusExpr(x,y)    -> (aval x varList) - (aval y varList)
//     | PowExpr(x,y)      -> (pow (aval x varList) (aval y varList))
//     | UPlusExpr(x)      -> (aval x varList)
//     | UMinusExpr(x)     -> - (aval x varList)
//     | _ -> 0

let rec cvalSign (c:Command) (varListSign:(int*(AExpr*(Signs)List)List)List) (q0:int) (q1:int) (length:int) =
    match length with
    | 0 -> printfn "Was in cvalSign between %i and %i" q0 q1
           varListSign
    | _ -> printfn "hey"
           (cvalSign c varListSign q0 q1 (length - 1))

    // | Assign(var, x) -> match var with
    //                     | Var(v)       -> setVariable var (aval x varList) varList []
    //                     | Array(v1,v2) -> setArray v1 (aval v2 varList) (aval x varList) varList []

// let rec bvalSign b (varList:(int*(AExpr*(Signs)List)List)List) =
//     match b with
//     | Bool(x)                   -> x
//     | AndExpr(x,y)              -> (bval x varList) & (bval y varList)
//     | NotExpr(x)                -> not (bval x varList)
//     | OrExpr(x,y)               -> (bval x varList) || (bval y varList)
//     | ShortOrExpr(x,y)          -> ((bval x varList) || (bval y varList))
//     | ShortAndExpr(x,y)         -> ((bval x varList) && (bval y varList))
//     | EqualsExpr(x,y)           -> (aval x varList) = (aval y varList)
//     | NotEqualsExpr(x,y)        -> (aval x varList) <> (aval y varList)
//     | GreaterExpr(x,y)          -> (aval x varList) > (aval y varList)
//     | LessExpr(x,y)             -> (aval x varList) < (aval y varList)
//     | GreaterOrEqualExpr(x,y)   -> (aval x varList) >= (aval y varList)
//     | LessOrEqualExpr(x,y)      -> (aval x varList) <= (aval y varList)

let rec getSignListLength (varListSign:(int*(AExpr*(Signs)List)List)List) (q:int) =
    match varListSign with
    | (q0,l)::tail when q0 = q -> match l with
                                  | (x,l1)::tail -> l1.Length
                                  | _ -> 0
    | (q0,l)::tail -> getSignListLength tail q
    | _ -> 0

let rec signAnalysis (edges:(int * SubTypes * int)List) (edgestail:(int * SubTypes * int)List) (varListSign:(int*(AExpr*(Signs)List)List)List) (q:int) =
    match edgestail with
    | (q0,c,q1)::tail  when q = q0 -> match (c) with 
                                    | SubC(x)                      -> printfn "Took path %i to %i" q0 q1
                                                                      signAnalysis edges edges (cvalSign x varListSign q0 q1 (getSignListLength varListSign q0) ) q1
    //                                 | SubB(x) when (bvalSign x varListSign)-> printfn "Took path %i to %i" q0 q1
    //                                                                           signAnalysis edges edges varList q1
    //                                 | _                            -> signAnalysis edges tail varList q
    | (q0,e,q1)::tail -> signAnalysis edges tail varListSign q
    // | _ when q = 1    -> printfn "Succes finished at node %i " q
    //                      varListSign
    | _               -> printfn "Error! stuck at node %i " q
                         varListSign

let rec containsNode (l:(int*(AExpr*(Signs)List)List)List) (q:int)=
    match l with
    | (x,y)::tail when (q = x) -> true 
    | (x,y)::tail -> containsNode tail q
    | _ -> false

let rec initializeSignVars (varList:(AExpr * (int)List) List) (nl:(AExpr*(Signs)List)List) =
    match varList with
    | (a,l):: tail -> [(a,[])]@(initializeSignVars tail nl)
    | _ -> nl

let rec initializeSigns (edges:(int * SubTypes * int)List) (varListSign:(AExpr*(Signs)List)List) (nl:(int*(AExpr*(Signs)List)List)List) (aExprList: AExpr List) = 
    match edges with
    | (q0,c,q1)::tail when not (containsNode nl q0) && (q0 = 0) -> (initializeSigns tail varListSign (nl@[(0, InitializationOfSigns aExprList [])]) aExprList)
    | (q0,c,q1)::tail when not (containsNode nl q0) -> (initializeSigns tail varListSign (nl@[(q0,varListSign)]) aExprList)
    | (q0,c,q1)::tail -> (initializeSigns tail varListSign nl aExprList)
    | _ -> nl@[(1,varListSign)]

//@[(q0,[(Var "x", [Plus]); (Var "y", [Plus])])]