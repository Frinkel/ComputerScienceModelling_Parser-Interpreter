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

let rec duplicateSign (sign:Signs) (i:int) nl=
    match i with
    | 0 -> nl
    | _ -> duplicateSign sign (i-1) (sign::nl)

let rec getSignsFromList (varListSign:(int*(AExpr*(Signs)List)List)List) (q:int) (var:AExpr) =
    match varListSign with
    | (q0,l)::tail when q0 = q -> getSignsFromNode l var
    | (q0,l)::tail -> getSignsFromList tail q var
    | _ -> []
    
and getSignsFromNode (node:(AExpr*(Signs)List)List) (var:AExpr) =
    match node with
    | (x,l)::tail when x = var -> l
    | (x,l)::tail -> getSignsFromNode tail var
    | _ -> []

let rec updateSigns (varListSign:(int*(AExpr*(Signs)List)List)List) (node:(AExpr*(Signs)List)List) (q0:int) (q1:int) (var:AExpr) (sign:Signs) (nl:(AExpr*(Signs)List)List) =
    match node with
    | (x,l)::tail when x = var -> updateSigns varListSign tail q0 q1 var sign [(x,(duplicateSign sign ((getSignListLength varListSign q0)) [])@l)]@nl
    | (x,l)::tail -> updateSigns varListSign tail q0 q1 var sign [(x,(getSignsFromList varListSign q0 x)@l)]@nl
    | _ -> nl

//(getSignsFromList varListSign q0 x)
let rec updateNode (varListSign:(int*(AExpr*(Signs)List)List)List) (varListSign2:(int*(AExpr*(Signs)List)List)List) (q0:int) (q1:int) (var:AExpr) (sign:Signs) (nl:(int*(AExpr*(Signs)List)List)List)=
    match varListSign with
    | (q,l)::tail when q = q1 -> updateNode tail varListSign2 q0 q1 var sign [q,(updateSigns varListSign2 l q0 q1 var sign [])]@nl
    | (q,l)::tail -> updateNode tail varListSign2 q0 q1 var sign [(q,l)]@nl
    | _ -> nl

let rec avalSign (a:AExpr) (varListSign:(int*(AExpr*(Signs)List)List)List) (q0:int) (q1:int) (nl:Signs List)=
    match a with
      | Num(x)            -> if x > 0 then [Plus]@nl else if x = 0 then [Zero]@nl else [Minus]@nl
//      | Array(var,x)      -> (getArray var (aval x varList) varList)
      | Var(x)            -> (getSignsFromList varListSign q0 a)
//      | TimesExpr(x,y)    -> (aval x varList) * (aval y varList)
//      | DivExpr(x,y)      -> (aval x varList) / (aval y varList)
      | PlusExpr(x,y)     -> (avalSign x varListSign q0 q1 nl)@(avalSign y varListSign q0 q1 nl)
//      | MinusExpr(x,y)    -> (aval x varList) - (aval y varList)
//      | PowExpr(x,y)      -> (pow (aval x varList) (aval y varList))
//      | UPlusExpr(x)      -> (aval x varList)
//      | UMinusExpr(x)     -> - (aval x varList)
//      | _ -> 0

let rec executeUpdateSign (varListSign:(int*(AExpr*(Signs)List)List)List) (q0:int) (q1:int) (var:AExpr) (signList:Signs List) =
    match signList with
    | s::tail -> executeUpdateSign (updateNode varListSign varListSign q0 q1 var s []) q0 q1 var tail
    | _ -> varListSign

let rec cvalSign (c:Command) (varListSign:(int*(AExpr*(Signs)List)List)List) (q0:int) (q1:int) =
    match c with
    | Assign(var, x) -> match var with
                        | Var(v)       -> executeUpdateSign varListSign q0 q1 var (avalSign x varListSign q0 q1 [])
//                        | Array(v1,v2) -> setArray v1 (aval v2 varList) (aval x varList) varList []







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

// Removes duplicates from the sign list.
let rec removeDuplicates (varListSign:(int*(AExpr*(Signs)List)List)List) =
    match varListSign with 
    | (q0,l)::tail -> [(q0,(removeDuplicatesHelper l [] 0))]@(removeDuplicates tail)
    | _ -> []
and removeDuplicatesHelper (l:(AExpr*(Signs)List)List) (duplicateList:((Signs)List)List) (index:int): (AExpr*(Signs)List)List =
    match l with
    | (x,xlist)::tail when index = xlist.Length -> l 
    | l when (listContains (getEntries l index) duplicateList) ->   printfn "%A 1 index: %i l.length: %i" duplicateList index l.Length
                                                                    removeDuplicatesHelper (removeEntries l index) (duplicateList) (index)
    | l ->  printfn "%A 2 index: %i l.length: %i" duplicateList index l.Length
            removeDuplicatesHelper l ([(getEntries l index)]@duplicateList) (index+1)
and getEntries (signList:(AExpr*(Signs)List)List) index =
    match signList with 
    | ((x,xlist))::tail -> [(listGetElemFromIndex xlist index)]@(getEntries tail index)
    | _ -> []
and removeEntries (signList:(AExpr*(Signs)List)List) index =
    match signList with
    | ((x,xlist))::tail -> [(x, (listRemoveElemByIndex xlist index 0))]@(removeEntries tail index)
    | _ -> []
and listContains (elem:(Signs)List) (l:((Signs)List)List) = List.exists (fun x -> x = elem) l
and listGetElemFromIndex l index = Seq.item index (Seq.ofList l)
and listRemoveElemByIndex l index incr =
    match l with 
    | x::xtail when index = incr -> xtail
    | x::xtail -> [x]@(listRemoveElemByIndex xtail index (incr+1))
    | _ -> []


let rec evalSign (c:Command) (varListSign:(int*(AExpr*(Signs)List)List)List) (q0:int) (q1:int) (length:int) = 
    match length with
    | 0 -> printfn "Was in cvalSign between %i and %i" q0 q1
           varListSign
    | _ -> printfn "hey"
           (evalSign c (cvalSign c varListSign q0 q1) q0 q1 (length - 1))

let rec signAnalysis (edges:(int * SubTypes * int)List) (edgestail:(int * SubTypes * int)List) (varListSign:(int*(AExpr*(Signs)List)List)List) (q:int) =
    match edgestail with
    | (q0,c,q1)::tail  when q = q0 -> match (c) with 
                                      | SubC(x)                      -> printfn "Took path %i to %i" q0 q1
                                                                        signAnalysis edges edges (removeDuplicates (evalSign x varListSign q0 q1 (getSignListLength varListSign q0) )) q1
    //                                 | SubB(x) when (bvalSign x varListSign)-> printfn "Took path %i to %i" q0 q1
    //                                                                           signAnalysis edges edges varList q1
    //                                 | _                            -> signAnalysis edges tail varList q
    | (q0,e,q1)::tail -> signAnalysis edges tail varListSign q
    // | _ when q = 1    -> printfn "Succes finished at node %i " q
    //                      varListSign
    | _               -> printfn "Error! stuck at node %i " q
                         (removeDuplicates varListSign)