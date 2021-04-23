module SecurityAnalyzer

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

let rec produceAllowedFlowList (secLattice: (AExpr * AExpr)List) (secClassification: (AExpr * AExpr)List) (secClassificationTail: (AExpr * AExpr)List) (allowedFlowList: (AExpr * AExpr)List) = 
    match secClassificationTail with 
    | (x,y)::tail when (checkSecurityLattice y secLattice) -> printfn  "Here 1 %A " allowedFlowList
                                                              produceAllowedFlowList secLattice secClassification tail (addToList x ([x]@(getVariableFromSecClassification ([y]@(getCorrespondingSecurity y secLattice [])) secClassification [])) allowedFlowList) 
    | (x,y)::tail ->    printfn "Here 2 %A " allowedFlowList
                        produceAllowedFlowList secLattice secClassification tail (addToList x ([x]) allowedFlowList)
    | _ ->  printfn "Here 3 %A " allowedFlowList
            removeDuplicates allowedFlowList []
and listContains elem l = List.exists (fun x -> x = elem) l
and getVariableFromSecClassification (secList: AExpr List) (secClassification: (AExpr * AExpr)List) (returnList: AExpr List) =
    match secClassification with
    | (x,sec)::tail when (listContains sec secList) -> getVariableFromSecClassification secList tail ([x]@returnList)
    | (x,sec)::tail -> getVariableFromSecClassification secList tail (returnList)
    | _ -> returnList
and checkSecurityLattice (sec: AExpr) (secLattice: (AExpr * AExpr)List) =
    match secLattice with
    | (x, y)::tail when x = sec -> true
    | (x, y)::tail -> checkSecurityLattice sec tail
    | _ -> false
and getCorrespondingSecurity (sec: AExpr) (secLattice: (AExpr * AExpr)List) (returnList: AExpr List) =
    match secLattice with
    | (x,y)::tail when x = sec -> getCorrespondingSecurity sec tail [y]@returnList
    | (x,y)::tail -> getCorrespondingSecurity sec tail returnList
    | _ -> returnList
and addToList (x:AExpr) (l:AExpr List) (allowedFlowList: (AExpr * AExpr)List) =
    match l with
    | head::tail -> addToList x tail ([(x,head)]@allowedFlowList)
    | _ -> allowedFlowList
and removeDuplicates (allowedFlowList: (AExpr * AExpr)List) (accumulatingAllowedFlowList: (AExpr * AExpr)List) =
    match allowedFlowList with
    | x::tail when (listContains x accumulatingAllowedFlowList) -> removeDuplicates tail accumulatingAllowedFlowList
    | x::tail -> removeDuplicates tail ([x]@accumulatingAllowedFlowList)
    | _ -> accumulatingAllowedFlowList

let (secLatTest: (AExpr * AExpr)List) = [(Var("Public"), Var("Private"))]
let (secClassTest: (AExpr * AExpr)List) = [(Var("x"), Var("Public")); (Var("y"), Var("Private"))]

produceAllowedFlowList secLatTest secClassTest secClassTest []