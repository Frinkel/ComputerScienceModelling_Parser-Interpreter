module SecurityAnalyzer

open System.Text.RegularExpressions

// From: https://stackoverflow.com/questions/53818476/f-match-many-regex
let (|Regex|_|) pattern input =
    let m = Regex.Match(input, pattern)
    if m.Success then Some(List.tail [ for g in m.Groups -> g.Value ])
    else None


let securityVarChecker (s:string) =
    match s with
    | Regex @"^([a-zA-Z]+)((?!.*\s.*).+)?$" [ grp1;grp2 ] -> Var(grp1+grp2)
    | _ ->  printfn "ERROR: Security variable failed to hold correct syntax of no spaces and no leading integers."
            failwith "ERROR: Security variable failed to hold correct syntax of no spaces and no leading integers."
;;

let securityLatticeChecker (s:string) =
    match s with
    | Regex @"(^(([a-zA-Z]+([a-zA-Z0-9]+)?)[<]([a-zA-Z]+([a-zA-Z0-9]+)?)[,]?)+$)" [ grp1;grp2;grp3;grp4;grp5;grp6 ] -> grp1
    | _ ->  printfn "ERROR: Security variable failed to hold correct syntax of \"Security1<Security2,...SecurityN<SecurityN+1\""
            failwith "ERROR: Security variable failed to hold correct syntax of \"Security1<Security2,...SecurityN<SecurityN+1\""
;;

let securityLatticeInitializer (s:string) =
    let b = Seq.toList s
    let rec securityLatticeStringToList (s:char List) (ns:string) (nl:string List) =
        match s with
        | [] -> nl
        | x::[]  -> securityLatticeStringToList [] "" (nl@[ns+(string x)])
        | x::tail when x = ',' -> securityLatticeStringToList tail "" (nl@[ns])
        | x::tail when x = '<' -> securityLatticeStringToList tail "" (nl@[ns])
        | x::tail -> securityLatticeStringToList tail (ns+(string x)) (nl)
    
    let rec securityLatticeListToTupleList (l:string List) (nl:(AExpr * AExpr) List) =
        match l with
        | [] -> nl
        | x::y::tail -> securityLatticeListToTupleList tail (nl@[(Var(x),Var(y))])

    securityLatticeListToTupleList (securityLatticeStringToList b "" []) []

securityLatticeInitializer "public<private,x<a";;

// Read console from the user
let rec InitializationOfSecurity (l: AExpr List) (nl:(AExpr * AExpr) List) = 
    match l with
    | [] -> nl
    | a::tail -> match a with
                 | Var(x)       -> InitializationOfSecurity tail (nl@[getVariableInitializationFromUser x])
                 | Array(x,y)   -> InitializationOfSecurity tail (nl@[getArrayInitializationFromUser x])
and getVariableInitializationFromUser (x:string) =
    printf "%s = " x
    (Var(x), securityVarChecker(Console.ReadLine()))
and getArrayInitializationFromUser (x:string) =
    printf "%s = " x
    (Array(x,Num(1)), securityVarChecker(Console.ReadLine()))


// [(Private, Public)]
// [(i, Public); (x, Public)]
// (^[a-z A-Z]+[a-zA-Z0-9]+?$)

let rec produceAllowedFlowList (secLattice: (AExpr * AExpr)List) (secClassification: (AExpr * AExpr)List) (secClassificationTail: (AExpr * AExpr)List) (allowedFlowList: (AExpr * AExpr)List) = 
    match secClassificationTail with 
    | (x,y)::tail when (checkSecurityLattice y secLattice) -> produceAllowedFlowList secLattice secClassification tail (addToList x ([x]@(getVariableFromSecClassification ([y]@(getCorrespondingSecurity y secLattice [])) secClassification [])) allowedFlowList) 
    | (x,y)::tail ->    produceAllowedFlowList secLattice secClassification tail (addToList x ([x]) allowedFlowList)
    | _ ->  removeDuplicates allowedFlowList []
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