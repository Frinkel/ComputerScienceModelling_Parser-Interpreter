module SecurityAnalyzer

open System.Text.RegularExpressions

// PRETTY PRINTER FOR SECURITY ANALYSIS
let rec prettySecurityPrint flowList = 
    match flowList with
    | (Var(x),Var(y))::[]   -> printfn "%s -> %s" (x:string) (y:string)
    | (Var(x),Var(y))::tail -> printf "%s -> %s, " (x:string) (y:string)
                               prettySecurityPrint tail;;


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

// securityLatticeInitializer "public<private,x<a";;

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



// let rec produceActualFlows2 (edges:(int * SubTypes * int)List) (edgestail:(int * SubTypes * int)List) (varList:(AExpr * (int)List) List) (actualFlowsList: (AExpr * AExpr)List) (q:int) =
//     match edgestail with
//     | (q0,c,q1)::tail  when q = q0 -> match (c) with 
//                                     | SubC(x)                      -> printfn "Took path %i to %i" q0 q1
//                                                                       produceActualFlows edges edges (cval x varList) actualFlowsList q1
//                                     | SubB(x) when (bval x varList)-> printfn "Took path %i to %i" q0 q1
//                                                                       produceActualFlows edges edges varList actualFlowsList q1
//                                     | _                            -> produceActualFlows edges tail varList actualFlowsList q
//     | (q0,e,q1)::tail -> produceActualFlows edges tail varList actualFlowsList q
//     | _ when q = 1    -> printfn "Succes finished at node %i " q
//                          actualFlowsList
//     | _               -> printfn "Error! stuck at node %i " q
//                          actualFlowsList


let rec produceActualFlows (edges:(int * SubTypes * int)List) (actualFlow:(AExpr * AExpr)List) (q:int) =
    match edges with
    | [] -> actualFlow
    | (q0, c, q1)::tail  when q = q0 -> match (c) with 
                                        | SubC(x) -> produceActualFlows tail (addFlowSubC actualFlow x) q1
                                        | SubB(x) -> produceActualFlows tail (addFlowSubB actualFlow x tail q1) q1
                                        | _ -> produceActualFlows tail actualFlow q
and addFlowSubC actualFlow x =
    match x with
    | Assign(a, b) -> match (a, b) with
                      | (Var(c), Var(d)) -> actualFlow@[(b,a)]
                      | (Var(c), _) -> actualFlow
and addFlowSubB actualFlow a tail q1 =
    match a with
    | Bool(x)                   -> actualFlow
    | AndExpr(x,y)              -> (addFlowSubB actualFlow x tail q1)@(addFlowSubB actualFlow y tail q1) // REVISIT?
    | NotExpr(x)                -> actualFlow
    | OrExpr(x,y)               -> (addFlowSubB actualFlow x tail q1)@(addFlowSubB actualFlow y tail q1) // REVISIT?
    | ShortOrExpr(x,y)          -> (addFlowSubB actualFlow x tail q1)@(addFlowSubB actualFlow y tail q1) // REVISIT?
    | ShortAndExpr(x,y)         -> (addFlowSubB actualFlow x tail q1)@(addFlowSubB actualFlow y tail q1) // REVISIT?
    | EqualsExpr(x,y)           -> addVarsFromBExprToActualFlow actualFlow (x,y) tail q1
    | NotEqualsExpr(x,y)        -> addVarsFromBExprToActualFlow actualFlow (x,y) tail q1
    | GreaterExpr(x,y)          -> addVarsFromBExprToActualFlow actualFlow (x,y) tail q1
    | LessExpr(x,y)             -> addVarsFromBExprToActualFlow actualFlow (x,y) tail q1
    | GreaterOrEqualExpr(x,y)   -> addVarsFromBExprToActualFlow actualFlow (x,y) tail q1
    | LessOrEqualExpr(x,y)      -> addVarsFromBExprToActualFlow actualFlow (x,y) tail q1
and addVarsFromBExprToActualFlow actualFlow (x,y) tail q1 = match (x,y) with
    | (Var(c), Var(d)) -> match tail with
                            | (nq0, c1, nq1)::tail2  when q1 = nq0 -> match c1 with
                                                                | SubB(z) -> addFlowSubB actualFlow z tail2 nq1
                                                                | SubC(z) -> match z with
                                                                             | Assign(g, f) -> actualFlow@[(x, g); (y, g)]
    | (Var(c), _) -> match tail with
                            | (nq0, c1, nq1)::tail2  when q1 = nq0 -> match c1 with
                                                                | SubB(z) -> addFlowSubB actualFlow z tail2 nq1
                                                                | SubC(z) -> match z with
                                                                             | Assign(g, f) ->  printfn ("C1: %A TAIL1: %A TAIL2: %A : nq1 : %i") [c] tail tail2 nq1
                                                                                                actualFlow@[(x, g)]@(produceActualFlows (tail2) [] nq1)
    | (_ , Var(c)) -> match tail with
                            | (nq0, c1, nq1)::tail2  when q1 = nq0 -> match c1 with
                                                                | SubB(z) -> addFlowSubB actualFlow z tail2 nq1
                                                                | SubC(z) -> match z with
                                                                             | Assign(g, f) -> actualFlow@[(y, g)]
    | _ -> actualFlow




produceActualFlows [(0, SubB (GreaterExpr (Var "b", Num 0)), 2); (2, SubC (Assign (Var "a", Num 2)), 3); (3, SubC (Assign (Var "c", Num 2)), 1)] [] 0 // NOT COVERED

produceActualFlows [(3, SubC (Assign (Var "c", Num 2)), 1)] [] 3
//[(0, SubC (Assign (Var "a", Var "b")), 1)]
// [(0, SubB (GreaterExpr (Var "b", Num 0)), 2); (2, SubC (Assign (Var "a", Num 2)), 3); (3, SubC (Assign (Var "c", Num 2)), 1); (0, SubB (GreaterExpr (Var "a", Num 1)), 4); (4, SubC (Assign (Var "b", Num 2)), 1)]




//produceActualFlows prog prog [Var "b"; Var "a"; Var "c"] [] 0;;


// let (secLatTest: (AExpr * AExpr)List) = [(Var("Public"), Var("Private"))]
// let (secClassTest: (AExpr * AExpr)List) = [(Var("x"), Var("Public")); (Var("y"), Var("Private"))]

// produceAllowedFlowList secLatTest secClassTest secClassTest []