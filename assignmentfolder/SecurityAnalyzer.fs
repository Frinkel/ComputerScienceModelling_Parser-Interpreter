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

let rec removeDuplicates (allowedFlowList: (AExpr * AExpr)List) (accumulatingAllowedFlowList: (AExpr * AExpr)List) =
    match allowedFlowList with
    | x::tail when (listContains x accumulatingAllowedFlowList) -> removeDuplicates tail accumulatingAllowedFlowList
    | x::tail -> removeDuplicates tail ([x]@accumulatingAllowedFlowList)
    | _ -> accumulatingAllowedFlowList

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
let rec checkLatticeAgainstVars (lattice:(AExpr * AExpr)List) (securityVars:(AExpr * AExpr)List) = 
    match securityVars with
    | [] -> true
    | (x,y)::tail when latticeContains y lattice -> checkLatticeAgainstVars lattice tail 
    | _ -> printfn "Security lattice doesn't match security classification for variables and arrays"
           failwith ""
and latticeContains (elem:(AExpr)) (lattice:(AExpr * AExpr)List) =
        match lattice with
        | [] -> true
        | (x,y)::tail when (elem = x || elem = y) -> latticeContains elem tail
        | _  -> false 

let rec produceActualFlows (edges:(int * SubTypes * int)List) (actualFlow:(AExpr * AExpr)List) (q:int) =
    match edges with
    | [] -> actualFlow
    | (q0, c, q1)::tail  when q0 = 0 && q1 = 1 ->  produceActualFlows tail actualFlow q
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
    | NotExpr(x)                -> addFlowSubB actualFlow x tail q1
    | OrExpr(x,y)               -> (addFlowSubB actualFlow x tail q1)@(addFlowSubB actualFlow y tail q1) // REVISIT?
    | ShortOrExpr(x,y)          -> (addFlowSubB actualFlow x tail q1)@(addFlowSubB actualFlow y tail q1) // REVISIT?
    | ShortAndExpr(x,y)         -> (addFlowSubB actualFlow x tail q1)@(addFlowSubB actualFlow y tail q1) // REVISIT?
    | EqualsExpr(x,y)           -> addVarsFromBExprToActualFlow actualFlow (x,y) a tail q1
    | NotEqualsExpr(x,y)        -> addVarsFromBExprToActualFlow actualFlow (x,y) a tail q1
    | GreaterExpr(x,y)          -> addVarsFromBExprToActualFlow actualFlow (x,y) a tail q1
    | LessExpr(x,y)             -> addVarsFromBExprToActualFlow actualFlow (x,y) a tail q1
    | GreaterOrEqualExpr(x,y)   -> addVarsFromBExprToActualFlow actualFlow (x,y) a tail q1
    | LessOrEqualExpr(x,y)      -> addVarsFromBExprToActualFlow actualFlow (x,y) a tail q1
and addVarsFromBExprToActualFlow actualFlow (x,y) a tail q1 = match (x,y) with
    | (Var(c), Var(d)) -> match tail with
                            | [] -> actualFlow
                            | (nq0, c1, nq1)::tail2  when q1 = nq0 -> match c1 with
                                                                | SubB(z) -> (produceActualFlows ([(0, SubB(a), nq1)]@tail2) [] 0)@(addFlowSubB actualFlow z tail2 nq1)
                                                                | SubC(z) -> match z with
                                                                             | Assign(g, f) -> actualFlow@[(x, g); (y, g)]@(produceActualFlows ([(0, SubB(a), nq1)]@tail2) [] 0)
                            | (nq0, c1, nq1)::tail2 -> failwith "d1"
                            
    | (Var(c), _) -> match tail with
                            | [] -> actualFlow
                            | (nq0, c1, nq1)::tail2  when q1 = nq0 -> match c1 with
                                                                | SubB(z) ->    printfn "%A %A" [z] tail2
                                                                                (produceActualFlows ([(0, SubB(a), nq1)]@tail2) [] 0)@(addFlowSubB actualFlow z tail2 nq1)
                                                                | SubC(z) -> match z with
                                                                             | Assign(g, f) -> actualFlow@[(x, g)]@(produceActualFlows ([(0, SubB(a), nq1)]@tail2) [] 0)
                            | (nq0, c1, nq1)::tail2 -> produceActualFlows tail2 actualFlow q1
                            
                            
    | (_ , Var(c)) -> match tail with
                            | [] -> actualFlow
                            | (nq0, c1, nq1)::tail2  when q1 = nq0 -> match c1 with
                                                                | SubB(z) -> (produceActualFlows ([(0, SubB(a), nq1)]@tail2) [] 0)@(addFlowSubB actualFlow z tail2 nq1)
                                                                | SubC(z) -> match z with
                                                                             | Assign(g, f) -> actualFlow@[(y, g)]@(produceActualFlows ([(0, SubB(a), nq1)]@tail2) [] 0)

    | _ -> actualFlow

;;

let rec removeInvalid (edges:(int * SubTypes * int)List) (edgesOG:(int * SubTypes * int)List) =
    match edges with
    | [] -> edgesOG
    | (q0, c, q1)::tail when q0 = 0 && q1 = 1 -> removeInvalid tail edgesOG
    | (q0, c, q1)::tail -> removeInvalid tail edgesOG@[(q0, c, q1)]
let reverseList list = List.fold (fun acc elem -> elem::acc) [] list

// WORKS!
// let (secLatTest: (AExpr * AExpr)List) = [(Var("Public"), Var("Private"))]
// let (secClassTest: (AExpr * AExpr)List) = [(Var("a"), Var("Public")); (Var("y"), Var("Private"))]


// let actualFlow = removeDuplicates (produceActualFlows (reverseList (removeInvalid [(0, SubB (GreaterExpr (Var "y", Num 2)), 2);(0, SubB (NotExpr (GreaterExpr (Var "y", Num 2))), 1);(2, SubC (Assign (Var "a", Num 2)), 3); (3, SubC (Assign (Var "y", PlusExpr (Var "y", Num 1))), 0)] [])) [] 0) [];;
// let allowedFlow = produceAllowedFlowList secLatTest secClassTest secClassTest []

let rec produceViolationFlow (actualFlow:(AExpr * AExpr)List) (allowedFlow:(AExpr * AExpr)List) (violationFlow:(AExpr * AExpr)List) = 
    match actualFlow with
    | [] -> violationFlow
    | (x,y)::tail when listContains (x,y) allowedFlow -> produceViolationFlow tail allowedFlow violationFlow
    | (x,y)::tail -> produceViolationFlow tail allowedFlow [(x,y)]@violationFlow

//produceActualFlows prog prog [Var "b"; Var "a"; Var "c"] [] 0;;
// produceViolationFlow actualFlow allowedFlow []


