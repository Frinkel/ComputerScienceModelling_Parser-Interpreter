module SignAnalyzer

open System.Text.RegularExpressions

let rec listContains (elem) (l) = List.exists (fun x -> x = elem) l

let cleanUpSignList sl = 
    if (listContains Plus sl) && (listContains Minus sl) && (listContains Zero sl) then [Plus;Zero;Minus]
    else if (listContains Plus sl) && (listContains Minus sl) then  [Plus;Minus]
    else if (listContains Plus sl) && (listContains Zero sl) then  [Plus;Zero]
    else if (listContains Minus sl) && (listContains Zero sl) then  [Minus;Zero]
    else if (listContains Plus sl) then [Plus]
    else if (listContains Minus sl) then [Minus]
    else [Zero]


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
    [Array(x,Num(1)), cleanUpSignList(arrayStringToSignList(Console.ReadLine()))]

let rec reverseListSign list = List.fold (fun acc elem -> elem::acc) [] list

let rec setNewSigns var s (l:(AExpr*(Signs)List)List) (nl:(AExpr*(Signs)List)List) =
    match l with
    | (ae,sl)::tail when var = ae -> setNewSigns var s tail ([(ae,s)]@nl)
    | (ae,sl)::tail -> setNewSigns var s tail ([(ae,sl)]@nl)
    | _ -> (reverseListSign nl)
and getParticularSigns var (l:(AExpr*(Signs)List)List) =
    match l with
    | (ae,sl)::tail when var = ae -> sl
                                    //  match sl with
                                    //  | s::tail -> s
                                    //  | _ -> Zero
    | (ae,sl)::tail -> getParticularSigns var tail
    | _ -> [Zero]



let rec plusEvalSign (s1:Signs) (s2:Signs) =
    match (s1,s2) with
    | (s1,s2) when s1 = Minus && s2 = Minus-> [Minus]
    | (s1,s2) when (s1 = Zero && s2 = Minus) || (s1 = Minus && s2 = Zero) -> [Minus]
    | (s1,s2) when (s1 = Plus && s2 = Minus) || (s1 = Minus && s2 = Plus) -> [Minus;Zero;Plus]
    | (s1,s2) when s1 = Zero && s2 = Zero-> [Zero]
    | (s1,s2) when (s1 = Zero && s2 = Plus) || (s1 = Plus && s2 = Zero) -> [Plus]
    | (s1,s2) when s1 = Plus && s2 = Plus-> [Plus]
and executePlusSign (sl1:Signs List) (sl2:Signs List) (nl:Signs List) =
    match (sl1,sl2) with
    | (s1::sl1tail,s2::sl2tail) -> executePlusSign sl1tail sl2tail ((plusEvalSign s1 s2)@nl)
    | _ -> cleanUpSignList(nl)

let rec minusEvalSign (s1:Signs) (s2:Signs) =
    match (s1,s2) with
    | (s1,s2) when s1 = Minus && s2 = Minus-> [Minus;Zero;Plus]
    | (s1,s2) when (s1 = Zero && s2 = Minus) -> [Plus]
    | (s1,s2) when (s1 = Minus && s2 = Zero) -> [Minus]
    | (s1,s2) when (s1 = Minus && s2 = Plus) -> [Minus]
    | (s1,s2) when (s1 = Plus && s2 = Minus) -> [Plus]
    | (s1,s2) when (s1 = Zero && s2 = Zero) -> [Zero]
    | (s1,s2) when (s1 = Zero && s2 = Plus) -> [Minus]
    | (s1,s2) when (s1 = Plus && s2 = Zero) -> [Plus]
    | (s1,s2) when (s1 = Plus && s2 = Plus) -> [Minus;Zero;Plus]
and executeMinusSign (sl1:Signs List) (sl2:Signs List) (nl:Signs List) =
    match (sl1,sl2) with
    | (s1::sl1tail,s2::sl2tail) -> executeMinusSign sl1tail sl2tail ((minusEvalSign s1 s2)@nl)
    | _ -> cleanUpSignList(nl)

let rec timesEvalSign (s1:Signs) (s2:Signs) =
    match (s1,s2) with
    | (s1,s2) when s1 = Minus && s2 = Minus-> [Plus]
    | (s1,s2) when (s1 = Zero || s2 = Zero) -> [Zero]
    | (s1,s2) when (s1 = Minus && s2 = Plus) || (s1 = Plus && s2 = Minus) -> [Minus]
    | (s1,s2) when (s1 = Plus && s2 = Plus) -> [Plus]
and executeTimesSign (sl1:Signs List) (sl2:Signs List) (nl:Signs List) =
    match (sl1,sl2) with
    | (s1::sl1tail,s2::sl2tail) -> executeTimesSign sl1tail sl2tail ((timesEvalSign s1 s2)@nl)
    | _ -> cleanUpSignList(nl)

let rec divideEvalSign (s1:Signs) (s2:Signs) =
    match (s1,s2) with
    | (s1,s2) when s2 = Zero -> printfn "Can't divide by zero"
                                failwith "Can't divide by zero"
    | (s1,s2) when s1 = Zero -> [Zero]
    | (s1,s2) when s1 = Minus && s2 = Minus-> [Plus]
    | (s1,s2) when (s1 = Minus && s2 = Plus) -> [Minus]
    | (s1,s2) when (s1 = Minus && s2 = Plus) || (s1 = Plus && s2 = Minus) -> [Minus]
    | (s1,s2) when (s1 = Plus && s2 = Plus) -> [Plus]
and executeDivideSign (sl1:Signs List) (sl2:Signs List) (nl:Signs List) =
    match (sl1,sl2) with
    | (s1::sl1tail,s2::sl2tail) -> executeDivideSign sl1tail sl2tail ((divideEvalSign s1 s2)@nl)
    | _ -> cleanUpSignList(nl)

let rec powEvalSign (s1:Signs) (s2:Signs) =
    match (s1,s2) with
    | (s1,s2) when  s2 = Zero -> [Plus]
    | (s1,s2) when s2 = Minus -> printfn "Can not take number to the power of negative number"
                                 failwith "Can not take number to the power of negative number"
    | (s1,s2) when s1 = Zero -> [Zero]
    | (s1,s2) when s1 = Minus -> [Minus;Plus]
    | (s1,s2) when s1 = Plus -> [Plus]
and executePowSign (sl1:Signs List) (sl2:Signs List) (nl:Signs List) =
    match (sl1,sl2) with
    | (s1::sl1tail,s2::sl2tail) -> executePowSign sl1tail sl2tail ((powEvalSign s1 s2)@nl)
    | _ -> cleanUpSignList(nl)

let rec reverseSign (sl:Signs List) nl = 
    match sl with
    | s::tail when s = Plus-> reverseSign tail ([Minus]@nl)
    | s::tail when s = Minus-> reverseSign tail ([Plus]@nl)
    | s::tail when s = Zero-> reverseSign tail ([Zero]@nl)
    | _ -> nl

let rec avalSign (a:AExpr) (varListSign:(AExpr*(Signs)List)List) (nl:Signs List) =
    match a with
      | Num(x)            -> if x > 0 then [Plus]@nl else if x = 0 then [Zero]@nl else [Minus]@nl
      | Array(var,x)      -> (getParticularSigns a varListSign)
      | Var(x)            -> (getParticularSigns a varListSign)
      | TimesExpr(x,y)    -> executeTimesSign (avalSign x varListSign []) (avalSign y varListSign []) []
      | DivExpr(x,y)      -> executeDivideSign (avalSign x varListSign []) (avalSign y varListSign []) []
      | PlusExpr(x,y)     -> executePlusSign (avalSign x varListSign []) (avalSign y varListSign []) []
      | MinusExpr(x,y)    -> executeMinusSign (avalSign x varListSign []) (avalSign y varListSign []) []
      | PowExpr(x,y)      -> executePowSign (avalSign x varListSign []) (avalSign y varListSign []) []
      | UPlusExpr(x)      -> (avalSign x varListSign [])
      | UMinusExpr(x)     -> reverseSign(avalSign x varListSign []) []

let rec equalsSign (s1:Signs) (s2:Signs) = (s1 = s2)
and executeEqualsSign (sl1:Signs List) (sl2:Signs List) b =
     match (sl1,sl2) with
    | (s1::sl1tail,s2::sl2tail) -> executeEqualsSign sl1tail sl2tail ((equalsSign s1 s2) || b)
    | _ -> b

let rec notEqualsSign (s1:Signs) (s2:Signs) = 
     match (s1,s2) with
     | (Zero,Zero) -> false
     | _ -> true
and executeNotEqualsSign (sl1:Signs List) (sl2:Signs List) b =
    match (sl1,sl2) with
    | (s1::sl1tail,s2::sl2tail) -> executeNotEqualsSign sl1tail sl2tail ((notEqualsSign s1 s2) || b)
    | _ -> b

let rec greaterSign (s1:Signs) (s2:Signs) =
    match (s1,s2) with
    | (Plus,_) -> true
    | (Zero,Minus) -> true
    | (Minus,Minus) -> true
    | _ -> false
and executeGreaterSign (sl1:Signs List) (sl2:Signs List) b =
     match (sl1,sl2) with
    | (s1::sl1tail,s2::sl2tail) -> executeGreaterSign sl1tail sl2tail ((greaterSign s1 s2) || b)
    | _ -> b

let rec lessSign (s1:Signs) (s2:Signs) =
    match (s1,s2) with
    | (Minus,_) -> true
    | (Plus,Plus) -> true
    | (Zero,Plus) -> true
    | _ -> false
and executeLessSign (sl1:Signs List) (sl2:Signs List) b =
     match (sl1,sl2) with
    | (s1::sl1tail,s2::sl2tail) -> executeLessSign sl1tail sl2tail ((lessSign s1 s2) || b)
    | _ -> b

let rec bvalSign b (varListSign:(AExpr*(Signs)List)List) =
    match b with
    | Bool(x)                   -> x
    | AndExpr(x,y)              -> (bvalSign x varListSign) & (bvalSign y varListSign)
    | NotExpr(x)                -> (bvalSign x varListSign) || not (bvalSign x varListSign)
    | OrExpr(x,y)               -> (bvalSign x varListSign) || (bvalSign x varListSign)
    | ShortOrExpr(x,y)          -> ((bvalSign x varListSign) || (bvalSign x varListSign))
    | ShortAndExpr(x,y)         -> ((bvalSign x varListSign) && (bvalSign x varListSign))
    | EqualsExpr(x,y)           -> (executeEqualsSign (avalSign x varListSign []) (avalSign y varListSign []) false)
    | NotEqualsExpr(x,y)        -> (executeNotEqualsSign (avalSign x varListSign []) (avalSign y varListSign []) false)
    | GreaterExpr(x,y)          -> (executeGreaterSign (avalSign x varListSign []) (avalSign y varListSign []) false)
    | LessExpr(x,y)             -> (executeLessSign (avalSign x varListSign []) (avalSign y varListSign []) false)
    | GreaterOrEqualExpr(x,y)   -> (executeGreaterSign (avalSign x varListSign []) (avalSign y varListSign []) false) || (executeEqualsSign (avalSign x varListSign []) (avalSign y varListSign []) false)
    | LessOrEqualExpr(x,y)      -> (executeLessSign (avalSign x varListSign []) (avalSign y varListSign []) false) || (executeEqualsSign (avalSign x varListSign []) (avalSign y varListSign []) false)


let rec getNewSigns var sl (l:(AExpr*(Signs)List)List) (nl:((AExpr*(Signs)List)List)List)  =
    match sl with
    | s::tail -> getNewSigns var tail l ([(setNewSigns var [s] l [])]@nl)
    | _ -> nl


let rec cvalSign (l:(AExpr*(Signs)List)List) (c:SubTypes) =
    match c with
    | SubC(x) -> match x with
                 | Assign(var, com) -> match var with
                                     | Var(v)       -> (getNewSigns var (avalSign com l []) l [])
                                     | Array(v1,v2) -> (getNewSigns var (avalSign com l []) l [])
    | SubB(x) -> (if (bvalSign x l) then [l] else [])




let rec containsNode (l:(int*((AExpr*(Signs)List)List)List)List) (q:int)=
    match l with
    | (x,y)::tail when (q = x) -> true 
    | (x,y)::tail -> containsNode tail q
    | _ -> false

let rec initializeSignVars (varList:(AExpr) List) (nl:((AExpr*(Signs)List)List)List) =
    match varList with
    | a:: tail -> [[(a,[])]]@(initializeSignVars tail nl)
    | _ -> nl

let rec initializeSigns (edges:(int * SubTypes * int)List) (varListSign:((AExpr*(Signs)List)List)List) (nl:(int*((AExpr*(Signs)List)List)List)List) (aExprList: AExpr List) = 
    match edges with
    | (q0,c,q1)::tail when not (containsNode nl q0) && (q0 = 0) -> (initializeSigns tail varListSign (nl@[(0, [ (InitializationOfSigns aExprList []) ])]) aExprList)
    | (q0,c,q1)::tail when not (containsNode nl q0) -> (initializeSigns tail varListSign (nl@[(q0,varListSign)]) aExprList)
    | (q0,c,q1)::tail -> (initializeSigns tail varListSign nl aExprList)
    | _ -> nl@[(1,varListSign)]


let rec removeDuplicatesSign (varListSign:(int*((AExpr*(Signs)List)List)List)List) =
    match varListSign with 
    | (q0,l)::tail -> [(q0,(removeDuplicatesSignHelper l []))]@(removeDuplicatesSign tail)
    | _ -> []
and removeDuplicatesSignHelper (l:((AExpr*(Signs)List)List)List) nl =
    match l with
    | elem::tail when (listContains elem tail) || (hasEmptySigns elem) -> removeDuplicatesSignHelper tail nl
    | elem::tail -> removeDuplicatesSignHelper tail ([elem]@nl)
    | _ -> nl
and hasEmptySigns (l:(AExpr*(Signs)List)List) =
    match l with
    | (ae,sl)::tail -> match sl with
                       | [] -> true
                       | _ -> false
    | _ -> false


let rec prepareWorkList (edges:(int * SubTypes * int)List) (varListSign:(int*((AExpr*(Signs)List)List)List)List) (wl:(int * ((int * SubTypes)List) * int)List)=
    match varListSign with
    | (q0,l)::tail when q0 = 0 -> prepareWorkList edges tail ([(q0,(getNodesLeadingTo edges q0 []),1)]@wl)
    | (q0,l)::tail -> prepareWorkList edges tail ([(q0,(getNodesLeadingTo edges q0 []),0)]@wl)
    | _ -> wl
and getNodesLeadingTo (edges:(int * SubTypes * int)List) (q:int) nl=
    match edges with
    | (q0,c,q1)::tail  when q = q1 -> getNodesLeadingTo tail q ([(q0,c)]@nl)
    | (q0,c,q1)::tail -> getNodesLeadingTo tail q nl
    | _ -> nl


let rec checkPrevStatus (node:int) (status:int) (wl:(int * ((int * SubTypes)List) * int)List) (originalWl:(int * ((int * SubTypes)List) * int)List)=
    match wl with
    | (n,l,s)::tail when n = node -> prevStatus n status l originalWl (true)
    | (n,l,s)::tail -> checkPrevStatus node status tail originalWl 
    | _ -> false
and prevStatus (n:int) (status:int) (l:((int * SubTypes)List)) (wl:(int * ((int * SubTypes)List) * int)List) (b:bool) =
    match l with
    | (i,c)::tail -> prevStatus n status tail wl (b && (statusFromNode i status wl))
    | _ -> b
and statusFromNode (node:int) (status:int) (wl:(int * ((int * SubTypes)List) * int)List) =
    match wl with
    | (n,l,s)::tail when node = n -> (s >= status)
    | (n,l,s)::tail -> statusFromNode node status tail
    | _ -> false

let rec onWorkListcomplete (node:int) (wl:(int * ((int * SubTypes)List) * int)List) nl =
    match wl with
    | (n,l,s)::tail when n = node -> onWorkListcomplete node tail ([((n,l,(s+1)))]@nl)
    | (n,l,s)::tail -> onWorkListcomplete node tail ([(n,l,s)]@nl)
    | _ -> nl

let rec runSignCommand q0 q1 c (varListSign:(int*((AExpr*(Signs)List)List)List)List) (varListSignOriginal:(int*((AExpr*(Signs)List)List)List)List) (nl:(int*((AExpr*(Signs)List)List)List)List) =
     match varListSign with
    | (q,l)::tail when q = q1 -> runSignCommand q0 q1 c tail varListSignOriginal ([(q,(updateNode q0 q1 c (getSignsFromNode q0 varListSignOriginal) [])@l)]@nl)//updateNode tail varListSign2 q0 q1 var sign [q,(updateSigns varListSign2 l q0 q1 var sign [])]@nl
    | (q,l)::tail -> runSignCommand q0 q1 c tail varListSignOriginal ((q,l)::nl)//updateNode tail varListSign2 q0 q1 var sign [(q,l)]@nl
    | _ -> nl
and getSignsFromNode node (varListSign:(int*((AExpr*(Signs)List)List)List)List) =
    match varListSign with
    | (q,l)::tail when q = node -> l
    | (q,l)::tail -> getSignsFromNode node tail
    | _ -> []
and updateNode q0 q1 c (l0:((AExpr*(Signs)List)List)List) (nl:((AExpr*(Signs)List)List)List) =
    match l0 with
    | el::tail -> updateNode q0 q1 c tail ((cvalSign el c)@nl)
    | _ -> nl


let rec evalSign (node:int) (l:((int * SubTypes)List)) (varListSign:(int*((AExpr*(Signs)List)List)List)List) = 
    match l with
    | (i,c)::tail -> evalSign node tail (runSignCommand i node c varListSign varListSign []) 
    | _ -> varListSign

let rec signAnalysis (wl:(int * ((int * SubTypes)List) * int)List) (wltail:(int * ((int * SubTypes)List) * int)List) (varListSign:(int*((AExpr*(Signs)List)List)List)List) (level:int) =
    match wltail with
    | (n,l,s)::tail when (checkPrevStatus n level wl wl) && s <> 1 -> signAnalysis (onWorkListcomplete n wl []) (onWorkListcomplete n wl []) (removeDuplicatesSign (evalSign n l varListSign)) level
    | (n,l,s)::tail -> signAnalysis wl tail varListSign level
    | _ when (isWlComplete wl (level) true) -> //printfn "Finished correctly"
                                               varListSign
    | _ -> //printfn "did not Finished correctly"
           (reverseListSign (signAnalysis wl wl (signAnalysis wl wl (varListSign) (level-1)) (level-1)))

and isWlComplete (wl:(int * ((int * SubTypes)List) * int)List) (level:int) (b:bool) =
    match wl with
    | (n,l,s)::tail -> isWlComplete tail level (b && (s >= level))
    | _ -> b

let rec prettySignPrinter (varListSign:(int*((AExpr*(Signs)List)List)List)List) =
    match varListSign with
    | (n,l)::tail when n = 1-> printfn "Node %i (Final node)" n
                               prettySignPrinterHelper l
                               prettySignPrinter tail
    | (n,l)::tail -> printfn "Node %i" n
                     prettySignPrinterHelper l
                     prettySignPrinter tail
    | _ -> printfn ""
and prettySignPrinterHelper (l:((AExpr*(Signs)List)List)List) =
    match l with
    | l1::tail -> prettySignPrintEachComb l1
                  prettySignPrinterHelper tail
    | _ -> printf ""
and prettySignPrintEachComb (l:(AExpr*(Signs)List)List) =
    match l with
    | (ae,sl)::tail -> printf "%s: %s" (stringASign ae) (printSignList sl)
                       prettySignPrintEachComb tail
    | _ -> printfn ""
and stringASign s = 
    match s with
    | Var(x)            -> x:string
    | Array(x,y)        -> (x:string) + "[" + "]"
and printSignList (sl:Signs List) =
    match sl with
    | s::tail -> (printSignList tail ) + " " + (printSign s) + " "
    | _ -> ""
and printSign s =
    match s with
    | Plus -> "+"
    | Minus -> "-"
    | Zero -> "0"