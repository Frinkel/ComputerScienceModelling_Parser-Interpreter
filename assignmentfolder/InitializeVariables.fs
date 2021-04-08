module InitializeVariables


open System.Text.RegularExpressions

let rec findVariablesWithDuplicates (l:(int * SubTypes * int)List) (nl:AExpr List) =
    match l with
    | [] -> nl
    | (q0, c, q1)::tail -> match (c) with 
                              | SubC(x) ->  findVariablesWithDuplicates tail (nl@(findVariableFromCommand x []))
                              | SubB(x) ->  findVariablesWithDuplicates tail (nl@findVariableFromBExpr x [])
and findVariableFromCommand (command:Command) (nl:AExpr List) =
    match command with
    | Assign(x,y)       -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])
    | SemiColon(c1,c2)  -> (findVariableFromCommand c1 []) @ (findVariableFromCommand c2 [])
    | If(Gc)            -> findVariableFromGc Gc []
    | Do(Gc)            -> findVariableFromGc Gc []
and findVariableFromGc (Gc:GuardedCommand) (nl:AExpr List) =
    match Gc with
    | ExecuteIf(b,c)    -> (findVariableFromBExpr b []) @ (findVariableFromCommand c [])
    | Else(gc1,gc2)     -> (findVariableFromGc gc1 []) @ (findVariableFromGc gc2 [])
and findVariableFromAExpr (a:AExpr) (nl:AExpr List) =
    match a with
    | Num(x)            -> nl
    | Var(x)            -> nl@[a]
    | Array(x,y)        -> nl@[Array(x,(Num(0)))]@(findVariableFromAExpr y [])
    | TimesExpr(x,y)    -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])
    | DivExpr(x,y)      -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])
    | PlusExpr(x,y)     -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])
    | MinusExpr(x,y)    -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])
    | PowExpr(x,y)      -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])
    | UPlusExpr(x)      -> (findVariableFromAExpr x [])
    | UMinusExpr(x)     -> (findVariableFromAExpr x [])
and findVariableFromBExpr (b:BExpr) (nl:AExpr List) =
    match b with
    | Bool(x)                   -> nl
    | AndExpr(x,y)              -> (findVariableFromBExpr x []) @ (findVariableFromBExpr y [])
    | NotExpr(x)                -> findVariableFromBExpr x []
    | OrExpr(x,y)               -> (findVariableFromBExpr x []) @ (findVariableFromBExpr y [])
    | ShortOrExpr(x,y)          -> (findVariableFromBExpr x []) @ (findVariableFromBExpr y [])
    | ShortAndExpr(x,y)         -> (findVariableFromBExpr x []) @ (findVariableFromBExpr y [])
    | EqualsExpr(x,y)           -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])
    | NotEqualsExpr(x,y)        -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])
    | GreaterExpr(x,y)          -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])
    | LessExpr(x,y)             -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])
    | GreaterOrEqualExpr(x,y)   -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])
    | LessOrEqualExpr(x,y)      -> (findVariableFromAExpr x []) @ (findVariableFromAExpr y [])

let rec RemoveDuplicates l nl = 
    match l with
    | [] -> nl
    | x::xtail -> RemoveDuplicates xtail (AddToList nl x)
and AddToList l x =
    if (ListContains l x) then l
    else l @ [x]
and ListContains list n = List.exists (fun x -> x = n) list

// Checks wether theres duplicate names in the variable assignments
let rec checkDuplicateNames (varList: AExpr List) (OGVarList: AExpr List) (nameList: string List) = 
    match varList with
    | [] -> OGVarList
    | head::tail -> match head with
                        | Var(s)        when not(ListContains nameList s) -> checkDuplicateNames tail OGVarList (nameList@[s])
                        | Array(s,n)    when not(ListContains nameList s) -> checkDuplicateNames tail OGVarList (nameList@[s])
                        | _                                               -> printfn  "Duplicate name found, please use different names for assignments!"
                                                                             failwith "Duplicate name found, please use different names for assignments!"

let findVariables (l:(int * SubTypes * int)List) = checkDuplicateNames (RemoveDuplicates (findVariablesWithDuplicates l []) []) (RemoveDuplicates (findVariablesWithDuplicates l []) []) []


// From: https://stackoverflow.com/questions/53818476/f-match-many-regex
let (|Regex|_|) pattern input =
    let m = Regex.Match(input, pattern)
    if m.Success then Some(List.tail [ for g in m.Groups -> g.Value ])
    else None


let dfaOrnfa c = 
    match c with
    | Regex @"(^d)" [ chr ] -> printfn "DFA chosen."
                               true
    | Regex @"(^n)" [ chr ] -> printfn "NFA chosen."
                               false
    | _                     -> printfn "Error: Please write either \'d\' or \'n\'."
                               failwith "Neither chosen"

// Check whether a string only consitst of an integer
let numberChecker (n:string) =
    match n with
    | Regex @"(^[-+]?\s*[0-9]+$)" [ num ] -> 
            //printfn "Variable succesfully initialized."
            num |> int
    | _ ->  printfn "ERROR: Variable failed to hold correct syntax of \"int\""
            failwith "Variable failed to hold correct syntax of \"int\""

// Check if the array syntax holds
let arrayChecker (a:string) =
    match a with
    | Regex @"^\{((\s*[0-9]+\s*,?\s*)+\s*[0-9]*\s*)\}" [ num; d ] ->
        num
    | _ ->  printfn "ERROR: Array failed to hold correct syntax of \"{int 1, int 2, ..., int N}\""
            failwith "Array failed to hold correct syntax of \"{int 1, int 2, ..., int N}\""

// Convert a string list to a int list
let arrayStringToList (s:string) =
    let sA = Seq.toList (arrayChecker s)
    let rec arrayStringToListW (l:char List) (s:string) (nl:int List) =
        match l with
        | [] -> nl
        | (x:char)::[] -> arrayStringToListW [] "" (nl@[(s + string x)|> int])
        | (x:char)::tail when x = ',' -> arrayStringToListW tail "" (nl@[s|> int])
        | (x:char)::tail -> arrayStringToListW tail (s + string x) (nl)

    arrayStringToListW sA "" []

let rec InitializationOfVariablesAndArrays (l: AExpr List) (nl:(AExpr * (int)List) List) = 
    match l with
    | [] -> nl
    | a::tail -> match a with
                 | Var(x)       -> InitializationOfVariablesAndArrays tail (nl@getVariableInitializationFromUser x)
                 | Array(x,y)   -> InitializationOfVariablesAndArrays tail (nl@getArrayInitializationFromUser x)
and getVariableInitializationFromUser (x:string) =
    printf "%s:=" x
    [Var(x), [numberChecker(Console.ReadLine())]]
and getArrayInitializationFromUser (x:string) =
    printfn "Enter all ellements of your array with the syntax \"{int 1, int 2, ..., int N}\""
    printf "%s :=" x
    [Array(x,Num(1)), arrayStringToList(Console.ReadLine())]
