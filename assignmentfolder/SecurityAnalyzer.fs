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
