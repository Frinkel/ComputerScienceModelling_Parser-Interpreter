module SignAnalyzer



let rec signAnalysis (edges:(int * SubTypes * int)List) (edgestail:(int * SubTypes * int)List) (varList:(AExpr * (int)List) List) (q:int) =
    match edgestail with
    | (q0,c,q1)::tail  when q = q0 -> match (c) with 
                                    | SubC(x)                      -> printfn "Took path %i to %i" q0 q1
                                                                      signAnalysis edges edges (cval x varList) q1
                                    | SubB(x) when (bval x varList)-> printfn "Took path %i to %i" q0 q1
                                                                      signAnalysis edges edges varList q1
                                    | _                            -> signAnalysis edges tail varList q
    | (q0,e,q1)::tail -> signAnalysis edges tail varList q
    | _ when q = 1    -> printfn "Succes finished at node %i " q
                         varList
    | _               -> printfn "Error! stuck at node %i " q
                         varList




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