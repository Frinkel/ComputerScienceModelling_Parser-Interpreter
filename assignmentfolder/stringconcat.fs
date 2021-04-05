module stringconcat



let rec stringA s = 
    match s with
    | Var(x)            ->  x:string
    | Num(x)            ->  sprintf "%i" x
    | Array(x,y)        ->  (x:string) + "[" + (stringA y) + "]"
    | TimesExpr(x,y)    ->  (stringA x) + " * " + (stringA y)
    | DivExpr(x,y)      ->  (stringA x) + " / " + (stringA y)
    | PlusExpr(x,y)     ->  (stringA x) + " + " + (stringA y) 
    | MinusExpr(x,y)    ->  (stringA x) + " - " + (stringA y)
    | PowExpr(x,y)      ->  (stringA x) + " ^ " + (stringA y)
    | UPlusExpr(x)      ->  (stringA x)
    | UMinusExpr(x)     ->  "-" + (stringA x)

let rec stringB s =
    match s with 
    | Bool(x)                   -> string x
    | NotExpr(x)                -> "!(" + (stringB x) + ")"
    | OrExpr(x,y)               -> (stringB x) + " | " + (stringB y)
    | ShortOrExpr(x,y)          -> (stringB x) + " || " + (stringB y)
    | ShortAndExpr(x,y)         -> (stringB x) + " && " + (stringB y)
    | AndExpr(x,y)              -> (stringB x) + " & " + (stringB y)
    | EqualsExpr(x,y)           -> (stringA x) + " = " + (stringA y)
    | NotEqualsExpr(x,y)        -> (stringA x) + " != " + (stringA y)
    | GreaterExpr(x,y)          -> (stringA x) + " > " + (stringA y)
    | LessExpr(x,y)             -> (stringA x) + " < " + (stringA y)
    | GreaterOrEqualExpr(x,y)   -> (stringA x) + " >= " + (stringA y)
    | LessOrEqualExpr(x,y)      -> (stringA x) + " <= " + (stringA y)   
    
let rec stringC s = 
    match s with 
    | Assign(var, x)                ->      (stringA var) + ":=" + (stringA x)
    | SemiColon(c1,c2)              ->      (stringC c1) 
                                            (stringC c2)
    | Skip                          ->      "skip"
    | If(Gc)                        ->      "if(" + (stringGc Gc)
    | Do(Gc)                        ->      "do(" + (stringGc Gc)         
and stringGc gs =
    match gs with
    | ExecuteIf(b,c)                ->      (stringB b) + " then " + (stringC c)
    | Else(gc1,gc2)                 ->      (stringGc gc1) + " else(" + (stringGc gc2) + ") "


// Print edges
let stringCEdges q0 c q1 = ((sprintf "%i" q0) + " -> " + (sprintf "%i" q1) + " [label = \"" + (stringC c) + "\"];\n")
let stringBEdges q0 b q1 = ((sprintf "%i" q0) + " -> " + (sprintf "%i" q1) + " [label = \"" + (stringB b) + "\"];\n")

let rec getStringFromList (l:(int * SubTypes * int)List) (str:string) =
    match l with
    | [] -> str
    | (q0, c, q1)::tail -> match (c) with 
                              | SubC(x) -> getStringFromList tail (str + (stringCEdges q0 x q1))
                              | SubB(x) -> getStringFromList tail (str + (stringBEdges q0 x q1))
//let testList:(int * SubTypes * int * int)List = [(0, SubC((If(ExecuteIf(NotExpr(Bool(false)), Assign(Var("x"), Num(2.0)))))), 1, 10); (0, SubB(Bool(true)), 1, 10); (0, SubC((If(ExecuteIf(NotExpr(Bool(false)), Assign(Var("x"), Num(2.0)))))), 1, 10)];;

let rec printAssignmentList (aList:(AExpr * (int)List) List) =
    match aList with
    | [] -> printf ""
    | head::tail -> match head with
                        | (x,y) -> match x with
                                    | Var(s)        -> printfn "%s = %s" s (getVar y)
                                    | Array(s,n)    -> printfn "%s = {%s}" s (getArray y "")
                    printAssignmentList tail
and getVar y =
    match y with
    | [] -> ""
    | head::tail -> head |> string
and getArray n newString =
    match n with
    | [] -> newString
    | head::[] -> newString + (head |> string)
    | head::tail -> getArray tail (newString + (head |> string) + ", ")


// Checks wether theres duplicate names in the variable assignments
let rec checkDuplicateNames (varList: AExpr List) (OGVarList: AExpr List) (nameList: string List) = 
    match varList with
    | [] -> OGVarList
    | head::tail -> match head with
                        | Var(s)        when not(ListContains nameList s) -> checkDuplicateNames tail OGVarList (nameList@[s])
                        | Array(s,n)    when not(ListContains nameList s) -> checkDuplicateNames tail OGVarList (nameList@[s])
                        | _                                               -> printfn  "Duplicate name found, please use different names for assignments!"
                                                                             failwith "Duplicate name found, please use different names for assignments!"
