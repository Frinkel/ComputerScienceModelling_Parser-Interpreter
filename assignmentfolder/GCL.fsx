// This script implements our interactive calculator

// For writing to file
open System
open System.IO

// We need to import a couple of modules, including the generated lexer and parser
#r "../FSLEXYACC_FILES/fslexyacc.runtime/10.2.0/lib/netstandard2.0/FsLexYacc.Runtime.dll"
open FSharp.Text.Lexing
open System
#load "GCLTypesAST.fs"
open GCLTypesAST
#load "GCLParser.fs"
open GCLParser
#load "GCLLexer.fs"
open GCLLexer

#load "stringconcat.fs"
open stringconcat

#load "NFAtoDFA.fs"
open NFAtoDFA

#load "InitializeVariables.fs"
open InitializeVariables

#load "Interpreter.fs"
open Interpreter

// We define the evaluation function recursively, by induction on the structure
// of arithmetic expressions (AST of type expr)

let checkIllegalAssignments a =
    match a with
    | Var(b) -> true
    | Array(x,y) -> true
    | _ -> false

//these Two function are used for calculating depth in the semicolon case in the edges function
let rec edgedDepth q0 c q1 n = 
    match c with
    | Assign(var,x)                 -> n 
    | Skip                          -> n
    | SemiColon(c1,c2)              -> edgedDepth q0 c1 (n+1) (n+1)
                                       edgedDepth (n+1) c2 q1 (n+1)
    | If(Gc)                        -> edgedGcDepth q0 Gc q1 (n)
    | Do(Gc)                        -> edgedGcDepth q0 Gc q1 (n+1)
and edgedGcDepth q0 Gc q1 n =
    match Gc with
    | ExecuteIf(b,c)                -> (n+1)
                                       (edgedDepth (n+1) c q1 (n+1))
    | Else(gc2,gc1)                 -> edgedGcDepth q0 gc1 q1 (n)
                                       edgedGcDepth q0 gc2 q1 (n+1)

let rec edges q0 c q1 n (l:(int * SubTypes * int)List) = 
    match c with
    | Assign(var,x) when  (checkIllegalAssignments var)  -> l @ [(q0, SubC(c), q1)]
    | Skip                          -> l @ [(q0, SubC(c), q1)]
    | SemiColon(c1,c2)              -> edges (n+1) c2 q1 ( (edgedDepth q0 c1 (n+1) (n+1))) (edges q0 c1 (n+1) (n+1) (l))
    | If(Gc)                        -> edgesGc q0 Gc q1 (n) l
    | Do(Gc)                        -> edgesDo q0 Gc q1 n l
                                       
and edgesGc q0 Gc q1 n (l:(int * SubTypes * int)List) =
    match Gc with
    | ExecuteIf(b,c)                -> (edges (n+1) c q1 (n+1) (l @ [(q0, SubB(b), (n+1))]))
    | Else(gc1,gc2)                 -> edgesGc q0 gc2 q1 (edgedGcDepth q0 gc1 q1 n) (edgesGc q0 gc1 q1 (n) (l))

and edgesDo q0 Gc q1 n (l:(int * SubTypes * int)List) = 
    match Gc with
    | ExecuteIf(b,c)                -> (edges (n+1) c q0 (n+1) (l @ [(q0, SubB(b), (n+1))] @ [(q0, SubB(NotExpr b), q1)]))
    | Else(gc1,gc2)                 -> edgesDo q0 gc2 q1 (edgedGcDepth q0 gc1 q1 n) (edgesDo q0 gc1 q1 (n) (l))



let toDFA (e:(int * SubTypes * int)List) (D:Boolean) =
    if D = true then convertNFAToDFA e [] [] else e
    
// We
let parse input =
    // translate string into a buffer of characters
    let lexbuf = LexBuffer<char>.FromString input
    // translate the buffer into a stream of tokens and parse them
    let res = GCLParser.start GCLLexer.tokenize lexbuf
    // return the result of parsing (i.e. value of type "expr")
    res



// We implement here the function that interacts with the user
let rec compute n =
    if n = 0 then
        printfn "Bye bye"
    else
        printfn ""
        printf "Enter your GCL program: "
        try
        // We parse the input string
        let e = parse (Console.ReadLine())

        // Get a list of all edges
        let edgeList = edges 0 e 1 1 []
        let edgeList = concatBExpr edgeList []

        printfn ""
        printf "Write \'d\' for DFA or \'n\' for NFA: "
        let DFA = dfaOrnfa (Console.ReadLine())
        let edgeList = toDFA edgeList DFA // Converts to DFA

        // Find all variables
        let varList = findVariables edgeList
        //printfn "%A" varList


        printfn ""
        // Print the program graph (textual)
        printfn "Textual representation of the program graph (see file, \'graph.dot\'):"
        let edgeListString = getStringFromList edgeList ""  
        printfn "%s" edgeListString
        

        // Initialization of Variables and Arrays
        printfn "Initialization of Variables and Arrays:"
        let initVars = InitializationOfVariablesAndArrays varList []
        //printfn "Initialization done:\n%A\n" initVars
        
        // Interpret the program
        printfn ""
        printfn "Interpretting the GCL program:"
        let varList = interpret edgeList edgeList initVars 0

        printfn ""
        printfn "Final variable assignment:"
        printAssignmentList varList
        // Writes the output to a dot file, that can be made into graphical representation using graphviz
        // Get a printable string from the edge list
        
        File.WriteAllText ("graph.dot", "digraph G {\n" + edgeListString + "}")

        compute n
        with err -> compute (n-1)

// Start interacting with the user
compute 3
