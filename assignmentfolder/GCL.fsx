    // This script implements our interactive calculator

    // For writing to file
    open System
    open System.IO
    open System.Text.RegularExpressions

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

    #load "SignAnalyzer.fs"
    open SignAnalyzer

    #load "SecurityAnalyzer.fs"
    open SecurityAnalyzer

    #load "MethodChecker.fs"
    open MethodChecker
    

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


    // Determine analysis variation
    // From: https://stackoverflow.com/questions/53818476/f-match-many-regex
    let (|Regex|_|) pattern input =
        let m = Regex.Match(input, pattern)
        if m.Success then Some(List.tail [ for g in m.Groups -> g.Value ])
        else None

    let analysisType c = 
        match c with
        | Regex @"(^step)" [ chr ] -> printfn "Step-wise execution chosen."
                                      0
        | Regex @"(^sig)" [ chr ] ->  printfn "Sign analyzer chosen."
                                      1
        | Regex @"(^sec)" [ chr ] ->  printfn "Security analyzer chosen."
                                      2
        | Regex @"(^met)" [ chr ] ->  printfn "Method checker chosen."
                                      3                                
        | _                     ->    printfn "Error: Please write either \'step\', \'sig\', \'sec\' or \'met\'."
                                      failwith "Neither chosen"


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
            try
            printfn("Choose your environment, \'step\' for step-wise, \'sig\' for sign analyzer, \'sec\' security analyzer or \'met\' for method checker.")
            let environment = analysisType(Console.ReadLine())

            // We parse the input string
            printfn ""
            printf "Enter your GCL program: "
            let e = parse (Console.ReadLine())

            // Get a list of all edges
            let edgeList = edges 0 e 1 1 []
            let edgeList = concatBExpr edgeList []
            

            // ***********
            if environment <> 2 then
                printfn ""
                printf "Write \'d\' for DFA or \'n\' for NFA: "
                let DFA = dfaOrnfa (Console.ReadLine())
                let edgeList = toDFA edgeList DFA // Converts to DFA
                printfn "reached"
            

            printfn ""
            // Print the program graph (textual)
            printfn "Textual representation of the program graph (see file, \'graph.dot\'):"
            let edgeListString = getStringFromList edgeList ""  
            printfn "%s" edgeListString

            
            // Find all variables
            let varList = findVariables edgeList
            //printfn "%A" varList

            printfn "TEST %A" edgeList
            // printfn "TEST %A" varList

            if environment = 2 then // Security analysis
                
                printfn "Specify security lattice."
                let lattice = securityLatticeChecker (Console.ReadLine())

                printfn ""
                printfn "Specify security classifications:"
                let initSecurityVars = InitializationOfSecurity varList []
                let securityLattice = (securityLatticeInitializer lattice)
                checkLatticeAgainstVars securityLattice initSecurityVars
                printfn ""

                printf "Actual flow: "
                let actualFlow = removeDuplicates (produceActualFlows (reverseList (removeInvalid edgeList [])) [] 0) []
                // printfn "TEST %A" actualFlow
                prettySecurityPrint actualFlow 

                printf "Allowed flow: "
                let allowedFlow = produceAllowedFlowList (securityLatticeInitializer lattice) initSecurityVars initSecurityVars []
                // printfn "TEST %A" allowedFlow
                prettySecurityPrint allowedFlow
                
                
                let violatingFlow = produceViolationFlow actualFlow allowedFlow []
                if violatingFlow <> [] then 
                    printf "Violating flow: "
                    // printfn "TEST %A" violatingFlow
                    prettySecurityPrint violatingFlow
                    printfn "Not secure"
                else 
                    printfn "Violating flow: none"
                    printfn "Secure"
                printfn ""

                

            elif environment = 0 then // Step-wise execution

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
               
            elif environment = 1 then
                let aExprList = findVariables edgeList

                // printfn ""
                // printfn "Final variable assignment:"
                // printAssignmentList varList
                // Writes the output to a dot file, that can be made into graphical representation using graphviz
                // Get a printable string from the edge list
                printfn "Initialization of sign values for Variables and Arrays:"
                let varListSign =  (initializeSigns edgeList (initializeSignVars aExprList []) [] aExprList)
                // printfn "%A" varListSign

                // let varListSign2 = updateNode varListSign varListSign 0 1 (Var("a")) Zero []
                // printfn "2 %A" varListSign2

                // let varListSign = signAnalysis edgeList edgeList varListSign 0
                let workList = prepareWorkList edgeList varListSign []
                // printfn "%A" workList
                // printfn " "
                // printfn "%A" workList
            
                let varListSign = signAnalysis workList workList varListSign 1
                //printfn "%A" varListSign

                prettySignPrinter varListSign
            

            elif environment = 3 then
                printfn ""
                printfn "Method checker is currently not working"
                printfn ""


            
            // Writes the output to a dot file, that can be made into graphical representation using graphviz
            // Get a printable string from the edge list

            File.WriteAllText ("assignmentfolder/graph.dot", "digraph G {\n" + edgeListString + "}")

            compute 3
            with err -> compute (n-1)

    // Start interacting with the user
    compute 3

