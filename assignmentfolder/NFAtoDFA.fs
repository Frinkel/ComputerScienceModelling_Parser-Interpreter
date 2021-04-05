module NFAtoDFA


let rec convertNFAToDFA (l:(int * SubTypes * int)List) (nl:(int * SubTypes * int)List) (l2:(BExpr * int)List) =
    match l with
    | [] -> nl
    | (q0, c, q1)::tail -> match (c) with 
                              | SubC(x) -> convertNFAToDFA tail (nl @ [(q0, c, q1)]) l2
                              | SubB(x) -> convertNFAToDFA tail (nl @ [(q0, SubB((convertB x l2 q0)), q1)]) [(convertB x l2 q0),q0]
and AndToOR (b:BExpr) (b3:BExpr)= 
    match b3 with
    | ShortAndExpr(b1, NotExpr(b2)) -> (ShortAndExpr(b, NotExpr(ShortOrExpr(b1,b2)))) 
    | AndExpr(b1, NotExpr(b2)) -> (ShortAndExpr(b, NotExpr(ShortOrExpr(b1,b2)))) 
    | _ -> b
and convertB (b:BExpr) (l:(BExpr * int)List) (i:int) =
    match l with
    | (b1,q)::tail when q = i-> (AndToOR b b1)
    | _ -> (ShortAndExpr(b, NotExpr(Bool(false))))



//Used to concatinate Boolean edgdes when working with do expressions
let rec concatBExpr (l:(int * SubTypes * int)List) (nl:(int * SubTypes * int)List) =
    match l with
    | [] -> nl
    | (q0, c, q1)::tail -> match (c) with 
                              | SubC(x) -> concatBExpr tail (nl @ [(q0, c, q1)])
                              | SubB(x) -> concatBExpr tail (intoAnd x q0 q1 nl [])

and intoAnd (b:BExpr) (x:int) (y:int) (l:(int * SubTypes * int)List) (nl:(int * SubTypes * int)List) =
    match l with
    | [] -> nl @ [(x,SubB(b),y)]
    | (q0 , SubB(b1) , q1 )::tail when (x=q0 && y=q1) -> intoAnd (ShortAndExpr(b,b1)) x y tail nl
    | (q0 , c , q1 )::tail -> intoAnd b x y tail (nl @ [(q0, c, q1)])
