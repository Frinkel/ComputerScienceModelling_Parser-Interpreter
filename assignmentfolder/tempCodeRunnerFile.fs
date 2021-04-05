 
    | Num(x)            ->  x:string
    | TimesExpr(x,y)    ->  (printerA x) + "*" + (printerA y)
    | DivExpr(x,y)      ->  (printerA x) + "/" + (printerA y)
    | PlusExpr(x,y)     ->  (printerA x) + "+" + (printerA y) 
    | MinusExpr(x,y)    ->  (printerA x) + "-" + (printerA y)
    | PowExpr(x,y)      ->  (printerA x) + "^" + (printerA y)
    | UPlusExpr(x)      ->  (printerA x)
    | UMinusExpr(x)     ->  "-" + (printerA x)