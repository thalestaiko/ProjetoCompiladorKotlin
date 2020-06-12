module KOTLIN-SYNTAX 
    import DOMAINS

    syntax Pgm ::= "fun main()" "{" Block "}"   

    syntax Skip ::= "Skip"

    syntax Block ::= Stmt                 

    syntax Stmt ::= AExp
                | BExp
                | Stmt Stmt [left]
                | DecVar
                | Skip
                | "if" "(" BExp ")" "{" Block "}" [strict(1)]
                | "if" "(" BExp ")" "{" Block "}" ElseIfStmt [strict(1)]
                | "if" "(" BExp ")" Block "else" Block [strict(1)] //mexemos aqui
                | "while" "(" BExp ")" "{" Block "}"
                | "do" "{" Block "}" "while" "(" BExp ")" //Validar while q foi alterado 
                | Assigner
                | AExpMod
                | Array
                | For
                | Print
              
    syntax Val ::= Int | Bool
    syntax Ids ::= List{Id, ","}


    syntax AExp ::= Int 
                > left: AExp "/" AExp [seqstrict, left]
                > left: AExp "*" AExp [seqstrict, left]
                | Int "+" AExp [seqstrict, left]
                | AExp "-" AExp [seqstrict, left]
                | Id


    syntax CExp ::= Id "+" Id 
        
    syntax BExp ::= Bool
                | AExp ">" AExp [strict]
                | AExp "<" AExp [strict]
                | AExp ">=" AExp [strict]
                | AExp "<=" AExp [strict]
                | AExp "==" AExp [strict]
                | BExp "||" BExp [seqstrict]
                | BExp "&&" BExp [seqstrict]

    syntax DecVar ::= "var" Id ":" Type
                    | "var" Id

    syntax Type ::= "Int" 
                  | "boolean" 
                  | "string"

    syntax AExpMod ::= Id "++"
                
    syntax Assigner ::= DecVar "=" CExp 
                        | Id "=" AExp [strict(2)]
                        | DecVar "=" AExp [strict(2)]
                        | Id "=" BExp [strict(2)]
                        | DecVar "=" BExp [strict(2)]
                        | Id "=" CExp 
                        | DecVar "=" Array
                        | Id "=" Array

    syntax ElseIfStmt ::= "else if" "(" BExp ")" "{" Block "}"
                        | "else" "{" Block "}"
                        | "else if" "(" BExp ")" "{" Block "}" ElseIfStmt
    
    syntax Print ::= "print" "(" Val ")" 
                   | "print" "(" Id ")" 

    syntax ListValues ::= List{Val, ","}
    syntax Array ::= "arrayOf(" ListValues ")"
    syntax For ::= "for" "("  Id "in" Array ")"  "{" Stmt "}"
                    |  "for" "("  Id "in" Id ")"  "{" Stmt "}"



    rule fun main() { B:Block } => B [structural]
    rule S1:Stmt S2:Stmt => S1 ~> S2 [structural]

    rule Skip => .
    
    rule I1:Int + I2:Int => I1 +Int I2
    rule I1:Int - I2:Int => I1 -Int I2
    rule I1:Int * I2:Int => I1 *Int I2
    rule I1:Int / I2:Int => I1 /Int I2
    rule I1:Int < I2:Int => I1 <Int I2
    rule I1:Int > I2:Int => I1 >Int I2
    rule I1:Int <= I2:Int => I1 <=Int I2
    rule I1:Int >= I2:Int => I1 >=Int I2
    rule I1:Int == I2:Int => I1 ==Int I2

    
    rule if (true) { S:Stmt } => S
    rule if ( B:BExp ) { S:Stmt } => S
    rule if (false) { _ } => Skip
    rule if (true) { B } S:ElseIfStmt => B
    rule if (false) { _ } S:ElseIfStmt => S
    rule else if ( B:BExp ) { S1:Stmt } S2:ElseIfStmt => if ( B ) { S1 } S2
    rule else if ( B:BExp ) { S:Stmt } => if ( B ) { S }
    rule else { S } => S

    rule if (true) B:Block else _ => B   //alteração do ternario em kotlin OBSERVACAO
    rule if (false)  _ else B:Block => B //aletação do ternario em kotlin OBSERVACAO

    rule while (B:BExp) { S:Stmt } => if(B){ S while (B) { S } } [structural]

    rule do { S:Stmt } while (B:BExp) => S ~> if(B){ do { S } while (B) } [structural]

    // print do kotlin
    rule <k>print(V:Val) => Skip ... </k>
        <out> P:Set => P SetItem(V) </out>

    rule <k>print(I:Id) => print(V:Val) ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> V ... </store>

    // FOR especifico do kotlin
    rule <k>
            for ( I:Id in arrayOf( (V:Int, Vs:ListValues) ) ) { S:Stmt }
            => S ~> for ( I in  arrayOf( Vs ) ) { S }
            ...
        </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>   

    rule <k>
            for ( I:Id in arrayOf( (V:Int, Vs:ListValues) ) ) { S:Stmt }
            => S ~> for ( I in arrayOf( Vs ) ) { S }
            ...
        </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> V </store>
        <loc> L:Int => L +Int 1 </loc>
        when notBool (I in keys(MEnv)) 

    rule for ( I:Id in arrayOf( .ListValues ) ) { S:Stmt } => Skip //verificar com JOÃO 

    rule <k>
            for ( I:Id in I2:Id ) { S:Stmt }
            => for (  I:Id in V:Array ) { S:Stmt }
            ...
        </k>
        <env> ... I2 |-> L ... </env>
        <store> ... L |-> V ... </store>  

    rule <k> I:Id => V ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> V ... </store>

    rule <k>  var I:Id : Int => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> I:Id = V:AExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    rule <k> var I:Id : Int = V:AExp => Skip ...</k>
        <env> MEnv:Map => MEnv I |-> L </env> 
        <store> MStore:Map => MStore L |-> V</store> 
        <loc> L:Int => L +Int 1</loc> 

    rule <k>I:Id ++ => Skip ...</k>
        <env> ... I |-> L ... </env> 
        <store> ... L |-> (V => V +Int 1) ... </store> 

    rule <k> var I:Id => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> 0 </store>
        <loc> L:Int => L +Int 1 </loc>

    rule <k> var I:Id = V:AExp => Skip ...</k>
        <env> MEnv:Map => MEnv I |-> L </env> 
        <store> MStore:Map => MStore L |-> V</store> 
        <loc> L:Int => L +Int 1</loc> 

    rule <k> var I:Id = V:BExp => Skip ...</k>
        <env> MEnv:Map => MEnv I |-> L </env> 
        <store> MStore:Map => MStore L |-> V</store> 
        <loc> L:Int => L +Int 1</loc>   

    rule <k>var I:Id : boolean = V:BExp => Skip ...</k>
        <env> MEnv:Map => MEnv I |-> L </env> 
        <store> MStore:Map => MStore L |-> V</store> 
        <loc> L:Int => L +Int 1</loc> 

    rule <k> var I:Id : boolean => Skip ... </k>
        <env> MEnv:Map => MEnv I |-> L </env>
        <store> MStore:Map => MStore L |-> false </store>
        <loc> L:Int => L +Int 1 </loc>
    
    rule <k> I:Id = V:BExp => Skip ... </k>
        <env> ... I |-> L ... </env>
        <store> ... L |-> (_ => V) ... </store>

    rule <k> var I:Id = I1:Id + I2:Id => var I = V1 + V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  
    
    rule <k> I:Id = I1:Id + I2:Id =>  I = V1 + V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>   

    rule <k> var I:Id : Int = I1:Id + I2:Id =>  var I : Int = V1 + V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  
    
    rule <k> var I:Id = I1:Id - I2:Id => var I = V1 - V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  
    
    rule <k> I:Id = I1:Id - I2:Id =>  I = V1 - V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>   

    rule <k> var I:Id : Int = I1:Id - I2:Id =>  var I : Int = V1 - V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  

    rule <k> var I:Id = I1:Id * I2:Id => var I = V1 * V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  
    
    rule <k> I:Id = I1:Id * I2:Id =>  I = V1 * V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>   

    rule <k> var I:Id : Int = I1:Id * I2:Id =>  var I : Int = V1 * V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  

    rule <k> var I:Id = I1:Id / I2:Id => var I = V1 / V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  
    
    rule <k> I:Id = I1:Id / I2:Id =>  I = V1 / V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>   

    rule <k> var I:Id : Int = I1:Id / I2:Id =>  var I : Int = V1 / V2 ... </k> 
        <env> 
            ... I1 |-> L1
                I2 |-> L2 ...
        </env>
        <store> 
            ... L1 |-> V1:Int  
                L2 |-> V2:Int ... 
        </store>  
        //ARRAY
                    
        rule <k> var I:Id = A:Array => Skip ... </k>
            <env> MEnv:Map => MEnv I |-> L </env>
            <store> MStore:Map => MStore L |-> A </store>
            <loc> L:Int => L +Int 1 </loc>

        rule <k> var I:Id : T:Type [] = A:Array => Skip ... </k>
            <env> MEnv:Map => MEnv I |-> L </env>
            <store> MStore:Map => MStore L |-> A </store>
            <loc> L:Int => L +Int 1 </loc>

        rule <k> I:Id = A:Array => Skip ... </k>
            <env> ... I |-> L ... </env>
            <store> ... L |-> (_ => A) ... </store>


    configuration <T>
        <k> $PGM:Pgm </k>
        <out> .Set </out>
        <env> .Map </env>
        <store> .Map </store>
        <loc> 1 </loc>
    </T>

endmodule

module KOTLIN
    import DOMAINS
    import KOTLIN-SYNTAX

    syntax KResult ::= Int | Bool
endmodule