```haskell
ident = r/[a-z_][a-zA-Z0-9_]*/ ;
number = r/[0-9]+(\.[0-9]+)?/ ;
string = r/"([^"\\]|\\.)*"/ ;
bool = "true" | "false" ;
literal = number | string | bool ;
key = ident | string;

program = type_def* block ;

type_ident = r/[A-Z][a-zA-Z0-9_]*/ ;
type_def = "struct" type_ident "=" type_expr ;
list_type = "[" type_expr "]" ;
lambda_type = "fn" type_expr* "->" type_expr ;

constraint = ":" type_expr ;

type_expr = type_ident
          | list_type
          | lambda_type ;

expr = ident
     | literal
     | lambda
     | block
     | map
     | list
     | unary
     | binary
     | app
     | if_expr ;

if_expr = "if" expr "then" expr "else" expr ;

lambda_param = key constraint? ("=" expr)? ;
lambda = "|" (lambda_param ("," lambda_param)*)? "|" ":" expr ;

assign = key constraint? "=" expr ";"
       | key constraint? ";" ; // inherit

block = "(" assign* expr ")" ;
map = "{" assign* "}" ;

list = "[" expr ("," expr)* "]" ;

app = expr expr ;

binary = expr ("+" | "-" | "*" | "/" | "==" | "!=" | "<" | ">" | "<=" | ">=" | ".") expr ;
unary = ("-" | "!" ) expr ;
```
