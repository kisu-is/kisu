```haskell
ident = r/[a-z_][a-zA-Z0-9_]*/ ;
number = r/[0-9]+(\.[0-9]+)?/ ;
string = r/"([^"\\]|\\.)*"/ ;
bool = "true" | "false" ;
literal = number | string | bool ;

program = struct_def* seq ;

type_ident = r/[A-Z][a-zA-Z0-9_]*/ ;

struct_field = ident ":" type_expr ;
struct_fields = struct_field ("," struct_field)* ;
struct_body = "{" struct_fields? "}" ;
field = ident constraint? ("=" expr)? ;
struct_expr = type_ident "{" (field (";" field)* ";"?)? "}" ;
struct_def = "struct" type_ident struct_body ;

list_type = "[" type_expr "]" ;
lambda_type = "fn" type_expr* "->" type_expr ;

constraint = ":" type_expr ;

type_expr = "(" type_expr ")"
          | type_ident
          | list_type
          | lambda_type ;

expr = ident
     | literal
     | lambda
     | group
     | struct_expr
     | list
     | unary
     | binary
     | app
     | if_expr ;

if_expr = "if" expr "then" expr "else" expr ;

lambda_param = ident constraint? ("=" expr)? ;
lambda = "|" (lambda_param ("," lambda_param)*)? "|" ":" seq ;

decl = "let" ident constraint? "=" expr ;
assign = ident "=" expr ;

stmt = decl
     | assign
     | expr ;

seq = (stmt ";")* expr? ;

group = "(" seq ")" ;

list = "[" expr ("," expr)* "]" ;

app = expr expr ;

binary = expr ("+" | "-" | "*" | "/" | "==" | "!=" | "<" | ">" | "<=" | ">=" | ".") expr ;
unary = ("-" | "!" ) expr ;
```
