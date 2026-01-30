```js
ident = r/[a-zA-Z_][a-zA-Z0-9_]*/ ;
number = r/[0-9]+(\.[0-9]+)?/ ;
string = r/"([^"\\]|\\.)*"/ ;

literal = number | string ;
bind = ident "=" expr ";" ;

program = expr ;

expr = ident
     | "(" expr ")"
     | literal
     | lambda
     | named_lambda
     | blockexpr
     | map
     | unary
     | binary
     | app ;

binary = expr ("+" | "-" | "*" | "/" | "==" | "!=" | "<" | ">" | "<=" | ">=") expr ;
unary = ("-" | "!" ) expr ;

lambda = ident ":" expr ;
named_lambda = "{" ident ("," ident)* "}" ":" expr ;

app = expr expr ;

block = "{" block_expr | map "}" ;
block_expr = bind* expr ;
map = bind* ;

```
