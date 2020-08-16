# 2020-06-15

I wrote this compiler in 2019. It translates a dynamically typed functional language to JavaScript.


# 2020-08-16

I am trying to understand the code.
The compiling pass starts from 'compile.rkt', line 29. The first pass is 'parse', which consumes an S-expression and produces an AST (represented as Racket structs).
The next pass 'anf' transform the program into Administrative Normal Form.
The pass 'cps' then transform the ANFed program into continuation-passing style. This pass eliminate all uses of 'call/cc'.
Finally the optimize pass performs constant propagation.