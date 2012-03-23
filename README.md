
Erlang compile time macros
==========================

The Erlang enivironment is in need for a powerful macro system
in order to meet the demand on code generation and simplify the
process of writing generic code.

To achive this the following primitivs are introduced:

Backqouting:

    `<expr> 

The compiler will parse the expression and return the
the abstract form of Expr. Example.

    `1 => {integer,0,1}

An other example:

    foo(X, Y) -> `(X + Y).

Returns

    {op,L,'+',{var,L,'X'},{var,L,'Y'}}.

Where L is the linenumber used.

    &<expe>

Partial eval operator. Reduce the expression by 
applying partial evaluation as much as possible without
breaking the semantics of Erlang.

In a macro &X means replace X with the binding of X.

    &`1       => {integer,1,1}
    `(1+2)    => {op,1,'+',{integer,1,1},{integer,1,2}}
    &`(1+2)   => 3
    `&(1+2+X) => {op,1,'+',{integer,1,3},{var,1,'X'}}


Compile time functions
======================

Macros are like functions and will evaluate as functions, the return
value MUST however be a compilable form.

    ^plus(X,Y) ->
        `(&X + &Y).

    %% Expansion test
    bar(A,B) ->
        ^plus(A+1, 2+B).

    bar(A,B) ->
        (A+1) + (2+B).

plus
    X={op,'+',{var,'A'},{integer,1}}
    Y={op,'+',{integer,2},{var,'B'}}

return the expression:
    {op,'+',{op,'+',{var,'A'},{integer,1}},
             {op,'+',{integer,2},{var,'B'}}}

    ^bar(List) ->
        `(&List).

    ^ite(Cond,Then,Else) ->
        `case &Cond of
         true -> &Then;
         false -> &Else
     end.

    ^may_cons(H, T) ->
      `if &H == undefined -> &T;
          true -> [&H|&T]
       end.

Planned but not yet working:

    ^struct(X) ->
       case X of
       `if &H -> &B1 end -> {H,B1};
       `case &Expr of &Cases end -> {Expr, Cases};
       `(&A + &B) -> {A,B};
       _ -> `false
     end.

Function prototypes, using & to generate instantiated functions.

    map(F, [H|T]) ->
      [F(H) | map(F,T)];
    map(_F, []) ->
      [].

    bar(X, List) ->
      <map>(fun(Y) -> Y+X end, List)

    1. uniq function

    map_12345(F, [H|T]) ->
      [F(H) | map_12345(F,T)];
    map_12345(_F, []) ->
      [].

2a. substitue literal arguments

    map_12345(F, Y, [H|T]) ->
      [(fun(Y)->Y+X end)(H) | map_12345(F,Y,T)];
    map_12345(_F, _Y, []) ->
      [].

2b. partial evaluate.

    map_12345(F, Y, [H|T]) ->
      [H+X  | map_12345(F,Y,T)];
    map_12345(_F, _Y, []) ->
      [].

2c. remove substituted arguments

    map_12345(Y, [H|T]) ->
      [H+X  | map_12345(Y,T)];
    map_12345(_Y, []) ->
      [].

Other example:

    fold(F, A, [H|T]) ->
      fold(F, F(H,A), T);
    fold(_F, A, []) ->
      A.

    test(N,List) ->
      %%  <fold>(fun(X,A) -> A+N end, 1, List)
      fold_123(N, 1, List).

    fold_123(N, A, [_|T]) ->
      fold_123(N, A+N, T);
    fold_123(_N, A, []) ->
      N.


   
