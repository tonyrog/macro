%% TEST-0  simple features

-module(test0).
-compile({parse_transform, macro}).  %% Add this in the parser!!!
-compile(export_all).

^square(A) ->
    `begin T=(&A),(T*T) end.

^plus(X,Y) ->
    `(&X + &Y).

foo(A, B) ->
    ^plus(A,B).

bar(A, B) ->
    `(A + B).

bar2(A, B) ->
    `(&A + &B).


dist({Ax,Ay},{Bx,By}) ->
    math:sqrt(^square(Bx-Ax)+^square(By-Ay)).


