%%% @author Tony Rogvall <tony@rogvall.se>
%%% @copyright (C) 2010, Tony Rogvall
%%% @doc
%%%  Test the backqoute syntax
%%% @end
%%% Created :  3 May 2010 by Tony Rogvall <tony@rogvall.se>

-module(test).
-compile({parse_transform, macro}).  %% Add this in the parser!!!
-compile(export_all).

^plus(X,Y) ->
    `(&X + &Y).

^ite(Cond,Then,Else) ->
    `case &Cond of
	 true -> &Then;
	 false -> &Else
     end.

my_fac(0) -> 1;
my_fac(1) -> 1;
my_fac(I) -> 
    io:format("I=~p\n", [I]),
    I*my_fac(I-1).

^fac(N) ->
    io:format("N=~p\n", [N]),
    my_fac(&N).

^cat(H, T) ->
    `[&H|&T].

foo(1, 2) ->
    ^plus(1,2).

bar(X,Y,Z,T) ->
    ^ite(X < Y, Z+T, Z-T).

bar() ->
    ^cat($A, "BC").

baz() ->
    ^fac(10).
