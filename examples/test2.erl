
-module(test2).

-compile({parse_transform, macro}).  %% Add this in the parser!!!
-compile(export_all).

-include("cx.erl").


run() ->
    C1 = ^new(1,2),
    C2 = ^new(1,3),
    ^add(C1,C2).
