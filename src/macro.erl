-module(macro).

-export([parse_transform/2]).

-type form()    :: any().
-type forms()   :: [form()].
-type options() :: [{atom(), any()}].

-spec parse_transform(forms(), options()) -> forms().

-record(s,
	{
	  macros = [],
	  functions = []
	}).

parse_transform(Forms, Options) ->
    %% Split input forms in one macro list and one the rest
    {Macros,Forms1} = 
	lists:partition(fun(T) -> element(1,T) == macro end, Forms),
    {Functions,_Forms2} = 
	lists:partition(fun(T) -> element(1,T) == function end, Forms1),
    S = #s { macros = Macros, functions = Functions },
    %% io:format("Macros=~p\nFunctions=~p\n", [Macros, Functions]),
    {NewForms,_} = 
        parse_trans:depth_first(fun xform_fun/4, S, Forms1, Options),
    %% io:format("NewForms = ~p\n", [NewForms]),
    parse_trans:revert(NewForms).

xform_fun(prefix_expr, Form, _Ctx, S) ->
    Op = erl_syntax:prefix_expr_operator(Form),
    OpName = erl_syntax:operator_name(Op),
    io:format("prefix_expr: op=~p:  ~p\n", [OpName,Form]),
    case OpName of
	'`' ->
	    Expr = erl_syntax:prefix_expr_argument(Form),
	    Expr1 = erl_syntax:revert(Expr),
	    io:format("Expr1= ~p\n", [Expr1]),
	    Form1 = erl_eval:expr_quote(Expr1),
	    io:format("prefix_expr quote: ~p\n", [Form1]),
	    {Form1, S};
	_ ->
	    {Form, S}
    end;
xform_fun(application, Form, _Ctx, S) ->
    App = erl_syntax_lib:analyze_application(Form),
    io:format("App=~p\n", [App]),
    case App of
	{'^macro',App0} ->
	    %% Check if Fun/Arity is a macro call.
	    case find_macro(App0, S#s.macros) of 
		false ->
		    {Form, S};
		{true,Macro} ->
		    Args = erl_syntax:application_arguments(Form),
		    RevArgs = parse_trans:revert(Args),
		    io:format("Expand macro '~s' (~p)\n", 
			      [element(3,Macro), RevArgs]),
		    case eval_macro(Macro, RevArgs, S) of
			{value,Value,[]} ->
			    {Value, S};
			Other ->
			    parse_trans:error(cannot_evaluate,?LINE,
					      [{expr, RevArgs},
					       {error, Other}])
		    end
            end;
        _ ->
            {Form, S}
    end;
xform_fun(_, Form, _Ctx, S) ->
    {Form, S}.

%% Lookup a macro
find_macro({Name,Arity},[M={macro,_,Name,Arity,_Clauses}|_]) ->
    {true,M};
find_macro(App, [_|Ms]) ->
    find_macro(App, Ms);
find_macro(_App, []) ->
    false.

%% Lookup a macro
find_function({Name,Arity},[F={function,_,Name,Arity,_Clauses}|_]) ->
    {true,F};
find_function(App, [_|Fs]) ->
    find_function(App, Fs);
find_function(_App, []) ->
    false.

eval_macro({macro,_,Name,Arity,Cs}, Args, S) ->
    Lf = {value, fun(F,As) -> eval_local(F,As,S) end},
    case erl_eval:match_clause(Cs, Args, [], Lf) of
	{Body, Bs} ->
	    io:format("Macro body = ~p, Bindings=~p\n", [Body, Bs]),
	    {value,Expr,_Bs1} = erl_eval:exprs(Body, Bs, Lf),
	    io:format("Expr=~p\n", [Expr]),
	    %% handle straigt values and make them abstract.
	    %% FIXME: Handle handle values looking like parse forms? how?
	    try erl_eval:make_constant(0, Expr) of
		Const -> {value,Const,[]}
	    catch
		error:_ ->
		    {value, Expr, []}
	    end;
	 nomatch ->
	    erlang:raise(error, {function_clause,{Name,Arity}})
    end.

eval_function({function,_,Name,Arity,Cs}, Args, S) ->
    Lf = {value, fun(F,As) -> eval_local(F,As,S) end},
    case erl_eval:match_clause(Cs, Args, [], Lf) of
	{Body, Bs} ->
	    io:format("Function body = ~p, Bindings=~p\n", [Body, Bs]),
	    {value,Res,_} = erl_eval:exprs(Body, Bs, Lf),
	    io:format("Result = ~w\n", [Res]),
	    Res;
	 nomatch ->
	    erlang:raise(error, {function_clause,{Name,Arity}})
    end.
    
eval_local({macro,Func}, As, S) ->
    Arity = length(As),
    case find_macro({Func,Arity}, S#s.macros) of 
	false ->
	    erlang:raise(error, {undef,{Func,Arity}});
	{true, Macro} ->
	    eval_macro(Macro, As, S)
    end;
eval_local(Func, As, S) ->
    Arity = length(As),
    case find_function({Func,Arity},S#s.functions) of
	false ->
	    erlang:raise(error, {undef,{Func,Arity}});
	{true,Function} ->
	    eval_function(Function, As, S)
    end.
