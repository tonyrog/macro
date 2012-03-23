%%
%% Complex implemented with macros
%%

^new(R,I) ->
    `[&R|&I].

^real(A) -> `hd(&A).

^imag([_|I]) -> `tl(&A).

^add(A, B) ->
    `begin
	 [A1|B1] = &A,
	 [A2|B2] = &B,
	 [A1+A2|B1+B2]
     end.

