%%% Verifiering av beviset och inläsning

verify(InputFileName) :- 
    see(InputFileName), read(Prems), read(Goal), read(Proof),
    seen,
    check_goal(Goal, Proof),
    valid_proof(Prems, Goal, Proof,[]).
    %write('
%predikatet uppfyllt
%
%').

%%% Kontrollerar om "Goal" (högerled) är lika med sista raden i beviset "Proof"

check_goal(Goal,[ [_ ,X, _] | [] ]):-
  Goal = X.

check_goal(Goal,[ _ |Tail]):-
      check_goal(Goal,Tail).

%%% Kontroll av varje steg

valid_proof(_, _, [], _).

valid_proof(Prems, Goal, [H|T], PrevLines) :-
    check_line(Prems, Goal, H, PrevLines),
    valid_proof(Prems, Goal, T, [H|PrevLines]).




%%%%% Nedan används "Check Line" för att kolla alla bevisregler %%%%%%





%%% Kontrollerar om "premiss" finns i "premisslistan" (i textfil)
check_line(Prems, _, [_, X, premise], _) :-
    member(X, Prems).


%%% Kontrollerar  "And" (både introduction och elimination) 
check_line(_, _, [_, and(X,Y), andint(A,B)], PrevLines) :-
    member([A, X, _], PrevLines),
    member([B, Y, _], PrevLines).

check_line(_, _, [_, X, andel1(A)], PrevLines) :-
	member([A, and(X,_), _], PrevLines).

check_line(_, _, [_, X, andel2(A)], PrevLines) :-
	member([A, and(_, X), _], PrevLines). 	   


%%% Kontrollerar "Implication" (både introduction och elimination)
check_line(_, _, [_, imp(X,Y), impint(A,B)], PrevLines) :-
    member(Lista , PrevLines),
    member([A, X, assumption], Lista),
    member([B, Y, _], Lista).

check_line(_, _, [_, Y, impel(A,B)], PrevLines) :-
	member([A, X, _], PrevLines),
	member([B, imp(X,Y), _], PrevLines).


%%% Kontrollerar "assumption", (eg. öppnar en box)
check_line(Prems, Goal, [[_,_,assumption]|T], PrevLines) :-
    valid_proof(Prems, Goal, T,[[_, _, assumption]|PrevLines]).


%%%%Kontrollerar "or" introduction
check_line(_, _, [_, or(X,_), orint1(A)], PrevLines) :-
	member([A, X, _], PrevLines).   

check_line(_, _, [_, or(_, Y), orint2(A)], PrevLines) :-
	member([A, Y, _], PrevLines).


%%%% Kontrollerar "copy"
check_line(_, _, [_, X, copy(A)], PrevLines) :-
	member([A, X, _], PrevLines).


%%%% Kontrollerar "contradiction-elemination" 
check_line(_, _, [_, _, contel(X)], PrevLines) :-
	member([X, cont, _], PrevLines).


%%%% Kontrollerar "negintroduction" och "negelemination"
check_line(_, _, [_, neg(X), negint(A,B)], PrevLines) :-
	member(Lista , PrevLines),
	member([A, X, assumption], Lista),
	member([B, cont, _], Lista).

check_line(_, _ , [_, cont, negel(A,B)], PrevLines) :-
	member([A, X, _], PrevLines),
	member([B, neg(X), _], PrevLines).


%%%% Kontrollerar "dubbel negint och negel"
check_line(_, _, [_, neg(neg(X)), negnegint(A)], PrevLines) :-
	member([A, X, _], PrevLines).

check_line(_, _, [_, X, negnegel(A)], PrevLines) :-
	member([A, neg(neg(X)), _], PrevLines).	


%%%% Kontrollerar "Modus Tollens" 
check_line(_, _, [_, neg(X), mt(A,B)], PrevLines) :-
	member([A, imp(X,Y), _], PrevLines),
	member([B, neg(Y), _], PrevLines).


%%%% Kontrollerar "PBC"
check_line(_, _, [_, X, pbc(A,B)], PrevLines) :-
	member(Lista , PrevLines),
	member([A, neg(X), assumption], Lista),
	member([B, cont, _], Lista).


%%%% Kontrollerar "LEM"
check_line(_, _, [_ , or(X,neg(X)), lem], _).
