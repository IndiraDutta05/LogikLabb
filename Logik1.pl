append([],L,L).
append([H|T],L,[H|R]) :- append(T,L,R).

appendEl(X, [], [X]).
appendEl(X, [H | T], [H | Y]) :-
appendEl(X, T, Y).

length([],0).
length([_|T],N) :- length(T,N1), N is N1+1.

nth(N,L,E) :- nth(1,N,L,E).
nth(N,N,[H|_],H).
nth(K,N,[_|T],H) :- K1 is K+1, nth(K1,N,T,H).

subset([], []).
subset([H|T], [H|R]) :- subset(T, R).
subset([_|T], R) :- subset(T, R).

select(X,[X|T],T).
select(X,[Y|T],[Y|R]) :- select(X,T,R).

member(X,L) :- select(X,L,_).
memberchk(X,L) :- select(X,L,_), !.



% Basfall: tom lista blir tom lista.
remove_duplicates([], []).

% Om huvudet (H) finns i svansen (T), ignorera det och fortsätt.
remove_duplicates([H|T], E) :- 
    member(H, T), 
    !,       
    remove_duplicates(T, E).

% Om huvudet (H) inte finns i svansen (T), lägg till det i resultatet.
remove_duplicates([H|T], [H|E]) :-  
    remove_duplicates(T, E).



