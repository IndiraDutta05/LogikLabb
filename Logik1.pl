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

% Uppgift 1
/*1. Vilka bindningar presenteras som resultat?
Output: 
T = f(a, a, b),
Y = X, X = a,
Z = b.
Here we unify two terms: T = f(a, Y, Z) and T = f(X, X, b) 
The first argument in both terms is a and X, so X = a, 
The second argument in both terms is Y and X.
Since we know from the previous step that X = a, 
this forces Y = a, The third argument in both terms is Z and b. 
Thus, Z = b.
*/

% Uppgift 2

% Entry point for removing duplicates
remove_duplicates(List, Result) :-
    remove_duplicates(List, [], Accumulator),
    reverse(Accumulator, Result).  % element is added to the front of the accumulator. This means that the first element found is thelast to be added, leading to a reversed order.

% Base case: When the input list is empty, the result is the accumulator.
remove_duplicates([], Accumulator, Accumulator).

% If the head is not in the accumulator, add it.
remove_duplicates([H|T], Accumulator, Result) :-
    \+ member(H, Accumulator),
    remove_duplicates(T, [H|Accumulator], Result).  % If H is not in the accumulator, it is added to the front of the accumulator , and the predicate recursively processes the tail.

% If the head is already in the accumulator, skip it.
remove_duplicates([H|T], Accumulator, Result) :-
    member(H, Accumulator),
    remove_duplicates(T, Accumulator, Result).

/*
2. Definiera alltså predikatet remove_duplicates/2! 
Förklara varför man kan kalla detta predikat för en funktion!

In Prolog, a predicate like remove_duplicates/2 
can be seen as a function because:
It takes an input list (List) and produces an output (Result), 
transforming the data in a predictable and consistent way.
In functional terms, it maps an input to an output without side effects 
(i.e., it doesn't change anything outside of the relation between List and Result).

*/


% Uppgift 3 

partstring(X, L, F) :-
    append([_, F, _], X),
    length(F, L),
    F \= [].


% Uppgift 4:
% Representation av en graf.
node(a).
node(b).
node(c).
node(d).
node(e).
node(f).

edge(a, b).
edge(a, d).
edge(a, f).
edge(b, a).
edge(b, c).
edge(b, e).
edge(c, b).
edge(c, d).
edge(d, a).
edge(d, c).
edge(d, e).
edge(e, b).
edge(e, d).
edge(e, f).
edge(f, a).
edge(f, e).

% Hitta alla moljiga paths.

path(A, B, List) :- walk(A, B, [], List).

walk(A, B, V, [A,B]) :- 
    edge(A, B),
    \+member(A,V).

walk(A, B, V, [A|List]) :- 
    \+ A=B,
    \+member(A, V), 
    edge(A, X),
    walk(X, B, [A|V], List).
