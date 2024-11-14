verify(InputFileName) :- see(InputFileName),
        read(Prems), read(Goal), read(Proof),
        seen,
        valid_proof(Prems, Goal, Proof).

% Check if last element in Proof is Goal and iterates through the proof and checks for validity.


valid_proof(Prems, Goal, Proof) :-
        last(Proof, [_, Goal, _]),
        check_proof(Prems, Proof, []),
        !.

% If the list of rows to validate is the empty list, we are done.
check_proof(_, [], _). 

% Check if the given proof is valid
check_proof(Prems, [ToProcess|ToBeProcessed], Processed) :-
        validate_line(Prems, ToProcess, Processed),
        append(Processed, [ToProcess], Concat),
        check_proof(Prems, ToBeProcessed, Concat).

% Checks box
check_box(FirstLine, LastLine, Processed) :-
        member([FirstLine|T], Processed),
        last(T, LastLine).

check_box(Line, Line, Processed) :-
        member([Line], Processed).

% Handles premise
validate_line(Prems, [_, Sats, premise], _) :-
        member(Sats, Prems).

% Handles assumption. Case when assumption gives box.
validate_line(Prems, [[_, _, assumption]|BoxTail], Processed) :-
        append(Processed, [[_, _, assumption]], Concat),
        check_proof(Prems, BoxTail, Concat).

% Handles copy.
validate_line(_, [_, A, copy(X)], Processed) :-
        member([X, A, _], Processed).

% Handles andint.
validate_line(_, [_, and(A, B), andint(X,Y)], Processed) :-
        member([X, A, _], Processed),
        member([Y, B, _], Processed).

% Handles andel1(X).
validate_line(_, [_, A, andel1(X)], Processed) :-
        member([X, and(A, _), _], Processed).

% Handles andel2(X).
validate_line(_, [_, B, andel2(X)], Processed) :-
        member([X, and(_, B), _], Processed).

% Handles orint1(X).
validate_line(_, [_, or(A, _), orint1(X)], Processed) :-
        member([X, A, _], Processed).

% Handles orint2(X).
validate_line(_, [_, or(_, B), orint2(X)], Processed) :-
        member([X, B, _], Processed).

% Handles orel(X, Y, U, V, W).
validate_line(_, [_, A, orel(X, Y, U, V, W)], Processed) :-
        member([X, or(B, D), _], Processed),
        check_box([Y, B, assumption], [U, A, _], Processed),
        check_box([V, D, assumption], [W, A, _], Processed).

% Handles impel(X, Y).
validate_line(_, [_, B, impel(X, Y)], Processed) :-
        member([X, A, _], Processed),
        member([Y, imp(A, B), _], Processed).

% Handles negint(X, Y).
validate_line(_, [_, neg(Z), negint(X, Y)], Processed) :-
        check_box([X, Z, assumption], [Y, cont, _], Processed).

% Handles negel(X, Y).
validate_line(_, [_, cont, negel(X, Y)], Processed) :-
        member([X, A, _], Processed),
        member([Y, neg(A), _], Processed).

% Handles contel(X).
validate_line(_, [_, _, contel(X)], Processed) :-
        member([X, cont, _], Processed).

% Handles negnegint(X).
validate_line(_, [_, neg(neg(Sats)), negnegint(X)], Processed) :-
        member([X, Sats, _], Processed).

% Handles negnegel(X).
validate_line(_, [_, Sats, negnegel(X)], Processed) :-
        member([X, neg(neg(Sats)), _], Processed).

% Handles mt
validate_line(_, [_, _, mt(X, Y)], Processed) :-
        member([X, imp(_, B), _], Processed),
        member([Y, neg(B), _], Processed).

% Handles pbc(X, Y).
validate_line(_, [_, A, pbc(X, Y)], Processed) :-
        check_box([X, neg(A), assumption], [Y, cont, _], Processed).

% Handles impint. 
validate_line(_, [_, imp(R,Q), impint(X,Y)], Processed) :-
        check_box([X, R, assumption], [Y, Q, _], Processed).

% Handles lem.
validate_line(_, [_, or(A, neg(A)), lem], _).
