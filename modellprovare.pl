% For SICStus, uncomment the line below: (needed for member/2)
% :- use_module(library(lists)).

% Load model, initial state, and formula from file.
verify(Input) :-
    see(Input),
    read(T), read(L), read(S), read(F),
    seen,
    check(T, L, S, [], F), !.
    
% check(T, L, S, U, F)
%
% Arguments:
% T - System transitions (adjacency lists).
% L - Labeling of states (set of true atomic propositions).
% S - Current state.
% U - Visited states (to avoid infinite loops).
% F - CTL formula to check.
%
% Purpose:
% Evaluates whether the CTL formula `F` is satisfied in state `S` given the model `(T, L)`, considering previously visited states `U` to prevent infinite recursion.
% The sequent `(T, L), S ⊨ F` holds if `F` is true in state `S` under the model `(T, L)`.

% Literals
check(_, L, S, [], X) :-
    member([S, Ls], L),
    member(X, Ls).

% Negation
check(_, L, S, [], neg(X)) :-
    member([S, Ls], L),
    \+ member(X, Ls).

% And
check(T, L, S, [], and(F, G)) :-
    check(T, L, S, [], F),
    check(T, L, S, [], G).

% Or
check(T, L, S, [], or(F, G)) :-
    check(T, L, S, [], F);
    check(T, L, S, [], G).

% Implication
check(T, L, S, [], imp(F, G)) :-
    \+ check(T, L, S, [], F);
    check(T, L, S, [], G).

% AX
check(T, L, S, [], ax(F)) :-
    member([S, Ns], T),
    check_all_states(T, L, Ns, [], F).

% EX
check(T, L, S, [], ex(F)) :-
    member([S, Ns], T),
    check_exist_state(T, L, Ns, [], F).

% AG1: State already visited
check(_, _, S, U, ag(_)) :-
    member(S, U).

% AG2: State not yet visited
check(T, L, S, U, ag(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F),
    member([S, Ns], T),
    check_all_states(T, L, Ns, [S | U], ag(F)).

% EG1: State already visited
check(_, _, S, U, eg(_)) :-
    member(S, U).

% EG2: State not yet visited
check(T, L, S, U, eg(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F),
    member([S, Ns], T),
    check_exist_state(T, L, Ns, [S | U], eg(F)).

% EF1
check(T, L, S, U, ef(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F).

% EF2
check(T, L, S, U, ef(F)) :-
    \+ member(S, U),
    member([S, Ns], T),
    check_exist_state(T, L, Ns, [S | U], ef(F)).

% AF1
check(T, L, S, U, af(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F).

% AF2
check(T, L, S, U, af(F)) :-
    \+ member(S, U),
    member([S, Ns], T),
    check_all_states(T, L, Ns, [S | U], af(F)).

% Helper predicate: check_all_states ensures all states satisfy the formula.
check_all_states(_, _, [], _, _).
check_all_states(T, L, [H | T1], U, F) :-
    check(T, L, H, U, F),
    check_all_states(T, L, T1, U, F).

% Helper predicate: check_exist_state succeeds if any state satisfies the formula.
check_exist_state(_, _, [], _, _) :- fail.
check_exist_state(T, L, [H | T1], U, F) :-
    check(T, L, H, U, F);
    check_exist_state(T, L, T1, U, F).
