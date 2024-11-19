% Main Predicate
verify(InputFileName) :-
    see(InputFileName),
    read(Premises), read(Goal), read(Proof),
    seen,
    validate_proof(Premises, Goal, Proof, []).

% If no unvalidated lines remain and the last validated line matches the goal.
validate_proof(_Premises, Goal, [], [[_LineNumber, Goal, _Rule] | _Validated]).

% The first line is a box starting with an assumption.
validate_proof(Premises, Goal, [[[LineNumber, Result, assumption] | BoxTail] | ProofTail], Validated) :-
    check_box(Premises, Goal, BoxTail, [[LineNumber, Result, assumption] | Validated]),
    validate_proof(Premises, Goal, ProofTail, [[[LineNumber, Result, assumption] | BoxTail] | Validated]).

% The first line is derived from applying a rule to previously validated lines.
validate_proof(Premises, Goal, [ProofHead | ProofTail], Validated) :-
    validate_rule(Premises, ProofHead, Validated),
    validate_proof(Premises, Goal, ProofTail, [ProofHead | Validated]).

% Rules for Validation
% premise
validate_rule(Premises, [_LineNumber, Result, premise], _Validated) :-
    member(Result, Premises).

% Treating imp as a premise  NEWWWW
validate_rule(Premises, [_LineNumber, imp(Antecedent, Result), premise], _Validated) :-
    member(imp(Antecedent, Result), Premises).

% Double negation elimination: negnegel(X)
validate_rule(_Premises, [_LineNumber, Result, negnegel(X)], Validated) :-
    member([X, neg(neg(Result)), _], Validated).

% Implication elimination: impel(X, Y)
validate_rule(_Premises, [_LineNumber, Result, impel(X, Y)], Validated) :-
    member([X, Antecedent, _], Validated),
    member([Y, imp(Antecedent, Result), _], Validated).

% Copy: copy(X)
validate_rule(_Premises, [_LineNumber, Result, copy(X)], Validated) :-
    member([X, Result, _], Validated).
	

% Conjunction introduction: andint(X, Y)
validate_rule(_Premises, [_LineNumber, and(Left, Right), andint(X, Y)], Validated) :-
    member([X, Left, _], Validated),
    member([Y, Right, _], Validated).

% Conjunction elimination 1: andel1(X)
validate_rule(_Premises, [_LineNumber, Result, andel1(X)], Validated) :-
    member([X, and(Result, _), _], Validated).

% Conjunction elimination 2: andel2(X)
validate_rule(_Premises, [_LineNumber, Result, andel2(X)], Validated) :-
    member([X, and(_, Result), _], Validated).

% Contradiction elimination: contel(X)
validate_rule(_Premises, [_LineNumber, _Result, contel(X)], Validated) :-
    member([X, cont, _], Validated).

% Double negation introduction: negnegint(X)
validate_rule(_Premises, [_LineNumber, neg(neg(Result)), negnegint(X)], Validated) :-
    member([X, Result, _], Validated).

% Disjunction introduction 1: orint1(X)
validate_rule(_Premises, [_LineNumber, or(Result, _), orint1(X)], Validated) :-
    member([X, Result, _], Validated).

% Disjunction introduction 2: orint2(X)
validate_rule(_Premises, [_LineNumber, or(_, Result), orint2(X)], Validated) :-
    member([X, Result, _], Validated).

% Law of excluded middle: lem
validate_rule(_Premises, [_LineNumber, or(X, neg(X)), lem], _Validated).

% Negation elimination: negel(X, Y)
validate_rule(_Premises, [_LineNumber, cont, negel(X, Y)], Validated) :-
    member([X, Proposition, _], Validated),
    member([Y, neg(Proposition), _], Validated).

% Modus tollens: mt(X, Y)
validate_rule(_Premises, [_LineNumber, neg(Result), mt(X, Y)], Validated) :-
    member([X, imp(Result, Other), _], Validated),
    member([Y, neg(Other), _], Validated).

% Negation introduction: negint(X, Y)
validate_rule(_Premises, [_LineNumber, neg(Result), negint(X, Y)], Validated) :-
    find_box(X, Validated, Box),
    member([X, Result, assumption], Box),
    member([Y, cont, _], Box).

% Proof by contradiction: pbc(X, Y)
validate_rule(_Premises, [_LineNumber, Result, pbc(X, Y)], Validated) :-
    find_box(X, Validated, Box),
    member([X, neg(Result), assumption], Box),
    member([Y, cont, _], Box).

% Implication introduction: impint(X, Y)
validate_rule(Premises, [_LineNumber, imp(Antecedent, Result), impint(X, Y)], Validated) :-
    % Ensure imp(Antecedent, Result) is not already a premise
    \+ member(imp(Antecedent, Result), Premises),

    % Find the box corresponding to the assumption of Antecedent
    find_box(X, Validated, Box),

    % Ensure the box starts with the antecedent as an assumption
    member([X, Antecedent, assumption], Box),

    % Ensure the consequent is derived logically in the box
    member([Y, Result, _], Box),

    % Ensure no redundant copies of the antecedent
    \+ (member([_, Antecedent, copy(_)], Box), \+ member(Antecedent, Premises)).


% Disjunction elimination: orel(X, Y, U, V, W)
validate_rule(_Premises, [_LineNumber, Result, orel(X, Y, U, V, W)], Validated) :-
    find_box(Y, Validated, FirstBox),
    find_box(V, Validated, SecondBox),
    member([X, or(Left, Right), _], Validated),
    member([Y, Left, _], FirstBox),
    member([U, Result, _], FirstBox),
    member([V, Right, _], SecondBox),
    member([W, Result, _], SecondBox).

% Handling Boxes
% A box is valid if all its lines are validated.
check_box(_Premises, _Goal, [], _Validated).

% The first line of the box is another box.
check_box(Premises, Goal, [[[LineNumber, Result, assumption] | BoxTail] | ProofTail], Validated) :-
    check_box(Premises, Goal, BoxTail, [[LineNumber, Result, assumption] | Validated]),
    check_box(Premises, Goal, ProofTail, [[[LineNumber, Result, assumption] | BoxTail] | Validated]).

% The first line is a result derived from a rule.
check_box(Premises, Goal, [ProofHead | ProofTail], Validated) :-
    validate_rule(Premises, ProofHead, Validated),
    check_box(Premises, Goal, ProofTail, [ProofHead | Validated]).

% Find a box containing a specific line.
find_box(TargetLine, [BoxHead | _], BoxHead) :-
    member([TargetLine, _, _], BoxHead).

% If not found, search the rest of the validated list.
find_box(TargetLine, [_ | Rest], Box) :-
    find_box(TargetLine, Rest, Box).
