% Main Predicate
% verify/1 reads premises, goal, and proof from an input file, and validates the proof.
verify(InputFileName) :-
    see(InputFileName), % Open the input file for reading.
    read(Premises), read(Goal), read(Proof), % Read premises, goal, and proof from the file.
    seen, % Close the file.
    validate_proof(Premises, Goal, Proof). % Validate the proof against the premises and goal.

% Proof Validation
% validate_proof/3 validates the proof using an auxiliary predicate that maintains a list of validated lines.
validate_proof(Premises, Goal, Proof) :-
    validate_proof(Premises, Goal, Proof, []). % Start with an empty list of validated lines.

% Base case: proof is valid if all lines are validated and the last validated line matches the goal.
validate_proof(_Premises, Goal, [], [[_LineNumber, Goal, _Rule] | _Validated]).

% Case 1: The first line of the proof starts a box with an assumption.
validate_proof(Premises, Goal, [[[LineNumber, Result, assumption] | BoxTail] | ProofTail], Validated) :-
    % Validate the lines within the box.
    validate_box(Premises, Goal, BoxTail, [[LineNumber, Result, assumption] | Validated]),
    % Continue validating the rest of the proof.
    validate_proof(Premises, Goal, ProofTail, [[[LineNumber, Result, assumption] | BoxTail] | Validated]).

% Case 2: The first line is derived from applying a rule to previously validated lines.
validate_proof(Premises, Goal, [ProofHead | ProofTail], Validated) :-
    validate_rule(Premises, ProofHead, Validated), % Validate the rule used.
    validate_proof(Premises, Goal, ProofTail, [ProofHead | Validated]). % Continue validating.

% Rules for Validation
% premise: A result is valid if it is a premise.
validate_rule(Premises, [_LineNumber, Result, premise], _Validated) :-
    member(Result, Premises).

% premise: Treating an implication as a premise.
validate_rule(Premises, [_LineNumber, imp(Antecedent, Result), premise], _Validated) :-
    member(imp(Antecedent, Result), Premises).

% negnegel: Double negation elimination.
validate_rule(_Premises, [_LineNumber, Result, negnegel(X)], Validated) :-
    member([X, neg(neg(Result)), _], Validated).

% impel: Implication elimination.
validate_rule(_Premises, [_LineNumber, Result, impel(X, Y)], Validated) :-
    member([X, Antecedent, _], Validated),
    member([Y, imp(Antecedent, Result), _], Validated).

% copy: Copy a previously validated result.
validate_rule(_Premises, [_LineNumber, Result, copy(X)], Validated) :-
    member([X, Result, _], Validated).

% andint: Conjunction introduction.
validate_rule(_Premises, [_LineNumber, and(Left, Right), andint(X, Y)], Validated) :-
    member([X, Left, _], Validated),
    member([Y, Right, _], Validated).

% andel1: Conjunction elimination (left component).
validate_rule(_Premises, [_LineNumber, Result, andel1(X)], Validated) :-
    member([X, and(Result, _), _], Validated).

% andel2: Conjunction elimination (right component).
validate_rule(_Premises, [_LineNumber, Result, andel2(X)], Validated) :-
    member([X, and(_, Result), _], Validated).

% contel: Contradiction elimination.
validate_rule(_Premises, [_LineNumber, _Result, contel(X)], Validated) :-
    member([X, cont, _], Validated).

% negnegint: Double negation introduction.
validate_rule(_Premises, [_LineNumber, neg(neg(Result)), negnegint(X)], Validated) :-
    member([X, Result, _], Validated).

% orint1: Disjunction introduction (left component).
validate_rule(_Premises, [_LineNumber, or(Result, _), orint1(X)], Validated) :-
    member([X, Result, _], Validated).

% orint2: Disjunction introduction (right component).
validate_rule(_Premises, [_LineNumber, or(_, Result), orint2(X)], Validated) :-
    member([X, Result, _], Validated).

% lem: Law of excluded middle.
validate_rule(_Premises, [_LineNumber, or(X, neg(X)), lem], _Validated).

% negel: Negation elimination.
validate_rule(_Premises, [_LineNumber, cont, negel(X, Y)], Validated) :-
    member([X, Proposition, _], Validated),
    member([Y, neg(Proposition), _], Validated).

% mt: Modus tollens.
validate_rule(_Premises, [_LineNumber, neg(Result), mt(X, Y)], Validated) :-
    member([X, imp(Result, Other), _], Validated),
    member([Y, neg(Other), _], Validated).

% negint: Negation introduction.
validate_rule(_Premises, [_LineNumber, neg(Result), negint(X, Y)], Validated) :-
    find_box(X, Validated, Box),
    member([X, Result, assumption], Box),
    member([Y, cont, _], Box).

% pbc: Proof by contradiction.
validate_rule(_Premises, [_LineNumber, Result, pbc(X, Y)], Validated) :-
    find_box(X, Validated, Box),
    member([X, neg(Result), assumption], Box),
    member([Y, cont, _], Box).

% impint: Implication introduction.
validate_rule(Premises, [_LineNumber, imp(Antecedent, Result), impint(X, Y)], Validated) :-
    \+ member(imp(Antecedent, Result), Premises), % Ensure not already a premise.
    find_box(X, Validated, Box), % Locate the assumption box.
    member([X, Antecedent, assumption], Box), % Verify the assumption.
    member([Y, Result, _], Box), % Verify the conclusion.
    \+ (member([_, Antecedent, copy(_)], Box), \+ member(Antecedent, Premises)). % Avoid redundant assumptions.

% orel: Disjunction elimination.
validate_rule(_Premises, [_LineNumber, Result, orel(X, Y, U, V, W)], Validated) :-
    find_box(Y, Validated, FirstBox), % Validate first box.
    find_box(V, Validated, SecondBox), % Validate second box.
    member([X, or(Left, Right), _], Validated),
    member([Y, Left, _], FirstBox),
    member([U, Result, _], FirstBox),
    member([V, Right, _], SecondBox),
    member([W, Result, _], SecondBox).

% Handling Boxes
% A box is valid if all its lines are validated.
validate_box(_Premises, _Goal, [], _Validated).

% Case 1: The first line of the box starts another nested box.
validate_box(Premises, Goal, [[[LineNumber, Result, assumption] | BoxTail] | ProofTail], Validated) :-
    validate_box(Premises, Goal, BoxTail, [[LineNumber, Result, assumption] | Validated]),
    validate_box(Premises, Goal, ProofTail, [[[LineNumber, Result, assumption] | BoxTail] | Validated]).

% Case 2: The first line is derived from a rule.
validate_box(Premises, Goal, [ProofHead | ProofTail], Validated) :-
    validate_rule(Premises, ProofHead, Validated),
    validate_box(Premises, Goal, ProofTail, [ProofHead | Validated]).

% find_box: Locate a box containing a specific line.
find_box(TargetLine, [BoxHead | _], BoxHead) :-
    member([TargetLine, _, _], BoxHead).

% If not found in the first box, search the remaining validated list.
find_box(TargetLine, [_ | Rest], Box) :-
    find_box(TargetLine, Rest, Box).
