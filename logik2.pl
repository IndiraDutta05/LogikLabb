% Main entry point for verifying the proof from a file
verify(InputFileName) :- 
    see(InputFileName),                  % Open the file for reading
    read(Premises),                       % Read premises list
    read(Goal),                           % Read goal (conclusion)
    read(Proof),                          % Read the proof steps
    seen,                                 % Close the file
    valid_proof(Premises, Goal, Proof).   % Validate the proof with these steps

% Checks if the last element in Proof matches Goal and validates proof line-by-line
valid_proof(Premises, Goal, Proof) :- 
    last(Proof, [_, Goal, _]),            % Ensure last line equals the goal
    check_proof_steps(Premises, Proof, []), % Validate proof steps starting with empty validated list
    !.

% Base case: no more steps to check
check_proof_steps(_, [], _).

% Recursively validate each step in the proof
check_proof_steps(Premises, [CurrentStep|RemainingSteps], ValidatedSteps) :-
    validate_line(Premises, CurrentStep, ValidatedSteps),           % Validate current step
    append(ValidatedSteps, [CurrentStep], UpdatedValidated),        % Add to validated steps
    check_proof_steps(Premises, RemainingSteps, UpdatedValidated).  % Continue with remaining steps

% Box validation: Checks if a box is valid from start to end line
check_box(StartLine, EndLine, Validated) :- 
    member([StartLine | InnerLines], Validated),
    last(InnerLines, EndLine).

check_box(Line, Line, Validated) :- 
    member([Line], Validated).

% Handles premise
validate_line(Premises, [_, Formula, premise], _) :- 
    member(Formula, Premises).

% Handles assumption and starts a box with assumption
validate_line(Premises, [[_, _, assumption] | BoxTail], Validated) :- 
    append(Validated, [[_, _, assumption]], ExtendedValidated),
    check_proof_steps(Premises, BoxTail, ExtendedValidated).

% Handles copy
validate_line(_, [_, Formula, copy(LineRef)], Validated) :- 
    member([LineRef, Formula, _], Validated).

% Handles and introduction ∧i
validate_line(_, [_, and(Left, Right), andint(LineX, LineY)], Validated) :- 
    member([LineX, Left, _], Validated),
    member([LineY, Right, _], Validated).

% Handles and elimination ∧e1 (left)
validate_line(_, [_, Left, andel1(LineRef)], Validated) :- 
    member([LineRef, and(Left, _), _], Validated).

% Handles and elimination ∧e2 (right)
validate_line(_, [_, Right, andel2(LineRef)], Validated) :- 
    member([LineRef, and(_, Right), _], Validated).

% Handles or introduction ∨i1 (left)
validate_line(_, [_, or(Left, _), orint1(LineRef)], Validated) :- 
    member([LineRef, Left, _], Validated).

% Handles or introduction ∨i2 (right)
validate_line(_, [_, or(_, Right), orint2(LineRef)], Validated) :- 
    member([LineRef, Right, _], Validated).

% Handles disjunction elimination ∨e
validate_line(_, [_, Formula, orel(X, Y, U, V, W)], Validated) :-
    member([X, or(Left, Right), _], Validated),
    check_box([Y, Left, assumption], [U, Formula, _], Validated),
    check_box([V, Right, assumption], [W, Formula, _], Validated).

% Handles implication elimination (→e)
validate_line(_, [_, Conclusion, impel(LineX, LineY)], Validated) :- 
    member([LineX, Premise, _], Validated),
    member([LineY, imp(Premise, Conclusion), _], Validated).

% Handles negation introduction ¬i
validate_line(_, [_, neg(Formula), negint(Start, End)], Validated) :- 
    check_box([Start, Formula, assumption], [End, cont, _], Validated).

% Handles negation elimination ¬e
validate_line(_, [_, cont, negel(LineX, LineY)], Validated) :- 
    member([LineX, Formula, _], Validated),
    member([LineY, neg(Formula), _], Validated).

% Handles contradiction elimination ⊥e
validate_line(_, [_, _, contel(LineRef)], Validated) :- 
    member([LineRef, cont, _], Validated).

% Handles double negation introduction ¬¬i
validate_line(_, [_, neg(neg(Formula)), negnegint(LineRef)], Validated) :- 
    member([LineRef, Formula, _], Validated).

% Handles double negation elimination ¬¬e
validate_line(_, [_, Formula, negnegel(LineRef)], Validated) :- 
    member([LineRef, neg(neg(Formula)), _], Validated).

% Handles modus tollens (mt)
validate_line(_, [_, neg(Antecedent), mt(LineX, LineY)], Validated) :- 
    member([LineX, imp(Antecedent, Consequent), _], Validated),
    member([LineY, neg(Consequent), _], Validated).

% Handles proof by contradiction pbc
validate_line(_, [_, Conclusion, pbc(Start, End)], Validated) :- 
    check_box([Start, neg(Conclusion), assumption], [End, cont, _], Validated).

% Handles implication introduction (→i)
validate_line(_, [_, imp(Antecedent, Consequent), impint(Start, End)], Validated) :- 
    check_box([Start, Antecedent, assumption], [End, Consequent, _], Validated).

% Handles law of excluded middle (lem)
validate_line(_, [_, or(Formula, neg(Formula)), lem], _).

