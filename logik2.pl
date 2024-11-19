% Main entry point for verifying the proof from a file
verify(InputFileName) :- 
    see(InputFileName),                 % Open the file for reading
    read(Premises),                     % Read premises list
    read(Goal),                         % Read goal (conclusion)
    read(Proof),                        % Read the proof steps
    seen,                               % Close the file
    check_goal(Goal, Proof),            % Verify that the last step matches the goal
    validate_proof(Premises, Goal, Proof, []).  % Validate proof with premises and proof steps

% Checks if the last line in the proof matches the goal
check_goal(Goal, [[_, X, _] | []]) :- 
    Goal = X.
check_goal(Goal, [_ | Tail]) :- 
    check_goal(Goal, Tail).

% Base case: no more steps to validate
validate_proof(_, _, [], _).

% Validate each step in the proof recursively
validate_proof(Premises, Goal, [CurrentStep | RemainingSteps], ValidatedSteps) :-
    validate_step(Premises, Goal, CurrentStep, ValidatedSteps), % Validate current step
    validate_proof(Premises, Goal, RemainingSteps, [CurrentStep | ValidatedSteps]). % Continue with the remaining steps

% Validate a single proof step according to its rule

% Validate a premise
validate_step(Premises, _, [_, Formula, premise], _) :- 
    member(Formula, Premises).

% Validate "and introduction" (∧ introduction)
validate_step(_, _, [_, and(Left, Right), andint(Line1, Line2)], Validated) :-
    member([Line1, Left, _], Validated),
    member([Line2, Right, _], Validated).

% Validate "and elimination" (∧ elimination, left and right)
validate_step(_, _, [_, Left, andel1(LineRef)], Validated) :-
    member([LineRef, and(Left, _), _], Validated).
validate_step(_, _, [_, Right, andel2(LineRef)], Validated) :-
    member([LineRef, and(_, Right), _], Validated).

% Validate "implication introduction" (→ introduction)
validate_step(_, _, [_, imp(Antecedent, Consequent), impint(Start, End)], Validated) :-
    member(Box, Validated),
    member([Start, Antecedent, assumption], Box),
    member([End, Consequent, _], Box).

% Validate "implication elimination" (→ elimination)
validate_step(_, _, [_, Consequent, impel(Line1, Line2)], Validated) :-
    member([Line1, Antecedent, _], Validated),
    member([Line2, imp(Antecedent, Consequent), _], Validated).

% Validate an assumption (starts a new box)
validate_step(Premises, Goal, [[_, _, assumption] | BoxTail], Validated) :-
    validate_proof(Premises, Goal, BoxTail, [[_, _, assumption] | Validated]).

% Validate "or introduction" (∨ introduction, left and right)
validate_step(_, _, [_, or(Left, _), orint1(LineRef)], Validated) :-
    member([LineRef, Left, _], Validated).
validate_step(_, _, [_, or(_, Right), orint2(LineRef)], Validated) :-
    member([LineRef, Right, _], Validated).

% Validate "copy"
validate_step(_, _, [_, Formula, copy(LineRef)], Validated) :-
    member([LineRef, Formula, _], Validated).

% Validate "contradiction elimination" (⊥ elimination)
validate_step(_, _, [_, _, contel(LineRef)], Validated) :-
    member([LineRef, cont, _], Validated).

% Validate "negation introduction" (¬ introduction)
validate_step(_, _, [_, neg(Formula), negint(Start, End)], Validated) :-
    member(Box, Validated),
    member([Start, Formula, assumption], Box),
    member([End, cont, _], Box).

% Validate "negation elimination" (¬ elimination)
validate_step(_, _, [_, cont, negel(Line1, Line2)], Validated) :-
    member([Line1, Formula, _], Validated),
    member([Line2, neg(Formula), _], Validated).

% Validate "double negation introduction" (¬¬ introduction)
validate_step(_, _, [_, neg(neg(Formula)), negnegint(LineRef)], Validated) :-
    member([LineRef, Formula, _], Validated).

% Validate "double negation elimination" (¬¬ elimination)
validate_step(_, _, [_, Formula, negnegel(LineRef)], Validated) :-
    member([LineRef, neg(neg(Formula)), _], Validated).

% Validate "modus tollens" (mt)
validate_step(_, _, [_, neg(Antecedent), mt(Line1, Line2)], Validated) :-
    member([Line1, imp(Antecedent, Consequent), _], Validated),
    member([Line2, neg(Consequent), _], Validated).

% Validate "proof by contradiction" (pbc)
validate_step(_, _, [_, Formula, pbc(Start, End)], Validated) :-
    member(Box, Validated),
    member([Start, neg(Formula), assumption], Box),
    member([End, cont, _], Box).

% Validate "law of excluded middle" (LEM)
validate_step(_, _, [_, or(Formula, neg(Formula)), lem], _).
