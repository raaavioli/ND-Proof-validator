/**
	Enter url to input-file where:
	Prems - All premises on the form [A, B, ...,E].
	Goal - The goal formed as a Propositional logic expression
	Proof - The proof on the form [[Row, Proposition, Rule], ..., [Row, Goal, Rule]]
*/
verify(InputFileName) :- see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).

/**
	A proof is valid if the last element of the proof contains the Goal,
	the proof is not empty and we can iterate, using rules of Natural Deduction,
	through the proof reaching the end of it.
*/
valid_proof(Prems, Goal, Proof) :-
	\+is_empty(Proof),
	last(Proof, [_, Goal, _]),
	iterate_proof(Prems, Goal, Proof, Proof).

/**	
	If we hit the last row of the proof and Prop != Goal, then the proof failed. 
	Also if we hit the last row and the Rule is an assumption, the proof fails.
*/
iterate_proof(_, Goal, [[Row, Prop, Rule]|[]], Proof) :-
	last(Proof, [Row, Prop, _]),
	\+(Rule = assumption),
	\+(Prop = Goal), !,
	fail.	

/**
	This signifies that a proof inside a box has reached its end. (could also be box of whole proof)

	In this case, iterate_proof is VALID, and we will either continue at #split,
	or consider that the proof holds.
*/
iterate_proof(_, _, [], Proof).

/** 	PREMISE

	If the rule is "premise", then check whether the current
	proposition is in the premis-list, if true, continue iterating.
*/
iterate_proof(Prems, Goal, [[Row, Prop, premise]|Proof_rest], Proof) :-
	member(Prop, Prems), !,
	iterate_proof(Prems, Goal, Proof_rest, Proof).

/**	And-Introduction
*/
iterate_proof(Prems, Goal, [[Row, and(A,B), andint(X,Y)]|Rest], Proof) :-
	search_line(Row, X, A, Proof, Proof),
	search_line(Row, Y, B, Proof, Proof),
	X < Row, Y < Row,
	iterate_proof(Prems, Goal, Rest, Proof);
	search_line(Row, X, B, Proof, Proof),
	search_line(Row, Y, A, Proof, Proof),
	X < Row, Y < Row,
	iterate_proof(Prems, Goal, Rest, Proof).

/**	And-Elimination-1
*/
iterate_proof(Prems, Goal, [[Row, Prop, andel1(X)]|Rest], Proof) :-
	search_line(Row, X, and(Prop, _), Proof, Proof),
	X < Row,
	iterate_proof(Prems, Goal, Rest, Proof).

/**	And-Elimination-2
*/
iterate_proof(Prems, Goal, [[Row, Prop, andel2(X)]|Rest], Proof) :-
	search_line(Row, X, and(_, Prop), Proof, Proof),
	X < Row,
	iterate_proof(Prems, Goal, Rest, Proof).

/**	Or-Introduction-1
*/
iterate_proof(Prems, Goal, [[Row, or(A,_), orint1(X)]|Rest], Proof) :-
	search_line(Row, X, A, Proof, Proof),
	X < Row,
	iterate_proof(Prems, Goal, Rest, Proof).

/**	Or-Introduction-2
*/
iterate_proof(Prems, Goal, [[Row, or(_,B), orint2(X)]|Rest], Proof) :-
	search_line(Row, X, B, Proof, Proof),
	X < Row,
	iterate_proof(Prems, Goal, Rest, Proof).

/**	Implication-Elimination

	If Rule is impel(x,y) then search and check whether row Y
	contains the proposition imp(T,Prop) where Prop is our current prop.
	Also check whether row X contains the element T in T -> Prop.
*/
iterate_proof(Prems, Goal, [[Row, Prop, impel(X,Y)]|Proof_rest], Proof) :-
	search_line(Row, Y, imp(T,Prop), Proof, Proof),
	search_line(Row, X, T, Proof, Proof),
	X < Row, Y < Row,
	iterate_proof(Prems, Goal, Proof_rest, Proof).

/**	Implication-Introduction
*/
iterate_proof(Prems, Goal, [[Row, imp(BoxStart,BoxEnd), impint(X,Y)]|Rest], Proof) :-
	search_box(Row, X, BoxStart, Y, BoxEnd, Proof),
	iterate_proof(Prems, Goal, Rest, Proof).
/**
	This function might need to be changed to also try reversed order of A and B.
	It might be the case that the A is the assumption of the box P-Q and not U-V
*/
iterate_proof(Prems, Goal, [[Row,Prop, orel(X,U,V,P,Q)]|Rest], Proof) :-
	search_line(Row, X, or(A,B), Proof, Proof),
	X < Row,
	search_box(Row, U, A, V, Prop, Proof),
	search_box(Row, P, B, Q, Prop, Proof),
	iterate_proof(Prems, Goal, Rest, Proof).

/**	Negation-Introduction
*/
iterate_proof(Prems, Goal, [[Row, neg(Prop), negint(X,Y)]|Rest], Proof) :-
	search_box(Row, X, Prop, Y, cont, Proof),
	iterate_proof(Prems, Goal, Rest, Proof). 

/**	Negation-Elimination
*/
iterate_proof(Prems, Goal, [[Row, cont, negel(X,Y)]|Rest], Proof) :-
	search_line(Row, X, Prop, Proof, Proof),
	search_line(Row, Y, neg(Prop), Proof, Proof),
	X < Row, Y < Row,
	iterate_proof(Prems, Goal, Rest, Proof).

/**	Contradiction-Elimination
*/
iterate_proof(Prems, Goal, [[Row, Prop, contel(X)]|Rest], Proof) :-
	search_line(Row, X, cont, Proof, Proof),
	X < Row,
	iterate_proof(Prems, Goal, Rest, Proof).

/**	Double-Negation-Introduction
*/
iterate_proof(Prems, Goal, [[Row, neg(neg(A)), negnegint(X)]|Rest], Proof) :-
	search_line(Row, X, A, Proof, Proof),
	X < Row,
	iterate_proof(Prems, Goal, Rest, Proof).

/**	Double-Negation-Elimination
*/
iterate_proof(Prems, Goal, [[Row, Prop, negnegel(X)]|Rest], Proof) :-
	search_line(Row, X, neg(neg(Prop)), Proof, Proof),
	X < Row,
	iterate_proof(Prems, Goal, Rest, Proof).

/** Modus Tollens 

	(P -> Q), !Q |- !P
*/
iterate_proof(Prems, Goal, [[Row, neg(P), mt(X,Y)]|Rest], Proof) :-
	search_line(Row, X, imp(P,Q), Proof, Proof),
	search_line(Row, Y, neg(Q), Proof, Proof),
	X < Row, Y < Row,
	iterate_proof(Prems, Goal, Rest, Proof).

/**	LEM
	|- (A OR !A)
*/
iterate_proof(Prems, Goal, [[Row, or(P, neg(P)), lem]|Rest], Proof) :-
	iterate_proof(Prems, Goal, Rest, Proof).

/**
	#Split
	In case we encounter a box-opening, we need to iterate into both the box and the rest of the proof.
*/
iterate_proof(Prems, Goal, [[[Row, Prop, assumption]|NextInBox] | Rest], Proof) :-
	iterate_proof(Prems, Goal, NextInBox, Proof),
	iterate_proof(Prems, Goal, Rest, Proof). 

/**	COPY
	Lets us copy something already proved into a later stage of the proof
*/
iterate_proof(Prems, Goal, [[Row, Prop, copy(X)]|Rest], Proof) :-
	search_line(Row, X, Prop, Proof, Proof),
	X < Row,
	iterate_proof(Prems, Goal, Rest, Proof). 

/**	Proof-By-Contradiction
	Assuming not(Prop) and being able to show a Contradiction
	lets us conclude that Prop is true.
*/
iterate_proof(Prems, Goal, [[Row, Prop, pbc(X,Y)]|Rest], Proof) :-
	search_box(Row, X, neg(Prop), Y, cont, Proof),
	iterate_proof(Prems, Goal, Rest, Proof).

/**	search_box
	
	Lets us, given a rule on row "Call_row", check whether
	a box starting on BStart_row and ending on BEnd_row is
	valid, contains the Propositions we assume and accessible from Call_row.
*/
search_box(Call_row, BStart_row, BStart_prop, BEnd_row, BEnd_prop, Proof) :-
	call_row_after_box( BStart_row, Call_row, Proof ),
	findRowIn(BStart_row, Proof, Rest),
	last(Rest, [BEnd_row, BEnd_prop, _]),
	first(Rest, [BStart_row, BStart_prop, _]).

/** A simple predicate telling if H is the first element of a List */
first([H|T], H).

/**
	Lets us check whether a rownumber is in the same box as a specific box.
	i.e:
	[a
		[b,
			[c,
			d],
		e]
	f]
	The proposition tells us if for example the box c-d is accessible from a row X.
	if X = e, the proposition in this case is true.
	Any other variable would return false as Callrow. 
*/
call_row_after_box(Boxstart, Callrow, [[[Boxstart, _, _]|Boxrest]|Rest]) :- 
	member([Callrow,_,_], Rest).
call_row_after_box( Boxstart, Callrow, [H|Rest] ) :-
	call_row_after_box( Boxstart, Callrow, Rest).
call_row_after_box( Boxstart, Callrow, [H|Rest] ) :-
	call_row_after_box( Boxstart, Callrow, H ).	

/**
	Looks for a specific "line"/proofrow in the Proof.
	If it is found, and it is found through valid_boxing,
	then search_line is true.
*/
search_line(Call_row, Prop_row, Prop, [[Prop_row, Prop, _]|Rest], Proof) :- valid_boxing(Prop_row, Call_row, Proof). 
search_line(Call_row, Prop_row, Prop, [Box|_], Proof) :-
	search_line(Call_row, Prop_row, Prop, Box, Proof).
search_line(Call_row, Prop_row, Prop, [_|Rest], Proof) :-
	search_line(Call_row, Prop_row, Prop, Rest, Proof).

/** 
	A boxing is valid if we can find a row R2
	given the Rest of the proof following R1 iterating
	sequentially through Rest.
*/
valid_boxing(R1, R2, Proof) :-
	R1 < R2,
	findRowIn(R1, Proof, Rest),
	findRowIn(R2, Rest, _);
	R2 < R1,
	findRowIn(R2, Proof, Rest),
	findRowIn(R1, Rest, _).

/**	Looks for a certain row of a proof and returns the rest of the proof given
	that found row.
*/
findRowIn(Row, [[Row, P, R]|Rest], [[Row, P, R]|Rest]).
findRowIn(Row, [[H|T]|Proof], Rest) :-
        findRowIn(Row, [H|T], Rest).
findRowIn(Row, [_|Proof], Rest) :-
	 findRowIn(Row, Proof, Rest). 

/** Tells if a list is empty */
is_empty([]).
is_empty([_,_]) :- fail.

/** Implements the Implication-proposition */
imp(true, Q) :- Q.
imp(P, true).
imp(fail, fail).

/** Implements logical-And */
and(P, Q) :- P, Q.

/** Implements logical-Or */
or(P, true).
or(true, Q).

/** Implements negation */
neg(X) :- \+X.


