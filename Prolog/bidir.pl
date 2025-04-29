lSize(X, X).
atomSize(X, X).


resize(atom(_)).
resize(cast(_)).
resize(comp(_, _)).
resize(logic(_, _)).
resize(red(_)).
resize(assign(_, _)).
resize(shiftAssign(_, _)).
resize(concat(_, _)).
resize(repl(_, _)).


synth(atom(X), T) :-
    lSize(X, T).

synth(binOp(A, B), T) :-
    synth(A, T),
    check(B, T).

synth(binOp(A, B), T) :-
    synth(B, T),
    check(A, T).

synth(unOp(E), T) :-
    synth(E, T).


synth(cast(E), T) :-
    synth(E, T).

synth(comp(A, B), 1) :-
    synth(A, T),
    check(B, T).

synth(comp(A, B), 1) :-
    synth(B, T),
    check(A, T).

synth(logic(A, B), 1) :-
    synth(A, _),
    synth(B, _).

synth(red(E), 1) :-
    synth(E, _).

synth(shif(A, B), T) :-
    synth(A, T),
    synth(B, _).


synth(assign(L, E), T) :-
    lSize(L, T),
    check(E, T).

synth(assign(L, E), T) :-
    lSize(L, T),
    synth(E, Te),
    T < Te.

synth(shiftAssign(L, E), T) :-
    lSize(L, T),
    synth(E, _).

synth(cond(E, A, B), T) :-
    synth(E, _),
    synth(A, T),
    check(B, T).

synth(cond(E, A, B), T) :-
    synth(E, _),
    synth(B, T),
    check(A, T).

synth(concat(A, B), T) :-
    synth(A, Ta),
    synth(B, Tb),
    T is Ta + Tb.

synth(repl(I, E), T) :-
    synth(E, Te),
    T is I * Te.

% Check Rules

check(binOp(A, B), T) :-
    check(A, T),
    check(B, T).

check(unOp(E), T) :-
    check(E, T).

check(shif(A, B), T) :-
    check(A, T),
    synth(B, _).

check(cond(E, A, B), T) :-
    synth(E, _),
    check(A, T),
    check(B, T).

check(E, T) :-
    synth(E, S),
    resize(E),
    S =< T.


% trace.
% synth(cond(atom(4), binOp(red(atom(5)), cast(binOp(atom(1), atom(2)))), atom(32)), X).