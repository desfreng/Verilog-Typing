max(A, A, B) :- A >= B.
max(B, A, B) :- B > A.

lSize(S, S).
atomSize(S, S).

type_(_, atom(X), S) :-
    atomSize(X, S).

type_(N, binOp(A, B), S) :-
    type_(N, A, Sa),
    type_(N, B, Sb),
    max(S, Sa, Sb).

type_(N, unOp(E), S) :-
    type_(N, E, S).

type_(_, cast(E), S) :-
    type_(S, E, S).

type_(_, comp(A, B), 1) :-
    type_(S, A, Sa),
    type_(S, B, Sb),
    max(S, Sa, Sb).

type_(_, logic(A, B), 1) :-
    type_(Sa, A, Sa),
    type_(Sb, B, Sb).

type_(_, red(E), 1) :-
    type_(S, E, S).

type_(N, shif(A, B), S) :-
    type_(N, A, S),
    type_(Sb, B, Sb).

type_(_, assign(L, E), S) :-
    lSize(L, S),
    type_(Ne, E, Se),
    max(Ne, S, Se).

type_(_, shiftAssign(L, E), S) :-
    lSize(L, S),
    type_(Se, E, Se).

type_(N, cond(E, A, B), S) :-
    type_(Se, E, Se),
    type_(N, A, Sa),
    type_(N, B, Sb),
    max(S, Sa, Sb).

type_(_, concat(A, B), S) :-
    type_(Sa, A, Sa),
    type_(Sb, B, Sb),
    S is Sa + Sb.

type_(_, repl(I, E), S) :-
    type_(Se, E, Se),
    S is I * Se.

show_type_(P, E, N) :-
    nl,
    write(P),
    print(E),
    write(': '),
    print(N).

% type_(N, E, S) :-
%     show_type_('?  ', E, N),
%     type_(N, E, S),
%     show_type_('-> ', E, N).

type(E, N) :- type_(N, E, N).

% trace.
% type_(cond(atom(4), binOp(red(atom(5)), cast(binOp(atom(1), atom(2)))), atom(32)), X).