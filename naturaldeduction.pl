%% Propositions:
%%
%% P ::= true
%%     | false
%%     | and(P, Q)
%%     | or(P, Q)
%%     | imp(P, Q)
%%     | not(P)
%%     | forall(X, P)
%%     | exists(X, P)
%%     | equal(t, u)
%%     | rel(r, [P...])
%%
%% Terms:
%% 
%% t ::= x
%%     | func(f, [t...])


%% Example proof of the commutativity of addition:
%% 
%% peano(DS), % Add the peano axioms
%% proves(DS, [],
%%
%%   % We proceed by induction on n.
%%   induction(
%%     % The base case is covered by specializing the axiom "forall all n, n + 0 = 0" to zero.
%%     specialize(add_zero, zero),
%%     % We do conditional proof for the inductive step, since we get the induction hypothesis as an assumption.
%%     cond(
%%       induction_hyp,
%%       % We can rewrite the goal using an equality.
%%       subst(
%%         % Rewrite the goal using 0 + succ(n) = succ(0  + n)
%%         specialize(specialize(add_succ, zero), n),
%%         subst(
%%           % Rewrite the goal with the IH, 0 + n = n
%%           induction_hyp),
%%           % Trivially, n = n
%%           refl(func(succ, [n]))
%%         )
%%       )
%%     )
%%   ),
%%   % We're trying to prove that for any n, 0 + n = n.  (The peano axioms define n + 0 = n, but not the other way.)
%%   forall(n, equal(func(add, [zero, n]), n))
%% ).

%% proves(D, A, Proof, P) is true when given the existing named
%% theorems D, the assumptions A (separated for user experience), the
%% proof Proof is a valid proof of the proposition P.

%% Introduction rules

proves(_, _, trivial, true).
%% No way to prove false.

proves(D, A, conj(Proof1, Proof2), and(P, Q)) :-
    proves(D, A, Proof1, P),
    proves(D, A, Proof2, Q).

proves(D, A,  left(Proof), or(P, _)) :-
    proves(D, A, Proof, P).
proves(D, A, right(Proof), or(_, Q)) :-
    proves(D, A, Proof, Q).

proves(D, A, cond(X, ProofQ), imp(P, Q)) :-
    proves(D, [X:P | A], ProofQ, Q).

proves(D, A, generalize(Proof), forall(X, P)) :-
    proves(D, A, Proof, P),
    not(free(X, P)).

proves(D, A, example(X, Proof), exists(Y, P)) :-
    proves(D, A, Proof, Q),
    subst(Y, X, P, Q).

proves(_, _, refl(X), equal(X, X)).

%% Elimination rules.

proves(D, A, proj_left(Proof1), P) :-
    proves(D, A, Proof1, and(P, _)).
proves(D, A, proj_right(Proof1), Q) :-
    proves(D, A, Proof1, and(_, Q)).

proves(D, A, case(ProofOr, ProofA, ProofB), C) :-
    proves(D, A, ProofOr, or(A, B)),
    proves(D, A, ProofA, imp(A, C)),
    proves(D, A, ProofB, imp(B, C)).

proves(D, A, mp(ProofImp, ProofP), Q) :-
    proves(D, A, ProofImp, imp(P, Q)),
    proves(D, A, ProofP, P).

proves(D, A, contra(ProofP, ProofNP), _) :-
    proves(D, A, ProofP, P),
    proves(D, A, ProofNP, not(P)).
    
proves(D, A, specialize(Proof, X), Q) :-
    proves(D, A, Proof, forall(Y, P)),
    subst(Y, X, P, Q).

proves(D, A, inspect(Proof), P) :-
    proves(D, A, Proof, exists(_, P)).

proves(D, A, induction(Proof0, ProofS), forall(N, P)) :-
    subst(N, zero, P, P0),
    subst(N, func(succ, [N]), P, PS),
    proves(D, A, Proof0, P0),
    proves(D, A, ProofS, imp(P, PS)).

proves(D, A, sym(Proof), equal(Y, X)) :-
    proves(D, A, Proof, equal(X, Y)).

proves(D, A, trans(Proof1, Proof2), equal(X, Z)) :-
    proves(D, A, Proof1, equal(X, Y)),
    proves(D, A, Proof2, equal(Y, Z)).

proves(D, A, subst(ProofEq, Proof), P) :-
    proves(D, A, ProofEq, equal(S, T)),
    subst(S, T, P, Q),
    proves(D, A, Proof, Q).

proves(D, _, X, P) :-
    atom(X),
    member(X:P, D).

proves(_, A, X, P) :-
    atom(X),
    member(X:P, A).

proves(_, A, hole(A, G), G).

%% free(X, Y) is true when X is free (appears as a variable, but is
%% not bound by a quantifier) in Y.
free(X, Y) :-
    atom(Y),
    dif(X, Y).
free(X, and(P, _)) :-
    free(X, P).
free(X, and(_, Q)) :-
    free(X, Q).
free(X, or(P, _)) :-
    free(X, P).
free(X, or(_, Q)) :-
    free(X, Q).
free(X, imp(P, _)) :-
    free(X, P).
free(X, imp(_, Q)) :-
    free(X, Q).
free(X, not(P)) :-
    free(X, P).
free(X, forall(Y, P)) :-
    dif(X, Y),
    free(X, P).
free(X, exists(Y, P)) :-
    dif(X, Y),
    free(X, P).
free(X, equal(T, U)) :-
    free(X, T),
    free(X, U).

%% subst(X, Y, A, B) is true when X, substituted for Y in A, gives you
%% B, properly avoiding capturing free variables in quantifiers.
subst(X, Y, X, Y).
subst(X, _, Z, Z) :-
    atom(Z),
    dif(X, Z).
subst(X, Y, and(P, Q), and(P2, Q2)) :-
    subst(X, Y, P, P2),
    subst(X, Y, Q, Q2).
subst(X, Y, or(P, Q), or(P2, Q2)) :-
    subst(X, Y, P, P2),
    subst(X, Y, Q, Q2).
subst(X, Y, imp(P, Q), imp(P2, Q2)) :-
    subst(X, Y, P, P2),
    subst(X, Y, Q, Q2).
subst(X, Y, not(P), not(P2)) :-
    subst(X, Y, P, P2).
subst(X, _, forall(X, P), forall(X, P)).
subst(X, Y, forall(Z, P), forall(Z, P2)) :-
    dif(X, Z),
    subst(X, Y, P, P2).
subst(X, _, exists(X, P), exists(X, P)).
subst(X, Y, exists(Z, P), exists(Z, P2)) :-
    dif(X, Z),
    subst(X, Y, P, P2).
subst(X, Y, equal(P, Q), equal(P2, Q2)) :-
    subst(X, Y, P, P2),
    subst(X, Y, Q, Q2).
subst(X, Y, rel(R, Ps), rel(R, Ps2)) :-
    maplist(subst(X, Y), Ps, Ps2).
subst(X, Y, func(F, Ts), func(F, Ts2)) :-
    maplist(subst(X, Y), Ts, Ts2).

%% peano(DS) is true when the list of defintiions contain the peano axioms.
peano(DS) :-
    DS = [
        succ_inj : forall(n, forall(m, imp(equal(func(succ, [n]), func(succ, [m])), equal(n, m)))),
        ne_zero : forall(n, not(equal(func(succ, [n]), zero))),
        add_zero : forall(a, equal(func(add, [a, zero]), a)),
        add_succ : forall(a, forall(b, equal(func(add, [a, func(succ, [b])]), func(succ, [func(add, [a, b])])))),
        mul_zero : forall(a, equal(func(mul, [a, zero]), zero)),
        mul_succ : forall(a, forall(b, equal(func(mul, [a, func(succ, [b])]), func(add, [a, func(mul, [a, b])]))))
        | _
    ].

%% Parser

keyword(X) :-
    Keywords = ['/\\', '\\/', '(', ')'],
    member(X, Keywords).

prop0(or(P, Q)) --> prop1(P), ['\\/'], prop0(Q).
prop0(X) --> prop1(X).

prop1(and(P, Q)) --> prop2(P), ['/\\'], prop1(Q).
prop1(X) --> prop2(X).

prop2(X) --> [X], {atom(X), not(keyword(X))}.
prop2(X) --> ['('], prop0(X), [')'].
