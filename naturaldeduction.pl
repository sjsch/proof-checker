%% We implement a form of natural deduction for first-order logic,
%% with equality, relation and function symbols, and induction on
%% natural numbers.  This is a simple system, yet it's powerful enough
%% to prove interesting theorems in number theory (as well as be
%% subject to Gödel's incompleteness theorems.)

%% Propositions (in prolog syntax):
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

% claim and_comm : P /\ Q -> Q /\ P
% proof and_comm {
%   cond (hyp_pq) {
%     conj {
%       proj_right { hyp_pq }
%     } {
%       proj_left { hyp_pq }
%     }
%   }
% }

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
%%   % We''re trying to prove that for any n, 0 + n = n.  (The peano axioms define n + 0 = n, but not the other way.)
%%   forall(n, equal(func(add, [zero, n]), n))
%% ).

%% proves(D, A, Proof, P) is true when given the existing named
%% theorems D, the assumptions A (separated for user experience), the
%% proof Proof is a valid proof of the proposition P.

%% Introduction rules

%% We can prove the goal "true" instantly and without assumptions.
%% Notice that true has an introduction rule and no elimination rule,
%% while false has an elimination rule but no introduction.
proves(_, _, trivial, true).

%% We can prove "P and Q" by giving a proof composed of P, as well as
%% a proof of Q.
proves(D, A, conj(Proof1, Proof2), and(P, Q)) :-
    proves(D, A, Proof1, P),
    proves(D, A, Proof2, Q).

%% We can prove "P or Q" by picking a side and proving only that one.
proves(D, A,  left(Proof), or(P, _)) :-
    proves(D, A, Proof, P).
proves(D, A, right(Proof), or(_, Q)) :-
    proves(D, A, Proof, Q).

%% To prove an implication like "P implies Q", we can do conditional
%% proof.  We introduce the antecedent as an assumption and give it a
%% name, which we can use in the proof of the consequent.
proves(D, A, cond(X, ProofQ), imp(P, Q)) :-
    proves(D, [X:P | A], ProofQ, Q).

%% If we already have a proof of "P", we can generalize it into a
%% proof of that statement for any individual, provided that the
%% variable we introduce does not appear in the proposition.
proves(D, A, generalize(Proof), forall(X, P)) :-
    proves(D, A, Proof, P),
    not(free(X, P)).

%% To prove an existential, we can simmple name an example individual
%% that satisfies the proposition.
proves(D, A, example(X, Proof), exists(Y, P)) :-
    proves(D, A, Proof, Q),
    subst(Y, X, P, Q).

%% For any individual x, we can produce a proof that x = x.
proves(_, _, refl(X), equal(X, X)).

%% Elimination rules.

%% Given a proof of "P and Q", we are allowed to produce a proof of P
%% or Q.
proves(D, A, proj_left(Proof1), P) :-
    proves(D, A, Proof1, and(P, _)).
proves(D, A, proj_right(Proof1), Q) :-
    proves(D, A, Proof1, and(_, Q)).

%% Given a proof of "P or Q", we must do case analysis by providing a
%% proof for the situation where P is true, and one for where Q is
%% true, that have the same conclusion.
proves(D, A, case(ProofOr, ProofA, ProofB), C) :-
    proves(D, A, ProofOr, or(A, B)),
    proves(D, A, ProofA, imp(A, C)),
    proves(D, A, ProofB, imp(B, C)).

%% If we have an implication, we are allowed to prove the conclusion
%% if we have a proof of the antecedent.
proves(D, A, mp(ProofImp, ProofP), Q) :-
    proves(D, A, ProofImp, imp(P, Q)),
    proves(D, A, ProofP, P).

%% Given a proof of P and a proof of not P, we are allowed to prove
%% anything we want: this is how we can eliminate absurd cases in our
%% case analysis.
proves(D, A, contra(ProofP, ProofNP), _) :-
    proves(D, A, ProofP, P),
    proves(D, A, ProofNP, not(P)).

%% If we have a proof of "P for any x", we can name a specific x and
%% get back a proof of P where that x is filled in.
proves(D, A, specialize(Proof, X), Q) :-
    proves(D, A, Proof, forall(Y, P)),
    subst(Y, X, P, Q).

%% Given a proof that there exists some x for which P is true, we are
%% allowed to bring in a free variable x and an assumption that P is
%% true for it, but we might not know what the x is.
proves(D, A, inspect(Proof), P) :-
    proves(D, A, Proof, exists(_, P)).

%% We can prove a universal statement about the natural numbers by
%% providing a proof that holds for 0, and a proof that P holding for
%% n implies it holds for the successor of n.
proves(D, A, induction(Proof0, ProofS), forall(N, P)) :-
    subst(N, zero, P, P0),
    subst(N, func(succ, [N]), P, PS),
    proves(D, A, Proof0, P0),
    proves(D, A, ProofS, imp(P, PS)).

%% We can take a proof that a = b and flip it to get a proof that b =
%% a.
proves(D, A, sym(Proof), equal(Y, X)) :-
    proves(D, A, Proof, equal(X, Y)).

%% We can combine proofs of a = b and b = c to get a = c.
proves(D, A, trans(Proof1, Proof2), equal(X, Z)) :-
    proves(D, A, Proof1, equal(X, Y)),
    proves(D, A, Proof2, equal(Y, Z)).

%% We can use an equality proof of x = y by substituting y for x in a
%% proposition that we have also proved.  We do the substitution "in
%% reverse" to support backwards reasoning with holes: you know what
%% you want to prove, and you can find out what you have to prove
%% after rewriting with the substitution by using this proof term.
proves(D, A, subst(ProofEq, Proof), P) :-
    proves(D, A, ProofEq, equal(S, T)),
    subst(S, T, P, Q),
    proves(D, A, Proof, Q).

%% If we have a named theorem in our context, we're allowed to
%% reference that.
proves(D, _, X, P) :-
    atom(X),
    member(X:P, D).

%% If we have an assumption, we can also use that.
proves(_, A, X, P) :-
    atom(X),
    member(X:P, A).

%% If we haven't completed a proof, we can put a hole in the missing
%% part.  Prolog's search will use backwards reasoning to find out
%% what kind of proof you have to put in the hole, and what
%% assumptions you may use, to complete the proof.
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

proof(N, P, Proof) -->
    symbol("proof"),
    ident(N),
    symbol(":"),
    prop0(P),
    symbol("{"),
    proofterm(Proof),
    symbol("}").

term0(func(add, [X, Y])) --> term1(X), symbol("+"), term0(Y).
term0(X) --> term1(X).

term1(func(mul, [X, Y])) --> term2(X), symbol("*"), term0(Y).
term1(X) -->  term2(X).

term2(func(F, Ts)) --> functional(term0, F, Ts).
term2(X) --> ident(X).
term2(PN) --> digit(C), digits(Cs), blanks, { number_codes(N, [C | Cs]), peano_num(N, PN) }.
term2(X) --> symbol("("), term0(X), symbol(")").

peano_num(0, zero).
peano_num(N, succ(PN1)) :-
    N > 0,
    N1 is N - 1,
    peano_num(N1, PN1).

prop0(imp(P, Q)) --> prop1(P), symbol("->"), prop0(Q).
prop0(P) --> prop1(P).

prop1(or(P, Q)) --> prop2(P), symbol("\\/"), prop0(Q).
prop1(P) --> prop2(P).

prop2(and(P, Q)) --> prop3(P), symbol("/\\"), prop0(Q).
prop2(P) --> prop3(P).

prop3(X) --> ident(X).
prop3(not(X)) --> symbol("~"), prop0(X).
prop3(X) --> symbol("("), prop0(X), symbol(")").
prop3(forall(X, P)) --> symbol("forall"), ident(X), symbol("."), prop0(P).
prop3(exists(X, P)) --> symbol("exists"), ident(X), symbol("."), prop0(P).
prop3(equal(T, U)) --> term0(T), symbol("="), term0(U).
prop3(rel(R, Ps)) --> functional(term0, R, Ps).

proofterm(trivial) --> symbol("trivial").

functional(P, F, As) --> ident(F), symbol("("), arglist(P, As), symbol(")").
functional(_, F, []) --> ident(F), symbol("("), symbol(")").

arglist(P, [H | T]) --> call(P, H), symbol(","), arglist(P, T).
arglist(P, [H]) --> call(P, H).

alnumident([C | T]) --> [C], { code_type(C, csym) }, alnumident(T).
alnumident([]) --> [].

ident(X) --> [C], { code_type(C, csymf) }, alnumident(T), { atom_string(X, [C | T]) }, blanks.

symbol(S) --> S, blanks.
