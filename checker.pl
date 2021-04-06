%% Right now, we implement the basic Calculus of Constructions.  Many
%% things can be defined within it, like formulae in propositional
%% logic, existentials, natural numbers.  However, some things like
%% induction on natural numbers cannot be derived, and we need to
%% introduce the induction principle as an axiom.
%%
%% (Our presentation based off of the original Calculus of
%% Constructions paper and Type Theory and Formal Proof):
%%
%% (Abstract) syntax for terms in the language (prolog syntax on the
%% left, mathy on the right):
%%
%% t ::= type
%%     | prop
%%     | var(x)          x
%%     | app(t1, t2)     t1 t2
%%     | lam(x, t1, t2)  λ x : t1, t2
%%     | pi(x, t1, t2)   Π x : t1, t2
%%
%% They are explained in comments next to the rules that implement
%% them.
%%

%% Contexts in our logic include two kinds of mappings:
%%   hastype(X, T)
%%     indicates that we have a hypothesis called X, that proves T.
%%   hasdef(X, T, D)
%%     indicates that we have a proof D of T called X.

%% addmap(E, G1, G2) is true if adding the mapping E to the context G1
%% results in G2.
addmap(E, G1, [E|G2]) :- delete(G1, E, G2).

%% hastype(G, X, T) is true if the variable X has the type T in the
%% context G (either by assumption or by definition).
hastype(G, X, T) :- member(hastype(X, T), G).
hastype(G, X, T) :- member(hasdef(X, T, _), G).

%% type(C, G, E, T) is true if E can be assigned type T in the context
%% G (aka E is a proof of T).  C is yes/no, and indicates whether or
%% not to allow simplification (beta reduction) in types.  This must
%% be no when inferring a type instead of just checking it, or else
%% this won't terminate.
%%
%% It is written G ⊢ X : T in the comments.

%% type/prop are our universes.  Propositions, like "x = y" or
%% "a /\ b", live in prop.  prop is impredicative: we can create new
%% props by quantifying over all props like "for any proposition P,
%% Q".  The type of prop is type, but type itself does not have a
%% type.
%%
%%   ---------------
%%   Γ ⊢ prop : type
type(_, _, prop, type).

%% If you have an assumption, or a definition that proves something
%% sitting in a variable somewhere, you can use it to prove the thing
%% that it proves (the type that it has).
%%
%%   hastype(Γ, x, A)
%%   ----------------
%%      Γ ⊢ x : A
type(_, G, var(X), A) :- hastype(G, X, A).

%% The pi type gives us universal quantification.  Π x : t1, t2 is the
%% proposition that for any proof of t1 (which we call x), t2 holds.
%% A pi type is valid if the thing we are quantifying over is valid,
%% and if the resulting proposition, given an assumption of the type
%% of the thing we're quantifying over is valid.
%%
%%   Γ ⊢ A : T  Γ, X : A ⊢ B : L
%%   ---------------------------
%%       Γ ⊢ Π x : A, B : L
type(C, G, pi(X, A, B), L) :-
    type(C, G, A, _),
    addmap(hastype(X, A), G, G2),
    type(C, G2, B, L),
    universe(L).

%% The lambda is how you prove a pi type: it lets you make an
%% assumption and give it a name, and then prove the right of the pi
%% type with the assumption.
%%
%%     Γ ⊢ A : T  Γ, x : A ⊢ N : B
%%   -------------------------------
%%   Γ ⊢ (λ x : A, N) : (Π x : A, B)
type(C, G, lam(X, A, N), pi(X, A, B)) :-
    type(C, G, A, _),
    addmap(hastype(X, A), G, G2),
    type(C, G2, N, B).

%% Application lets us use proofs of universal quantification.  This
%% plays the role of both modus ponens (applying a proof of A to a
%% proof that for any proof of A, B) as well as universal
%% instantiation, (applying an A to a proof that for any A, B).
%%
%%   Γ ⊢ M : (Π x : A, B)  Γ ⊢ N : A
%%   -------------------------------
%%         Γ ⊢ M N : B[N / X]
type(C, G, app(M, N), B2) :-
    type(C, G, M, pi(X, A, B)),
    type(C, G, N, A),
    subst(X, N, B, B2).

%% This rules lets us do simplifications: if your proof proves A, and
%% A can be simplified to B, then it proves B.
%%
%%   Γ ⊢ M : A  Γ ⊢ A ≈ B
%%   --------------------
%%        Γ ⊢ M : B
type(yes, G, M, B) :-
    type(no, G, M, A),
    beta(A, B),
    type(yes, G, B, _).

%% universe(T) is true if T is one of the universes: type, or prop.
universe(prop).
universe(type).

%% beta(G, X, Y) is true if X can be simplified to Y in the context G.
%% Beta reduction is both computation and proof simplification.
beta(G, lam(X, A, B), lam(X, A2, B)) :-
    beta(G, A, A2).
beta(G, lam(X, A, B), lam(X, A, B2)) :-
    beta(G, B, B2).
beta(G, pi(X, A, B), pi(X, A2, B)) :-
    beta(G, A, A2).
beta(G, pi(X, A, B), pi(X, A, B2)) :-
    beta(G, B, B2).
beta(G, succ(A), succ(A2)) :-
    beta(G, A, A2).
beta(G, app(lam(X, _, A), B), C) :-
    subst(G, X, B, A, C).
beta(G, app(A, B), app(A2, B)) :-
    beta(G, A, A2).
beta(G, var(X), D) :-
    member(hasdef(X, _, D), G).

%% subst(X, Y, E1, E2) is true if substituing Y for the variable
%% var(X) in E1 results in E2.  Written E1[Y/X].
subst(X, Y, var(X), Y).
subst(_, _, prop, prop).
subst(_, _, type, type).
subst(X, Y, app(A, B), app(A2, B2)) :-
    subst(X, Y, A, A2),
    subst(X, Y, B, B2).
subst(X, _, pi(X, A, B), pi(X, A, B)).
subst(X, Y, pi(V, A, B), pi(V, A2, B2)) :-
    dif(X, V),
    subst(X, Y, A, A2),
    subst(X, Y, B, B2).
subst(X, _, lam(X, A, B), lam(X, A, B)).
subst(X, Y, lam(V, A, B), lam(V, A2, B2)) :-
    dif(X, V),
    subst(X, Y, A, A2),
    subst(X, Y, B, B2).
