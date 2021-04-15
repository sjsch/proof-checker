:- use_module(library(dcg/basics)).

parsing(hi) --> "hello".
parsing(braces(X)) --> "{", blanks, alnumident(X), blanks, alnumident(X), "}", blanks.

alnumident([C | T]) --> [C], { code_type(C, csym) }, alnumident(T).
alnumident([]) --> [].

ident(X) --> [C], { code_type(C, csymf) }, alnumident(T), { atom_string(X, [C | T]) }, blanks.
