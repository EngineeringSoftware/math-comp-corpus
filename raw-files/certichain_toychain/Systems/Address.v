From mathcomp.ssreflect
Require Import ssreflect ssrnat ssrfun eqtype choice fintype ssrbool seq.
From fcsl
Require Import ordtype.

Module Type NetAddr.
Definition half := prod 'I_1 'I_1.
Definition ip := prod half half.
Definition port := half.

Definition Address := prod ip port.
Definition Address_ordMixin := fin_ordMixin [finType of Address].
Canonical Address_ordType := Eval hnf in OrdType Address Address_ordMixin.

End NetAddr.

Module Addr <: NetAddr.
Include NetAddr.
End Addr.