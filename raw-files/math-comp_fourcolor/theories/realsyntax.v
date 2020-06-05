
From fourcolor Require Import real.

Import Real.
Export RealCoercions.

Bind Scope real_scope with val.
Bind Scope realset_scope with set.
Delimit Scope real_scope with Rval.
Delimit Scope realset_scope with Rset.
Local Open Scope real_scope.

Arguments val R : rename, simpl never.
Arguments set R : rename, simpl never.
Arguments rel R : rename, simpl never.
Arguments le {R} x%Rval y%Rval : rename, simpl never.
Arguments sup {R} E%Rset : rename, simpl never.
Arguments add {R} x%Rval y%Rval : rename, simpl never.
Arguments opp {R} x%Rval : rename, simpl never.
Arguments mul {R} x%Rval y%Rval : rename, simpl never.
Arguments inv {R} x%Rval : rename, simpl never.
Arguments eq {R} x%Rval y%Rval.
Arguments ub {R} E%Rset x%Rval.
Arguments down {R} E%Rset x%Rval.
Arguments nonempty {R} E%Rset.
Arguments has_ub {R} E%Rset.
Arguments has_sup {R} E%Rset.
Arguments image {R S} phi E%Rset y%Rval.
Arguments nat R n%nat: simpl never.
Arguments select_set {R} P%type x%Rval y%Rval _%Rval.
Arguments select {R} P%type x%Rval y%Rval.
Arguments extended_inv {R} x%Rval.
Arguments extended_sup {R} E%Rset.

Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Reserved Notation "x ^-1" (at level 3, left associativity, format "x ^-1").

Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x != y" (at level 70, no associativity).
Reserved Notation "x == y == z"
  (at level 70, no associativity, y at next level).

Notation "x <= y" := (le x y) : real_scope.
Notation "x + y" := (add x y) : real_scope.
Notation "0" := (zero _) : real_scope.
Notation "- y" := (opp y) : real_scope.
Notation "x * y" := (mul x y) : real_scope.
Notation "1" := (one _) : real_scope.

Notation "x - y" := (x + (- y)) : real_scope.
Notation "x ^-1" := (extended_inv x) : real_scope.
Notation "x / y" := (x * y^-1) : real_scope.
Notation "2" := (1 + 1) : real_scope.
Notation "- 1" := (- (1)) : real_scope.
Notation "- 2" := (- (2)) : real_scope.
Notation "n %:R" := (nat _ n) : real_scope.

Notation "x == y" := (eq x y) : real_scope.
Notation "x != y" := (~ (x == y)) : real_scope.
Notation "x >= y" := (y <= x) (only parsing) : real_scope.
Notation "x < y" := (~ (x >= y)) : real_scope.
Notation "x > y" := (y < x) (only parsing) : real_scope.
Notation "x == y == z" := (x == y /\ y == z) : real_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z) : real_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : real_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : real_scope.
Notation "x < y < z" := (x < y /\ y < z) : real_scope.

Notation "{ x | P }" := (fun x : val _ => P : Prop) : realset_scope.
Notation "'IF' P 'then' x 'else' y" := (select P x y) : real_scope.
Notation sup := extended_sup.