

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition excluded_middle := forall P : Prop, P \/ ~ P.

Module Real.

Record structure : Type := Structure {
   val : Type;
   set := val -> Prop;
   rel := val -> set;
   le : rel;
   sup : set -> val;
   add : val -> val -> val;
   zero : val;
   opp : val -> val;
   mul : val -> val -> val;
   one : val;
   inv : val -> val
}.

Definition eq R : rel R := fun x y => le x y /\ le y x.

Definition ub R (E : set R) : set R := fun z => forall y, E y -> le y z.

Definition down R (E : set R) : set R := fun x => exists2 y, E y & le x y.

Definition nonempty R (E : set R) : Prop := exists x, E x.
Definition has_ub R (E : set R) : Prop := nonempty (ub E).
Definition has_sup R (E : set R) : Prop := nonempty E /\ has_ub E.

Record axioms R : Prop := Axioms {
  le_reflexive (x : val R) :
    le x x;
  le_transitive (x y z : val R) :
    le x y -> le y z -> le x z;
  sup_upper_bound (E : set R) :
    has_sup E -> ub E (sup E);
  sup_total (E : set R) (x : val R) :
    has_sup E -> down E x \/ le (sup E) x;
  add_monotone (x y z : val R) :
    le y z -> le (add x y) (add x z);
  add_commutative (x y : val R) :
    eq (add x y) (add y x);
  add_associative (x y z : val R) :
    eq (add x (add y z)) (add (add x y) z);
  add_zero_left (x : val R) :
    eq (add (zero R) x) x;
  add_opposite_right (x : val R) :
    eq (add x (opp x)) (zero R);
  mul_monotone x y z :
    le (zero R) x -> le y z -> le (mul x y) (mul x z);
  mul_commutative (x y : val R) :
    eq (mul x y) (mul y x);
  mul_associative (x y z : val R) :
    eq (mul x (mul y z)) (mul (mul x y) z);
  mul_distributive_right (x y z : val R) :
    eq (mul x (add y z)) (add (mul x y) (mul x z));
  mul_one_left (x : val R) :
    eq (mul (one R) x) x;
  mul_inverse_right (x : val R) :
    ~ eq x (zero R) -> eq (mul x (inv x)) (one R);
  one_nonzero : ~ eq (one R) (zero R)
}.

Record model : Type := Model {
  model_structure : structure;
  model_axioms : axioms model_structure
}.

Definition image R S (phi : val R -> val S) (E : set R) (y : val S) :=
  exists2 x, E x & eq y (phi x).

Record morphism R S (phi : val R -> val S) : Prop := Morphism {
  morph_le x y :
   le (phi x) (phi y) <-> le x y;
  morph_sup (E : set R) :
   has_sup E -> eq (phi (sup E)) (sup (image phi E));
  morph_add x y :
   eq (phi (add x y)) (add (phi x) (phi y));
  morph_zero :
   eq (phi (zero R)) (zero S);
  morph_opp x :
   eq (phi (opp x)) (opp (phi x));
  morph_mul x y :
   eq (phi (mul x y)) (mul (phi x) (phi y));
  morph_one :
   eq (phi (one R)) (one S);
  morph_inv x :
   ~ eq x (zero R) -> eq (phi (inv x)) (inv (phi x))
}.

Notation lt x y := (~ le y x).

Fixpoint nat R (n : Datatypes.nat) := match n with
  | 0 => zero R
  | 1 => one R
  | Datatypes.S n1 => add (nat R n1) (one R)
  end.

Definition select_set R P x y : set R := fun z => IF P then eq z x else eq z y.

Definition select R P x y : val R := sup (select_set P x y).

Definition extended_inv R x : val R := select (eq x (zero R)) x (inv x).

Definition extended_sup R E : val R := select (has_sup E) (sup E) (zero R).

End Real.

Module RealCoercions.

Import Real.
Coercion val : structure >-> Sortclass.
Identity Coercion in_set : set >-> Funclass.
Identity Coercion in_rel : rel >-> Funclass.
Coercion model_structure : model >-> structure.
Coercion model_axioms : model >-> axioms.

End RealCoercions.