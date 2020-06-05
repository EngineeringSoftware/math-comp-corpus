

From Coq Require Import ssreflect ssrfun Eqdep ClassicalFacts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom pext : forall p1 p2 : Prop, (p1 <-> p2) -> p1 = p2.
Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x),
               (forall x, f1 x = f2 x) -> f1 = f2.

Lemma pf_irr (P : Prop) (p1 p2 : P) : p1 = p2.
Proof. by apply/ext_prop_dep_proof_irrel_cic/pext. Qed.

Lemma eta A (B : A -> Type) (f : forall x, B x) : f = [eta f].
Proof. by apply: fext. Qed.

Lemma sval_inj A P : injective (@sval A P).
Proof.
move=>[x Hx][y Hy] /= H; move: Hx Hy; rewrite H=>*.
congr exist; apply: pf_irr.
Qed.

Lemma svalE A (P : A -> Prop) x H : sval (exist P x H) = x.
Proof. by []. Qed.

Lemma compf1 A B (f : A -> B) : f = f \o id.
Proof. by apply: fext. Qed.

Lemma comp1f A B (f : A -> B) : f = id \o f.
Proof. by apply: fext. Qed.

Section Cast.
Variable (C : Type) (interp : C -> Type).

Definition cast A B (pf : A = B) (v : interp B) : interp A :=
  ecast _ _ (esym pf) v.

Lemma eqc A (pf : A = A) (v : interp A) : cast pf v = v.
Proof. by move: pf; apply: Streicher_K. Qed.

Definition jmeq A B (v : interp A) (w : interp B) := forall pf, v = cast pf w.

Lemma jmrefl A (v : interp A) : jmeq v v.
Proof. by move=>pf; rewrite eqc. Qed.

Lemma jmsym A B (v : interp A) (w : interp B) : jmeq v w -> jmeq w v.
Proof.
move=> H pf; rewrite (H (esym pf)).
by move: (pf); rewrite pf in w H * => {pf}-pf; rewrite !eqc.
Qed.

Lemma jmE A (v w : interp A) : jmeq v w <-> v = w.
Proof. by split=>[/(_ erefl) //|->]; apply: jmrefl. Qed.

Lemma castE A B (pf1 pf2 : A = B) (v1 v2 : interp B) :
        v1 = v2 <-> cast pf1 v1 = cast pf2 v2.
Proof. by move: (pf1) pf2; rewrite pf1 =>*; rewrite !eqc. Qed.

End Cast.

Arguments cast {C} interp [A][B] pf v.
Arguments jmeq {C} interp [A][B] v w.
Hint Resolve jmrefl : core.
Notation icast pf v := (@cast _ id _ _ pf v).
Notation ijmeq v w := (@jmeq _ id _ _ v w).

Section Dynamic.
Variables (A : Type) (P : A -> Type).

Definition dynamic := sigT P.
Definition dyn := existT P.
Definition dyn_tp := @projT1 _ P.
Definition dyn_val := @projT2 _ P.
Definition dyn_eta := @sigT_eta _ P.
Definition dyn_injT := @eq_sigT_fst _ P.
Definition dyn_inj := @inj_pair2 _ P.

End Dynamic.

Prenex Implicits dyn_tp dyn_val dyn_injT dyn_inj.
Arguments dyn {C} interp {A} _ : rename.
Notation idyn v := (@dyn _ id _ v).

Lemma dynE (A B : Type) interp (pf : A = B) (v : interp A) (w : interp B) :
        jmeq interp v w <-> dyn interp v = dyn interp w.
Proof. by rewrite -pf in w *; rewrite jmE; split => [->|/dyn_inj]. Qed.