

From Coq Require Import Basics Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive leb a b := Leb of (a ==> b).

Lemma leb_eq a b : leb a b <-> (a -> b).
Proof. move: a b => [|] [|]; firstorder. Qed.

Instance: PreOrder leb.
Proof. split => [[|]|[|][|][|][?][?]]; try exact: Leb. Qed.

Instance: Proper (leb ==> leb ==> leb) andb.
Proof. move => [|] [|] [A] c d [B]; exact: Leb. Qed.

Instance: Proper (leb ==> leb ==> leb) orb.
Proof. move => [|] [|] [A] [|] d [B]; exact: Leb. Qed.

Instance: Proper (leb ==> impl) is_true.
Proof. move => a b []. exact: implyP. Qed.

Instance: Proper (le --> le ++> leb) leq.
Proof. move => n m /leP ? n' m' /leP ?. apply/leb_eq => ?. eauto using leq_trans. Qed.

Instance: Proper (le ==> le ==> le) addn.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_add. Qed.

Instance: Proper (le ==> le ==> le) muln.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_mul. Qed.

Instance: Proper (le ++> le --> le) subn.
Proof. move => n m /leP ? n' m' /leP ?. apply/leP. exact: leq_sub. Qed.

Instance: Proper (le ==> le) S.
Proof. move => n m /leP ?. apply/leP. by rewrite ltnS. Qed.

Program Instance: RewriteRelation le := _.
Next Obligation.
by [].
Qed.

Definition leqRW m n  : m <= n -> le m n := leP.

Lemma T1 : forall x y, x <= y -> x + 1 <= y + 1.
Proof. move => x y h. by rewrite (leqRW h). Qed.

Lemma T2 : forall x y, x <= y -> (x + 1 <= y + 1) && true.
Proof. move => x y h. by rewrite (leqRW h) andbT. Qed.