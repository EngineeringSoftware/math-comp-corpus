
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint gen_dyck m n {struct n} :=
  match n, m with
  | 0, 1 => 1
  | n'.+1, m'.+1 => gen_dyck m.+1 n' + gen_dyck m' n'
  | _, _ => 0
  end.

Definition dyck := gen_dyck 1.

Lemma gen_dyck_max m n : n.+1 < m -> gen_dyck m n = 0.
Proof.
elim: n m => [|n IHn] [] //= => [[] // | m lt_n1_m].
by rewrite !IHn // 2?ltnW.
Qed.

Lemma gen_dyck_all_close m : gen_dyck m.+1 m = 1.
Proof. by elim: m => //= m ->; rewrite gen_dyck_max. Qed.

Lemma even_dyck_pos n : 0 < dyck n.*2.
Proof.
rewrite -[n.*2]addn0 /dyck; elim: n {-1}0 => [|n IHn] m.
  by rewrite gen_dyck_all_close.
by rewrite doubleS addSnnS addSn ltn_addr.
Qed.