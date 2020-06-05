
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Lra.
Require Import Reals_ext ssrR logb Rbigop proba channel.

Reserved Notation "e( W , c )" (at level 50).
Reserved Notation "echa( W , c )" (at level 50).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope channel_scope.
Local Open Scope R_scope.

Section code_definition.

Variables A B M : finType.
Variable n : nat.

Local Open Scope ring_scope.

Definition encT := {ffun M -> 'rV[A]_n}.
Definition decT := {ffun 'rV[B]_n -> option M}.

Record code := mkCode { enc : encT ; dec : decT }.

Definition CodeRate (c : code) := (log (INR #| M |) / INR n)%R.

Definition preimC (phi : decT) m := ~: (phi @^-1: xpred1 (Some m)).

Definition ErrRateCond (W : `Ch_1(A, B)) c m :=
  Pr (W ``(| enc c m)) (preimC (dec c) m).

Local Notation "e( W , c )" := (ErrRateCond W c) (at level 50).

Definition CodeErrRate (W : `Ch_1(A, B)) c :=
  (1 / INR #| M | * \rsum_(m in M) e(W, c) m)%R.

Local Notation "echa( W , c )" := (CodeErrRate W c) (at level 50).

Lemma echa_ge0 (HM : (0 < #| M |)%nat) W (c : code) : 0 <= echa(W , c).
Proof.
apply mulR_ge0.
- apply divR_ge0; [lra | exact/ltR0n].
- apply: rsumr_ge0 => ? _; apply: rsumr_ge0 => ? _; exact: DMC_ge0.
Qed.

Lemma echa1 (HM : (0 < #| M |)%nat) W (c : code) : echa(W , c) <= 1.
Proof.
rewrite /CodeErrRate div1R.
apply (@leR_pmul2l (INR #|M|)); first exact/ltR0n.
rewrite mulRA mulRV ?INR_eq0' -?lt0n // mul1R -iter_addR -big_const.
apply: ler_rsum => m _; exact: Pr_1.
Qed.

End code_definition.

Notation "e( W , c )" := (ErrRateCond W c) : channel_code_scope.
Notation "echa( W , c )" := (CodeErrRate W c) : channel_code_scope.

Record CodeRateType := mkCodeRateType {
  rate :> R ;
  _ : exists n d, (0 < n)%nat /\ (0 < d)%nat /\ rate = log (INR n) / INR d }.