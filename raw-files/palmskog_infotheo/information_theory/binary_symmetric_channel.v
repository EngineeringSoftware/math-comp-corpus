
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg perm zmodp matrix.
Require Import Reals Lra.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import entropy binary_entropy_function channel hamming channel_code.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope channel_scope.
Local Open Scope R_scope.

Module BSC.
Section BSC_sect.

Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Variable p : prob.

Definition c : `Ch_1(A, A) := Binary.d card_A p.

End BSC_sect.
End BSC.

Lemma closed p : 0 < p < 1 -> 0 <= p <= 1.
Proof. case => ?; split; by apply Rlt_le. Qed.

Local Open Scope channel_scope.
Local Open Scope entropy_scope.

Section bsc_capacity_proof.

Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Variable P : dist A.
Variable p : R.
Hypothesis p_01' : (0 < p < 1)%R.

Let p_01 : prob := Prob.mk (closed p_01').

Lemma HP_HPW : `H P - `H(P, BSC.c card_A p_01) = - H2 p.
Proof.
rewrite {2}/entropy /=.
rewrite (eq_bigr (fun a => (`J( P, (BSC.c card_A p_01))) (a.1, a.2) *
  log ((`J( P, (BSC.c card_A p_01))) (a.1, a.2)))); last by case.
rewrite -(pair_big xpredT xpredT (fun a b => (`J( P, (BSC.c card_A p_01)))
  (a, b) * log ((`J( P, (BSC.c card_A p_01))) (a, b)))) /=.
rewrite {1}/entropy .
set a := \rsum_(_ in _) _. set b := \rsum_(_ <- _) _.
apply trans_eq with (- (a + (-1) * b)); first by field.
rewrite /b {b} big_distrr /= /a {a} -big_split /=.
rewrite !Set2sumE /= !JointDistChan.dE /BSC.c !Binary.dE /=.
rewrite !/Binary.f !eqxx /Binary.f eq_sym !(negbTE (Set2.a_neq_b card_A)) /H2.
set a := Set2.a _. set b := Set2.b _.
case: (Req_EM_T (P a) 0) => H1.
  rewrite H1 !(mul0R, mulR0, addR0, add0R).
  move: (epmf1 P); rewrite Set2sumE /= -/a -/b.
  rewrite H1 add0R => ->.
  rewrite /log Log_1 !(mul0R, mulR0, addR0, add0R, mul1R, mulR1); field.
rewrite /log LogM; last 2 first.
  rewrite -dist_gt0; exact/eqP.
  case: p_01' => ? ?; lra.
rewrite /log LogM; last 2 first.
  rewrite -dist_gt0; exact/eqP.
  by case: p_01'.
case: (Req_EM_T (P b) 0) => H2.
  rewrite H2 !(mul0R, mulR0, addR0, add0R).
  move: (epmf1 P); rewrite Set2sumE /= -/a -/b.
  rewrite H2 addR0 => ->.
  rewrite /log Log_1 !(mul0R, mulR0, addR0, add0R, mul1R, mulR1); field.
rewrite /log LogM; last 2 first.
  rewrite -dist_gt0; exact/eqP.
  by case: p_01'.
rewrite /log LogM; last 2 first.
  rewrite -dist_gt0; exact/eqP.
  rewrite subR_gt0; by case: p_01'.
transitivity (p * (P a + P b) * log p + (1 - p) * (P a + P b) * log (1 - p) ).
  rewrite /log; by field.
move: (epmf1 P); rewrite Set2sumE /= -/a -/b => ->; rewrite /log; by field.
Qed.

Lemma IPW : `I(P, BSC.c card_A p_01) = `H(P `o BSC.c card_A p_01) - H2 p.
Proof.
rewrite /MutualInfoChan.mut_info addRC.
set a := `H(_ `o _).
apply trans_eq with (a + (`H P - `H(P , BSC.c card_A p_01))); first by field.
by rewrite HP_HPW.
Qed.

Lemma H_out_max : `H(P `o BSC.c card_A p_01) <= 1.
Proof.
rewrite {1}/entropy /= Set2sumE /= !OutDist.dE 2!Set2sumE /=.
set a := Set2.a _. set b := Set2.b _.
rewrite /BSC.c !Binary.dE !eqxx /= !(eq_sym _ a).
rewrite (negbTE (Set2.a_neq_b card_A)).
move: (epmf1 P); rewrite Set2sumE /= -/a -/b => P1.
have -> : p * P a + (1 - p) * P b = 1 - ((1 - p) * P a + p * P b).
  rewrite -{2}P1; by field.
have H01 : 0 < ((1 - p) * P a + p * P b) < 1.
  move: (dist_ge0 P a) => H1.
  move: (dist_max P b) => H4.
  move: (dist_max P a) => H3.
  case: p_01' => Hp1 Hp2.
  split.
    case/Rle_lt_or_eq_dec : H1 => H1.
    - apply addR_gt0wl; by [apply mulR_gt0; lra | apply mulR_ge0; lra].
    - by rewrite -H1 mulR0 add0R (_ : P b = 1) ?mulR1 // -P1 -H1 add0R.
  rewrite -{2}P1.
  case: (Req_EM_T (P a) 0) => Hi.
    rewrite Hi mulR0 !add0R.
    rewrite Hi add0R in P1.
    by rewrite P1 mulR1.
  case: (Req_EM_T (P b) 0) => Hj.
    rewrite Hj addR0 in P1.
    rewrite Hj mulR0 !addR0 P1 mulR1.
    lra.
  case/Rle_lt_or_eq_dec : H1 => H1.
  - apply leR_lt_add.
    + rewrite -{2}(mul1R (P a)); apply leR_wpmul2r; lra.
    + rewrite -{2}(mul1R (P b)); apply ltR_pmul2r => //.
      apply/ltRP; rewrite lt0R; apply/andP; split; [exact/eqP|exact/leRP/dist_ge0].
  - rewrite -H1 mulR0 2!add0R.
    have -> : P b = 1 by rewrite -P1 -H1 add0R.
    by rewrite mulR1.
rewrite (_ : forall a b, - (a + b) = - a - b); last by move=> *; field.
rewrite -mulNR.
set q := (1 - p) * P a + p * P b.
apply: (@leR_trans (H2 q)); last exact: H2_max.
rewrite /H2 !mulNR; apply Req_le; field.
Qed.

Lemma bsc_out_H_half' : 0 < INR 1 / INR 2 < 1.
Proof. rewrite /= (_ : INR 1 = 1) // (_ : INR 2 = 2) //; lra. Qed.

Lemma H_out_binary_uniform : `H(Uniform.d card_A `o BSC.c card_A p_01) = 1.
Proof.
rewrite {1}/entropy !Set2sumE /= !OutDist.dE !Set2sumE /=.
rewrite /BSC.c !Binary.dE !eqxx (eq_sym _ (Set2.a _)) !Uniform.dE.
rewrite (negbTE (Set2.a_neq_b card_A)).
rewrite -!mulRDl (_ : 1 - p + p = 1); last by field.
rewrite mul1R (_ : p + (1 - p) = 1); last by field.
rewrite mul1R -!mulRDl card_A /= (_ : INR 2 = 2) // /log LogV; last lra.
rewrite Log_n //=; field.
Qed.

End bsc_capacity_proof.

Section bsc_capacity_theorem.

Variable A : finType.
Hypothesis card_A : #|A| = 2%nat.
Variable p : R.
Hypothesis p_01' : 0 < p < 1.
Let p_01 := Prob.mk (closed p_01').

Theorem BSC_capacity : capacity (BSC.c card_A p_01) (1 - H2 p).
Proof.
rewrite /capacity; split.
- move=> d.
  move: (@IPW _ card_A d _ p_01') => tmp.
  suff : `H(d `o BSC.c card_A p_01) <= 1.
    move=> ?.
    unfold p_01 in *.
    lra.
  exact: H_out_max.
- move=> d Hd.
  move: (@IPW _ card_A (Uniform.d card_A) _ p_01').
  rewrite H_out_binary_uniform => <-.
  exact: Hd.
Qed.

End bsc_capacity_theorem.

Section dH_BSC.

Variable p : prob.

Let card_F2 : #| 'F_2 | = 2%nat. by rewrite card_Fp. Qed.

Let W := BSC.c card_F2 p.

Variables (M : finType) (n : nat) (f : encT [finType of 'F_2] M n).

Local Open Scope vec_ext_scope.

Lemma DMC_BSC_prop : forall m y,
  let d := dH y (f m) in
  W ``(y | f m) = ((1 - p) ^ (n - d) * p ^ d)%R.
Proof.
move=> m y d; rewrite DMCE.
transitivity ((\rprod_(i < n | (f m) ``_ i == y ``_ i) (1 - p)) *
              (\rprod_(i < n | (f m) ``_ i != y ``_ i) p))%R.
  rewrite (bigID [pred i | (f m) ``_ i == y ``_ i]) /=; congr (_ * _).
    by apply eq_bigr => // i /eqP ->; rewrite /BSC.c Binary.dE eqxx.
  apply eq_bigr => //= i /negbTE Hyi; by rewrite /BSC.c Binary.dE eq_sym Hyi.
congr (_ * _).
by rewrite big_const /= iter_mulR /= card_dHC.
by rewrite big_const /= iter_mulR /= card_dH_vec.
Qed.

End dH_BSC.