
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier FunctionalExtensionality.
Require Import ssrR Reals_ext ssr_ext ssralg_ext logb Rbigop proba entropy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.
Local Open Scope vec_ext_scope.

Section mlog_prop.

Variables (A : finType) (P : dist A).

Lemma E_mlog : `E (--log P) = `H P.
Proof.
rewrite /entropy big_morph_oppR; apply eq_bigr=> a _; by rewrite /= mulNR mulRC.
Qed.

Definition aep_sigma2 := (\rsum_(a in A) P a * (log (P a))^2 - (`H P)^2)%R.

Lemma V_mlog : `V (--log P) = aep_sigma2.
Proof.
rewrite /Var E_trans_RV_id_rem E_mlog /aep_sigma2.
transitivity
  (\rsum_(a in A) ((- log (P a))^2 * P a - 2 * `H P * - log (P a) * P a + `H P ^ 2 * P a))%R.
  apply eq_bigr => a _.
  rewrite /scale_RV /mlog_RV /trans_add_RV /sq_RV /comp_RV /= /sub_RV /p_of; field.
rewrite big_split /= big_split /= -big_distrr /= (epmf1 P) mulR1.
rewrite (_ : \rsum_(a in A) - _ = - (2 * `H P ^ 2))%R; last first.
  rewrite -{1}big_morph_oppR; congr (- _)%R.
  rewrite [X in X = _](_ : _ =
    \rsum_(a in A) (2 * `H P) * (- (P a * log (P a))))%R; last first.
    apply eq_bigr => a _; by rewrite -!mulRA (mulRC (P a)) mulNR.
  rewrite -big_distrr [in LHS]/= -{1}big_morph_oppR.
  by rewrite -/(entropy P) -mulRA /= mulR1.
set s := (\rsum_(a in A ) _ in LHS).
rewrite [in RHS](_ : \rsum_(a in A) _ = s); last by apply eq_bigr => a _; field.
field.
Qed.

Lemma aep_sigma2_ge0 : 0 <= aep_sigma2.
Proof. rewrite -V_mlog /Var; apply Ex_ge0 => ?; exact: pow_even_ge0. Qed.

End mlog_prop.

Definition sum_mlog_prod A (P : dist A) n : {RV (P `^ n) -> R} :=
  (fun t => \rsum_(i < n) - log (P t ``_ i))%R.

Arguments sum_mlog_prod {A} _ _.

Lemma sum_mlog_prod_sum_map_mlog A (P : dist A) n :
  sum_mlog_prod P n.+1 \=sum (\row_(i < n.+1) --log P).
Proof.
elim : n => [|n IH].
- move: (@sum_n_1 A (\row_i --log P)).
  set mlogP := cast_rV1_fun_rV1 _.
  move => HmlogP.
  set mlogprodP := @sum_mlog_prod _ _ 1.
  suff -> : mlogprodP = mlogP by [].
  rewrite /mlogprodP /mlogP /sum_mlog_prod /cast_rV1_fun_rV1 /= mxE /=.
  apply functional_extensionality => ta; by rewrite big_ord_recl big_ord0 addR0.
- rewrite [X in _ \=sum X](_ : _ =
      row_mx (\row_(i < 1) (--log P)) (\row_(i < n.+1) --log P)); last first.
    apply/rowP => b; rewrite !mxE; case: splitP.
      move=> a; rewrite {a}(ord1 a) => _; by rewrite mxE.
    move=> k _; by rewrite mxE.
  apply: (sum_n_cons IH _) => /= ta.
  rewrite /sum_mlog_prod /= big_ord_recl /=; congr (_ + _)%R.
  apply eq_bigr => i _; by rewrite mxE.
Qed.

Section aep_k0_constant.

Variables (A : finType) (P : dist A).

Definition aep_bound epsilon := (aep_sigma2 P / epsilon ^ 3)%R.

Lemma aep_bound_ge0 e (_ : 0 < e) : 0 <= aep_bound e.
Proof. apply divR_ge0; [exact: aep_sigma2_ge0 | exact/pow_lt]. Qed.

Lemma aep_bound_decreasing e e' : 0 < e' <= e -> aep_bound e <= aep_bound e'.
Proof.
case=> Oe' e'e.
apply leR_wpmul2l; first exact: aep_sigma2_ge0.
apply leR_inv => //; first exact/pow_lt.
apply pow_incr => //; split; [exact/ltRW | exact/e'e ].
Qed.

End aep_k0_constant.

Section AEP.

Variables (A : finType) (P : dist A) (n : nat) (epsilon : R).
Hypothesis Hepsilon : 0 < epsilon.

Lemma aep : aep_bound P epsilon <= INR n.+1 ->
  Pr (P `^ n.+1) [set t | (0 <b P `^ n.+1 t) &&
    (`| (--log (P `^ n.+1) `/ n.+1) t - `H P | >b= epsilon) ] <= epsilon.
Proof.
move=> Hbound.
apply (@leR_trans (aep_sigma2 P / (n.+1%:R * epsilon ^ 2))); last first.
  rewrite /aep_bound in Hbound.
  apply (@leR_wpmul2r (epsilon / n.+1%:R)) in Hbound; last first.
    apply divR_ge0; [exact/ltRW/Hepsilon | exact/ltR0n].
  rewrite [in X in _ <= X]mulRCA mulRV ?INR_eq0' // ?mulR1 in Hbound.
  apply/(leR_trans _ Hbound)/Req_le; field.
  split; [by rewrite INR_eq0 | exact: gtR_eqF].
have Hsum := sum_mlog_prod_sum_map_mlog P n.
have H1 : forall k i, `E ((\row_(i < k.+1) --log P) ``_ i) = `H P.
  by move=> k i; rewrite mxE E_mlog.
have H2 : forall k i, `V ((\row_(i < k.+1) --log P) ``_ i) = aep_sigma2 P.
  by move=> k i; rewrite mxE V_mlog.
have {H1 H2} := (wlln (H1 n) (H2 n) Hsum Hepsilon).
move/(leR_trans _); apply.
apply/Pr_incl/subsetP => ta; rewrite 2!inE => /andP[H1].
rewrite /sum_mlog_prod [--log _]lock /= -lock /= /scale_RV /mlog_RV.
rewrite TupleDist.dE log_rmul_rsum_mlog //.
apply: (rprodr_gt0_inv (dist_ge0 P)).
move: H1; by rewrite TupleDist.dE => /ltRP.
Qed.

End AEP.