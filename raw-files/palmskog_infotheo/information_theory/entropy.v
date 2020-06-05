
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun bigop.
From mathcomp Require Import matrix.
Require Import Reals Lra.
Require Import ssrR Reals_ext ssralg_ext Rbigop bigop_ext logb ln_facts.
Require Import proba divergence.

Reserved Notation "'`H'" (at level 5).

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.

Section entropy_definition.

Variables (A : finType) (P : dist A).

Definition entropy := - \rsum_(a in A) P a * log (P a).
Local Notation "'`H'" := (entropy).

Lemma entropy_ge0 : 0 <= `H.
Proof.
rewrite /entropy big_endo ?oppR0 //; last by move=> *; rewrite oppRD.
rewrite (_ : \rsum_(_ in _) _ = \rsum_(i in A | predT A) - (P i * log (P i))); last first.
  apply eq_bigl => i /=; by rewrite inE.
apply rsumr_ge0 => i _.
case/boolP : (P i == 0) => [/eqP ->|Hi].
  rewrite mul0R oppR0; exact/leRR.
rewrite mulRC -mulNR.
apply mulR_ge0; last exact: dist_ge0.
apply oppR_ge0.
rewrite /log -(Log_1 2).
apply Log_increasing_le => //; last exact: dist_max.
apply/ltRP; rewrite lt0R Hi; exact/leRP/dist_ge0.
Qed.

Hypothesis P_pos : forall b, 0 < P b.

Lemma entropy_pos_P_pos : 0 <= `H.
Proof.
rewrite /entropy big_endo ?oppR0 //; last by move=> *; rewrite oppRD.
rewrite (_ : \rsum_(_ in _) _ = \rsum_(i in A | predT A) - (P i * log (P i))).
  apply rsumr_ge0 => i _.
  rewrite mulRC -mulNR.
  apply mulR_ge0; last exact: dist_ge0.
  apply oppR_ge0.
  rewrite /log -(Log_1 2).
  apply Log_increasing_le => //; by [by apply P_pos | exact: dist_max].
apply eq_bigl => i /=; by rewrite inE.
Qed.

End entropy_definition.

Notation "'`H'" := (entropy) : entropy_scope.

Local Open Scope entropy_scope.
Local Open Scope proba_scope.

Lemma entropy_Ex {A} (P : dist A) : `H P = `E (--log P).
Proof.
rewrite /entropy /mlog_RV /= big_morph_oppR.
apply eq_bigr => a _; by rewrite mulRC -mulNR.
Qed.

Lemma xlnx_entropy {A} (P : dist A) :
  `H P = / ln 2 * - \rsum_(a : A) xlnx (P a).
Proof.
rewrite /entropy mulRN; f_equal.
rewrite (big_morph _ (morph_mulRDr _) (mulR0 _)).
apply eq_bigr => a _ ;rewrite /log /Rdiv mulRA mulRC; f_equal.
rewrite /xlnx; case : ifP => // /ltRP Hcase.
have : P a = 0; last by move=> ->; rewrite mul0R.
case (Rle_lt_or_eq_dec 0 (P a)) => //; exact: dist_ge0.
Qed.

Lemma entropy_uniform {A : finType} n (HA : #|A| = n.+1) :
  `H (Uniform.d HA) = log (INR #|A|).
Proof.
rewrite /entropy (eq_bigr (fun a => / INR #|A| * log (/INR #|A|))); last first.
  by move=> a _; rewrite Uniform.dE.
rewrite big_const iter_addR mulRA mulRV; last by rewrite INR_eq0' HA.
rewrite mul1R /log LogV ?oppRK //; by rewrite HA; apply/ltR0n.
Qed.

Local Open Scope reals_ext_scope.

Lemma entropy_max (A : finType) (P : dist A) : `H P <= log (INR #|A|).
Proof.
have [n HA] : exists n, #|A| = n.+1.
  exists (#|A|.-1); rewrite prednK //; exact: (dist_domain_not_empty P).
have /div_ge0 H : P << (Uniform.d HA) by apply dom_by_uniform.
rewrite -subR_ge0; apply/(leR_trans H)/Req_le.
transitivity (\rsum_(a|a \in A) P a * log (P a) +
              \rsum_(a|a \in A) P a * - log ((Uniform.d HA) a)).
  rewrite -big_split /=; apply eq_bigr => a _; rewrite -mulRDr.
  case/boolP : (P a == 0) => [/eqP ->|H0]; first by rewrite !mul0R.
  congr (_ * _); rewrite logDiv ?addR_opp //.
  by rewrite -dist_gt0.
  rewrite Uniform.dE; apply/invR_gt0; rewrite HA; exact/ltR0n.
rewrite [in X in _ + X](eq_bigr (fun a => P a * - log (/ INR #|A|))); last first.
  by move=> a _; rewrite Uniform.dE.
rewrite -[in X in _ + X = _]big_distrl /= epmf1 mul1R.
rewrite addRC /entropy /log LogV ?oppRK ?subR_opp // HA; exact/ltR0n.
Qed.

Lemma entropy_from_bivar (A : finType) n (P : {dist A * 'rV[A]_n}) :
  `H (Multivar.from_bivar P) = `H P.
Proof.
rewrite /entropy /=; congr (- _).
rewrite -(big_rV_cons_behead _ xpredT xpredT) /= pair_bigA /=.
apply eq_bigr => -[a b] _ /=.
by rewrite Multivar.from_bivarE /= row_mx_row_ord0 rbehead_row_mx.
Qed.

Lemma entropy_to_bivar (A : finType) n (P : {dist 'rV[A]_n.+1}) :
  `H (Multivar.to_bivar P) = `H P.
Proof.
rewrite /entropy /=; congr (- _).
rewrite -(big_rV_cons_behead _ xpredT xpredT) /= pair_bigA /=.
apply eq_bigr => -[a b] _ /=; by rewrite Multivar.to_bivarE /=.
Qed.