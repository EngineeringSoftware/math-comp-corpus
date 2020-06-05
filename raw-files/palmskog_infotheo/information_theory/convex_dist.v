
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import choice fintype finfun bigop prime binomial ssralg.
From mathcomp Require Import finset fingroup finalg matrix.
Require Import Reals Fourier Ranalysis_ext Lra.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop proba.
Require Import entropy proba cproba convex binary_entropy_function.
Require Import log_sum divergence.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope convex_scope.

Local Open Scope entropy_scope.

Section entropy_log_div.
Variables (A : finType) (p : dist A) (n : nat) (A_not_empty : #|A| = n.+1).
Let u := Uniform.d A_not_empty.

Local Open Scope divergence_scope.

Lemma entropy_log_div : entropy p = log #|A|%:R - D(p || u).
Proof.
rewrite /entropy /div.
evar (RHS : A -> R).
have H : forall a : A, p a * log (p a / u a) = RHS a.
  move => a.
  move : (pos_ff_ge0 (pmf p) a) => [H|H].
  - rewrite Uniform.dE.
    change (p a * log (p a / / #|A|%:R)) with (p a * log (p a * / / #|A|%:R)).
    have H0 : 0 < #|A|%:R by rewrite A_not_empty ltR0n.
    have H1 : #|A|%:R <> 0 by apply gtR_eqF.
    rewrite invRK // logM // mulRDr.
    by instantiate (RHS := fun a => p a * log (p a) + p a * log #|A|%:R).
  - by rewrite /RHS -H /= 3!mul0R add0R.
have H0 : \rsum_(a in A) p a * log (p a / u a) = \rsum_(a in A) RHS a.
  move : H; rewrite /RHS => H.
  exact: eq_bigr.
rewrite H0 /RHS.
rewrite big_split /=.
rewrite -big_distrl /=.
rewrite (epmf1 p) mul1R.
by rewrite -addR_opp oppRD addRC -addRA Rplus_opp_l addR0.
Qed.
End entropy_log_div.

Module DominatedPair.
Section def.
Variable (A : finType).
Definition T := {d : dist A * dist A | d.1 << d.2}.
Lemma avg_dominates_compatible (a b c d : dist A) t : a << b -> c << d -> (a <|t|> c) << (b <|t|> d).
Proof.
rewrite !dominatesP => Hab Hcd i.
rewrite /Conv/= !Conv2Dist.dE.
rewrite paddR_eq0; [|apply mulR_ge0;[exact:prob_ge0|exact:dist_ge0]|apply mulR_ge0;[exact:prob_ge0|exact:dist_ge0]].
rewrite !mulR_eq0.
case; case.
- move->; case; first by rewrite onem0=>H; have : 1 <> 0 by lra; move /(_ H).
  by move/Hcd->; rewrite mul0R mulR0 addR0.
move/Hab->.
rewrite mulR0 onem_eq0 add0R.
case.
- by move->; rewrite onem1 mul0R.
by move/Hcd->; rewrite mulR0.
Qed.
Definition avg (x y : T) (t : prob) : T:=
  let ab := proj1_sig x in
  let Hab := proj2_sig x in
  let cd := proj1_sig y in
  let Hcd := proj2_sig y in
  exist _ (ab <|t|> cd) (avg_dominates_compatible t Hab Hcd).
Definition simple_elim (U : Type) (f : dist A -> dist A -> U) (x : T) := f (sval x).1 (sval x).2.
End def.

Section proof_irrelevance.
Lemma eq_sig_irrelevant {A : Type} (P : A -> Prop) (u1 v1 : A) (u2 : P u1) (v2 : P v1) (p : u1 = v1) : exist P u1 u2 = exist P v1 v2.
have p' : sval (exist P u1 u2) = sval (exist P v1 v2) by exact p.
apply (eq_sig _ _ p').
exact: ProofIrrelevance.proof_irrelevance.
Qed.
End proof_irrelevance.

Section prop.
Variable (A : finType).
Let T := T A.
Lemma avg1 (x y : T) : avg x y (`Pr 1) = x.
Proof.
  rewrite /avg; case x => x0 H /=.
  apply eq_sig_irrelevant.
  exact: conv1.
Qed.
Lemma avgI (x : T) (p : prob) : avg x x p = x.
Proof.
  rewrite /avg; case x => x0 H /=.
  apply eq_sig_irrelevant.
  exact: convmm.
Qed.
Lemma avgC (x y : T) (p : prob) : avg x y p = avg y x `Pr p.~.
Proof.
rewrite /avg; apply eq_sig_irrelevant.
exact: convC.
Qed.
Lemma avgA (p q : prob) (d0 d1 d2 : T) :
  avg d0 (avg d1 d2 q) p = avg (avg d0 d1 [r_of p, q]) d2 [s_of p, q].
Proof.
rewrite /avg /=; apply eq_sig_irrelevant.
exact: convA.
Qed.
End prop.
End DominatedPair.

Section dominated_pair_convex_space.
Import DominatedPair.
Variable (A : finType).
Definition dominatedPairConvMixin := ConvexSpace.Class
  (@avg1 A) (@avgI A) (@avgC A) (@avgA A).
Canonical dominatedPairConvType := ConvexSpace.Pack dominatedPairConvMixin.
End dominated_pair_convex_space.

Section divergence_convex.
Variables (A : finType) (n : nat) (A_not_empty : #|A| = n.+1).

Local Open Scope divergence_scope.

Lemma div_convex : convex_function (DominatedPair.simple_elim (@div A)).
Proof.
rewrite /ConvexFunction.axiom => [] [[p1 q1] /= pq1] [[p2 q2] /= pq2] t.
rewrite /DominatedPair.simple_elim /=.
rewrite /Conv /= /avg /=.
rewrite 2!big_distrr /= -big_split /= /div.
rewrite rsum_setT [in X in _ <= X]rsum_setT.
apply ler_rsum => a _.
rewrite 2!Conv2Dist.dE.
case/boolP : (q2 a == 0) => [|] q2a0.
  rewrite (eqP q2a0) !(mul0R,mulR0,add0R).
  have p2a0 : p2 a == 0.
    apply/eqP.
    move/dominatesP in pq2.
    exact/pq2/eqP.
  rewrite (eqP p2a0) !(mulR0,addR0,mul0R).
  case/boolP : (q1 a == 0) => [|] q1a0.
    have p1a0 : p1 a == 0.
      apply/eqP.
      move/dominatesP in pq1.
      exact/pq1/eqP.
    rewrite (eqP p1a0) !(mulR0,mul0R); exact/leRR.
  case/boolP : (t == `Pr 0) => [/eqP /=|] t0.
    rewrite t0 !mul0R; exact/leRR.
  apply/Req_le.
  rewrite mulRA; congr (_ * _ * log _).
  field.
  split; exact/eqP.
case/boolP : (q1 a == 0) => [|] q1a0.
  rewrite (eqP q1a0) !(mul0R,mulR0,add0R).
  have p1a0 : p1 a == 0.
    apply/eqP.
    move/dominatesP in pq1.
    exact/pq1/eqP.
  rewrite (eqP p1a0) !(mulR0,addR0,mul0R,add0R).
  case/boolP : (t.~ == 0) => [/eqP ->|t0].
    rewrite !mul0R; exact/leRR.
  apply/Req_le.
  rewrite mulRA; congr (_ * _ * log _).
  field.
  split; exact/eqP.
set h : dist A -> dist A -> {ffun 'I_2 -> R} := fun p1 p2 => [ffun i => [eta (fun=> 0) with
  ord0 |-> t * p1 a, lift ord0 ord0 |-> t.~ * p2 a] i].
have hdom : ((h p1 p2) << (h q1 q2)).
  apply/dominatesP => i.
  rewrite /h /= !ffunE; case: ifPn => _.
  rewrite mulR_eq0 => -[->|/eqP].
  by rewrite mul0R.
  by rewrite (negbTE q1a0).
  case: ifPn => // _.
  rewrite mulR_eq0 => -[->|/eqP].
  by rewrite mul0R.
  by rewrite (negbTE q2a0).
set f : 'I_2 -> R := h p1 p2.
set g : 'I_2 -> R := h q1 q2.
have h0 : forall p1 p2, [forall i, 0 <b= h p1 p2 i].
  move=> p1' p2'; apply/forallP_leRP => ?; rewrite /h /= ffunE.
  case: ifPn => [_ | _]; first by apply mulR_ge0; [exact/prob_ge0|exact/dist_ge0].
  case: ifPn => [_ |  _]; [|exact/leRR].
  apply/mulR_ge0; [apply/onem_ge0; exact/prob_le1|exact/dist_ge0].
move: (@log_sum _ setT (mkPosFfun (h0 p1 p2)) (mkPosFfun (h0 q1 q2)) hdom).
rewrite /=.
have rsum_setT' : forall (f : 'I_2 -> R),
  \rsum_(i < 2) f i = \rsum_(i in [set: 'I_2]) f i.
  move=> f0; by apply eq_bigl => i; rewrite inE.
rewrite -!rsum_setT' !big_ord_recl !big_ord0 !addR0.
rewrite /h /= !ffunE; move/leR_trans; apply.
apply/Req_le; congr (_ + _).
  case/boolP : (t == `Pr 0) => [/eqP ->|t0]; first by rewrite !mul0R.
  rewrite mulRA; congr (_ * _ * log _).
  rewrite !eqxx.
  field.
  split; exact/eqP.
case/boolP : (t.~ == 0) => [/eqP ->|t1]; first by rewrite !mul0R.
rewrite mulRA; congr (_ * _ * log _).
rewrite /=.
field.
split; exact/eqP.
Qed.

Lemma div_convex' : forall (p1 p2 q1 q2 : dist A) (t : prob),
  p1 << q1 -> p2 << q2 ->
  div (p1 <| t |> p2) (q1 <| t |> q2) <= div p1 q1 <| t |> div p2 q2.
Proof.
move => p1 p2 q1 q2 t pq1 pq2.
move:div_convex.
rewrite/ConvexFunction.axiom/convex_function_at/DominatedPair.simple_elim/=.
move/(_ (exist _ (p1,q1) pq1) (exist _ (p2,q2) pq2))=>/=.
by apply.
Qed.
End divergence_convex.

Section entropy_concave.
Variable (A : finType).
Hypothesis A_not_empty : (0 < #|A|)%nat.
Let A_not_empty' : #|A| = #|A|.-1.+1.
Proof. by rewrite prednK. Qed.
Let u : {dist A} := Uniform.d A_not_empty'.

Local Open Scope divergence_scope.

Lemma entropy_concave : concave_function (fun P : dist A => `H P).
Proof.
apply R_concave_functionN' => p q t; rewrite /convex_function_at.
rewrite !(entropy_log_div _ A_not_empty') /=.
rewrite /Leconv /= [in X in _ <= X]/Conv /= /avg /=.
rewrite oppRD oppRK 2!mulRN mulRDr mulRN mulRDr mulRN oppRD oppRK oppRD oppRK.
rewrite addRCA !addRA -2!mulRN -mulRDl (addRC _ t) onemKC mul1R -addRA leR_add2l.
move: (div_convex' t (dom_by_uniform p A_not_empty') (dom_by_uniform q A_not_empty')).
by rewrite convmm.
Qed.

End entropy_concave.

Module entropy_concave_alternative_proof_binary_case.

Lemma pderivable_H2 : pderivable H2 (CSet.car open_unit_interval).
Proof.
move=> x /= [Hx0 Hx1].
apply derivable_pt_plus.
apply derivable_pt_opp.
apply derivable_pt_mult; [apply derivable_pt_id|apply derivable_pt_Log].
assumption.
apply derivable_pt_opp.
apply derivable_pt_mult.
apply derivable_pt_Rminus.
apply derivable_pt_comp.
apply derivable_pt_Rminus.
apply derivable_pt_Log.
lra.
Defined.

Lemma expand_interval_closed_to_open a b c d :
  a < b -> b < c -> c < d -> forall x, b <= x <= c -> a < x < d.
Proof.
  move => Hab Hbc Hcd x [Hbx Hxc].
  by apply conj; [eapply Rlt_le_trans|eapply Rle_lt_trans]; [exact Hab|exact Hbx|exact Hxc|exact Hcd].
Qed.

Lemma expand_internal_closed_to_closed a b c d :
  a <= b -> b < c -> c <= d -> forall x, b <= x <= c -> a <= x <= d.
Proof.
  move => Hab Hbc Hcd x [Hbx Hxc].
  by apply conj; [eapply Rle_trans|eapply Rle_trans]; [exact Hab|exact Hbx|exact Hxc|exact Hcd].
Qed.

Lemma expand_interval_open_to_open a b c d :
  a < b -> b < c -> c < d -> forall x, b < x < c -> a < x < d.
Proof.
  move => Hab Hbc Hcd x [Hbx Hxc].
  by apply conj; [eapply Rlt_trans|eapply Rlt_trans]; [exact Hab|exact Hbx|exact Hxc|exact Hcd].
Qed.

Lemma expand_interval_open_to_closed a b c d :
  a <= b -> b < c -> c <= d -> forall x, b < x < c -> a <= x <= d.
Proof.
  move => Hab Hbc Hcd x [Hbx Hxc].
  by apply conj; [eapply Rle_trans|eapply Rle_trans]; [exact Hab|apply or_introl; exact Hbx|apply or_introl; exact Hxc|exact Hcd].
Qed.

Lemma concavity_of_entropy_x_le_y x y (t : prob) :
  x \in open_unit_interval -> y \in open_unit_interval -> x < y ->
  concave_function_at H2 x y t.
Proof.
rewrite !classical_sets.in_setE => -[H0x Hx1] [H0y Hy1] Hxy.
apply R_concave_function_atN'.
set Df := fun z : R => log z - log (1 - z).
have @f_derive : pderivable (fun x0 => - H2 x0) (fun z => x <= z <= y).
  move => z Hz.
  exact/derivable_pt_opp/pderivable_H2/(@expand_interval_closed_to_open 0 x y 1).
have @derive_pt_f : forall z (Hz : x <= z <= y),
  Df z = derive_pt (fun x1 => - H2 x1) _ (f_derive _ Hz).
  move => z Hz.
  rewrite derive_pt_opp.
  set H := expand_interval_closed_to_open _ _ _ _.
  rewrite /pderivable_H2.
  case H => [H0z Hz1].
  rewrite derive_pt_plus.
  rewrite 2!derive_pt_opp.
  rewrite 2!derive_pt_mult.
  rewrite derive_pt_id derive_pt_comp 2!derive_pt_Log /=.
  rewrite mul1R mulN1R mulRN1.
  rewrite [X in z * X]mulRC [X in (1 - z) * - X]mulRC mulRN 2!mulRA.
  rewrite !mulRV; [|by apply/eqP => /subR_eq0 /gtR_eqF | exact/eqP/gtR_eqF].
  rewrite mul1R -2!oppRD oppRK.
  by rewrite [X in X + - _]addRC oppRD addRA addRC !addRA Rplus_opp_l add0R addR_opp.
have @pderivable_Df : pderivable Df (fun z => x <= z <= y).
  move => z [Hxz Hzy].
  apply derivable_pt_minus.
  apply derivable_pt_Log.
  apply (ltR_leR_trans H0x Hxz).
  apply derivable_pt_comp.
  apply derivable_pt_Rminus.
  apply derivable_pt_Log.
  apply subR_gt0.
  exact: leR_ltR_trans Hzy Hy1.
set DDf := fun z => / (z * (1 - z) * ln 2).
have derive_pt_Df : forall z (Hz : x <= z <= y), DDf z = derive_pt Df z (pderivable_Df z Hz).
  rewrite -/Df => z [Hxz Hzy].
  rewrite derive_pt_minus derive_pt_comp 2!derive_pt_Log /=.
  rewrite mulRN1 -[X in _ = X]addR_opp oppRK.
  rewrite -mulRDr [X in _ = X]mulRC.
  have Hzn0 : z != 0 by apply/eqP/gtR_eqF/(ltR_leR_trans H0x Hxz).
  have H1zn0 : 1 - z != 0.
    apply /eqP; move => /subR_eq0 /gtR_eqF H.
    by apply /H /leR_ltR_trans; [exact Hzy| exact Hy1].
  have Hzn0' : z <> 0 by move : Hzn0 => /eqP.
  have H1zn0' : 1 - z <> 0 by move : H1zn0 => /eqP.
  have Hz1zn0 : z * (1 - z) <> 0 by rewrite mulR_neq0.
  have ln2n0 : ln 2 <> 0 by move : ln2_gt0 => /gtR_eqF.
  have -> : / z = (1 - z) / (z * (1 - z)).
    change (/ z = (1 - z) * / (z * (1 - z))).
    by rewrite invRM // [X in _ = _ * X]mulRC mulRA mulRV // mul1R.
  have -> : / (1 - z) = z  / (z * (1 - z)).
    change (/ (1 - z) = z * / (z * (1 - z))).
    by rewrite invRM // mulRA mulRV // mul1R.
  by rewrite -Rdiv_plus_distr -addRA Rplus_opp_l addR0 div1R -invRM.
have DDf_nonneg : forall z, x <= z <= y -> 0 <= DDf z.
  move => z [Hxz Hzy].
  have Hz : 0 < z by apply /ltR_leR_trans; [exact H0x| exact Hxz].
  have H1z : 0 < 1 - z by apply /subR_gt0 /leR_ltR_trans; [exact Hzy| exact Hy1].
  apply/or_introl/invR_gt0/mulR_gt0; [exact/mulR_gt0 | exact/ln2_gt0].
exact: (@second_derivative_convexf_pt _ _ _ _ Df _ _ DDf).
Qed.

Lemma concavity_of_entropy : concave_function_in open_unit_interval H2.
Proof.
rewrite /concave_function_in => x y t Hx Hy.
apply R_concave_function_atN'.
move : t.
move : (Rtotal_order x y) => Hxy.
wlog : x y Hx Hy Hxy / x < y.
  move => H.
  case Hxy; [apply H|] => //.
  case => [-> t|]; [exact/convex_function_atxx|].
  move => Hxy' t.
  apply: convex_function_sym => // t0.
  apply H => //.
  by apply or_introl.
move => Hxy' t.
by apply /R_convex_function_atN /concavity_of_entropy_x_le_y.
Qed.

End entropy_concave_alternative_proof_binary_case.

Require Import chap2.

Section mutual_information_concave.

Variables (A B : finType) (Q : A -> dist B).
Hypothesis B_not_empty : (0 < #|B|)%nat.

Lemma mutual_information_concave :
  concave_function (fun P => MutualInfo.mi (CDist.make_joint P Q)).
Proof.
suff : concave_function (fun P => let PQ := Swap.d (CDist.make_joint P Q) in
                           `H (Bivar.fst PQ) - CondEntropy.h PQ).
  set f := fun _ => _. set g := fun _ => _.
  rewrite (FunctionalExtensionality.functional_extensionality f g) //.
  move=> d; rewrite {}/f {}/g /=.
  by rewrite -MutualInfo.miE2 -mi_sym.
apply R_concave_functionB.
- move: (entropy_concave B_not_empty) => H.
  apply R_concave_functionN.
  move=> p q t /=.
  rewrite 3!Swap.fst.
  move : H.
  move /R_convex_functionN' => H.
  apply: leR_trans (H (Bivar.snd (CDist.make_joint p Q)) (Bivar.snd (CDist.make_joint q Q)) t).
  destruct t. rewrite /Conv /=.
  rewrite -ProdDist.snd_convex; exact/leRR.
- suff : affine_function (fun x => CondEntropy.h (Swap.d (CDist.make_joint x Q))) by move /affine_functionP => [].
  move => p q t.
  rewrite /affine_function_at /= /Conv /= /avg /=.
  rewrite /CondEntropy.h /CondEntropy.h1.
  rewrite 2!big_distrr -big_split /=; apply eq_bigr => a _.
  rewrite !Swap.snd !Bivar.fstE !mulRN -oppRD; congr (- _).
  rewrite !big_distrr -big_split /=; apply eq_bigr => b _.
  rewrite !big_distrl !big_distrr -big_split /=; apply eq_bigr => b0 _.
  rewrite !ProdDist.dE /= Conv2Dist.dE /=.
  rewrite !(mulRA t) !(mulRA t.~).
  case/boolP: (t * p a == 0) => /eqP Hp.
    rewrite Hp.
    case/boolP: (t.~ * q a == 0) => /eqP Hq.
      rewrite Hq; field.
    rewrite !(mul0R,add0R).
    rewrite -CDist.E /=; last by rewrite Conv2Dist.dE Hp add0R.
    rewrite -CDist.E /= //; by move: Hq; rewrite mulR_neq0 => -[].
  case/boolP: (t.~ * q a == 0) => /eqP Hq.
    rewrite Hq !(mul0R,addR0).
    rewrite -CDist.E; last by rewrite Conv2Dist.dE Hq addR0.
    rewrite -CDist.E /= //; by move: Hp; rewrite mulR_neq0 => -[].
  rewrite -CDist.E; last first.
    rewrite /= Conv2Dist.dE paddR_eq0; [tauto | |].
    apply/mulR_ge0; [exact/prob_ge0 | exact/dist_ge0].
    apply/mulR_ge0; [apply/onem_ge0; exact/prob_le1 | exact/dist_ge0].
  rewrite -CDist.E; last by move: Hp; rewrite mulR_neq0 => -[].
  rewrite -CDist.E //=; last by move: Hq; rewrite mulR_neq0 => -[].
  field.
Qed.

End mutual_information_concave.

Section mutual_information_convex.

Variables (A B : finType) (P : dist A).

Local Open Scope divergence_scope.

Lemma mutual_information_convex :
  convex_function (fun (Q : A -> dist B) => MutualInfo.mi (CDist.make_joint P Q)).
Proof.
move=> p1yx p2yx t.
pose p1' := CDist.mkt P p1yx.
pose p2' := CDist.mkt P p2yx.
pose p1xy := CDist.joint_of p1'.
pose p2xy := CDist.joint_of p2'.
pose p1 := Bivar.snd p1xy.
pose p2 := Bivar.snd p2xy.
pose plambdayx := fun a : A => p1yx a <| t |> p2yx a.
pose plambda' := CDist.mkt P plambdayx.
pose plambdaxy := CDist.joint_of plambda'.
pose plambday := Bivar.snd plambdaxy.
pose qlambdaxy := P `x plambday.
pose q1xy := P `x p1.
pose q2xy := P `x p2.
rewrite /convex_function_at.
have -> : MutualInfo.mi (CDist.make_joint P (fun x : A => p1yx x <| t |> p2yx x)) =
       D(plambdaxy || qlambdaxy).
  rewrite MutualInfo.miE /div pair_big /=.
  apply eq_bigr => -[a b] _ /=.
  congr (_ * log (_ / _)).
  rewrite /qlambdaxy.
  by rewrite ProdDist.dE /= /CDist.make_joint /CDist.joint_of /= ProdDist.fst; congr (_ * _).
have -> : qlambdaxy = q1xy <| t |> q2xy.
  apply/dist_ext => -[a b].
  rewrite !ProdDist.dE !Conv2Dist.dE /=.
  rewrite /q1xy /q2xy !ProdDist.dE /=.
  rewrite /p1 /plambday.
  rewrite !Bivar.sndE !big_distrr /= -big_split /=.
  apply eq_bigr => a0 _.
  rewrite /plambdaxy /= !ProdDist.dE /= /p1xy /plambdayx.
  rewrite Conv2Dist.dE /=.
  field.
have -> : plambdaxy = p1xy <| t |> p2xy.
  apply/dist_ext => -[a b].
  rewrite !ProdDist.dE !Conv2Dist.dE /=.
  rewrite /p1xy /p2xy !ProdDist.dE /=.
  field.
have -> : MutualInfo.mi (CDist.make_joint P p1yx) = D(p1xy || q1xy).
  rewrite MutualInfo.miE /div pair_big /=.
  apply eq_bigr => -[a b] _ /=.
  congr (_ * log (_ / _)).
  by rewrite /q1xy ProdDist.dE /CDist.make_joint /CDist.joint_of /= ProdDist.fst.
have -> : MutualInfo.mi (CDist.make_joint P p2yx) = D(p2xy || q2xy).
  rewrite MutualInfo.miE /div pair_big /=.
  apply eq_bigr => -[a b] _ /=.
  congr (_ * log (_ / _)).
  by rewrite /q2xy ProdDist.dE /CDist.make_joint /CDist.joint_of /= ProdDist.fst.
apply: div_convex'.
- apply/dominatesP => -[a b].
  rewrite /q1xy /p1xy ProdDist.dE /= mulR_eq0.
  rewrite /p1 /p1xy /CDist.joint_of => -[|].
    by rewrite ProdDist.dE => ->; rewrite mul0R.
  rewrite Bivar.sndE.
  move/prsumr_eq0P => -> // a0 _; exact/dist_ge0.
-  apply/dominatesP => -[a b].
  rewrite /q1xy /p1xy ProdDist.dE /= mulR_eq0.
  rewrite /p1 /p1xy /CDist.joint_of => -[|].
    by rewrite ProdDist.dE => ->; rewrite mul0R.
  rewrite Bivar.sndE.
  move/prsumr_eq0P => -> // a0 _; exact/dist_ge0.
Qed.

End mutual_information_convex.