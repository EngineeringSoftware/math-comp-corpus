From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype.
From mathcomp
Require Import bigop ssralg finset fingroup zmodp poly ssrnum.
From mathcomp
Require Import matrix mxalgebra vector falgebra ssrnum algC algnum.
From mathcomp
Require Import fieldext.
From mathcomp Require Import vector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Reserved Notation "'[ u , v ]"
  (at level 2, format "'[hv' ''[' u , '/ '  v ] ']'").
Reserved Notation "'[ u , v ]_ M"
         (at level 2, format "'[hv' ''[' u , '/ '  v ]_ M ']'").
Reserved Notation "'[ u ]_ M" (at level 2, format "''[' u ]_ M").
Reserved Notation "'[ u ]" (at level 2, format "''[' u ]").
Reserved Notation "u '``_' i"
    (at level 3, i at level 2, left associativity, format "u '``_' i").
Reserved Notation "A ^_|_"    (at level 8, format "A ^_|_").
Reserved Notation "A _|_ B" (at level 69, format "A  _|_  B").
Reserved Notation "eps_theta .-sesqui" (at level 2, format "eps_theta .-sesqui").

Notation "u '``_' i" := (u (GRing.zero (Zp_zmodType O)) i) : ring_scope.
Notation "''e_' i" := (delta_mx 0 i)
 (format "''e_' i", at level 3) : ring_scope.

Lemma mxdirect_delta (F : fieldType) (T : finType) (n : nat) (P : pred T) f :
  {in P & , injective f} ->
  mxdirect (\sum_(i | P i) <<'e_(f i) : 'rV[F]_n>>)%MS.
Proof.
pose fP := image f P => Uf; have UfP: uniq fP by apply/dinjectiveP.
suffices /mxdirectP: mxdirect (\sum_i <<'e_i : 'rV[F]_n>>).
  rewrite /= !(bigID [mem fP] predT) -!big_uniq //= !big_map !big_filter.
  by move/mxdirectP; rewrite mxdirect_addsE => /andP[].
apply/mxdirectP=> /=; transitivity (mxrank (1%:M : 'M[F]_n)).
  apply/eqmx_rank; rewrite submx1 mx1_sum_delta summx_sub_sums // => i _.
  by rewrite -(mul_delta_mx (0 : 'I_1)) genmxE submxMl.
rewrite mxrank1 -[LHS]card_ord -sum1_card.
by apply/eq_bigr=> i _; rewrite /= mxrank_gen mxrank_delta.
Qed.

Lemma row_mx_eq0 (M : zmodType) (m n1 n2 : nat)
 (A1 : 'M[M]_(m, n1)) (A2 : 'M_(m, n2)):
 (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
apply/eqP/andP; last by case=> /eqP-> /eqP->; rewrite row_mx0.
by rewrite -row_mx0 => /eq_row_mx [-> ->].
Qed.

Lemma col_mx_eq0 (M : zmodType) (m1 m2 n : nat)
 (A1 : 'M[M]_(m1, n)) (A2 : 'M_(m2, n)):
 (col_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
by rewrite -![_ == 0](inj_eq (@trmx_inj _ _ _)) !trmx0 tr_col_mx row_mx_eq0.
Qed.

Local Notation "M ^ phi" := (map_mx phi M).
Local Notation "M ^t phi" := (map_mx phi (M ^T)) (phi at level 30, at level 30).

Structure revop X Y Z (f : Y -> X -> Z) := RevOp {
  fun_of_revop :> X -> Y -> Z;
  _ : forall x, f x =1 fun_of_revop^~ x
}.

Lemma map_mx_comp (R S T : ringType) m n (M : 'M[R]_(m,n))
      (f : R -> S) (g : S -> T) : M ^ (g \o f) = (M ^ f) ^ g.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma eq_map_mx (R S : ringType) m n (M : 'M[R]_(m,n))
      (g f : R -> S) : f =1 g -> M ^ f = M ^ g.
Proof. by move=> eq_fg; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_mx_id (R : ringType) m n (M : 'M[R]_(m,n)) : M ^ id = M.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma eq_map_mx_id (R : ringType) m n (M : 'M[R]_(m,n)) (f : R -> R) :
  f =1 id -> M ^ f = M.
Proof. by move=> /eq_map_mx->; rewrite map_mx_id. Qed.

Module Bilinear.

Section ClassDef.

Variables (R : ringType) (U U' : lmodType R) (V : zmodType) (s s' : R -> V -> V).
Implicit Type phUU'V : phant (U -> U' -> V).

Local Coercion GRing.Scale.op : GRing.Scale.law >-> Funclass.
Definition axiom (f : U -> U' -> V) (s_law : GRing.Scale.law s) (eqs : s = s_law)
                                    (s'_law : GRing.Scale.law s') (eqs' : s' = s'_law) :=
  ((forall u', GRing.Linear.axiom (f^~ u') eqs)
  * (forall u, GRing.Linear.axiom (f u) eqs'))%type.

Record class_of (f : U -> U' -> V) : Prop := Class {
  basel : forall u', GRing.Linear.class_of s (f^~ u');
  baser : forall u, GRing.Linear.class_of s' (f u)
}.

Lemma class_of_axiom f s_law s'_law Ds Ds' :
   @axiom f s_law Ds s'_law Ds' -> class_of f.
Proof.
by pose coa := GRing.Linear.class_of_axiom; move=> [/(_ _) /coa ? /(_ _) /coa].
Qed.

Structure map phUU'V := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Definition class (phUU'V : _)  (cF : map phUU'V) :=
   let: Pack _ c as cF' := cF return class_of cF' in c.

Canonical additiver phU'V phUU'V (u : U) cF := GRing.Additive.Pack phU'V
  (baser (@class phUU'V cF) u).
Canonical linearr phU'V  phUU'V (u : U) cF := GRing.Linear.Pack phU'V
  (baser (@class phUU'V cF) u).

Definition applyr_head t (f : U -> U' -> V) u v := let: tt := t in f v u.
Notation applyr := (@applyr_head tt).

Canonical additivel phUV phUU'V (u' : U') (cF : map _) :=
  @GRing.Additive.Pack _ _ phUV (applyr cF u') (basel (@class phUU'V cF) u').
Canonical linearl phUV phUU'V  (u' : U') (cF : map _) :=
  @GRing.Linear.Pack _ _ _ _ phUV (applyr cF u') (basel (@class phUU'V cF) u').

Definition pack (phUV : phant (U -> V)) (phU'V : phant (U' -> V))
           (revf : U' -> U -> V) (rf : revop revf) f (g : U -> U' -> V) of (g = fun_of_revop rf) :=
  fun (bFl : U' -> GRing.Linear.map s phUV) flc of (forall u', revf u' = bFl u') &
      (forall u', phant_id (GRing.Linear.class (bFl u')) (flc u')) =>
  fun (bFr : U -> GRing.Linear.map s' phU'V) frc of (forall u, g u = bFr u) &
      (forall u, phant_id (GRing.Linear.class (bFr u)) (frc u)) =>
  @Pack (Phant _) f (Class flc frc).


End ClassDef.

Module Exports.
Delimit Scope linear_ring_scope with linR.
Notation bilinear_for s s' f := (axiom f (erefl s) (erefl s')).
Notation bilinear f := (bilinear_for *:%R *:%R f).
Notation biscalar f := (bilinear_for *%R *%R f).
Notation bilmorphism_for s s' f := (class_of s s' f).
Notation bilmorphism f := (bilmorphism_for *:%R *:%R f).
Coercion class_of_axiom : axiom >-> bilmorphism_for.
Coercion baser : bilmorphism_for >-> Funclass.
Coercion apply : map >-> Funclass.
Notation "{ 'bilinear' fUV | s & s' }" := (map s s' (Phant fUV))
  (at level 0, format "{ 'bilinear'  fUV  |  s  &  s' }") : ring_scope.
Notation "{ 'bilinear' fUV | s }" := (map s.1 s.2 (Phant fUV))
  (at level 0, format "{ 'bilinear'  fUV  |  s }") : ring_scope.
Notation "{ 'bilinear' fUV }" := {bilinear fUV | *:%R & *:%R}
  (at level 0, format "{ 'bilinear'  fUV }") : ring_scope.
Notation "{ 'biscalar' U }" := {bilinear U -> U -> _ | *%R & *%R}
  (at level 0, format "{ 'biscalar'  U }") : ring_scope.
Notation "[ 'bilinear' 'of' f 'as' g ]" :=
  (@pack  _ _ _ _ _ _ _ _ _ _ f g erefl _ _
         (fun=> erefl) (fun=> idfun) _ _ (fun=> erefl) (fun=> idfun)).
Notation "[ 'bilinear' 'of' f ]" :=  [bilinear of f as f]
  (at level 0, format "[ 'bilinear'  'of'  f ]") : form_scope.
Coercion additiver : map >-> GRing.Additive.map.
Coercion linearr : map >->  GRing.Linear.map.
Canonical additiver.
Canonical linearr.
Canonical additivel.
Canonical linearl.
Notation applyr := (@applyr_head _ _ _ _ tt).
End Exports.

End Bilinear.
Include Bilinear.Exports.

Section BilinearTheory.

Variable R : ringType.

Section GenericProperties.

Variables (U U' : lmodType R) (V : zmodType) (s : R -> V -> V) (s' : R -> V -> V).
Variable f : {bilinear U -> U' -> V | s & s'}.

Lemma linear0r z : f z 0 = 0. Proof. by rewrite raddf0. Qed.
Lemma linearNr z : {morph f z : x / - x}. Proof. exact: raddfN. Qed.
Lemma linearDr z : {morph f z : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma linearBr z : {morph f z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma linearMnr z n : {morph f z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma linearMNnr z n : {morph f z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma linear_sumr z I r (P : pred I) E :
  f z (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f z (E i).
Proof. exact: raddf_sum. Qed.

Lemma linearZr_LR z : scalable_for s' (f z). Proof. exact: linearZ_LR. Qed.
Lemma linearPr z a : {morph f z : u v / a *: u + v >-> s' a u + v}.
Proof. exact: linearP. Qed.

Lemma applyrE x : applyr f x =1 f^~ x. Proof. by []. Qed.

Lemma linear0l z : f 0 z = 0. Proof. by rewrite -applyrE raddf0. Qed.
Lemma linearNl z : {morph f^~ z : x / - x}.
Proof. by move=> ?; rewrite -applyrE raddfN. Qed.
Lemma linearDl z : {morph f^~ z : x y / x + y}.
Proof. by move=> ??; rewrite -applyrE raddfD. Qed.
Lemma linearBl z : {morph f^~ z : x y / x - y}.
Proof. by move=> ??; rewrite -applyrE raddfB. Qed.
Lemma linearMnl z n : {morph f^~ z : x / x *+ n}.
Proof. by move=> ?; rewrite -applyrE raddfMn. Qed.
Lemma linearMNnl z n : {morph f^~ z : x / x *- n}.
Proof. by move=> ?; rewrite -applyrE raddfMNn. Qed.
Lemma linear_suml z I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) z = \sum_(i <- r | P i) f (E i) z.
Proof. by rewrite -applyrE raddf_sum. Qed.

Lemma linearZl_LR z : scalable_for s (f^~ z).
Proof. by move=> ??; rewrite -applyrE linearZ_LR. Qed.
Lemma linearPl z a : {morph f^~ z : u v / a *: u + v >-> s a u + v}.
Proof. by move=> ??; rewrite -applyrE linearP. Qed.

End GenericProperties.

Section BidirectionalLinearZ.

Variables (U : lmodType R) (V : zmodType) (s : R -> V -> V).
Variables (S : ringType) (h : S -> V -> V) (h_law : GRing.Scale.law h).

End BidirectionalLinearZ.

End BilinearTheory.

Canonical rev_mulmx (R : ringType) m n p := @RevOp _ _ _ (@mulmxr_head R m n p tt)
  (@mulmx R m n p) (fun _ _ => erefl).

Canonical mulmx_bilinear (R : comRingType) m n p := [bilinear of @mulmx R m n p].

Section BilinearForms.

Variables (R : fieldType) (theta : {rmorphism R -> R}).
Variables (n : nat) (M : 'M[R]_n).
Implicit Types (a b : R) (u v : 'rV[R]_n) (N P Q : 'M[R]_n).

Definition form u v := (u *m M *m (v ^t theta)) 0 0.

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Lemma form0l u : '[0, u] = 0.
Proof. by rewrite /form !mul0mx mxE. Qed.

Lemma form0r u : '[u, 0] = 0.
Proof. by rewrite /form trmx0 map_mx0 mulmx0 mxE. Qed.

Lemma formDl u v w : '[u + v, w] = '[u, w] + '[v, w].
Proof. by rewrite /form !mulmxDl mxE. Qed.

Lemma formDr u v w : '[u, v + w] = '[u, v] + '[u, w].
Proof. by rewrite /form linearD !map_mxD !mulmxDr mxE. Qed.

Lemma formZr a u v : '[u, a *: v] = theta a * '[u, v].
Proof. by rewrite /form !(linearZ, map_mxZ) /= mxE. Qed.

Lemma formZl a u v : '[a *: u, v] = a * '[u, v].
Proof.
by do !rewrite /form  -[_ *: _ *m _]/(mulmxr _ _) linearZ /=; rewrite mxE.
Qed.

Lemma formNl u v : '[- u, v] = - '[u, v].
Proof. by rewrite -scaleN1r formZl mulN1r. Qed.

Lemma formNr u v : '[u, - v] = - '[u, v].
Proof. by rewrite -scaleN1r formZr rmorphN1 mulN1r. Qed.

Lemma formee i j : '['e_i, 'e_j] = M i j.
Proof.
rewrite /form -rowE -map_trmx map_delta_mx -[M in LHS]trmxK.
by rewrite -tr_col -trmx_mul -rowE !mxE.
Qed.

Lemma form0_eq0 : M = 0 -> forall u v, '[u, v] = 0.
Proof. by rewrite/form=> -> u v; rewrite mulmx0 mul0mx mxE. Qed.

End BilinearForms.

Section Sesquilinear.

Variable R : fieldType.
Variable n : nat.
Implicit Types (a b : R) (u v : 'rV[R]_n) (N P Q : 'M[R]_n).

Section Def.
Variable eps_theta : (bool * {rmorphism R -> R}).

Definition sesqui :=
  [qualify M : 'M_n | M == ((-1) ^+ eps_theta.1) *: M ^t eps_theta.2].
Fact sesqui_key : pred_key sesqui. Proof. by []. Qed.
Canonical sesqui_keyed := KeyedQualifier sesqui_key.
End Def.

Local Notation "eps_theta .-sesqui" := (sesqui eps_theta).

Variables (eps : bool) (theta : {rmorphism R -> R}).
Variables (M : 'M[R]_n).
Local Notation "''[' u , v ]" := (form theta M u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u%R, u%R]%R : ring_scope.

Lemma sesquiE : (M \is (eps,theta).-sesqui) = (M == (-1) ^+ eps *: M ^t theta).
Proof. by rewrite qualifE. Qed.

Lemma sesquiP : reflect (M = (-1) ^+ eps *: M ^t theta)
                        (M \is (eps,theta).-sesqui).
Proof. by rewrite sesquiE; apply/eqP. Qed.

Hypothesis (thetaK : involutive theta).
Hypothesis (M_sesqui : M \is (eps, theta).-sesqui).

Lemma trmx_sesqui : M^T = (-1) ^+ eps *: M ^ theta.
Proof.
rewrite [in LHS](sesquiP _) // -mul_scalar_mx trmx_mul.
by rewrite tr_scalar_mx mul_mx_scalar map_trmx trmxK.
Qed.

Lemma maptrmx_sesqui : M^t theta = (-1) ^+ eps *: M.
Proof.
by rewrite trmx_sesqui map_mxZ rmorph_sign -map_mx_comp eq_map_mx_id.
Qed.

Lemma formC u v : '[u, v] = (-1) ^+ eps * theta '[v, u].
Proof.
rewrite /form [M in LHS](sesquiP _) // -mulmxA !mxE rmorph_sum mulr_sumr.
apply: eq_bigr => /= i _; rewrite !(mxE, mulr_sumr, mulr_suml, rmorph_sum).
apply: eq_bigr => /= j _; rewrite !mxE !rmorphM  mulrCA -!mulrA.
by congr (_ * _); rewrite mulrA mulrC thetaK.
Qed.

Lemma form_eq0C u v : ('[u, v] == 0) = ('[v, u] == 0).
Proof. by rewrite formC mulf_eq0 signr_eq0 /= fmorph_eq0. Qed.



Definition ortho m (B : 'M_(m,n)) := (kermx (M *m (B ^t theta))).
Local Notation "B ^_|_" := (ortho B) : ring_scope.
Local Notation "A _|_ B" := (A%MS <= B^_|_)%MS : ring_scope.

Lemma normalE u v : (u _|_ v) = ('[u, v] == 0).
Proof.
by rewrite (sameP sub_kermxP eqP) mulmxA [_ *m _^t _]mx11_scalar fmorph_eq0.
Qed.

Lemma form_eq0P {u v} : reflect ('[u, v] = 0) (u _|_ v).
Proof. by rewrite normalE; apply/eqP. Qed.

Lemma normalP p q (A : 'M_(p, n)) (B :'M_(q, n)) :
  reflect (forall (u v : 'rV_n), (u <= A)%MS -> (v <= B)%MS -> u _|_ v)
          (A _|_ B).
Proof.
apply: (iffP idP) => AnB.
  move=> u v uA vB; rewrite (submx_trans uA) // (submx_trans AnB) //.
  apply/sub_kermxP; have /submxP [w ->] := vB.
  rewrite trmx_mul map_mxM !mulmxA -[kermx _ *m _ *m _]mulmxA.
  by rewrite [kermx _ *m _](sub_kermxP _) // mul0mx.
apply/rV_subP => u /AnB /(_ _) /sub_kermxP uMv; apply/sub_kermxP.
suff: forall m (v : 'rV[R]_m),
  (forall i, v *m 'e_i ^t theta = 0 :> 'M_1) -> v = 0.
  apply => i; rewrite !mulmxA -!mulmxA -map_mxM -trmx_mul uMv //.
  by apply/submxP; exists 'e_i.
move=> /= m v Hv; apply: (can_inj (@trmxK _ _ _)).
rewrite trmx0; apply/row_matrixP=> i; rewrite row0 rowE.
apply: (can_inj (@trmxK _ _ _)); rewrite trmx0 trmx_mul trmxK.
by rewrite -(map_delta_mx theta) map_trmx Hv.
Qed.

Lemma normalC p q (A : 'M_(p, n)) (B :'M_(q, n)) : (A _|_ B) = (B _|_ A).
Proof.
gen have nC : p q A B / A _|_ B -> B _|_ A; last by apply/idP/idP; apply/nC.
move=> AnB; apply/normalP => u v ? ?; rewrite normalE.
rewrite formC mulf_eq0 ?fmorph_eq0 ?signr_eq0 /=.
by rewrite -normalE (normalP _ _ AnB).
Qed.

Lemma normal_ortho_mx p (A : 'M_(p, n)) : ((A^_|_) _|_ A).
Proof. by []. Qed.

Lemma normal_mx_ortho p (A : 'M_(p, n)) : (A _|_ (A^_|_)).
Proof. by rewrite normalC. Qed.

Lemma rank_normal u : (\rank (u ^_|_) >= n.-1)%N.
Proof.
rewrite mxrank_ker -subn1 leq_sub2l //.
by rewrite (leq_trans (mxrankM_maxr  _ _)) // rank_leq_col.
Qed.

Definition rad := 1%:M^_|_.

Lemma rad_ker : rad = kermx M.
Proof. by rewrite /rad /ortho trmx1 map_mx1 mulmx1. Qed.

Theorem formDd u v : u _|_ v -> '[u + v] = '[u] + '[v].
Proof.
move=> uNv; rewrite formDl !formDr ['[v, u]]formC.
by rewrite ['[u, v]](form_eq0P _) // rmorph0 mulr0 addr0 add0r.
Qed.

Lemma formZ a u : '[a *: u]= (a * theta a) * '[u].
Proof. by rewrite formZl formZr mulrA. Qed.

Lemma formN u : '[- u] = '[u].
Proof. by rewrite formNr formNl opprK. Qed.

Lemma form_sign m u : '[(-1) ^+ m *: u] = '[u].
Proof. by rewrite -signr_odd scaler_sign; case: odd; rewrite ?formN. Qed.

Lemma formD u v : let d := '[u, v] in
  '[u + v] = '[u] + '[v] + (d + (-1) ^+ eps * theta d).
Proof. by rewrite formDl !formDr ['[v, _]]formC [_ + '[v]]addrC addrACA. Qed.

Lemma formB u v : let d := '[u, v] in
  '[u - v] = '[u] + '[v] - (d + (-1) ^+ eps * theta d).
Proof. by rewrite formD formN !formNr rmorphN mulrN -opprD. Qed.

Lemma formBd u v : u _|_ v -> '[u - v] = '[u] + '[v].
Proof.
by move=> uTv; rewrite formDd ?formN // normalE formNr oppr_eq0 -normalE.
Qed.

End Sesquilinear.

Notation "eps_theta .-sesqui" := (sesqui _ eps_theta) : ring_scope.

Notation symmetric := (false, [rmorphism of idfun]).-sesqui.
Notation skew := (true, [rmorphism of idfun]).-sesqui.
Notation hermitian := (false, @conjC _).-sesqui.