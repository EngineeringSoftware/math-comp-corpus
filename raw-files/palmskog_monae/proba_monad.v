Require Import Reals Lra ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import boolp.
Require Import monad.
From infotheo Require Import ssrR Reals_ext proba.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "mx <| p |> my" (format "mx  <| p |>  my", at level 50).

Local Open Scope reals_ext_scope.

Module MonadProb.
Record mixin_of (M : monad) : Type := Mixin {
  choice : forall (p : prob) A, M A -> M A -> M A
           where "mx <| p |> my" := (choice p mx my) ;
  _ : forall A (mx my : M A), mx <| `Pr 0 |> my = my ;
  _ : forall A (mx my : M A), mx <| `Pr 1 |> my = mx ;
  _ : forall A p (mx my : M A), mx <| p |> my = my <| `Pr p.~ |> mx ;
  _ : forall A p, idempotent (@choice p A) ;
  _ : forall A (p q r s : prob) (mx my mz : M A),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz ;
  _ : forall p, BindLaws.left_distributive (@Bind M) (choice p)
}.
Record class_of (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of (Monad.Pack base) }.
Structure t := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) := Monad.Pack (MonadProb.base (class M)).
Module Exports.
Definition Choice (M : t) : forall p A, m M A -> m M A -> m M A :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _ _ )) := M return
    forall p A, m M A -> m M A -> m M A in x.
Arguments Choice {M} : simpl never.
Notation "mx <| p |> my" := (Choice p _ mx my) : proba_monad_scope.
Notation probMonad := t.
Coercion baseType : probMonad >-> monad.
Canonical baseType.
End Exports.
End MonadProb.
Export MonadProb.Exports.

Local Open Scope proba_monad_scope.

Section prob_lemmas.
Variable (M : probMonad).
Lemma choicemm : forall A p, idempotent (@Choice M p A).
Proof. by case: M => m [? []]. Qed.
Lemma choice0 : forall A (mx my : M A), mx <| `Pr 0 |> my = my.
Proof. by case: M => m [? []]. Qed.
Lemma choice1 : forall A (mx my : M A), mx <| `Pr 1 |> my = mx.
Proof. by case: M => m [? []]. Qed.
Lemma choiceA A : forall (p q r s : prob) (mx my mz : M A),
    (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
    mx <| p |> (my <| q |> mz) = (mx <| r |> my) <| s |> mz.
Proof. by case: M A => m [? []]. Qed.
Lemma choiceC : forall A (p : prob) (mx my : M A), mx <| p |> my = my <| `Pr p.~ |> mx.
Proof. by case: M => m [? []]. Qed.
Lemma prob_bindDl p : BindLaws.left_distributive (@Bind M) (Choice p).
Proof. by case: M => m [? []]. Qed.
End prob_lemmas.
Arguments choiceA {M} {A} _ _ _ _ {mx} {my} {mz}.
Arguments choiceC {M} {A} _ {mx} {my}.

Fixpoint uniform {M : probMonad} {A} (def : A) (s : seq A) : M A :=
  match s with
    | [::] => Ret def
    | [:: x] => Ret x
    | x :: xs => Ret x <| `Pr / IZR (Z_of_nat (size (x :: xs))) |> uniform def xs
  end.

Lemma uniform_nil (M : probMonad) A (def : A) :
  uniform def [::] = Ret def :> M A.
Proof. by []. Qed.

Lemma choice_ext (q p : prob) (M : probMonad) A (m1 m2 : M A) :
  p = q :> R -> m1 <| p |> m2 = m1 <| q |> m2.
Proof. by move/prob_ext => ->. Qed.

Lemma uniform_cons (M : probMonad) A (def : A) h s :
  uniform def (h :: s) = Ret h <| `Pr / IZR (Z_of_nat (size (h :: s))) |> uniform def s :> M A.
Proof.
case: s => //.
rewrite (@choice_ext (`Pr 1)) // ?choice1 //.
by rewrite /= Rinv_1.
Qed.

Lemma uniform_singl (M : probMonad) A (def : A) h : size h = 1%nat ->
  uniform def h = Ret (head def h) :> M A.
Proof.
case: h => // h [|//] _.
by rewrite uniform_cons uniform_nil (@choice_ext (`Pr 1)) ?choice1 //= invR1.
Qed.

Lemma uniform_nseq (M : probMonad) A (def : A) h n :
  uniform def (nseq n.+1 h) = Ret h :> M A.
Proof.
elim: n => // n IH.
by rewrite (_ : nseq _ _ = h :: nseq n.+1 h) // uniform_cons IH choicemm.
Qed.

Lemma uniform_cat (M : probMonad) A (a : A) s t :
  let m := size s in let n := size t in
  uniform a (s ++ t) = uniform a s <| `Pr (divRnnm m n) |> uniform a t :> M _.
Proof.
elim: s t => [t m n|s1 s2 IH t m n].
  rewrite cat0s uniform_nil /= [X in _ <| X |> _](_ : _ = `Pr 0) ?choice0 //.
  by apply prob_ext => /=; rewrite /divRnnm div0R.
case/boolP : (m.-1 + n == 0)%nat => [{IH}|] m1n0.
  have s20 : s2 = [::] by move: m1n0; rewrite {}/m /=; case: s2.
  have t0 : t = [::] by move: m1n0; rewrite {}/n /= addnC; case: t.
  subst s2 t.
  rewrite cats0 (_ : Prob.mk _ = `Pr 1) ?choice1 //.
  by apply prob_ext => /=; rewrite /divRnnm div1R invR1.
rewrite cat_cons uniform_cons uniform_cons.
set pv := ((/ _)%R).
set v : prob := @Prob.mk pv _.
set u := @Prob.mk (INR (size s2) / INR (size s2 + size t))%R (prob_divRnnm _ _).
rewrite -[RHS](choiceA v u).
  by rewrite -IH.
split.
  rewrite 3!probpK -INR_IZR_INZ.
  rewrite (_ : INR _ = INR m) // mulRA mulVR; last by rewrite INR_eq0'.
  by rewrite mul1R /pv -INR_IZR_INZ [size _]/= size_cat -addSn.
rewrite 3!probpK.
transitivity ( (1 - 1 / INR (m + n)) * (1 - INR (m.-1) / INR (m.-1 + n)))%R; last first.
  congr (_ .~ * _)%R.
  by rewrite /v /pv probpK INR_IZR_INZ [size _]/= size_cat -addSn div1R.
transitivity (INR n / INR (m + n))%R.
  rewrite {1}/onem -{1}(Rinv_r (INR (m + n))); last exact/not_0_INR.
  rewrite -mulRBl -minus_INR; last by apply/leP; rewrite leq_addr.
  by rewrite minusE addnC addnK.
rewrite {1}/Rdiv mulRC.
rewrite {1}/Rdiv -[in LHS](mul1R (INR n)).
rewrite -{1}(mulRV (INR (m.-1 + n))); last by rewrite INR_eq0'.
rewrite 2!mulRA -(mulRA (_ * _)%R); congr Rmult.
  rewrite mulRC -subn1.
  rewrite addnC addnBA // minus_INR; last by apply/leP; rewrite addn_gt0 orbT.
  rewrite -/(_ / INR (m + n))%R.
  rewrite Rdiv_minus_distr {1}/Rdiv addnC Rinv_r //; exact/not_0_INR.
rewrite -{1}(Rinv_r (INR (m.-1 + n))); last exact/not_0_INR/eqP.
rewrite -Rdiv_minus_distr mulRC; congr (_ * _)%R.
rewrite -minus_INR; last by apply/leP; rewrite leq_addr.
by rewrite addnC minusE -subnBA // subnn subn0.
Qed.

Lemma uniform2 (M : probMonad) A (def : A) a b :
  uniform def [:: a; b] = uniform def [:: b; a] :> M _.
Proof.
rewrite uniform_cons uniform_singl // uniform_cons uniform_singl //.
set pa := Prob.mk _.
rewrite choiceC /= (@choice_ext pa) //=.
rewrite /onem; field.
Qed.

Module MonadProbDr.
Record mixin_of (M : probMonad) : Type := Mixin {
  prob_bindDr : forall p, BindLaws.right_distributive (@Bind M) (Choice p)
} .
Record class_of (m : Type -> Type) := Class {
  base : MonadProb.class_of m ;
  mixin : mixin_of (MonadProb.Pack base) }.
Structure t := Pack { m : Type -> Type; class : class_of m }.
Definition baseType (M : t) := MonadProb.Pack (base (class M)).
Module Exports.
Notation probDrMonad := t.
Coercion baseType : probDrMonad >-> probMonad.
Canonical baseType.
End Exports.
End MonadProbDr.
Export MonadProbDr.Exports.

Lemma uniform_inde (M : probMonad) A a (x : seq A) {B} (m : M B) :
  do x <- uniform a x; m = m.
Proof.
elim: x m => [/= m|x xs IH m]; first by rewrite bindretf.
by rewrite uniform_cons prob_bindDl IH bindretf choicemm.
Qed.

Lemma uniform_naturality (M : probMonad) A B (a : A) (b : B) (f : A -> B) :
  forall x, (0 < size x)%nat ->
  ((@uniform M _ b) \o map f) x = (M # f \o uniform a) x.
Proof.
elim=> // x [_ _|x' xs]; first by rewrite [in RHS]compE -/(fmap _ _) fmapE bindretf.
move/(_ isT) => IH _.
rewrite compE [in RHS]compE [in LHS]uniform_cons [in RHS]uniform_cons.
set p := (@Prob.mk (/ IZR (Z.of_nat (size _)))%R _ in X in _ = X).
rewrite (_ : @Prob.mk (/ _)%R _ = p); last first.
  by apply prob_ext => /=; rewrite size_map.
move: IH; rewrite 2!compE => ->.
rewrite -[in RHS]/(fmap _ _) [in RHS]fmapE prob_bindDl bindretf -/(fmap _ _) fmapE.
by congr Choice.
Qed.
Arguments uniform_naturality {M A B}.

Lemma mpair_uniform_base_case (M : probMonad) A a x (y : seq A) :
  (0 < size y)%nat ->
  uniform (a, a) (cp [:: x] y) = mpair (uniform a [:: x], uniform a y) :> M _.
Proof.
move=> y0; rewrite cp1.
transitivity (do y' <- @uniform M _ a y; Ret (x, y')).
  by rewrite -(compE (uniform _)) (uniform_naturality a) // compE -/(fmap _ _) fmapE.
transitivity (do z <- Ret x; do y' <- uniform a y; Ret (z, y') : M _).
  by rewrite bindretf.
by [].
Qed.

Lemma mpair_uniform (M : probMonad) A a (x y : seq A) :
  (0 < size x)%nat -> (0 < size y)%nat ->
  mpair (uniform a x, uniform a y) = uniform (a, a) (cp x y) :> M (A * A)%type.
Proof.
elim: x y => // x; case=> [_ y _ size_y|x' xs IH y _ size_y]; apply/esym.
  exact/mpair_uniform_base_case.
set xxs := x' :: xs.
rewrite /cp -cat1s allpairs_cat -/(cp _ _) cp1 uniform_cat.
pose n := size y.
pose l := size (cp xxs y).
rewrite (_ : size _ = n); last by rewrite size_map.
rewrite (_ : Prob.mk _ = probdivRnnm n l); last first.
  rewrite -/(cp _ _) -/l.
  by apply prob_ext => /=.
pose m := size xxs.
have lmn : (l = m * n)%nat by rewrite /l /m /n size_allpairs.
rewrite (_ : probdivRnnm _ _ = @Prob.mk (/ (INR (1 + m))) (prob_invn _))%R; last first.
  apply prob_ext => /=.
  rewrite lmn /divRnnm -mulSn mult_INR {1}/Rdiv Rinv_mult_distr; last 2 first.
    by rewrite INR_eq0.
    by rewrite INR_eq0; apply/eqP; rewrite -lt0n.
  rewrite mulRC -mulRA mulVR; last by rewrite INR_eq0' -lt0n.
  by rewrite mulR1 -addn1 addnC.
rewrite -IH //.
rewrite -/xxs.
move: (@mpair_uniform_base_case M _ a x _ size_y).
rewrite {1}/cp [in X in uniform _ X]/= cats0 => ->.
rewrite -prob_bindDl.
rewrite [in RHS]/mpair uniform_cat.
rewrite [in RHS](_ : Prob.mk _ = probinvn m) //.
by apply prob_ext => /=; rewrite /divRnnm div1R.
Qed.

Module MonadAltProb.
Record mixin_of (M : altCIMonad) (a : prob -> forall A, M A -> M A -> M A) := Mixin {
  _ : forall A (p : prob),
    right_distributive (fun x y : M A => a p _ x y) (fun x y => Alt x y)
}.
Record class_of (m : Type -> Type) := Class {
  base : MonadAltCI.class_of m ;
  base2 : MonadProb.mixin_of (Monad.Pack (MonadAlt.base (MonadAltCI.base base))) ;
  mixin : @mixin_of (MonadAltCI.Pack base) (@MonadProb.choice _ base2)
}.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) : altCIMonad := MonadAltCI.Pack (base (class M)).
Definition altType (M : t) : altMonad := MonadAlt.Pack (MonadAltCI.base (base (class M))).
Module Exports.
Notation altProbMonad := t.
Coercion baseType : altProbMonad >-> altCIMonad.
Canonical baseType.
Definition altprob_is_prob M :=
  MonadProb.Pack (MonadProb.Class (base2 (class M))).
Canonical altprob_is_prob.
Canonical altType.
End Exports.
End MonadAltProb.
Export MonadAltProb.Exports.

Section altprob_lemmas.
Variable (M : altProbMonad).
Lemma choiceDr : forall A p,
  right_distributive (fun x y : M A => x <| p |> y) (fun x y => x [~] y).
Proof. by case: M => m [? ? []]. Qed.
End altprob_lemmas.

Section convexity_property.

Variables (M : altProbMonad) (A : Type) (p q : M A).

Lemma convexity w : p [~] q =
  (p <| w |> p) [~] (q <| w |> p) [~] (p <| w |> q) [~] (q <| w |> q).
Proof.
rewrite -[LHS](choicemm (probcplt w)).
rewrite choiceDr.
rewrite -[in RHS]altA altACA.
rewrite -2![in RHS]choiceDr.
by rewrite -2!choiceC.
Qed.

End convexity_property.

Definition bcoin {M : probMonad} (p : prob) : M bool :=
  Ret true <| p |> Ret false.
Arguments bcoin : simpl never.

Definition arb {M : altMonad} : M bool := Ret true [~] Ret false.

Section mixing_choices.

Variable M : altProbMonad.

Definition arbcoin p : M bool :=
  do a <- arb ; (do c <- bcoin p; Ret (a == c) : M _).
Definition coinarb p : M bool :=
  do c <- bcoin p ; (do a <- arb; Ret (a == c) : M _).

Lemma Ret_eqb_addL b :
  (fun c => Ret (b == c)) = (fun c => Ret (~~ b (+) c)) :> (bool -> M bool).
Proof. case: b; rewrite funeqE; by case. Qed.

Lemma Ret_eqb_addR b :
  (fun c => Ret (c == b)) = (fun c => Ret (~~ b (+) c)) :> (bool -> M bool).
Proof. case: b; rewrite funeqE; by case. Qed.

Definition Ret_eqb_add := (Ret_eqb_addL, Ret_eqb_addR).

Lemma arbcoin_spec p :
  arbcoin p = (bcoin p : M _) [~] bcoin (`Pr p.~).
Proof.
rewrite /arbcoin /arb.
rewrite alt_bindDl.
rewrite 2!bindretf.
rewrite 2!Ret_eqb_add ![fun _ => Ret _]/=.
rewrite bindmret; congr (_ [~] _).
rewrite [in RHS]/bcoin choiceC.
rewrite [in RHS](@choice_ext p); last by rewrite /= onemK.
by rewrite {1}/bcoin prob_bindDl 2!bindretf.
Qed.

Lemma coinarb_spec p : coinarb p = arb.
Proof.
rewrite [in LHS]/coinarb [in LHS]/bcoin.
rewrite prob_bindDl.
rewrite 2!bindretf.
rewrite 2!Ret_eqb_add [fun _ => Ret _]/= [in X in _ <| _ |> X = _]/=.
rewrite bindmret.
rewrite {2}/arb alt_bindDl !bindretf [Ret _]/= [Ret (~~ _)]/=.
rewrite {1}/arb.
by rewrite altC choicemm altC.
Qed.

Lemma coinarb_spec_convexity p w : coinarb p =
  (bcoin w : M _) [~] (Ret false : M _) [~] (Ret true  : M _) [~] bcoin (`Pr w.~).
Proof.
rewrite coinarb_spec [in LHS]/arb [in LHS](convexity _ _ w) 2!choicemm.
rewrite [in LHS]altC -(altA _ (Ret false)) altCA -2![in RHS]altA; congr (_ [~] _).
rewrite -altA altCA; congr (_ [~] _).
by rewrite /bcoin choiceC altC.
Qed.

End mixing_choices.

Module MonadExceptProb.
Record mixin_of (M : exceptMonad) (a : prob -> forall A : Type, M A -> M A -> M A) := Mixin {
  catchDl : forall A w, left_distributive (@Catch M A) (fun x y => a w A x y)
}.
Record class_of (m : Type -> Type) := Class {
  base : MonadExcept.class_of m ;
  base2 : MonadProb.mixin_of (Monad.Pack (MonadFail.base (MonadExcept.base base))) ;
  mixin : @mixin_of (MonadExcept.Pack base) (@Choice (MonadProb.Pack (MonadProb.Class base2)))
}.
Structure t : Type := Pack { m : Type -> Type ; class : class_of m }.
Definition baseType (M : t) : exceptMonad := MonadExcept.Pack (base (class M)).
Module Exports.
Notation exceptProbMonad := t.
Coercion baseType : exceptProbMonad >-> exceptMonad.
Canonical baseType.
Definition prob_of_exceptprob M :=
  MonadProb.Pack (MonadProb.Class (base2 (class M))).
Canonical prob_of_exceptprob.
End Exports.
End MonadExceptProb.
Export MonadExceptProb.Exports.

Definition coins23 {M : exceptProbMonad} : M bool :=
  Ret true <| `Pr / 2 |> (Ret false <| `Pr / 2 |> (Fail : M _)).

Lemma H23 : (0 <= 2/3 <= 1)%R. Proof. split; lra. Qed.

Lemma choiceA_compute {N : probMonad} (T F : bool) (f : bool -> N bool) :
  f T <|`Pr / 9|> (f F <|`Pr / 8|> (f F <|`Pr / 7|> (f F <|`Pr / 6|>
 (f T <|`Pr / 5|> (f F <|`Pr / 4|> (f F <|`Pr / 3|> (f F <|`Pr / 2|>
  f T))))))) = f F <|`Pr / 3|> (f F <|`Pr / 2|> f T) :> N _.
Proof.
have H34 : (0 <= 3/4 <= 1)%R by split; lra.
have H27 : (0 <= 2/7 <= 1)%R by split; lra.
have H721 : (0 <= 7/21 <= 1)%R by split; lra.
have H2156 : (0 <= 21/56 <= 1)%R by split; lra.
have H25 : (0 <= 2/5 <= 1)%R by split; lra.
rewrite [in RHS](choiceA _ _ (`Pr /2) (@Prob.mk (2/3) H23)); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (`Pr /3) (`Pr /2) (`Pr /2) (@Prob.mk (2/3) H23)); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (`Pr /4) (@Prob.mk (2/3) H23) (`Pr /3) (@Prob.mk (3/4) H34)); last first.
  by rewrite 4!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (`Pr /7) (`Pr /6) (`Pr /2) (@Prob.mk (2/7) H27)); last first.
  by rewrite 4!probpK /= /onem; split; field.
rewrite choicemm.
rewrite [in LHS](choiceA (`Pr /8) (@Prob.mk (2/7) H27) (@Prob.mk (7/21) H721) (@Prob.mk (21/56) H2156)); last first.
  by rewrite 4!probpK /= /onem; split; field.
rewrite (choiceC (@Prob.mk (3/4) H34)).
rewrite [in LHS](choiceA (`Pr /5) (probcplt (@Prob.mk (3/4) H34)) (`Pr /2) (@Prob.mk (2/5) H25)); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite choicemm.
rewrite (choiceC (@Prob.mk (2/5) H25)).
rewrite [in LHS](choiceA (@Prob.mk (21/56) H2156) (probcplt (Prob.mk H25)) (`Pr /2) (Prob.mk H34)); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm.
rewrite (choiceC (Prob.mk H34)).
rewrite [in LHS](choiceA (`Pr /9) (probcplt (Prob.mk H34)) (`Pr /3) (`Pr /3)); last first.
  by rewrite 3!probpK /= /onem; split; field.
rewrite choicemm choiceC.
rewrite (@choice_ext (Prob.mk H23)) //= /onem; by field.
Qed.

Definition uFFT {M : probMonad} : M bool :=
  uniform true [:: false; false; true].

Lemma uFFTE (M : probMonad) : uFFT = bcoin (`Pr /3) :> M _.
Proof.
rewrite /uFFT /bcoin uniform_cons.
rewrite (_ : `Pr _ = `Pr /3)%R; last exact/prob_ext.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : `Pr _ = `Pr /2)%R; last first.
  exact/prob_ext.
rewrite uniform_singl //=.
rewrite (choiceA _ _ (`Pr /2) (Prob.mk H23)); last first.
  rewrite /= /onem; split; field.
rewrite choicemm choiceC.
rewrite (_ : (`Pr / 3)%R = probcplt (Prob.mk H23)) //.
apply prob_ext => /=; rewrite /onem; field.
Qed.

Definition uTTF {M : probMonad} : M bool :=
  uniform true [:: true; true; false].

Lemma uTTFE (M : probMonad) : uTTF = bcoin (@Prob.mk (2/3) H23) :> M _.
Proof.
rewrite /uTTF /bcoin uniform_cons.
rewrite (_ : `Pr _ = `Pr /3)%R; last exact: prob_ext.
rewrite uniform_cons.
rewrite [in X in _ <| _ |> X](_ : `Pr _ = `Pr /2)%R; last exact/prob_ext.
rewrite uniform_singl //=.
rewrite (choiceA _ _ (`Pr /2) (Prob.mk H23)); last first.
  rewrite /= /onem; split; field.
by rewrite choicemm choiceC.
Qed.

Lemma uniform_notin (M : probMonad) (A : eqType) (def : A) (s : seq A) B
  (ma mb : A -> M B) (p : pred A) :
  s != [::] ->
  (forall x, x \in s -> ~~ p x) ->
  (do t <- uniform def s ; if p t then ma t else mb t) =
  (do t <- uniform def s ; mb t).
Proof.
elim: s => [//|h t IH _ H].
rewrite uniform_cons.
case/boolP : (t == [::]) => [/eqP -> {IH}|t0].
  rewrite uniform_nil.
  rewrite (_ : `Pr _ = `Pr 1); last by apply prob_ext => /=; rewrite Rinv_1.
  rewrite choice1.
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
rewrite 2!prob_bindDl; congr (_ <| _ |> _).
  rewrite 2!bindretf ifF //; apply/negbTE/H; by rewrite mem_head.
by rewrite IH // => a ta; rewrite H // in_cons ta orbT.
Qed.