
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype.
From mathcomp Require Import bigop finset fingroup morphism automorphism.
From mathcomp Require Import quotient gproduct.

Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope gFun_scope with gF.

Module GFunctor.

Definition object_map := forall gT : finGroupType, {set gT} -> {set gT}.

Bind Scope gFun_scope with object_map.

Section Definitions.

Implicit Types gT hT : finGroupType.

Variable F : object_map.

Definition group_valued := forall gT (G : {group gT}), group_set (F G).

Definition closed := forall gT (G : {group gT}), F G \subset G.

Definition continuous :=
  forall gT hT (G : {group gT}) (phi : {morphism G >-> hT}),
    phi @* F G \subset F (phi @* G).

Definition iso_continuous :=
  forall gT hT (G : {group gT}) (phi : {morphism G >-> hT}),
   'injm phi -> phi @* F G \subset F (phi @* G).

Lemma continuous_is_iso_continuous : continuous -> iso_continuous.
Proof. by move=> Fcont gT hT G phi inj_phi; apply: Fcont. Qed.

Definition pcontinuous :=
  forall gT hT (G D : {group gT}) (phi : {morphism D >-> hT}),
    phi @* F G \subset F (phi @* G).

Lemma pcontinuous_is_continuous : pcontinuous -> continuous.
Proof. by move=> Fcont gT hT G; apply: Fcont. Qed.

Definition hereditary :=
  forall gT (H G : {group gT}), H \subset G -> F G :&: H \subset F H.

Lemma pcontinuous_is_hereditary : pcontinuous -> hereditary.
Proof.
move=> Fcont gT H G sHG; rewrite -{2}(setIidPl sHG) setIC.
by do 2!rewrite -(morphim_idm (subsetIl H _)) morphimIdom ?Fcont.
Qed.

Definition monotonic :=
  forall gT (H G : {group gT}), H \subset G -> F H \subset F G.

Variables (k : unit) (F1 F2 : object_map).

Definition comp_head : object_map := fun gT A => let: tt := k in F1 (F2 A).

Definition modulo : object_map :=
  fun gT A => coset (F2 A) @*^-1 (F1 (A / (F2 A))).

End Definitions.

Section ClassDefinitions.

Structure iso_map := IsoMap {
  apply : object_map;
  _ : group_valued apply;
  _ : closed apply;
  _ : iso_continuous apply
}.
Local Coercion apply : iso_map >-> object_map.

Structure map := Map { iso_of_map : iso_map; _ : continuous iso_of_map }.
Local Coercion iso_of_map : map >-> iso_map.

Structure pmap := Pmap { map_of_pmap : map; _ : hereditary map_of_pmap }.
Local Coercion map_of_pmap : pmap >-> map.

Structure mono_map := MonoMap { map_of_mono : map; _ : monotonic map_of_mono }.
Local Coercion map_of_mono : mono_map >-> map.

Definition pack_iso F Fcont Fgrp Fsub := @IsoMap F Fgrp Fsub Fcont.

Definition clone_iso (F : object_map) :=
  fun Fgrp Fsub Fcont (isoF := @IsoMap F Fgrp Fsub Fcont) =>
  fun isoF0 & phant_id (apply isoF0) F & phant_id isoF isoF0 => isoF.

Definition clone (F : object_map) :=
  fun isoF & phant_id (apply isoF) F =>
  fun (funF0 : map) & phant_id (apply funF0) F =>
  fun Fcont (funF := @Map isoF Fcont) & phant_id funF0 funF => funF.

Definition clone_pmap (F : object_map) :=
  fun (funF : map) & phant_id (apply funF) F =>
  fun (pfunF0 : pmap) & phant_id (apply pfunF0) F =>
  fun Fher (pfunF := @Pmap funF Fher) & phant_id pfunF0 pfunF => pfunF.

Definition clone_mono (F : object_map) :=
  fun (funF : map) & phant_id (apply funF) F =>
  fun (mfunF0 : mono_map) & phant_id (apply mfunF0) F =>
  fun Fmon (mfunF := @MonoMap funF Fmon) & phant_id mfunF0 mfunF => mfunF.

End ClassDefinitions.

Module Exports.

Identity Coercion fun_of_object_map : object_map >-> Funclass.
Coercion apply : iso_map >-> object_map.
Coercion iso_of_map : map >-> iso_map.
Coercion map_of_pmap : pmap >-> map.
Coercion map_of_mono : mono_map >-> map.
Coercion continuous_is_iso_continuous : continuous >-> iso_continuous.
Coercion pcontinuous_is_continuous : pcontinuous >-> continuous.
Coercion pcontinuous_is_hereditary : pcontinuous >-> hereditary.

Notation "[ 'igFun' 'by' Fsub & Fcont ]" :=
    (pack_iso (continuous_is_iso_continuous Fcont) (fun gT G => groupP _) Fsub)
  (at level 0, format "[ 'igFun'  'by'  Fsub  &  Fcont ]") : form_scope.

Notation "[ 'igFun' 'by' Fsub & ! Fcont ]" :=
    (pack_iso Fcont (fun gT G => groupP _) Fsub)
  (at level 0, format "[ 'igFun'  'by'  Fsub  &  ! Fcont ]") : form_scope.

Notation "[ 'igFun' 'of' F ]" := (@clone_iso F _ _ _ _ id id)
  (at level 0, format "[ 'igFun'  'of'  F ]") : form_scope.

Notation "[ 'gFun' 'by' Fcont ]" := (Map Fcont)
  (at level 0, format "[ 'gFun'  'by'  Fcont ]") : form_scope.

Notation "[ 'gFun' 'of' F ]" := (@clone F _ id _ id _ id)
  (at level 0, format "[ 'gFun'  'of'  F ]") : form_scope.

Notation "[ 'pgFun' 'by' Fher ]" := (Pmap Fher)
  (at level 0, format "[ 'pgFun'  'by'  Fher ]") : form_scope.

Notation "[ 'pgFun' 'of' F ]" := (@clone_pmap F _ id _ id _ id)
  (at level 0, format "[ 'pgFun' 'of'  F ]") : form_scope.

Notation "[ 'mgFun' 'by' Fmon ]" := (MonoMap Fmon)
  (at level 0, format "[ 'mgFun'  'by'  Fmon ]") : form_scope.

Notation "[ 'mgFun' 'of' F ]" := (@clone_mono F _ id _ id _ id)
  (at level 0, format "[ 'mgFun' 'of'  F ]") : form_scope.

End Exports.

End GFunctor.
Export GFunctor.Exports.

Bind Scope gFun_scope with GFunctor.object_map.

Notation "F1 \o F2" := (GFunctor.comp_head tt F1 F2) : gFun_scope.
Notation "F1 %% F2" := (GFunctor.modulo F1 F2) : gFun_scope.

Section FunctorGroup.

Variables (F : GFunctor.iso_map) (gT : finGroupType) (G : {group gT}).
Lemma gFgroupset : group_set (F gT G). Proof. by case: F. Qed.
Canonical gFgroup := Group gFgroupset.

End FunctorGroup.

Canonical gFmod_group
    (F1 : GFunctor.iso_map) (F2 : GFunctor.object_map)
    (gT : finGroupType) (G : {group gT}) :=
  [group of (F1 %% F2)%gF gT G].

Section IsoFunctorTheory.

Implicit Types gT rT : finGroupType.
Variable F : GFunctor.iso_map.

Lemma gFsub gT (G : {group gT}) : F gT G \subset G.
Proof. by case: F gT G. Qed.

Lemma gFsub_trans gT (G : {group gT}) (A : {pred gT}) :
  G \subset A -> F gT G \subset A.
Proof. exact/subset_trans/gFsub. Qed.

Lemma gF1 gT : F gT 1 = 1. Proof. exact/trivgP/gFsub. Qed.

Lemma gFiso_cont : GFunctor.iso_continuous F.
Proof. by case F. Qed.

Lemma gFchar gT (G : {group gT}) : F gT G \char G.
Proof.
apply/andP; split => //; first by apply: gFsub.
apply/forall_inP=> f Af; rewrite -{2}(im_autm Af) -(autmE Af).
by rewrite -morphimEsub ?gFsub ?gFiso_cont ?injm_autm.
Qed.

Lemma gFnorm gT (G : {group gT}) : G \subset 'N(F gT G).
Proof. exact/char_norm/gFchar. Qed.

Lemma gFnorms gT (G : {group gT}) : 'N(G) \subset 'N(F gT G).
Proof. exact/char_norms/gFchar. Qed.

Lemma gFnormal gT (G : {group gT}) : F gT G <| G.
Proof. exact/char_normal/gFchar. Qed.

Lemma gFchar_trans gT (G H : {group gT}) : H \char G -> F gT H \char G.
Proof. exact/char_trans/gFchar. Qed.

Lemma gFnormal_trans gT (G H : {group gT}) : H <| G -> F gT H <| G.
Proof. exact/char_normal_trans/gFchar. Qed.

Lemma gFnorm_trans gT (A : {pred gT}) (G : {group gT}) :
  A \subset 'N(G) -> A \subset 'N(F gT G).
Proof. by move/subset_trans/(_ (gFnorms G)). Qed.

Lemma injmF_sub gT rT (G D : {group gT}) (f : {morphism D >-> rT}) :
  'injm f -> G \subset D -> f @* (F gT G) \subset F rT (f @* G).
Proof.
move=> injf sGD; have:= gFiso_cont (injm_restrm sGD injf).
by rewrite im_restrm morphim_restrm (setIidPr _) ?gFsub.
Qed.

Lemma injmF gT rT (G D : {group gT}) (f : {morphism D >-> rT}) :
  'injm f -> G \subset D -> f @* (F gT G) = F rT (f @* G).
Proof.
move=> injf sGD; have [sfGD injf'] := (morphimS f sGD, injm_invm injf).
apply/esym/eqP; rewrite eqEsubset -(injmSK injf') ?gFsub_trans //.
by rewrite !(subset_trans (injmF_sub _ _)) ?morphim_invm // gFsub_trans.
Qed.

Lemma gFisom gT rT (G D : {group gT}) R (f : {morphism D >-> rT}) :
  G \subset D -> isom G (gval R) f -> isom (F gT G) (F rT R) f.
Proof.
case/(restrmP f)=> g [gf _ _ _]; rewrite -{f}gf => /isomP[injg <-].
by rewrite sub_isom ?gFsub ?injmF.
Qed.

Lemma gFisog gT rT (G : {group gT}) (R : {group rT}) :
  G \isog R -> F gT G \isog F rT R.
Proof. by case/isogP=> f injf <-; rewrite -injmF // sub_isog ?gFsub. Qed.

End IsoFunctorTheory.

Section FunctorTheory.

Implicit Types gT rT : finGroupType.
Variable F : GFunctor.map.

Lemma gFcont : GFunctor.continuous F.
Proof. by case F. Qed.

Lemma morphimF gT rT (G D : {group gT}) (f : {morphism D >-> rT}) :
  G \subset D -> f @* (F gT G) \subset F rT (f @* G).
Proof.
move=> sGD; rewrite -(setIidPr (gFsub F G)).
by rewrite -{3}(setIid G) -!(morphim_restrm sGD) gFcont.
Qed.

End FunctorTheory.

Section PartialFunctorTheory.

Implicit Types gT rT : finGroupType.

Section BasicTheory.

Variable F : GFunctor.pmap.

Lemma gFhereditary : GFunctor.hereditary F.
Proof. by case F. Qed.

Lemma gFunctorI gT (G H : {group gT}) :
  F gT G :&: H = F gT G :&: F gT (G :&: H).
Proof.
rewrite -{1}(setIidPr (gFsub F G)) [G :&: _]setIC -setIA.
rewrite -(setIidPr (gFhereditary (subsetIl G H))).
by rewrite setIC -setIA (setIidPr (gFsub F (G :&: H))).
Qed.

Lemma pmorphimF : GFunctor.pcontinuous F.
Proof.
move=> gT rT G D f; rewrite -morphimIdom -(setIidPl (gFsub F G)) setICA.
apply: (subset_trans (morphimS f (gFhereditary (subsetIr D G)))).
by rewrite (subset_trans (morphimF F _ _ )) ?morphimIdom ?subsetIl.
Qed.

Lemma gFid gT (G : {group gT}) : F gT (F gT G)  = F gT G.
Proof.
apply/eqP; rewrite eqEsubset gFsub.
by move/gFhereditary: (gFsub F G); rewrite setIid /=.
Qed.

End BasicTheory.

Section Modulo.

Variables (F1 : GFunctor.pmap) (F2 : GFunctor.map).

Lemma gFmod_closed : GFunctor.closed (F1 %% F2).
Proof. by move=> gT G; rewrite sub_cosetpre_quo ?gFsub ?gFnormal. Qed.

Lemma gFmod_cont : GFunctor.continuous (F1 %% F2).
Proof.
move=> gT rT G f; have nF2 := gFnorm F2.
have sDF: G \subset 'dom (coset (F2 _ G)) by rewrite nF2.
have sDFf: G \subset 'dom (coset (F2 _ (f @* G)) \o f).
  by rewrite -sub_morphim_pre ?subsetIl // nF2.
pose K := 'ker (restrm sDFf (coset (F2 _ (f @* G)) \o f)).
have sFK: 'ker (restrm sDF (coset (F2 _ G))) \subset K.
  rewrite {}/K !ker_restrm ker_comp /= subsetI subsetIl !ker_coset /=.
  by rewrite -sub_morphim_pre ?subsetIl // morphimIdom ?morphimF.
have sOF := gFsub F1 (G / F2 _ G); have sGG: G \subset G by [].
rewrite -sub_quotient_pre; last first.
  by apply: subset_trans (nF2 _ _); rewrite morphimS ?gFmod_closed.
suffices im_fact H : F2 _ G \subset gval H -> H \subset G ->
  factm sFK sGG @* (H / F2 _ G) = f @* H / F2 _ (f @* G).
- rewrite -2?im_fact ?gFmod_closed ?gFsub //.
    by rewrite cosetpreK morphimF /= ?morphim_restrm ?setIid.
  by rewrite -sub_quotient_pre ?normG //= trivg_quotient sub1G.
move=> sFH sHG; rewrite -(morphimIdom _ (H / _)) /= {2}morphim_restrm setIid.
rewrite -morphimIG ?ker_coset // -(morphim_restrm sDF) morphim_factm.
by rewrite morphim_restrm morphim_comp -quotientE morphimIdom.
Qed.

Canonical gFmod_igFun := [igFun by gFmod_closed & gFmod_cont].
Canonical gFmod_gFun := [gFun by gFmod_cont].

End Modulo.

Variables F1 F2 : GFunctor.pmap.

Lemma gFmod_hereditary : GFunctor.hereditary (F1 %% F2).
Proof.
move=> gT H G sHG; set FGH := _ :&: H; have nF2H := gFnorm F2 H.
rewrite -sub_quotient_pre; last exact: subset_trans (subsetIr _ _) _.
pose rH := restrm nF2H (coset (F2 _ H)); pose rHM := [morphism of rH].
have rnorm_simpl: rHM @* H = H / F2 _ H by rewrite morphim_restrm setIid.
have nF2G := subset_trans sHG (gFnorm F2 G).
pose rG := restrm nF2G (coset (F2 _ G)); pose rGM := [morphism of rG].
have sqKfK: 'ker rGM \subset 'ker rHM.
  rewrite !ker_restrm !ker_coset (setIidPr (gFsub F2 _)) setIC /=.
  exact: gFhereditary.
have sHH := subxx H; rewrite -rnorm_simpl /= -(morphim_factm sqKfK sHH) /=.
apply: subset_trans (gFcont F1 _); rewrite /= {2}morphim_restrm setIid /=.
apply: subset_trans (morphimS _ (gFhereditary _ (quotientS _ sHG))) => /=.
have ->: FGH / _ = restrm nF2H (coset _) @* FGH.
  by rewrite morphim_restrm setICA setIid.
rewrite -(morphim_factm sqKfK sHH) morphimS //= morphim_restrm -quotientE.
by rewrite setICA setIid (subset_trans (quotientI _ _ _)) // cosetpreK.
Qed.

Canonical gFmod_pgFun := [pgFun by gFmod_hereditary].

End PartialFunctorTheory.

Section MonotonicFunctorTheory.

Implicit Types gT rT : finGroupType.

Lemma gFunctorS (F : GFunctor.mono_map) : GFunctor.monotonic F.
Proof. by case: F. Qed.

Section Composition.

Variables (F1 : GFunctor.mono_map) (F2 : GFunctor.map).

Lemma gFcomp_closed : GFunctor.closed (F1 \o F2).
Proof. by move=> gT G; rewrite !gFsub_trans. Qed.

Lemma gFcomp_cont : GFunctor.continuous (F1 \o F2).
Proof.
move=> gT rT G phi; rewrite (subset_trans (morphimF _ _ (gFsub _ _))) //.
by rewrite (subset_trans (gFunctorS F1 (gFcont F2 phi))).
Qed.

Canonical gFcomp_igFun := [igFun by gFcomp_closed & gFcomp_cont].
Canonical gFcomp_gFun :=[gFun by gFcomp_cont].

End Composition.

Variables F1 F2 : GFunctor.mono_map.

Lemma gFcompS : GFunctor.monotonic (F1 \o F2).
Proof. by move=> gT H G sHG; rewrite !gFunctorS. Qed.

Canonical gFcomp_mgFun := [mgFun by gFcompS].

End MonotonicFunctorTheory.

Section GFunctorExamples.

Implicit Types gT : finGroupType.

Definition idGfun gT := @id {set gT}.

Lemma idGfun_closed : GFunctor.closed idGfun. Proof. by []. Qed.
Lemma idGfun_cont : GFunctor.continuous idGfun. Proof. by []. Qed.
Lemma idGfun_monotonic : GFunctor.monotonic idGfun. Proof. by []. Qed.

Canonical bgFunc_id := [igFun by idGfun_closed & idGfun_cont].
Canonical gFunc_id := [gFun by idGfun_cont].
Canonical mgFunc_id := [mgFun by idGfun_monotonic].

Definition trivGfun gT of {set gT} := [1 gT].

Lemma trivGfun_cont : GFunctor.pcontinuous trivGfun.
Proof. by move=> gT rT D G f; rewrite morphim1. Qed.

Canonical trivGfun_igFun := [igFun by sub1G & trivGfun_cont].
Canonical trivGfun_gFun := [gFun by trivGfun_cont].
Canonical trivGfun_pgFun := [pgFun by trivGfun_cont].

End GFunctorExamples.