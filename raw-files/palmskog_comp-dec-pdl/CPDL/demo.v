
Require Import Relations Classical_Pred_Type.
From mathcomp Require Import all_ssreflect.
From CDPDL Require Import edone bcase fset base.
From CDPDL Require Import CPDL.PDL_def.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Arguments subsep [T X P].

Implicit Types (S cls X Y : {fset clause}) (C D : clause).

Definition rtrans a C D := (R a C `<=` D) && (Rc a D `<=` C).

Fixpoint reach_demo cls p : rel clause :=
  match p with
  | pV a => rtrans a
  | pSeq p0 p1 => (fun C D => [some C' in cls, reach_demo cls p0 C C' && reach_demo cls p1 C' D])
  | pCh p0 p1 => (fun C D => reach_demo cls p0 C D || reach_demo cls p1 C D)
  | pStar p => (fun C D => connect_in cls (reach_demo cls p) C D)
  | pTest s => (fun C D => (C == D) && (s^+ \in C))
  | pConv p => (fun C D => reach_demo cls p D C)
  end.

Definition D0 cls := forall C, C \in cls -> hintikka C.
Definition D1 cls := forall C, C \in cls -> forall p s, [p]s^- \in C -> [some D in cls, reach_demo cls p C D &&  (s^- \in D)].

Record demo := Demo {
  cls :> {fset clause} ;
  demoD0 : D0 cls ;
  demoD1 : D1 cls }.

Arguments demoD1 [d C] _ [p s] _.

Canonical demo_predType := PredType (fun (S : demo) (C : clause) => nosimpl C \in cls S).

Lemma LCF (S : demo) C : C \in S -> ((fF^+ \in C) = false) * (forall p, (fV p^+ \in C) && (fV p^- \in C) = false).
Proof.
  move/demoD0. case/andP => /andP [/negbTE -> /allP H] _. split => // x.
  case inC: (fV x^+ \in C) => //=. apply: negbTE. apply: H _ inC.
Qed.


Section ModelExistience.
  Variables (S : demo).
  Hypothesis cnf_S : (forall s C, s \in C -> C \in S -> is_cnf (drop_sign s)).

  Definition Mtype := seq_sub S.
  Definition Mtrans a : rel Mtype := @restrict _ S (rtrans a).
  Definition Mlabel (x: var) (C : Mtype) := fV x^+ \in val C.

  Definition model_of := FModel Mtrans Mlabel.

  Implicit Types (c d e : model_of).

  Unset Printing Records.

  Lemma model_of_cnf c s : s \in val c -> is_cnf (drop_sign s).
  Proof. move => A. exact: cnf_S (valP c). Qed.

  Lemma model_of_dc c s : s \in val c -> hintikka' s (val c).
  Proof. case/demoD0/andP : (valP c) => _ /allP. apply. Qed.

  Lemma model_reach_pos p s c d :
    (forall t e, sizef t < sizep p -> t^- \in val e -> ~ eval t e) ->
    [p]s^+ \in val c -> reach p c d -> s^+ \in val d.
  Proof.
    elim: p s c d => [a|p0 IH0 p1 IH1|p0 IH0 p1 IH1|p IHp|t|p IHp] s c d /= Ht.
    - rewrite /= /Mtrans /restrict /= /rtrans => A /andP[] /subP B _. apply: B. by rewrite RE.
    - move/model_of_dc => /= /andP[A B] [].
      + apply: IH0 => // t e H. apply: Ht. by somega.
      + apply: IH1 => // t e H. apply: Ht. by somega.
    - move/model_of_dc => /= A [e E1 E2].
      (apply: IH1 E2; last apply: IH0 E1 => //) => t e' ?; apply Ht; by somega.
    - move => /= A B. elim: B A => {c d} [c|c e d A _ IH B]; first by case/model_of_dc/andP.
      apply: IH. case/model_of_dc/andP : B => _ ?. apply: IHp A => //.
      move => t {e} e A. apply: Ht. by somega.
    - case/model_of_dc/orP; last by move => ? [->].
      move => A [->] B. exfalso. apply: Ht A B. by somega.
    - move => A. case: p {IHp Ht} A (model_of_cnf A) => //= a.
      rewrite /= /Mtrans /restrict /= /rtrans => A _ /andP[_] /subP B.
      apply: B. by rewrite RcE.
  Qed.

  Lemma demo2reach p c d :
    (forall t e, sizef t < sizep p -> t^+ \in val e -> eval t e) ->
    reach_demo S p (val c) (val d) -> reach p c d.
  Proof.
    elim : p c d => [a|p0 IH0 p1 IH1|p0 IH0 p1 IH1|p IHp|s|p IHp] c d //= Ht.
    - move/orP => [H|H];[left; apply: IH0|right;apply: IH1] => // t e ?; apply Ht; by somega.
    - move/hasP => [C' inS /andP [L R]]. exists (SeqSub C' inS).
      + apply IH0 => // t e ?. by apply: Ht; somega.
      + apply IH1 => // t e ?. by apply: Ht; somega.
    - case/connect_inP => cs. elim: cs c d => /= [|e cd IH] c d.
      + case => _ _ /eqP. rewrite -[_ d == _ c]/(d == c) => /eqP->. by constructor.
      + case => /and3P[A B C] /andP[D E] F. apply: (StarL (z := SeqSub e B)).
        * apply: IHp => // t e' E'. apply: Ht; somega.
        * apply IH. by rewrite /= B C E F.
    - rewrite -[_ c == _ d]/(c == d) => /andP[/eqP-> A]. split => //. by apply: Ht A; somega.
    - apply: IHp => t e ?. by apply: Ht; somega.
  Qed.

  Ltac discharge_with tac := case/(_ _)/Wrap; first by tac.

  Theorem demo_eval s b c :  (s, b) \in val c -> eval (interp (s, b)) c.
  Proof with discharge_with somega.
    move: s b c. apply: (nat_size_ind (f := sizef)) => s IH b.
    case: s b IH => [|x|s t|p s] [|] IH c;
      try by rewrite /= ?(LCF (ssvalP c)); auto.
    - move => /= nx. rewrite /Mlabel. case: (LCF (ssvalP c)) => /= _ H px. move: (H x).
        by rewrite px nx.
    - case/hint_imp_pos ; first by case: c => C; exact: demoD0.
      move/IH => //=... tauto. move/IH => /=... by auto.
    - case/hint_imp_neg; first by case: c => C; exact: demoD0.
      move/IH => /=... move => Hs /IH => /=... by auto.
    - move => H d cRd. apply: (IH s _ true) => /=; first by somega.
      apply: model_reach_pos cRd => // t e A. apply: IH => //=. by somega.
    - move => inC /=. apply: ex_not_not_all.
      have /hasP CD: [some D in S , reach_demo S p (val c) D && (s^- \in D)]
        by apply: (demoD1 (ssvalP c)).
      case: CD => D DinS /andP [cRD inD]. exists (SeqSub D DinS).
      case/(_ _)/Wrap.
      + apply: demo2reach => // t e A. apply IH => //; by somega.
      + rewrite -/(not _). apply: (IH s _ false) => //=. by somega.
  Qed.

End ModelExistience.

Section Pruning.

  Variable (F: {fset form}).
  Hypothesis sfc_F : sf_closed F.
  Definition PU := powerset (flipcl F).
  Definition S0 := [fset C in PU | hintikka C && maximal F C].

  Definition pcond C S := ~~ [all u in C, if u is [p]s^- then
    [some D in S, reach_demo S p C D && (s^- \in D)] else true].

  Lemma prune_D0 : D0 (prune pcond S0).
  Proof.
    move => C. move/(subP (prune_sub _ _)). rewrite inE. by case/and3P.
  Qed.

  Lemma prune_D1 : D1 (prune pcond S0).
  Proof.
    move => C /pruneE. rewrite negbK. move/allP => H p s Hs. exact: (H ([p]s^-) Hs).
  Qed.

  Definition DD := Demo prune_D0 prune_D1.

  Definition supp S (C: clause) := [some D in S, C `<=` D].

  Local Notation "S |> C" := (supp S C) (at level 30, format "S  |>  C").

  Definition coref (ref : clause -> Prop) S :=
    forall C, C \in S0 `\` S -> ref C.

  Inductive pref : clause -> Prop :=
  | P1 S C : coref pref S -> C \in PU -> ~~ S |> C -> pref C
  | P2 S C p s : S `<=` S0 -> coref pref S -> C \in S
                 -> [p]s^- \in C -> ~~[some D in S, reach_demo S p C D && (s^- \in D)] -> pref C.

  Lemma corefD1 S C : pref C -> coref pref S -> coref pref (S `\` [fset C]).
  Proof.
    move => rC coS D. rewrite !in_fsetD negb_and andb_orr -in_fsetD negbK in_fset1.
    case/orP; first exact: coS. by case/andP => [_ /eqP ->].
  Qed.

  Lemma coref_DD : coref pref DD.
  Proof.
    apply: prune_myind => [C|C S]; first by rewrite inE andbN.
    case/allPn. case. case => // p s. case => // inC H inS corS sub.
    apply: corefD1 => //. exact: (P2 sub).
  Qed.

  Lemma DD_refute C : C \in PU -> ~~ DD |> C -> pref C.
  Proof. move => inU. apply: P1 _ inU => //. exact: coref_DD. Qed.

End Pruning.

Definition satT (M: cmodel) C := { w: M | forall s, s \in C -> eval (interp s) w}.

Notation "S |> C" := (supp S C) (at level 30, format "S  |>  C").

Theorem pruning_completeness F (sfc_F : sf_closed F) (C: clause) :
  (forall s E, s \in E -> E \in PU F -> is_cnf (drop_sign s)) ->
  C \in PU F -> pref F C + { M: fmodel & satT M C & #|{: M}| <= 2 ^ (2 * size F)}.
Proof.
  move => cnf_S inPU. case: (boolP ((DD F) |> C)) => H; [right|left; exact: DD_refute].
  exists (model_of (DD F)).
  - case/hasS : H => D D1 /subP D2. exists (SeqSub _ D1) => s inC.
    move: inPU. move/powersetP => sub. case: s inC => s b inC.
    apply: demo_eval => //=; last exact: D2.
    move => t E inE H. apply: cnf_S inE _. move: H. apply/subP.
    apply: sub_trans (prune_sub _ _) _. exact: subsep.
  - rewrite card_seq_sub ?funiq //.
    apply: leq_trans; last by apply: (leq_pexp2l _ (size_flipcl F)).
    rewrite -powerset_size subset_size /DD /S0 //=.
    apply: sub_trans; [exact: prune_sub | exact: subsep].
Qed.