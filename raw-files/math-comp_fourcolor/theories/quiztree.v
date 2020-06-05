
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp
Require Import path fingraph.
From fourcolor
Require Import hypermap geometry color coloring quiz cfmap cfquiz cfreducible.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive quiz_tree :=
  | QztNil
  | QztLeaf of question & question & question & quiz_tree
  | QztNode of quiz_tree & quiz_tree & quiz_tree & quiz_tree
  | QztHubNode of quiz_tree & quiz_tree & quiz_tree & quiz_tree.

Definition qzt_proper qt' := if qt' is QztNil then false else true.

Fixpoint qzt_put1 (qa : qarity) (qr : quiz_tree -> quiz_tree) (t : quiz_tree)
    {struct t} : quiz_tree :=
  match t, qa with
  | QztNode t5 t6 t7 t8, Qa5 => QztNode (qr t5) t6 t7 t8
  | QztNode t5 t6 t7 t8, Qa6 => QztNode t5 (qr t6) t7 t8
  | QztNode t5 t6 t7 t8, Qa7 => QztNode t5 t6 (qr t7) t8
  | QztNode t5 t6 t7 t8, Qa8 => QztNode t5 t6 t7 (qr t8)
  | QztHubNode t58 t9 t10 t11, Qa9 => QztHubNode t58 (qr t9) t10 t11
  | QztHubNode t58 t9 t10 t11, Qa10 => QztHubNode t58 t9 (qr t10) t11
  | QztHubNode t58 t9 t10 t11, Qa11 => QztHubNode t58 t9 t10 (qr t11)
  | QztHubNode t58 t9 t10 t11, _ =>
      QztHubNode (qzt_put1 qa qr t58) t9 t10 t11
  | _, _ => t
  end.

Definition qzt_put3 qa1 qa2 qa3 q1 q2 q3 :=
  qzt_put1 qa1 (qzt_put1 qa2 (qzt_put1 qa3 (QztLeaf q1 q2 q3))).

Definition qzt_put3rot qa1 qa2 qa3 q1 q2 q3 t :=
  qzt_put3 qa1 qa2 qa3 q1 q2 q3
    (qzt_put3 qa2 qa3 qa1 q2 q3 q1 (qzt_put3 qa3 qa1 qa2 q3 q1 q2 t)).

Definition qzt_put (qa1 qa2 qa3 : qarity) q1 q2 q3 :=
  if 8 < qa1 then qzt_put3 qa1 qa2 qa3 q1 q2 q3 else
  qzt_put3rot qa1 qa2 qa3 q1 q2 q3.

Definition qzt_empty :=
  let mkn t := QztNode t t t t in
  let n2 := mkn (mkn QztNil) in QztHubNode (mkn n2) n2 n2 n2.

Definition normq q :=
  match q with
  | Qask1 qa => QaskLR qa Qask0 Qask0
  | QaskL qa ql => QaskLR qa ql Qask0
  | QaskR qa qr => QaskLR qa Qask0 qr
  | _ => q
  end.

Definition store_qz qz :=
  if qz is Quiz (QaskR qa1 q1) (QaskR qa2 q2) then
      match normq q1, normq q2 with
      | QaskLR qa1r q1l q1r, QaskLR qa2r q2l q2r =>
          if qa1r < qa2r then qzt_put qa1 qa2 qa1r q1l q2 q1r else
                              qzt_put qa1 qa2r qa2 q1 q2r q2l
      | QaskLR qa1r q1l q1r, _ => qzt_put qa1 qa2 qa1r q1l q2 q1r
      | _, QaskLR qa2r q2l q2r => qzt_put qa1 qa2r qa2 q1 q2r q2l
      | _, _ => fun t => t
      end
  else fun t => t.

Definition store_cf_qz qz (sym : bool) t :=
   store_qz qz (if sym then t else store_qz (flipqz qz) t).

Fixpoint cfquiz_tree_rec (qt : quiz_tree) (cfs : seq config) : quiz_tree :=
  if cfs isn't cf :: cfs' then qt else
  let qt' := store_cf_qz (cfquiz cf) (cfsym cf) qt in
  if qt' is QztHubNode _ _ _ _ then cfquiz_tree_rec qt' cfs' else QztNil.

Definition cfquiz_tree := cfquiz_tree_rec qzt_empty.

Fixpoint qzt_size (t : quiz_tree) : nat :=
  match t with
  | QztLeaf _ _ _ t' => (qzt_size t').+1
  | QztNode t5 t6 t7 t8 =>
      qzt_size t5 + (qzt_size t6 + (qzt_size t7 + qzt_size t8))
  | QztHubNode t58 t9 t10 t11 =>
      qzt_size t58 + (qzt_size t9 + (qzt_size t10 + qzt_size t11))
  | _ => 0
  end.

Definition cf_main_arity cf :=
  if cfquiz cf is Quiz (QaskR qa _) _ then qa : nat else 0.

Definition cf_qzt_size1 cf :=
  let nperm := if cf_main_arity cf <= 8 then 3 else 1 in
  if cfsym cf then nperm else double nperm.

Definition cf_qzt_size := foldr (fun cf => plus (cf_qzt_size1 cf)) 0.

Definition configs_compiled cfs := qzt_size (cfquiz_tree cfs) = cf_qzt_size cfs.

Fixpoint qzt_get1 (qa : qarity) (t : quiz_tree) {struct t} : quiz_tree :=
  match t, qa with
  | QztNode t' _ _ _, Qa5 => t'
  | QztNode _ t' _ _, Qa6 => t'
  | QztNode _ _ t' _, Qa7 => t'
  | QztNode _ _ _ t', Qa8 => t'
  | QztHubNode _ t' _ _, Qa9 => t'
  | QztHubNode _ _ t' _, Qa10 => t'
  | QztHubNode _ _ _ t', Qa11 => t'
  | QztHubNode t' _ _ _, _ => qzt_get1 qa t'
  | _, _ => QztNil
  end.

Definition qzt_get2 qa2 qa3 t := qzt_get1 qa3 (qzt_get1 qa2 t).

Definition qzt_get3 qa1 qa2 qa3 t := qzt_get2 qa2 qa3 (qzt_get1 qa1 t).

Section FitQuizTree.

Variables (cfs : seq config) (G : hypermap).
Hypothesis geoG : plain_cubic G.
Let De2 := plain_eq geoG.
Let Dn3 := cubic_eq geoG.

Lemma fit_normq (x : G) q : fitq x (normq q) = fitq x q.
Proof. by case: q => *; rewrite /fitq /= ?cats0. Qed.

Variable x1 : G.
Notation x2 := (node x1).
Notation x3 := (node x2).
Let ax1 := qarity_of_nat (arity x1).
Let ax2 := qarity_of_nat (arity x2).
Let ax3 := qarity_of_nat (arity x3).

Local Notation "x '=a' y" := (x == arity y :> nat) (at level 70, only parsing).
Definition qzt_fita := [&& ax1 =a x1, ax2 =a x2 & ax3 =a x3].

Fixpoint qzt_fitl (t : quiz_tree) : bool :=
  if t is QztLeaf q1 q2 q3 t' then
      [&& fitq (qstepR x1) q1, fitq (qstepR x2) q2 & fitq (qstepR x3) q3]
    || qzt_fitl t'
  else false.

Definition qzt_fit t := qzt_fita && qzt_fitl (qzt_get3 ax1 ax2 ax3 t).

Local Notation quiz3 := (fun qa1 qa2 qa3 q1 q2 q3 =>
   Quiz (QaskR qa1 (QaskLR qa3 q1 q3)) (QaskR qa2 q2)).

Lemma qzt_get_put1 qa qa' qr t :
    qa = qa' /\ qr (qzt_get1 qa t) = qzt_get1 qa (qzt_put1 qa' qr t)
 \/ qzt_get1 qa t = qzt_get1 qa (qzt_put1 qa' qr t).
Proof. by elim: t; auto; case qa'; auto; case qa; auto. Qed.

Let qgp1 := qzt_get_put1.
Lemma qzt_fit_put3 qa1 qa2 qa3 q1 q2 q3 t :
   qzt_fit (qzt_put3 qa1 qa2 qa3 q1 q2 q3 t) ->
 fitqz (edge x2) (quiz3 qa1 qa2 qa3 q1 q2 q3) \/ qzt_fit t.
Proof.
case/andP=> Eax; rewrite /qzt_fit Eax /fitqz /= !eqseq_cons -arity_face nodeK.
rewrite /qstepR De2 /qstepL Dn3 -!catA /= 2!fitq_cat map_cons eqseq_cons.
have{Eax} [/eqP <- /eqP <- /eqP <-] := and3P Eax.
rewrite /qzt_get3 /qzt_get2 /qzt_put3; set qr := QztLeaf q1 q2 q3.
have [[<- <-]|<-] := qgp1 ax1 qa1 (qzt_put1 qa2 (qzt_put1 qa3 qr)) t; auto.
have [[<- <-]|<-] := qgp1 ax2 qa2 (qzt_put1 qa3 qr) (qzt_get1 ax1 t); auto.
have [[<- <-]|<-] := qgp1 ax3 qa3 qr (qzt_get1 ax2 (qzt_get1 ax1 t)); auto.
by rewrite !eqxx !andTb /= [rhc in _ && rhc]andbC => /orP[]; auto.
Qed.

Lemma fitqz_rot (y : G) qa1 qa2 qa3 q1 q2 q3 :
  fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3)
   = fitqz (edge (face y)) (quiz3 qa3 qa1 qa2 q3 q1 q2).
Proof.
rewrite /fitqz /= !eqseq_cons -!catA !fitq_cat !map_cons !eqseq_cons.
rewrite /qstepL /qstepR !De2 faceK -{1}[node (edge y)]nodeK !arity_face.
by rewrite -{1 2}[edge y]edgeK De2 Dn3 -{8 9}[y]De2 edgeK; do !bool_congr.
Qed.

Lemma qzt_fit_put qa1 qa2 qa3 q1 q2 q3 t :
   qzt_fit (qzt_put qa1 qa2 qa3 q1 q2 q3 t) ->
 (exists y : G, fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3)) \/ qzt_fit t.
Proof.
rewrite /qzt_put /qzt_put3rot.
case (8 < qa1); first by case/qzt_fit_put3; auto; left; exists (edge x2).
case/qzt_fit_put3; first by left; exists (edge x2).
case/qzt_fit_put3; first by rewrite fitqz_rot nodeK; left; exists (edge x1).
case/qzt_fit_put3; auto.
by rewrite 2!fitqz_rot -[x1]Dn3 !nodeK; left; exists (edge x3).
Qed.

Lemma fitqz_swap (y : G) qa1 qa2 qa3 q1 q2 q3 :
  fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3) =
    fitqz (face y) (Quiz (QaskR qa1 q1) (QaskR qa3 (QaskLR qa2 q3 q2))).
Proof.
rewrite /fitqz /= !eqseq_cons -!catA !fitq_cat !map_cons !eqseq_cons fitq_cat.
rewrite /qstepR /qstepL !De2 -{1}[node (edge y)]nodeK !arity_face faceK.
by rewrite -{1 2}[edge y]edgeK De2 Dn3 -{10 11}[y]De2 edgeK; do !bool_congr.
Qed.

Lemma qzt_fit_store qz t :
    qzt_fit (store_qz qz t) ->
  (isQuizR qz /\ exists y : G, fitqz y qz) \/ qzt_fit t.
Proof.
case: qz => q1 []; auto; case: q1; auto => qa1 q1 qa2 q2 qz_t.
set qz := Quiz _ _; pose fit_qzt := (exists y : G, fitqz y qz) \/ qzt_fit t.
suffices: fit_qzt by case; [left | right].
have fit_q1LR qa1r q1l q1r: normq q1 = QaskLR qa1r q1l q1r ->
  qzt_fit (qzt_put qa1 qa2 qa1r q1l q2 q1r t) -> fit_qzt.
- move=> Dq1 /qzt_fit_put[[y fit_y]|]; [left; exists y | by right].
  by move: fit_y; rewrite -Dq1 /fitqz !eqseq_cons fitq_cat fit_normq -fitq_cat.
have fit_q2LR qa2r q2l q2r: normq q2 = QaskLR qa2r q2l q2r ->
  qzt_fit (qzt_put qa1 qa2r qa2 q1 q2r q2l t) -> fit_qzt.
- move=> Dq2 /qzt_fit_put[[y fit_y]|]; [left; exists (face y) | by right].
  apply: etrans fit_y; rewrite fitqz_swap -Dq2 /fitqz !eqseq_cons !fitq_cat.
  by rewrite /= !eqseq_cons; congr [&& _, _, _ & _]; apply/esym/fit_normq.
move: qz_t => /=.
case Dq1: (normq q1); case Dq2: (normq q2); try case: ifP; by [right | eauto].
Qed.

Lemma qzt_fit_store_cf qz sym t :
     qzt_fit (store_cf_qz qz sym t) ->
   [/\ isQuizR qz
     & (exists y : G, fitqz y qz) \/ (exists y : mirror G, fitqz y qz)]
 \/ qzt_fit t.
Proof.
rewrite /store_cf_qz /=; case: sym; do!case/qzt_fit_store; try tauto.
case=> qzR [y]; have{qzR} qzR: isQuizR qz by case: (qz) qzR => q1 []; case: q1.
by rewrite fitqz_flip //; left; split; last by right; exists (face y).
Qed.

Lemma qzt_fit_cfquiz cfs1 :
   qzt_fit (cfquiz_tree cfs1) ->
 exists2 i, i < size cfs1  & exists2 qz,
   (exists y : G, fitqz y qz) \/ (exists y : mirror G, fitqz y qz)
 & let r := cfring (nth cf000 cfs1 i) in
   embeddable r /\ (exists u, valid_quiz r u qz).
Proof.
rewrite /cfquiz_tree.
have: qzt_fit qzt_empty = false.
  by rewrite /qzt_fit andbC; case: ax1 => //; case: ax2 => //; case ax3.
elim: cfs1 qzt_empty => [|cf cfs1 IHcfs] qt0 /= => [-> // | fit'qt0].
have fit'nil: ~ qzt_fit QztNil by case/andP.
set qt := store_cf_qz _ _ qt0.
case Dqt: qt => // [t58 t9 t10 t11]; rewrite -{t58 t9 t10 t11}Dqt => fit_cfs1.
case fit_qt: (qzt_fit qt); last by have [//| i] := IHcfs _ fit_qt; exists i.+1.
case/qzt_fit_store_cf: fit_qt fit'qt0 => [[cfR fit_cf] _ | -> //].
exists 0 => //; exists (cfquiz cf) => //.
by split; [apply: embeddable_cfquiz | apply: valid_cfquiz].
Qed.

Definition qzt_truncate t :=
  if t is QztHubNode (QztNode _ _ _ _ as t58) _ _ _ then t58 else t.

Lemma qzt_get1_truncate qa t :
  let t' := qzt_get1 qa (qzt_truncate t) in qzt_proper t' -> t' = qzt_get1 qa t.
Proof. by case: qa t => [] // [] // []. Qed.

End FitQuizTree.