
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq.
From fourcolor
Require Import color.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive ctree :=
  | CtreeNode of ctree & ctree & ctree
  | CtreeLeaf of ctree
  | CtreeEmpty.

Inductive ctree_pair := CtreePair of ctree & ctree.

Definition ctree_empty t := if t is CtreeEmpty then true else false.

Definition ctree_leaf t := if t is CtreeLeaf _ then true else false.

Definition ctree_empty_node t :=
  match t with
  | CtreeNode CtreeEmpty CtreeEmpty CtreeEmpty => true
  | CtreeNode _ CtreeEmpty CtreeEmpty => false
  | CtreeNode _ _ CtreeEmpty => false
  | _ => false
  end.

Inductive eq3_CtreeEmpty : forall t1 t2 t3 : ctree, Prop :=
    Eq3_CtreeEmpty : eq3_CtreeEmpty CtreeEmpty CtreeEmpty CtreeEmpty.

Definition ctree_sel t : color -> ctree :=
  match t with
  | CtreeNode t1 t2 t3 => palette CtreeEmpty t1 t2 t3
  | _ => fun _ => CtreeEmpty
  end.

Fixpoint ctree_proper h t {struct t} : Prop :=
  match t, h with
  | CtreeEmpty, _ => True
  | CtreeNode t1 t2 t3, h'.+1 =>
    [/\ ctree_empty_node t = false,
        ctree_proper h' t1, ctree_proper h' t2 & ctree_proper h' t3]
  | CtreeLeaf lf, 0 => ctree_proper 0 lf
  | _, _ => False
  end.

Fixpoint ctree_sub t et {struct t} :=
  match t, et with
  | CtreeNode t1 t2 t3, e :: et' =>
    (palette (fun _ => 0) (ctree_sub t1) (ctree_sub t2) (ctree_sub t3)) e et'
  | CtreeLeaf lf, [::] => (ctree_sub lf et).+1
  | _, _ => 0
  end.

Definition ctree_mem t et := ctree_sub t et != 0.

Definition ctree_empty_pair := CtreePair CtreeEmpty CtreeEmpty.

Definition ctree_pair_sub ctp b :=
  let: CtreePair t0 t1 := ctp in if b then t1 else t0.

Definition ctree_leaf_of n := iter n CtreeLeaf CtreeEmpty.

Definition ctree_cons t1 t2 t3 :=
  let t := CtreeNode t1 t2 t3 in
  match t with
  | CtreeNode CtreeEmpty CtreeEmpty CtreeEmpty => t1
  | CtreeNode _ CtreeEmpty CtreeEmpty => t
  | CtreeNode _ _ CtreeEmpty => t
  | _ => t
  end.

Definition ctree_cons0 (_ : ctree) := CtreeEmpty.

Definition ctree_cons1 t := ctree_cons t CtreeEmpty CtreeEmpty.

Definition ctree_cons2 t := ctree_cons CtreeEmpty t CtreeEmpty.

Definition ctree_cons3 t := ctree_cons CtreeEmpty CtreeEmpty t.

Definition ctree_simple_leaf := CtreeLeaf CtreeEmpty.

Definition ctree_cons_e :=
  palette ctree_cons0 ctree_cons1 ctree_cons2 ctree_cons3.

Definition ctree_of_ttail : colseq -> ctree :=
  foldr ctree_cons_e ctree_simple_leaf.

Fixpoint ctree_union tl tr {struct tr} :=
  match tl, tr with
  | CtreeNode tl1 tl2 tl3, CtreeNode tr1 tr2 tr3 =>
    ctree_cons (ctree_union tl1 tr1) (ctree_union tl2 tr2) (ctree_union tl3 tr3)
  | CtreeEmpty, _ => tr
  | _, CtreeEmpty => tl
  | _, _          => ctree_simple_leaf
  end.

Fixpoint ctree_rotl t :=
  if t isn't CtreeNode t1 t2 t3 then t else
  ctree_cons (ctree_rotl t3) (ctree_rotl t1) (ctree_rotl t2).

Fixpoint ctree_rotr t :=
  if t isn't CtreeNode t1 t2 t3 then t else
  ctree_cons (ctree_rotr t2) (ctree_rotr t3) (ctree_rotr t1).

Definition ctree_cons_rot t := ctree_cons t (ctree_rotl t) (ctree_rotr t).

Fixpoint ctree_union_rotlr tl tr {struct tr} :=
  match tl, tr with
  | CtreeNode tl1 tl2 tl3, CtreeNode tr1 tr2 tr3 =>
      let cur := ctree_union_rotlr in
      ctree_cons (cur tl3 tr2) (cur tl1 tr3) (cur tl2 tr1)
  | CtreeLeaf _, CtreeLeaf _ =>
    ctree_simple_leaf
  | _, _ =>
    ctree_union (ctree_rotl tl) (ctree_rotr tr)
  end.
Definition ctree_rotlr t := ctree_union_rotlr t t.

Fixpoint ctree_disjoint tl tr {struct tr} :=
  match tl, tr with
  | CtreeLeaf _, CtreeLeaf _ => false
  | CtreeNode tl1 tl2 tl3, CtreeNode tr1 tr2 tr3 =>
      if ctree_disjoint tl1 tr1
      then if ctree_disjoint tl2 tr2 then ctree_disjoint tl3 tr3 else false
      else false
  | _, _ => true
  end.

Lemma fold_ctree_empty A (ve vne : A) t :
 (if t is CtreeEmpty then ve else vne) = (if ctree_empty t then ve else vne).
Proof. by case : t. Qed.

Lemma fold_ctree_leaf A (vlf vnlf : A) t :
 (if t is CtreeLeaf _ then vlf else vnlf)
   = (if ctree_leaf t then vlf else vnlf).
Proof. by case: t. Qed.

Lemma ctree_empty_eq t : ctree_empty t -> t = CtreeEmpty.
Proof. by case: t. Qed.

Lemma ctree_empty_node_eq t1 t2 t3 :
  ctree_empty_node (CtreeNode t1 t2 t3) -> eq3_CtreeEmpty t1 t2 t3.
Proof. by move: t1 t2 t3; do 3!case=> [? ? ?|?|]. Qed.

Lemma ctree_empty_nodeP {t} :
 reflect (t = CtreeNode CtreeEmpty CtreeEmpty CtreeEmpty)
         (ctree_empty_node t).
Proof. by case: t; by [right | do 3!case=> [? ? ?|?|]; constructor]. Qed.

Lemma ctree_sel_0 t : ctree_sel t Color0 = CtreeEmpty.
Proof. by case: t. Qed.

Lemma ctree_proper_sel h t e :
  ctree_proper h t -> ctree_proper h.-1 (ctree_sel t e).
Proof. by case: h t e => [|h] [t1 t2 t3|lf|] //= [] []. Qed.

Lemma ctree_sub_0 t (et : colseq) : Color0 \in et -> ctree_sub t et = 0.
Proof.
by elim: et t => [|e et IHet] // [] // t1 t2 t3; case: e => //= /IHet.
Qed.

Lemma ctree_mem_0 t (et : colseq) : Color0 \in et -> ctree_mem t et = false.
Proof. by rewrite /ctree_mem => /ctree_sub_0->. Qed.

Lemma ctree_mem_seq0 t : ctree_mem t [::] = ctree_leaf t.
Proof. by case: t. Qed.

Lemma ctree_sub_sel t e (et : colseq) :
  ctree_sub t (e :: et) = ctree_sub (ctree_sel t e) et.
Proof. by case: t e => [t1 t2 t3|lf|] // []. Qed.

Lemma ctree_mem_sel t e (et : colseq) :
  ctree_mem t (e :: et) = ctree_mem (ctree_sel t e) et.
Proof. by rewrite /ctree_mem !ctree_sub_sel. Qed.

Lemma ctree_mem_leaf lf et : ctree_mem (CtreeLeaf lf) et = (size et == 0).
Proof. by case: et. Qed.

Lemma ctree_leaf_of_proper n : ctree_proper 0 (ctree_leaf_of n).
Proof. by case: n => //=; elim=> /=. Qed.

Lemma ctree_sub_leaf_of n et :
  ctree_sub (ctree_leaf_of n) et = (if size et == 0 then n else 0).
Proof. by case: et n => [|e et] [] //=; elim=> //= n ->. Qed.

Lemma ctree_cons_spec t1 t2 t3 (t := CtreeNode t1 t2 t3) :
  ctree_cons t1 t2 t3 = (if ctree_empty_node t then CtreeEmpty else t).
Proof. by do [move: t1 t2 t3; do 3!case=> [? ? ?|?|]] in t *. Qed.

Lemma ctree_leaf_cons t1 t2 t3 : ctree_leaf (ctree_cons t1 t2 t3) = false.
Proof. by rewrite ctree_cons_spec; case: ifP. Qed.

Lemma ctree_sel_cons t1 t2 t3 e :
  ctree_sel (ctree_cons t1 t2 t3) e = ctree_sel (CtreeNode t1 t2 t3) e.
Proof.
by rewrite ctree_cons_spec; case: ctree_empty_nodeP => // ->; case: e.
Qed.

Lemma ctree_cons_proper h t1 t2 t3 :
   ctree_proper h t1 -> ctree_proper h t2 -> ctree_proper h t3 ->
 ctree_proper h.+1 (ctree_cons t1 t2 t3).
Proof. by move=> t1ok t2ok t3ok; rewrite ctree_cons_spec; case: ifP. Qed.

Lemma ctree_sub_cons t1 t2 t3 et :
  ctree_sub (ctree_cons t1 t2 t3) et = ctree_sub (CtreeNode t1 t2 t3) et.
Proof.
rewrite ctree_cons_spec; case: ctree_empty_nodeP => // ->.
by case: et => [|[] et].
Qed.

Lemma ctree_mem_cons t1 t2 t3 et :
  ctree_mem (ctree_cons t1 t2 t3) et = ctree_mem (CtreeNode t1 t2 t3) et.
Proof. by rewrite /ctree_mem ctree_sub_cons. Qed.

Lemma ctree_cons_e_spec (e : color) t :
 let t_if_e c := if c == e then t else CtreeEmpty in
 ctree_cons_e e t = ctree_cons (t_if_e Color1) (t_if_e Color2) (t_if_e Color3).
Proof. by case: e t => [] []. Qed.

Lemma ctree_cons_e_proper h e t :
  ctree_proper h t -> ctree_proper h.+1 (ctree_cons_e e t).
Proof.
by move=> t_ok; rewrite ctree_cons_e_spec; apply: ctree_cons_proper; case: e.
Qed.

Lemma ctree_of_ttail_proper h (et : colseq) :
  size et = h -> ctree_proper h (ctree_of_ttail et).
Proof. by move <-; elim: et => // e et IHet; apply: ctree_cons_e_proper. Qed.

Lemma ctree_of_ttail_mem  (et et' : colseq) :
 Color0 \notin et -> reflect (et' = et) (ctree_mem (ctree_of_ttail et) et').
Proof.
elim: et et' => [|e et IHet] et' /=; first by case: et'; constructor.
rewrite inE => /norP[/eqP nz_e nz_et]; rewrite ctree_cons_e_spec ctree_mem_cons.
case: et' => [|e' et'] /=; first by right.
case De': e'; do [by right=> [] [] | rewrite ctree_mem_sel /= -{}De'];
  do [case: (e' =P e) => [<- | ]; last by right=> [] []];
  by apply: (iffP (IHet _ nz_et)) => [|[]] ->.
Qed.

Lemma ctree_union_Nl t : ctree_union CtreeEmpty t = t.
Proof. by case: t. Qed.

Lemma ctree_union_Nr t : ctree_union t CtreeEmpty = t.
Proof. by case: t. Qed.

Lemma ctree_union_sym t1 t2 : ctree_union t1 t2 = ctree_union t2 t1.
Proof.
elim: t1 t2 => [t11 IH1 t12 IH2 t13 IH3|l1 IHl|] [t21 t22 t23|l2|] //=.
by rewrite IH1 IH2 IH3.
Qed.

Lemma ctree_union_proper h tl tr :
  ctree_proper h tl -> ctree_proper h tr -> ctree_proper h (ctree_union tl tr).
Proof.
elim: h => [|h IHh] in tl tr *; first by case: tl => //; case: tr.
case: tl => // [tl1 tl2 tl3|]; case: tr => //= tr1 tr2 tr3 [? ? ? ?] [*].
by apply: ctree_cons_proper; apply: IHh.
Qed.

Lemma ctree_mem_union h tl tr et :
   ctree_proper h tl -> ctree_proper h tr ->
 ctree_mem (ctree_union tl tr) et = ctree_mem tl et || ctree_mem tr et.
Proof.
rewrite /ctree_mem; elim: h => [|h IHh] in tl tr et *.
  by case: tl; rewrite ?ctree_union_Nl //; case: tr => //; case: (et).
case: tl; rewrite ?ctree_union_Nl //= => tl1 tl2 tl3 [Htlne Htl1 Htl2 Htl3].
case: tr => //= [tr1 tr2 tr3 [*]|]; last by rewrite orbF.
by rewrite ctree_sub_cons; case: et => [|[] et] //=; apply: IHh.
Qed.

Lemma ctree_rotl_proper h t :
  ctree_proper h t -> ctree_proper h (ctree_rotl t).
Proof.
elim: h t => [|h IHh] [t1 t2 t3|lf|] //= [*].
by apply: ctree_cons_proper; apply: IHh.
Qed.

Lemma ctree_rotr_proper h t :
  ctree_proper h t -> ctree_proper h (ctree_rotr t).
Proof.
elim: h t => [|h IHh] [t1 t2 t3|lf|] //= [Hne Ht1 Ht2 Ht3].
by apply: ctree_cons_proper; apply: IHh.
Qed.

Lemma ctree_mem_rotl t et :
  ctree_mem (ctree_rotl t) et = ctree_mem t (permt Eperm312 et).
Proof.
rewrite /ctree_mem; elim: et t => [|e et IHet] [t1 t2 t3|lf|] //=;
 by rewrite ctree_sub_cons //; case: e => /=.
Qed.

Lemma ctree_mem_rotr t et :
  ctree_mem (ctree_rotr t) et = ctree_mem t (permt Eperm231 et).
Proof.
rewrite /ctree_mem; elim: et t => [|e et IHh] [t1 t2 t3|lf|] //=;
 by rewrite ctree_sub_cons //; case: e => /=.
Qed.

Lemma ctree_cons_rot_proper h t :
  ctree_proper h t -> ctree_proper h.+1 (ctree_cons_rot t).
Proof.
by rewrite /ctree_cons_rot => t_ok; apply: ctree_cons_proper;
  [| apply: ctree_rotl_proper | apply: ctree_rotr_proper].
Qed.

Lemma ctree_mem_cons_rot t et :
  ctree_mem (ctree_cons_rot t) et = ctree_mem t (ttail et).
Proof.
rewrite /ctree_cons_rot /ttail; case: et => [|e et].
  by rewrite /= ctree_mem_seq0 ctree_leaf_cons ctree_mem_0.
case: e; try by [rewrite /= !ctree_mem_0];
  rewrite ctree_mem_cons {1}/ctree_mem /=;
  by rewrite ?permt_id -1?ctree_mem_rotl -1?ctree_mem_rotr.
Qed.

Lemma ctree_rotlr_spec t :
  ctree_rotlr t = ctree_union (ctree_rotl t) (ctree_rotr t).
Proof.
rewrite /ctree_rotlr; set u := {2 4}t.
elim: t u => [t1 IHt1 t2 IHt2 t3 IHt3 | _ _ |]  [] //= u1 u2 u3.
rewrite {}IHt1 {}IHt2 {}IHt3 [in RHS]ctree_cons_spec.
case: ifP => [/ctree_empty_node_eq[] | ne_t]; first by rewrite !ctree_union_Nl.
rewrite [in RHS]ctree_cons_spec; case: ifP => // /ctree_empty_node_eq[].
by rewrite !ctree_union_Nr ctree_cons_spec ne_t.
Qed.

Lemma ctree_rotlr_proper h t :
  ctree_proper h t -> ctree_proper h (ctree_rotlr t).
Proof.
move=> t_ok; rewrite ctree_rotlr_spec.
by apply: ctree_union_proper;
   [apply: ctree_rotl_proper | apply: ctree_rotr_proper].
Qed.

Lemma ctree_mem_rotlr h t et :
    let preim_t g := ctree_mem t \o permt g in
    ctree_proper h t ->
  ctree_mem (ctree_rotlr t) et = preim_t Eperm312 et || preim_t Eperm231 et.
Proof.
rewrite ctree_rotlr_spec /= => t_ok.
by rewrite -ctree_mem_rotl -ctree_mem_rotr (@ctree_mem_union h) //;
  [apply: ctree_rotl_proper | apply: ctree_rotr_proper].
Qed.

Lemma ctree_mem_disjoint_spec tl tr :
  reflect (exists et, ctree_mem tl et && ctree_mem tr et)
          (~~ ctree_disjoint tl tr).
Proof.
have Ineg := @negbT (ctree_disjoint _ _).
elim: tl tr => [tl1 IH1 tl2 IH2 tl3 IH3 | lfl IHl|] [tr1 tr2 tr3|lfr|];
  try by [right=> [[[|? ?]]] //=; rewrite ?andbF | left; exists nil].
rewrite /= -if_neg; case: IH1 => [tlr_et | tl'r1].
  by left; have [et] := tlr_et; exists (Color1 :: et).
rewrite /= -if_neg; case: IH2 => [tlr_et | tl'r2].
  by left; have [et] := tlr_et; exists (Color2 :: et).
case: IH3 => [tlr_et | tl'r3]; [left | right].
  by have [et] := tlr_et; exists (Color3 :: et).
by case=> -[|[] et] //= ?; [case: tl'r1 | case: tl'r2 | case: tl'r3]; exists et.
Qed.

Lemma ctree_mem_disjoint tl tr et :
  ctree_disjoint tl tr -> ctree_mem tr et -> ctree_mem tl et = false.
Proof.
move=> tl'tr tr_et; apply: contraTF tl'tr => tl_et.
by apply/ctree_mem_disjoint_spec; exists et; apply/andP.
Qed.