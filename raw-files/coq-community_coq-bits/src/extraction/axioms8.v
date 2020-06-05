From Coq
     Require Import ZArith.ZArith Extraction.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple.
From Bits
     Require Import bits.

Definition wordsize := 8.

Axiom Int8: Type.
Extract Inlined Constant Int8 => "int".


Axiom forallInt8 : (Int8 -> bool) -> bool.
Extract Inlined Constant forallInt8 => "Forall.forall_int8".

Axiom eq: Int8 -> Int8 -> bool.
Extract Inlined Constant eq => "(=)".

Section Trust.

Axiom eqInt8P : Equality.axiom eq.

Definition viewP (P: pred Int8) (PP: Int8 -> Prop) := forall x, reflect (PP x) (P x).

Axiom forallInt8P : forall P PP,
  viewP P PP ->
    reflect (forall x, PP x) (forallInt8 (fun x => P x)).

End Trust.

Axiom zero : Int8.
Extract Inlined Constant zero => "0".

Axiom one : Int8.
Extract Inlined Constant one => "1".

Axiom succ : Int8 -> Int8.
Extract Constant succ => "(fun x -> (x + 1) land 0xff)".

Axiom lor: Int8 -> Int8 -> Int8.
Extract Inlined Constant lor => "(lor)".

Axiom lsl: Int8 -> Int8 -> Int8.
Extract Inlined Constant lsl => "(fun x y -> (x lsl y) land 0xff)".

Axiom land: Int8 -> Int8 -> Int8.
Extract Inlined Constant land => "(land)".

Axiom lt: Int8 -> Int8 -> bool.
Extract Inlined Constant lt => "(<)".

Axiom lsr: Int8 -> Int8 -> Int8.
Extract Inlined Constant lsr => "(lsr)".

Axiom neg: Int8 -> Int8.
Extract Inlined Constant neg => "(fun x -> (-x) land 0xff)".

Axiom lnot: Int8 -> Int8.
Extract Inlined Constant lnot => "(fun x -> (lnot x) land 0xff)".

Axiom lxor: Int8 -> Int8 -> Int8.
Extract Inlined Constant lxor => "(lxor)".

Axiom dec: Int8 -> Int8.
Extract Constant dec => "(fun x -> (x - 1) land 0xff)".

Axiom add: Int8 -> Int8 -> Int8.
Extract Inlined Constant add => "(fun x y -> (x + y) land 0xff)".

Fixpoint PbitsToInt8 (p: seq bool): Int8 :=
  match p with
    | true :: p => lor one (lsl (PbitsToInt8 p) one)
    | false :: p => lsl (PbitsToInt8 p) one
    | [::] => zero
  end.

Definition bitsToInt8 (bs: BITS wordsize): Int8 := PbitsToInt8 bs.

Fixpoint bitsFromInt8S (k: nat)(n: Int8): seq bool :=
  match k with
    | 0 => [::]
    | k.+1 =>
      let p := bitsFromInt8S k (lsr n one) in
      (eq (land n one) one) :: p
  end.

Lemma bitsFromInt8P {k} (n: Int8): size (bitsFromInt8S k n) == k.
Proof.
  elim: k n => // [k IH] n //=.
  rewrite eqSS //.
Qed.

Canonical bitsFromInt8 (n: Int8): BITS wordsize
  := Tuple (bitsFromInt8P n).

Definition bitsToInt8K_test: bool :=
 [forall bs , bitsFromInt8 (bitsToInt8 bs) == bs ].

Axiom bitsToInt8K_valid: bitsToInt8K_test.

Lemma bitsToInt8K: cancel bitsToInt8 bitsFromInt8.
Proof.
  move=> bs; apply/eqP; move: bs.
  by apply/forallP: bitsToInt8K_valid.
Qed.

Definition bitsFromInt8_inj_test: bool :=
  forallInt8 (fun x =>
    forallInt8 (fun y =>
      (bitsFromInt8 x == bitsFromInt8 y) ==> (eq x y))).

Axiom bitsFromInt8_inj_valid: bitsFromInt8_inj_test.

Lemma bitsFromInt8_inj: injective bitsFromInt8.
Proof.
  move=> x y /eqP H.
  apply/eqInt8P.
  move: H; apply/implyP.
  move: y; apply/(forallInt8P (fun y => (bitsFromInt8 x == bitsFromInt8 y) ==> eq x y)).
  move=> y; apply idP.
  move: x; apply/forallInt8P; last by apply bitsFromInt8_inj_valid.
  move=> x; apply idP.
Qed.

Lemma bitsFromInt8K: cancel bitsFromInt8 bitsToInt8.
Proof.
  apply: inj_can_sym; auto using bitsToInt8K, bitsFromInt8_inj.
Qed.

Lemma bitsFromInt8_bij: bijective bitsFromInt8.
Proof.
  split with (g := bitsToInt8);
  auto using bitsToInt8K, bitsFromInt8K.
Qed.


Definition native_repr (i: Int8)(bs: BITS wordsize): bool
  := eq i (bitsToInt8 bs).

Lemma eq_adj: forall i bs, eq i (bitsToInt8 bs) = (bitsFromInt8 i == bs) .
Proof.
  move=> i bs.
  apply/eqInt8P/eqP; intro; subst;
  auto using bitsFromInt8K, bitsToInt8K.
Qed.

Lemma eq_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    (eq i i') = (bs == bs').
Proof.
  move=> i i' bs bs'.
  rewrite /native_repr.
  repeat (rewrite eq_adj; move/eqP=> <-).
  apply/eqInt8P/eqP; intro; subst; auto using bitsFromInt8_inj.
Qed.

Definition zero_test: bool
  := eq zero (bitsToInt8 #0).

Axiom zero_valid: zero_test.

Lemma zero_repr: native_repr zero #0.
Proof. apply zero_valid. Qed.

Definition one_test: bool
  := eq one (bitsToInt8 #1).

Axiom one_valid: one_test.

Lemma one_repr: native_repr one #1.
Proof. apply one_valid. Qed.

Definition succ_test: bool
  := forallInt8 (fun i =>
     native_repr (succ i) (incB (bitsFromInt8 i))).

Axiom succ_valid: succ_test.

Lemma succ_repr: forall i bs,
    native_repr i bs -> native_repr (succ i) (incB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqInt8P.
  move: i; apply/forallInt8P; last by apply succ_valid.
  move=> x; apply/eqInt8P.
Qed.

Definition lnot_test: bool
  := forallInt8 (fun i =>
       native_repr (lnot i) (invB (bitsFromInt8 i))).

Axiom lnot_valid: lnot_test.

Lemma lnot_repr: forall i bs,
    native_repr i bs -> native_repr (lnot i) (invB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqInt8P.
  move: i; apply/forallInt8P; last by apply lnot_valid.
  move=> i; apply/eqInt8P.
Qed.

Definition land_test: bool
  := forallInt8 (fun i =>
       forallInt8 (fun i' =>
         native_repr (land i i') (andB (bitsFromInt8 i) (bitsFromInt8 i')))).

Axiom land_valid: land_test.

Lemma land_repr: forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (land i i') (andB bs bs').
Proof.
  move=> i i' ? ?.
  repeat (rewrite /native_repr eq_adj; move/eqP=> <-).
  apply/eqInt8P.
  move: i'; apply/(forallInt8P (fun i' => eq (land i i') (bitsToInt8 (andB (bitsFromInt8 i) (bitsFromInt8 i'))))).
  move=> i'; apply/eqInt8P.
  move: i; apply/forallInt8P; last by apply land_valid.
  move=> i'; apply idP.
Qed.

Definition lor_test: bool
  := forallInt8 (fun i =>
       forallInt8 (fun i' =>
         native_repr (lor i i') (orB (bitsFromInt8 i) (bitsFromInt8 i')))).

Axiom lor_valid: lor_test.

Lemma lor_repr: forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (lor i i') (orB bs bs').
Proof.
  move=> i i' ? ?.
  repeat (rewrite /native_repr eq_adj; move/eqP=> <-).
  apply/eqInt8P.
  move: i'; apply/(forallInt8P (fun i' => eq (lor i i') (bitsToInt8 (orB (bitsFromInt8 i) (bitsFromInt8 i'))))).
  move=> i'; apply/eqInt8P.
  move: i; apply/forallInt8P; last by apply lor_valid.
  move=> i'; apply idP.
Qed.

Definition lxor_test: bool
  := forallInt8 (fun i =>
       forallInt8 (fun i' =>
         native_repr (lxor i i') (xorB (bitsFromInt8 i) (bitsFromInt8 i')))).

Axiom lxor_valid: lxor_test.


Lemma lxor_repr: forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (lxor i i') (xorB bs bs').
Proof.
  move=> i i' ? ?.
  repeat (rewrite /native_repr eq_adj; move/eqP=> <-).
  apply/eqInt8P.
  move: i'; apply/(forallInt8P (fun i' => eq (lxor i i') (bitsToInt8 (xorB (bitsFromInt8 i) (bitsFromInt8 i'))))).
  move=> i'; apply/eqInt8P.
  move: i; apply/forallInt8P; last by apply lxor_valid.
  move=> i'; apply idP.
Qed.

Definition natural_repr (i: Int8)(n: nat): bool :=
  [exists bs, native_repr i bs && (# n == bs)].

Definition lsr_test: bool
  := forallInt8 (fun i =>
       forallInt8 (fun i' =>
         (toNat (bitsFromInt8 i') <= wordsize) ==> native_repr (lsr i i') (shrBn (bitsFromInt8 i) (toNat (bitsFromInt8 i'))))).

Axiom lsr_valid: lsr_test.

Lemma lsr_repr: forall i j bs k, k <= wordsize ->
    native_repr i bs -> natural_repr j k ->
    native_repr (lsr i j) (shrBn bs k).
Proof.
  move=> i i' ? k ltn_k.
  rewrite /native_repr eq_adj; move/eqP=> <-.
  rewrite /natural_repr.
  move/existsP=> [bs' /andP [H /eqP H']].
  rewrite /native_repr eq_adj in H.
  move/eqP: H=> H.
  apply/eqInt8P.
  have Hk: k = toNat (bitsFromInt8 i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallInt8P (fun i' => (toNat (bitsFromInt8 i') <= wordsize) ==> (eq (lsr i i') (bitsToInt8 (shrBn (bitsFromInt8 i) (toNat ((bitsFromInt8 i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqInt8P.
  move: (H H')=> H''.
  by apply/eqInt8P.
  move: i; apply/forallInt8P; last by apply lsr_valid.
  move=> i'; apply idP.
Qed.

Definition lsl_test: bool
  := forallInt8 (fun i =>
       forallInt8 (fun i' =>
         (toNat (bitsFromInt8 i') <= wordsize) ==> native_repr (lsl i i') (shlBn (bitsFromInt8 i) (toNat (bitsFromInt8 i'))))).

Axiom lsl_valid: lsl_test.

Lemma lsl_repr: forall i j bs k, k <= wordsize ->
    native_repr i bs -> natural_repr j k ->
    native_repr (lsl i j) (shlBn bs k).
Proof.
  move=> i i' ? k ltn_k.
  rewrite /native_repr eq_adj; move/eqP=> <-.
  rewrite /natural_repr.
  move/existsP=> [bs' /andP [H /eqP H']].
  rewrite /native_repr eq_adj in H.
  move/eqP: H=> H.
  apply/eqInt8P.
  have Hk: k = toNat (bitsFromInt8 i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallInt8P (fun i' => (toNat (bitsFromInt8 i') <= wordsize) ==> (eq (lsl i i') (bitsToInt8 (shlBn (bitsFromInt8 i) (toNat ((bitsFromInt8 i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqInt8P.
  move: (H H')=> H''.
  by apply/eqInt8P.
  move: i; apply/forallInt8P; last by apply lsl_valid.
  move=> i'; apply idP.
Qed.

Definition neg_test: bool
  := forallInt8 (fun i =>
       native_repr (neg i) (negB (bitsFromInt8 i))).

Axiom neg_valid: neg_test.

Lemma neg_repr: forall i bs,
    native_repr i bs -> native_repr (neg i) (negB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqInt8P.
  move: i; apply/forallInt8P; last by apply neg_valid.
  move=> i; apply/eqInt8P.
Qed.

Definition dec_test: bool
  := forallInt8 (fun i =>
       native_repr (dec i) (decB (bitsFromInt8 i))).

Axiom dec_valid: dec_test.

Lemma dec_repr: forall i bs,
    native_repr i bs -> native_repr (dec i) (decB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqInt8P.
  move: i; apply/forallInt8P; last by apply dec_valid.
  move=> i; apply/eqInt8P.
Qed.

Definition add_test: bool
  := forallInt8 (fun i =>
       forallInt8 (fun i' =>
         native_repr (add i i') (addB (bitsFromInt8 i) (bitsFromInt8 i')))).

Axiom add_valid: add_test.

Lemma add_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (add i i') (addB bs bs').
Proof.
  move=> i i' ? ?.
  repeat (rewrite /native_repr eq_adj; move/eqP=> <-).
  apply/eqInt8P.
  move: i'; apply/(forallInt8P (fun i' => eq (add i i') (bitsToInt8 (addB (bitsFromInt8 i) (bitsFromInt8 i'))))).
  move=> i'; apply/eqInt8P.
  move: i; apply/forallInt8P; last by apply add_valid.
  move=> i'; apply idP.
Qed.

Require Import ExtrOcamlBasic.

Definition allb s := foldr (andb) true s.

Definition binop_tests x bitsX y bitsY :=
  allb
    [:: (bitsX == bitsY) ==> (eq x y) ;
      native_repr (land x y) (andB bitsX bitsY) ;
      native_repr (lor x y) (orB bitsX bitsY) ;
      native_repr (lxor x y) (xorB bitsX bitsY) ;
      native_repr (add x y) (addB bitsX bitsY)].

Definition shift_tests x toNatX y bitsY :=
  allb
    [:: native_repr (lsr y x) (shrBn bitsY toNatX) ;
        native_repr (lsl y x) (shlBn bitsY toNatX)].

Definition unop_tests x :=
  let bitsX := bitsFromInt8 x in
  let toNatX := toNat bitsX in
  allb
    [:: native_repr (succ x) (incB bitsX) ;
      native_repr (lnot x) (invB bitsX) ;
      native_repr (neg x) (negB bitsX) ;
      native_repr (dec x) (decB bitsX) ;
      if (toNatX <= wordsize) then
        forallInt8 (fun y =>
          let bitsY := bitsFromInt8 y in
          (binop_tests x bitsX y bitsY) && (shift_tests x toNatX y bitsY))
      else
        forallInt8 (fun y => binop_tests x bitsX y (bitsFromInt8 y))].

Definition tests
  := allb
       [:: bitsToInt8K_test ;
         zero_test ;
         one_test ;
         forallInt8
           (fun x => unop_tests x)].

Lemma implies_unop : tests -> forall x, unop_tests x.
  move=> /andP [_ /andP [_ /andP[_ /andP [H _]]]] x.
  rewrite /succ_test.
  move: H=> /forallInt8P H.
  move: (H unop_tests)=> H'.
  apply H'=> x'.
  by apply idP.
Qed.

Lemma implies_binop : tests -> forall x y, binop_tests x (bitsFromInt8 x) y (bitsFromInt8 y).
  move => H x y.
  have H': unop_tests x by apply implies_unop.
  move: H'=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [H1 _]]]]].
  case Hc: (toNat (bitsFromInt8 x) <= wordsize); rewrite Hc in H1.
  have Hb: (binop_tests x (bitsFromInt8 x) y (bitsFromInt8 y)) && (shift_tests x (toNat (bitsFromInt8 x)) y (bitsFromInt8 y)).
    move: H1=> /forallInt8P H1.
    move: (H1 (fun y => (binop_tests x (bitsFromInt8 x) y (bitsFromInt8 y)) && (shift_tests x (toNat (bitsFromInt8 x)) y (bitsFromInt8 y))))=> H2.
    apply H2=> y'.
    by apply idP.
  by move: Hb=> /andP [-> _].
  move: H1=> /forallInt8P H1.
  move: (H1 (fun y => binop_tests x (bitsFromInt8 x) y (bitsFromInt8 y)))=> H2.
  apply H2=> y'.
  by apply idP.
Qed.

Lemma implies_bitsToInt8K : tests -> bitsToInt8K_test.
  by move=> /andP [H _].
Qed.

Lemma implies_bitsFromInt8_inj : tests -> bitsFromInt8_inj_test.
  move=> H.
  apply/forallInt8P=> x.
  apply idP.
  apply/forallInt8P=> y.
  apply idP.
  by move: (implies_binop H x y)=> /andP [-> _].
Qed.

Lemma implies_zero : tests -> zero_test.
  by move=> /andP [_ /andP [H _]].
Qed.

Lemma implies_one : tests -> one_test.
  by move=> /andP [_ /andP [_ /andP[H _]]].
Qed.

Lemma implies_succ : tests -> succ_test.
  move=> H.
  apply/forallInt8P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [H1 _].
Qed.

Lemma implies_lnot : tests -> lnot_test.
  move=> H.
  apply/forallInt8P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [_ /andP [H1 _]].
Qed.

Lemma implies_land : tests -> land_test.
  move=> H.
  apply/forallInt8P=> x.
  apply idP.
  apply/forallInt8P=> y.
  apply idP.
  by move: (implies_binop H x y)=> /andP [_ /andP [-> _]].
Qed.

Lemma implies_lor : tests -> lor_test.
  move=> H.
  apply/forallInt8P=> x.
  apply idP.
  apply/forallInt8P=> y.
  apply idP.
  by move: (implies_binop H x y)=> /andP [_ /andP [_ /andP [-> _]]].
Qed.

Lemma implies_lxor : tests -> lxor_test.
  move=> H.
  apply/forallInt8P=> x.
  apply idP.
  apply/forallInt8P=> y.
  apply idP.
  by move: (implies_binop H x y)=> /andP [_ /andP [_ /andP [_ /andP [-> _]]]].
Qed.

Lemma implies_shift : tests -> forall x y, toNat (bitsFromInt8 x) <= wordsize -> shift_tests x (toNat (bitsFromInt8 x)) y (bitsFromInt8 y).
  move => H x y Hlt.
  move: (implies_unop H x)=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [H1 _]]]]].
  rewrite Hlt in H1.
  have Hb: (binop_tests x (bitsFromInt8 x) y (bitsFromInt8 y)) && (shift_tests x (toNat (bitsFromInt8 x)) y (bitsFromInt8 y)).
    move: H1=> /forallInt8P H1.
    move: (H1 (fun y => (binop_tests x (bitsFromInt8 x) y (bitsFromInt8 y)) && (shift_tests x (toNat (bitsFromInt8 x)) y (bitsFromInt8 y))))=> H2.
    apply H2=> y'.
    by apply idP.
  by move: Hb=> /andP [_ ->].
Qed.

Lemma implies_lsr : tests -> lsr_test.
  move=> H.
  apply/forallInt8P=> y.
  apply idP.
  apply/forallInt8P=> x.
  apply idP.
  apply/implyP=> H'.
  by move: (implies_shift H x y H')=> /andP [-> _].
Qed.

Lemma implies_lsl : tests -> lsl_test.
  move=> H.
  apply/forallInt8P=> y.
  apply idP.
  apply/forallInt8P=> x.
  apply idP.
  apply/implyP=> H'.
  by move: (implies_shift H x y H')=> /andP [_ /andP [-> _]].
Qed.

Lemma implies_neg : tests -> neg_test.
  move=> H.
  apply/forallInt8P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [_ /andP [_ /andP [H1 _]]].
Qed.

Lemma implies_dec : tests -> dec_test.
  move=> H.
  apply/forallInt8P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [_ /andP [_ /andP [_ /andP [H1 _]]]].
Qed.

Lemma implies_add : tests -> add_test.
  move=> H.
  apply/forallInt8P=> x.
  apply idP.
  apply/forallInt8P=> y.
  apply idP.
  by move: (implies_binop H x y)=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [-> _]]]]].
Qed.

Cd "src/extraction".
Extraction "axioms8.ml" tests.
Cd "../..".