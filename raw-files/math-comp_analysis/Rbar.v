

Require Import Reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import ssralg ssrnum.
Require Import Rstruct posnum.
Import GRing.Theory Num.Theory Num.Def.
Local Open Scope ring_scope.

Inductive Rbar := | Finite of R | p_infty | m_infty.
Notation "'+oo'" := p_infty : R_scope.
Notation "'-oo'" := m_infty : R_scope.
Definition real (x : Rbar) := if x is Finite x then x else 0.
Coercion Finite : R >-> Rbar.
Coercion real : Rbar >-> R.

Definition is_finite (x : Rbar) := Finite (real x) = x.
Lemma is_finite_correct (x : Rbar) :
  is_finite x <-> exists y : R, x = Finite y.
Proof. by case: x => [x||]; (split; [move=> //; eexists|case=> //]). Qed.

Definition Rbar_lt (x y : Rbar) : bool :=
  match x, y with
    | p_infty, _ | _, m_infty => false
    | m_infty, _ | _, p_infty => true
    | Finite x, Finite y => (x < y)%R
  end.

Definition Rbar_le (x y : Rbar) : bool :=
  match x, y with
    | m_infty, _ | _, p_infty => true
    | p_infty, _ | _, m_infty => false
    | Finite x, Finite y => x <= y
  end.

Definition Rbar_eq (x y : Rbar) : bool :=
  match x, y with
    | m_infty, m_infty | p_infty, p_infty => true
    | Finite x, Finite y => x == y
    | _, _ => false
  end.

Program Definition Rbar_eqMixin := @EqMixin Rbar Rbar_eq _.
Next Obligation.
elim=> [x||] [y||] //=; do ?[by constructor].
by apply: (iffP eqP) => [|[]]->.
Qed.
Canonical Rbar_eqType := EqType Rbar Rbar_eqMixin.


Definition Rbar_opp (x : Rbar) :=
  match x with
    | Finite x => Finite (-x)
    | p_infty => m_infty
    | m_infty => p_infty
  end.

Definition Rbar_plus' (x y : Rbar) :=
  match x,y with
    | p_infty, m_infty | m_infty, p_infty => None
    | p_infty, _ | _, p_infty => Some p_infty
    | m_infty, _ | _, m_infty => Some m_infty
    | Finite x', Finite y' => Some (Finite (x' + y'))
  end.
Definition Rbar_plus (x y : Rbar) :=
  match Rbar_plus' x y with Some z => z | None => Finite 0 end.
Arguments Rbar_plus !x !y /.
Definition is_Rbar_plus (x y z : Rbar) : bool := Rbar_plus' x y == Some z.
Definition ex_Rbar_plus (x y : Rbar) : bool := Rbar_plus' x y.
Arguments ex_Rbar_plus !x !y /.

Lemma is_Rbar_plus_unique (x y z : Rbar) :
  is_Rbar_plus x y z -> Rbar_plus x y = z.
Proof.
  unfold is_Rbar_plus, ex_Rbar_plus, Rbar_plus.
  by case: Rbar_plus' => // a /eqP[].
Qed.
Lemma Rbar_plus_correct (x y : Rbar) :
  ex_Rbar_plus x y -> is_Rbar_plus x y (Rbar_plus x y).
Proof.
  unfold is_Rbar_plus, ex_Rbar_plus, Rbar_plus.
  by case: Rbar_plus'.
Qed.

Definition Rbar_minus (x y : Rbar) := Rbar_plus x (Rbar_opp y).
Arguments Rbar_minus !x !y /.
Definition is_Rbar_minus (x y z : Rbar) : bool :=
  is_Rbar_plus x (Rbar_opp y) z.
Definition ex_Rbar_minus (x y : Rbar) : bool :=
  ex_Rbar_plus x (Rbar_opp y).
Arguments ex_Rbar_minus !x !y /.

Definition Rbar_inv (x : Rbar) : Rbar :=
  match x with
    | Finite x => Finite (x^-1)
    | _ => Finite 0
  end.

Local Open Scope ring_scope.
Definition Rbar_mult' (x y : Rbar) : option Rbar :=
  match x, y with
    | Finite x, Finite y => Some (Finite (x * y))
    | Finite x, p_infty | p_infty, Finite x =>
      if x > 0 then Some p_infty else if x < 0 then Some m_infty else None
    | Finite x, m_infty | m_infty, Finite x =>
      if x > 0 then Some m_infty else if x < 0 then Some p_infty else None
    | p_infty, p_infty | m_infty, m_infty => Some p_infty
    | p_infty, m_infty | m_infty, p_infty => Some m_infty
  end.

Definition Rbar_mult (x y : Rbar) :=
  match Rbar_mult' x y with Some z => z | None => Finite 0 end.
Arguments Rbar_mult !x !y /.

Definition is_Rbar_mult (x y z : Rbar) : Prop :=
  Rbar_mult' x y = Some z.
Definition ex_Rbar_mult (x y : Rbar) : Prop :=
  match x, y with
    | Finite x, p_infty | Finite x, m_infty
    | p_infty, Finite x | m_infty, Finite x => x != 0
    | _, _ => true
  end.
Arguments ex_Rbar_mult !x !y /.

Definition Rbar_mult_pos (x : Rbar) (y : posreal) :=
  match x with
    | Finite x => Finite (x * y%:num)
    | _ => x
  end.

Lemma is_Rbar_mult_unique (x y z : Rbar) :
  is_Rbar_mult x y z -> Rbar_mult x y = z.
Proof.
rewrite /is_Rbar_mult.
by case: x y z => [x||] [y||] [z||] //=; do ?[case: ltrgtP=> ? //] => -[->].
Qed.

Lemma Rbar_mult_correct (x y : Rbar) :
  ex_Rbar_mult x y -> is_Rbar_mult x y (Rbar_mult x y).
Proof.
rewrite /ex_Rbar_mult /is_Rbar_mult /Rbar_mult /Rbar_mult'.
by case: x y => [x||] [y||] //=; case: ltrgtP.
Qed.

Lemma Rbar_mult_correct' (x y z : Rbar) :
  is_Rbar_mult x y z -> ex_Rbar_mult x y.
Proof.
rewrite /ex_Rbar_mult /is_Rbar_mult /Rbar_mult /Rbar_mult'.
by case: x y z => [x||] [y||] [z||] //=; do ?[case: ltrgtP=> ? //] => -[->].
Qed.


Definition Rbar_div (x y : Rbar) : Rbar :=
  Rbar_mult x (Rbar_inv y).
Arguments Rbar_div !x !y /.
Definition is_Rbar_div (x y z : Rbar) : Prop :=
  is_Rbar_mult x (Rbar_inv y) z.
Definition ex_Rbar_div (x y : Rbar) : Prop :=
  ex_Rbar_mult x (Rbar_inv y).
Arguments ex_Rbar_div !x !y /.
Definition Rbar_div_pos (x : Rbar) (y : posreal) :=
  match x with
    | Finite x => Finite (x / y%:num)
    | _ => x
  end.

Lemma Rbar_finite_eq (x y : R) :
  Finite x = Finite y <-> x = y.
Proof. by split=> [[]|->]. Qed.

Lemma Rbar_lt_not_eq (x y : Rbar) :
  Rbar_lt x y -> (x == y) = false.
Proof. by move: x y => [x||] [y||] => //= /ltr_eqF; apply. Qed.

Lemma Rbar_not_le_lt (x y : Rbar) :
  ~~ Rbar_le x y -> Rbar_lt y x.
Proof. by move: x y => [x||] [y||] => //=; rewrite ltrNge. Qed.

Lemma Rbar_lt_not_le (x y : Rbar) :
  Rbar_lt y x -> ~~ Rbar_le x y.
Proof. by move: x y => [x||] [y||] => //=; rewrite ltrNge. Qed.

Lemma Rbar_not_lt_le (x y : Rbar) :
  ~~ Rbar_lt x y -> Rbar_le y x.
Proof. by move: x y => [x||] [y||] => //=; rewrite lerNgt. Qed.

Lemma Rbar_le_not_lt (x y : Rbar) :
  Rbar_le y x -> ~~ Rbar_lt x y.
Proof. by move: x y => [x||] [y||] => //=; rewrite lerNgt. Qed.

Lemma Rbar_le_refl (x : Rbar) : Rbar_le x x.
Proof. by case: x => [] /=. Qed.

Lemma Rbar_lt_le (x y : Rbar) : Rbar_lt x y -> Rbar_le x y.
Proof. by move: x y => [x||] [y||] => //=; case: ltrgtP. Qed.

Lemma Rbar_total_order (x y : Rbar) :
  {Rbar_lt x y} + {x = y} + {Rbar_lt y x}.
Proof.
move: x y => [x||] [y||] /=; do ?by [left;left|right|left;right].
by case: (ltrgtP x y) => [||->]; [left;left|right|left;right].
Qed.

Lemma Rbar_eq_dec (x y : Rbar) : {x = y} + {x != y}.
Proof. by have [] := eqVneq x y; [left|right]. Qed.

Lemma Rbar_lt_dec (x y : Rbar) : {Rbar_lt x y} + {~~ Rbar_lt x y}.
Proof. by have [] := boolP (Rbar_lt x y); [left|right]. Qed.

Lemma Rbar_lt_le_dec (x y : Rbar) : {Rbar_lt x y} + {Rbar_le y x}.
Proof.
by have [] := boolP (Rbar_lt x y); [left|right]; rewrite // Rbar_not_lt_le.
Qed.

Lemma Rbar_le_dec (x y : Rbar) : {Rbar_le x y} + {~~ Rbar_le x y}.
Proof. by have [] := boolP (Rbar_le x y); [left|right]. Qed.

Lemma Rbar_le_lt_dec (x y : Rbar) :
  {Rbar_le x y} + {Rbar_lt y x}.
Proof.
by have [] := boolP (Rbar_le x y); [left|right]; rewrite // Rbar_not_le_lt.
Qed.

Lemma Rbar_le_lt_or_eq_dec (x y : Rbar) :
  Rbar_le x y -> { Rbar_lt x y } + { x = y }.
Proof.
have [[->|->]|] := Rbar_total_order x y; [left|right|]=> //.
by move=> /Rbar_lt_not_le /negPf->.
Qed.

Lemma Rbar_lt_trans (x y z : Rbar) :
  Rbar_lt x y -> Rbar_lt y z -> Rbar_lt x z.
Proof. by case: x y z => [x||] [y||] [z||] //; apply: ltr_trans. Qed.

Lemma Rbar_lt_le_trans (x y z : Rbar) :
  Rbar_lt x y -> Rbar_le y z -> Rbar_lt x z.
Proof. by case: x y z => [x||] [y||] [z||] //; apply: ltr_le_trans. Qed.

Lemma Rbar_le_lt_trans (x y z : Rbar) :
  Rbar_le x y -> Rbar_lt y z -> Rbar_lt x z.
Proof. by case: x y z => [x||] [y||] [z||] //; apply: ler_lt_trans. Qed.

Lemma Rbar_le_trans (x y z : Rbar) :
  Rbar_le x y -> Rbar_le y z -> Rbar_le x z.
Proof. by case: x y z => [x||] [y||] [z||] //; apply: ler_trans. Qed.

Lemma Rbar_le_antisym (x y : Rbar) :
  Rbar_le x y -> Rbar_le y x -> x = y.
Proof.
case: x y => [x||] [y||] //=.
by move=> xy /(conj xy) /andP; rewrite -eqr_le => /eqP->.
Qed.

Lemma Rbar_opp_involutive (x : Rbar) : (Rbar_opp (Rbar_opp x)) = x.
Proof. by case: x => //= x; rewrite opprK. Qed.

Lemma Rbar_opp_lt (x y : Rbar) :
   Rbar_lt (Rbar_opp x) (Rbar_opp y) = Rbar_lt y x.
Proof. by case: x y => [x||] [y||] //=; rewrite ltr_opp2. Qed.

Lemma Rbar_opp_le (x y : Rbar) :
   Rbar_le (Rbar_opp x) (Rbar_opp y) = Rbar_le y x.
Proof. by case: x y => [x||] [y||] //=; rewrite ler_opp2. Qed.

Lemma Rbar_opp_eq (x y : Rbar) : (Rbar_opp x == Rbar_opp y) = (x == y).
Proof. by case: x y => [x||] [y||] //=; rewrite [_ == _]eqr_opp. Qed.

Lemma Rbar_opp_real (x : Rbar) : real (Rbar_opp x) = - real x.
Proof. by case: x => [x||] //=; rewrite oppr0. Qed.

Lemma Rbar_plus'_comm x y : Rbar_plus' x y = Rbar_plus' y x.
Proof. by case: x y => [x||] [y||] //=; rewrite addrC. Qed.

Lemma ex_Rbar_plus_comm x y : ex_Rbar_plus x y -> ex_Rbar_plus y x.
Proof. by case: x y => [x||] [y||]. Qed.

Lemma ex_Rbar_plus_opp (x y : Rbar) :
  ex_Rbar_plus x y -> ex_Rbar_plus (Rbar_opp x) (Rbar_opp y).
Proof. by case: x y => [x||] [y||]. Qed.

Lemma Rbar_plus_0_r (x : Rbar) : Rbar_plus x (Finite 0) = x.
Proof. by case: x => //= x; rewrite addr0. Qed.

Lemma Rbar_plus_0_l (x : Rbar) : Rbar_plus (Finite 0) x = x.
Proof. by case: x => //= x; rewrite add0r. Qed.

Lemma Rbar_plus_comm (x y : Rbar) : Rbar_plus x y = Rbar_plus y x.
Proof. by case: x y => [x||] [y||] //=; rewrite addrC. Qed.

Lemma Rbar_plus_lt_compat (a b c d : Rbar) :
  Rbar_lt a b -> Rbar_lt c d -> Rbar_lt (Rbar_plus a c) (Rbar_plus b d).
Proof. by move: a b c d => [a||] [b||] [c||] [d||] //= ??; apply: ltr_add. Qed.

Lemma Rbar_plus_le_compat (a b c d : Rbar) :
  Rbar_le a b -> Rbar_le c d -> Rbar_le (Rbar_plus a c) (Rbar_plus b d).
Proof. by move: a b c d => [a||] [b||] [c||] [d||] //= ??; apply: ler_add. Qed.

Lemma Rbar_plus_opp (x y : Rbar) :
  Rbar_plus (Rbar_opp x) (Rbar_opp y) = Rbar_opp (Rbar_plus x y).
Proof. by case: x y => [x||] [y||] //=; rewrite ?oppr0 // opprD. Qed.

Lemma Rbar_minus_eq_0 (x : Rbar) : Rbar_minus x x = Finite 0.
Proof. by case: x => //= x; rewrite subrr. Qed.

Lemma Rbar_opp_minus (x y : Rbar) :
  Rbar_opp (Rbar_minus x y) = Rbar_minus y x.
Proof. by case: x y => [x||] [y||] //=; rewrite ?oppr0 // opprB. Qed.

Lemma Rbar_inv_opp (x : Rbar) :
  x != Finite 0 -> Rbar_inv (Rbar_opp x) = Rbar_opp (Rbar_inv x).
Proof. by case: x => [x||] /=; rewrite ?oppr0//= ?invrN. Qed.

Lemma Rbar_mult'_comm (x y : Rbar) :
  Rbar_mult' x y = Rbar_mult' y x.
Proof. by case: x y => [x||] [y||] //=; rewrite /Rbar_mult' mulrC. Qed.

Lemma Rbar_mult'_opp_r (x y : Rbar) :
  Rbar_mult' x (Rbar_opp y) =
  match Rbar_mult' x y with Some z => Some (Rbar_opp z) | None => None end.
Proof.
case: x y => [x||] [y||] //=; (do ?by rewrite mulrN);
by rewrite ?oppr_gt0 ?oppr_lt0; case: ltrgtP.
Qed.

Lemma Rbar_mult_comm (x y : Rbar) :
  Rbar_mult x y = Rbar_mult y x.
Proof. by rewrite /Rbar_mult Rbar_mult'_comm. Qed.

Lemma Rbar_mult_opp_r (x y : Rbar) :
  Rbar_mult x (Rbar_opp y) = (Rbar_opp (Rbar_mult x y)).
Proof.
rewrite /Rbar_mult Rbar_mult'_opp_r.
by case: Rbar_mult' => //=; rewrite oppr0.
Qed.

Lemma Rbar_mult_opp_l (x y : Rbar) :
  Rbar_mult (Rbar_opp x) y = Rbar_opp (Rbar_mult x y).
Proof.
  rewrite ?(Rbar_mult_comm _ y).
  by apply Rbar_mult_opp_r.
Qed.
Lemma Rbar_mult_opp (x y : Rbar) :
  Rbar_mult (Rbar_opp x) (Rbar_opp y) = Rbar_mult x y.
Proof.
  by rewrite Rbar_mult_opp_l -Rbar_mult_opp_r Rbar_opp_involutive.
Qed.

Lemma Rbar_mult_0_l (x : Rbar) : Rbar_mult (Finite 0) x = Finite 0.
Proof. by case: x => [x||] //=; rewrite ?mul0r ?ltrr. Qed.

Lemma Rbar_mult_0_r (x : Rbar) : Rbar_mult x (Finite 0) = (Finite 0).
Proof. by rewrite Rbar_mult_comm ; by apply Rbar_mult_0_l. Qed.

Lemma Rbar_mult_eq_0 (y x : Rbar) :
  Rbar_mult x y = Finite 0 -> x = Finite 0 \/ y = Finite 0.
Proof.
case: x y => [x||] [y||] //=; do ?case: ltrgtP=> /eqP ? //=;
  do ?by [left; apply/eqP|right; apply/eqP].
by move=> /eqP; rewrite [_ == _]mulf_eq0 => /orP[/eqP->|/eqP->]; [left|right].
Qed.

Lemma ex_Rbar_mult_sym (x y : Rbar) :
  ex_Rbar_mult x y -> ex_Rbar_mult y x.
Proof. by case: x y => [x||] [y||] //=. Qed.

Lemma ex_Rbar_mult_opp_l (x y : Rbar) :
  ex_Rbar_mult x y -> ex_Rbar_mult (Rbar_opp x) y.
Proof. by case: x y => [x | | ] [y | | ] //=; rewrite oppr_eq0. Qed.

Lemma ex_Rbar_mult_opp_r (x y : Rbar) :
  ex_Rbar_mult x y -> ex_Rbar_mult x (Rbar_opp y).
Proof. by case: x y => [x | | ] [y | | ] //=; rewrite oppr_eq0. Qed.

Lemma is_Rbar_mult_sym (x y z : Rbar) :
  is_Rbar_mult x y z = is_Rbar_mult y x z.
Proof.
rewrite /is_Rbar_mult; case: x y z => [x||] [y||] [z||] //=;
by rewrite ?oppr_gt0 ?oppr_lt0 1?mulrC; do ?[by case: ltrgtP].
Qed.

Lemma is_Rbar_mult_opp_l (x y z : Rbar) :
  is_Rbar_mult x y z -> is_Rbar_mult (Rbar_opp x) y (Rbar_opp z).
Proof.
rewrite /is_Rbar_mult; case: x y z => [x||] [y||] [z||] //=;
by rewrite ?oppr_gt0 ?oppr_lt0 ?mulNr; do ?[by case: ltrgtP] => -[->].
Qed.

Lemma is_Rbar_mult_opp_r (x y z : Rbar) :
  is_Rbar_mult x y z -> is_Rbar_mult x (Rbar_opp y) (Rbar_opp z).
Proof.
rewrite /is_Rbar_mult; case: x y z => [x||] [y||] [z||] //=;
by rewrite ?oppr_gt0 ?oppr_lt0 ?mulrN; do ?[by case: ltrgtP] => -[->].
Qed.

Lemma is_Rbar_mult_p_infty_pos (x : Rbar) :
  Rbar_lt (Finite 0) x -> is_Rbar_mult p_infty x p_infty.
Proof. by rewrite /is_Rbar_mult; case: x => [x||] //= ->. Qed.

Lemma is_Rbar_mult_p_infty_neg (x : Rbar) :
  Rbar_lt x (Finite 0) -> is_Rbar_mult p_infty x m_infty.
Proof. by rewrite /is_Rbar_mult; case: x => [x||] //=; case: ltrgtP. Qed.

Lemma is_Rbar_mult_m_infty_pos (x : Rbar) :
  Rbar_lt (Finite 0) x -> is_Rbar_mult m_infty x m_infty.
Proof. by rewrite /is_Rbar_mult; case: x => [x||] //=; case: ltrgtP. Qed.

Lemma is_Rbar_mult_m_infty_neg (x : Rbar) :
  Rbar_lt x (Finite 0) -> is_Rbar_mult m_infty x p_infty.
Proof. by rewrite /is_Rbar_mult; case: x => [x||] //=; case: ltrgtP. Qed.

Lemma is_Rbar_div_p_infty (x : R) : is_Rbar_div x p_infty (Finite 0).
Proof. by rewrite /is_Rbar_div /is_Rbar_mult /= mulr0. Qed.

Lemma is_Rbar_div_m_infty (x : R) : is_Rbar_div x m_infty (Finite 0).
Proof. by rewrite /is_Rbar_div /is_Rbar_mult /= mulr0. Qed.

Lemma Rbar_mult_pos_eq (x y : Rbar) (z : posreal) :
  x = y <-> (Rbar_mult_pos x z) = (Rbar_mult_pos y z).
Proof. by case: x y => [x||] [y||] //=; split=> [[->]|[/mulIf->]]. Qed.

Lemma Rbar_mult_pos_lt (x y : Rbar) (z : posreal) :
  Rbar_lt x y <-> Rbar_lt (Rbar_mult_pos x z) (Rbar_mult_pos y z).
Proof. by case: x y => [x||] [y||] //=; rewrite ltr_pmul2r. Qed.

Lemma Rbar_mult_pos_le (x y : Rbar) (z : posreal) :
  Rbar_le x y <-> Rbar_le (Rbar_mult_pos x z) (Rbar_mult_pos y z).
Proof. by case: x y => [x||] [y||] //=; rewrite ler_pmul2r. Qed.

Lemma Rbar_div_pos_eq (x y : Rbar) (z : posreal) :
  x = y <-> (Rbar_div_pos x z) = (Rbar_div_pos y z).
Proof. by case: x y => [x||] [y||] //=; split=> [[->]|[/divIf->]]. Qed.

Lemma Rbar_div_pos_lt (x y : Rbar) (z : posreal) :
  Rbar_lt x y <-> Rbar_lt (Rbar_div_pos x z) (Rbar_div_pos y z).
Proof. by case: x y => [x||] [y||] //=; rewrite ltr_pmul2r. Qed.

Lemma Rbar_div_pos_le (x y : Rbar) (z : posreal) :
  Rbar_le x y <-> Rbar_le (Rbar_div_pos x z) (Rbar_div_pos y z).
Proof. by case: x y => [x||] [y||] //=; rewrite ler_pmul2r. Qed.

Definition Rbar_min (x y : Rbar) : Rbar :=
  match x, y with
  | z, p_infty | p_infty, z => z
  | _ , m_infty | m_infty, _ => m_infty
  | Finite x, Finite y => minr x y
  end.

Lemma Rbar_lt_locally (a b : Rbar) (x : R) :
  Rbar_lt a x -> Rbar_lt x b ->
  exists delta : posreal,
    forall y, `|y - x| < delta -> Rbar_lt a y && Rbar_lt y b.
Proof.
move=> [:wlog]; case: a b => [a||] [b||] //= ltax ltxb.
- move: a b ltax ltxb; abstract: wlog.
  move=> {a b} a b ltxa ltxb.
  have m_gt0 : minr ((x - a) / 2) ((b - x) / 2) > 0.
    by rewrite ltr_minr !divr_gt0 ?subr_gt0.
  exists (PosNum m_gt0) => y //=; rewrite ltr_minr !ltr_distl.
  move=> /andP[/andP[ay _] /andP[_ yb]].
  rewrite (ltr_trans _ ay) ?(ltr_trans yb) //=.
    by rewrite -subr_gt0 opprD addrA {1}[b - x]splitr addrK divr_gt0 ?subr_gt0.
  by rewrite -subr_gt0 addrAC {1}[x - a]splitr addrK divr_gt0 ?subr_gt0.
- have [//||d dP] := wlog a (x + 1); rewrite ?ltr_addl //.
  by exists d => y /dP /andP[->].
- have [//||d dP] := wlog (x - 1) b; rewrite ?gtr_addl ?ltrN10 //.
  by exists d => y /dP /andP[_ ->].
- by exists 1%:pos.
Qed.

Lemma Rbar_min_comm (x y : Rbar) : Rbar_min x y = Rbar_min y x.
Proof. by case: x y => [x||] [y||] //=; rewrite minrC. Qed.

Lemma Rbar_min_r (x y : Rbar) : Rbar_le (Rbar_min x y) y.
Proof. by case: x y => [x||] [y||] //=; rewrite ler_minl lerr orbT. Qed.

Lemma Rbar_min_l (x y : Rbar) : Rbar_le (Rbar_min x y) x.
Proof. by rewrite Rbar_min_comm Rbar_min_r. Qed.

Lemma Rbar_min_case (x y : Rbar) (P : Rbar -> Type) :
  P x -> P y -> P (Rbar_min x y).
Proof. by case: x y => [x||] [y||] //=; case: minrP. Qed.

Lemma Rbar_min_case_strong (x y : Rbar) (P : Rbar -> Type) :
  (Rbar_le x y -> P x) -> (Rbar_le y x -> P y)
    -> P (Rbar_min x y).
Proof.
case: x y => [x||] [y||] //=; do 1?[case: minrP => ltxy];
do ?by [move=> /(_ isT) //|move=> _ /(_ isT) //=].
by move=> _; rewrite ler_eqVlt ltxy orbT; apply.
Qed.

Definition Rbar_abs (x : Rbar) :=
   if x is Finite x then Finite `|x| else p_infty.

Lemma Rbar_abs_lt_between (x y : Rbar) :
  Rbar_lt (Rbar_abs x) y = (Rbar_lt (Rbar_opp y) x && Rbar_lt x y).
Proof. by case: x y => [x||] [y||] //=; rewrite ltr_norml. Qed.

Lemma Rbar_abs_opp (x : Rbar) :
  Rbar_abs (Rbar_opp x) = Rbar_abs x.
Proof. by case: x => [x||] //=; rewrite normrN. Qed.

Lemma Rbar_abs_pos (x : Rbar) :
  Rbar_le (Finite 0) x -> Rbar_abs x = x.
Proof. by case: x => [x||] //= /ger0_norm->. Qed.

Lemma Rbar_abs_neg (x : Rbar) :
  Rbar_le x (Finite 0) -> Rbar_abs x = Rbar_opp x.
Proof. by case: x => [x||] //= /ler0_norm->. Qed.