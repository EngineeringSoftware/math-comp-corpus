
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype path fingraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation cancel3 f g h := (cancel f (fun x => g (h x))).

Notation "@ 'cancel3' T f g h" :=
  (@cancel T T f (fun x : T => g (h x : T)))
  (at level 10, T, f, g, h at level 8, format "'@' 'cancel3'  T  f  g  h").

Record hypermap := Hypermap {
  dart :> finType;
  edge : dart -> dart;
  node : dart -> dart;
  face : dart -> dart;
  _ : cancel3 edge node face
}.

Arguments edge {G} : rename.
Arguments node {G} : rename.
Arguments face {G} : rename.

Notation cedge := (fconnect edge).
Notation cnode := (fconnect node).
Notation cface := (fconnect face).

Section FiniteMap.

Variable G : hypermap.
Implicit Types x y : G.

Lemma edgeK : @cancel3 G edge node face. Proof. by case: G. Qed.
Lemma faceK : @cancel3 G face edge node. Proof. exact: canF_sym edgeK. Qed.
Lemma nodeK : @cancel3 G node face edge. Proof. exact: canF_sym faceK. Qed.

Lemma edgeI : @injective G G edge. Proof. exact: can_inj edgeK. Qed.
Lemma nodeI : @injective G G node. Proof. exact: can_inj nodeK. Qed.
Lemma faceI : @injective G G face. Proof. exact: can_inj faceK. Qed.

Lemma cedgeC x y : cedge x y = cedge y x.
Proof. exact: (fconnect_sym edgeI). Qed.
Lemma cnodeC x y : cnode x y = cnode y x.
Proof. exact: (fconnect_sym nodeI). Qed.
Lemma cfaceC x y : cface x y = cface y x.
Proof. exact: (fconnect_sym faceI). Qed.

Lemma same_cedge x y : cedge x y -> cedge x =1 cedge y.
Proof. exact: (same_connect cedgeC). Qed.
Lemma same_cnode x y : cnode x y -> cnode x =1 cnode y.
Proof. exact: (same_connect cnodeC). Qed.
Lemma same_cface x y : cface x y -> cface x =1 cface y.
Proof. exact: (same_connect cfaceC). Qed.

Lemma cedge1 x : cedge x =1 cedge (edge x).
Proof. exact: (same_fconnect1 edgeI). Qed.
Lemma cedge1r y x : cedge x y = cedge x (edge y).
Proof. exact: (same_fconnect1_r edgeI). Qed.

Lemma cnode1 x : cnode x =1 cnode (node x).
Proof. exact: (same_fconnect1 nodeI). Qed.
Lemma cnode1r y x : cnode x y = cnode x (node y).
Proof. exact: (same_fconnect1_r nodeI). Qed.

Lemma cface1 x : cface x =1 cface (face x).
Proof. exact: (same_fconnect1 faceI). Qed.
Lemma cface1r y x : cface x y = cface x (face y).
Proof. exact: (same_fconnect1_r faceI). Qed.

End FiniteMap.

Arguments edgeI {G} [x1 x2] : rename.
Arguments nodeI {G} [x1 x2] : rename.
Arguments faceI {G} [x1 x2] : rename.
Arguments edgeK {G} x : rename.
Arguments nodeK {G} x : rename.
Arguments faceK {G} x : rename.
Arguments cedgeC {G} x y : rename.
Arguments cnodeC {G} x y : rename.
Arguments cfaceC {G} x y : rename.

Section Components.

Variable G : hypermap.

Definition glink : rel G := relU (frel edge) (relU (frel node) (frel face)).

Lemma glinkE x : glink x (edge x). Proof. by rewrite /glink /= eqxx. Qed.
Lemma glinkN x : glink x (node x). Proof. by rewrite /glink /= eqxx !orbT. Qed.
Lemma glinkF x : glink x (face x). Proof. by rewrite /glink /= eqxx !orbT. Qed.

Lemma glinkC : connect_sym glink.
Proof.
by do !apply: relU_sym; [apply: cedgeC | apply: cnodeC | apply: cfaceC].
Qed.

Definition connectedb : bool := n_comp glink G == 1.
Definition connected : Prop := n_comp glink G == 1.

End Components.

Arguments glink {G} x y.
Arguments glinkC {G} x y.
Notation gcomp := (connect glink).

Section Genus.

Variable G : hypermap.

Definition Euler_lhs := double (n_comp glink G) + #|G|.
Definition Euler_rhs := fcard edge G + (fcard node G + fcard face G).
Definition genus := (Euler_lhs - Euler_rhs)./2.

Definition even_genus : Prop := Euler_lhs = genus.*2 + Euler_rhs.

Definition planarb : bool := genus == 0.
Definition planar : Prop := genus == 0.

End Genus.

Section Jordan.

Variable G : hypermap.

Definition clink : rel G := relU (frel (finv node)) (frel face).

Lemma clinkP x y : reflect (x = node y \/ face x = y) (clink x y).
Proof. by rewrite /clink /= (canF_eq (f_finv nodeI)); apply: pred2P. Qed.

Lemma clinkN x : clink (node x) x. Proof. by apply/clinkP; left. Qed.
Lemma clinkF x : clink x (face x). Proof. by apply/clinkP; right. Qed.

Lemma clinkC : connect_sym clink.
Proof.
by apply: relU_sym; [apply: (fconnect_sym (finv_inj nodeI)) | apply: cfaceC].
Qed.

Lemma clink_glink : connect clink =2 gcomp.
Proof.
move=> x; apply/subset_eqP/andP.
split; apply/subsetP; apply: connect_sub x => x y.
  case/clinkP=> [-> | <-]; last by rewrite connect1 ?glinkF.
  by rewrite glinkC connect1 ?glinkN.
case/predU1P=> [<- | /pred2P[<- | <-]]; last by rewrite connect1 ?clinkF.
  rewrite -{1}[x]edgeK (connect_trans (connect1 (clinkN _))) //.
  by rewrite clinkC connect1 ?clinkF.
by rewrite clinkC connect1 ?clinkN.
Qed.

Lemma connected_clink x y :
  connected G -> exists2 p, path clink x p & y = last x p.
Proof.
move=> ccG; apply: connectP; rewrite clink_glink.
apply/(rootP glinkC); set rx := root glink x; set ry := root glink y.
apply: contraTeq ccG => neq_rxy; rewrite [n_comp _ G](cardD1 ry) (cardD1 rx).
by rewrite !inE neq_rxy !(roots_root glinkC).
Qed.


Definition Moebius_path q :=
  if q isn't x :: p then false else
  [&& uniq q, path clink x p & mem2 p (finv node (last x p)) (node x)].

Definition Jordan := forall q, ~~ Moebius_path q.

End Jordan.

Arguments clink {G} x y.
Arguments clinkC {G} x y.
Arguments Moebius_path {G} q.
Arguments clinkP {G x y}.

Section DerivedMaps.

Variable G : hypermap.

Definition permN := Hypermap (@nodeK G : cancel3 node face edge).

Remark gcomp_permN : (gcomp : rel permN) =2 (gcomp : rel G).
Proof. by apply: eq_connect => x y; rewrite /glink /= orbA orbC. Qed.

Lemma connected_permN : connected permN = connected G.
Proof. by rewrite /connected (eq_n_comp gcomp_permN). Qed.

Lemma genus_permN : genus permN = genus G.
Proof.
by rewrite /genus /Euler_rhs /= addnA addnC /Euler_lhs (eq_n_comp gcomp_permN).
Qed.

Lemma planar_permN : planar permN = planar G.
Proof. by rewrite /planar genus_permN. Qed.

Definition permF := Hypermap (@faceK G : cancel3 face edge node).

Remark gcomp_permF : (gcomp : rel permF) =2 (gcomp : rel G).
Proof. by apply: eq_connect => x y; rewrite /glink /= orbC orbA. Qed.

Lemma connected_permF : connected permF = connected G.
Proof. by rewrite /connected (eq_n_comp gcomp_permF). Qed.

Lemma genus_permF : genus permF = genus G.
Proof.
by rewrite /genus /Euler_rhs /= addnC addnA /Euler_lhs (eq_n_comp gcomp_permF).
Qed.

Lemma planar_permF : planar permF = planar G.
Proof. by rewrite /planar genus_permF. Qed.

Fact hypermap_dualP : @cancel3 G (finv edge) (finv face) (finv node).
Proof.
by move=> x; rewrite -{1}[x]faceK (finv_f edgeI) (finv_f nodeI) (finv_f faceI).
Qed.

Definition dual : hypermap := Hypermap hypermap_dualP.

Remark clink_dual : @clink dual =2 @clink G.
Proof. by move=> x y; rewrite /clink /= (finv_inv faceI) orbC. Qed.

Remark gcomp_dual : (gcomp : rel dual) =2 (gcomp : rel G).
Proof. by move=> x y; rewrite -!clink_glink (eq_connect clink_dual). Qed.

Lemma connected_dual : connected dual = connected G.
Proof. by rewrite /connected (eq_n_comp gcomp_dual). Qed.

Lemma genus_dual : genus dual = genus G.
Proof.
rewrite {1}/genus /Euler_rhs /= addnCA addnC -addnA /Euler_lhs.
rewrite (eq_n_comp gcomp_dual) (fcard_finv edgeI).
by rewrite (fcard_finv nodeI) (fcard_finv faceI).
Qed.

Lemma planar_dual : planar dual = planar G.
Proof. by rewrite /planar genus_dual. Qed.

Lemma Jordan_dual : Jordan G -> Jordan dual.
Proof.
move=> JordanG [//|x p]; apply/and3P; rewrite (eq_path clink_dual) => -[Up xCp].
rewrite /= (finv_inv faceI); move Lp: (last x p) => /= y p_fy_f'x.
case/splitP2r: p / p_fy_f'x => p1 _ /splitPl[p2 p3 Lp2] in Up xCp Lp.
rewrite -cat_cons !last_cat !cat_path /= Lp2 -!andbA in Lp xCp.
rewrite -!cat_cons uniq_catCA catA uniq_catC in Up.
case: p3 => [|z p3] in Up xCp Lp.
  by rewrite -Lp (f_finv faceI) /= mem_cat mem_head orbT in Up.
case/and4P: xCp => xCp1 /clinkP[Lp1 | /faceI-Dy] yCp2 /=; last first.
  rewrite catA uniq_catC catA !cat_uniq lastI Dy in Up.
  by rewrite has_sym has_rcons -Lp /= mem_last andbF in Up.
case/andP=> /clinkP[Dnz | Dz] zCp3; last first.
  by rewrite /= -Dz (f_finv faceI) -cat_cons !mem_cat mem_head !orbT in Up.
have /and3P[] := JordanG (z :: p3 ++ (face y :: p2) ++ x :: p1); split=> //.
  rewrite cat_path /= zCp3 cat_path /= yCp2 Lp2 -Lp clinkF xCp1.
  by rewrite /clink /= (f_finv faceI) eqxx orbT.
rewrite !last_cat /= Lp1 (finv_f nodeI) mem2_cat mem2_cons eqxx.
by rewrite -cat_cons mem_cat -Dnz -Lp2 mem_last orbT.
Qed.

Fact hypermap_mirrorP : @cancel3 G (face \o node) (finv node) (finv face).
Proof. by move=> x; rewrite /= (finv_f faceI) (finv_f nodeI). Qed.

Definition mirror : hypermap := Hypermap hypermap_mirrorP.

Lemma cnode_mirror : (cnode : rel mirror) =2 (cnode : rel G).
Proof. exact: same_fconnect_finv (@nodeI G). Qed.

Lemma cface_mirror : (cface : rel mirror) =2 (cface : rel G).
Proof. exact: same_fconnect_finv (@faceI G). Qed.

Remark mirror_edge_adj : @fun_adjunction mirror G face edge (finv edge) G.
Proof.
apply: strict_adjunction=> //; try apply: faceI; try exact: (@cedgeC dual).
  by apply/subsetP => x _; rewrite -(@nodeK G x) codom_f.
by move=> x y _ /=; rewrite (inj_eq faceI) (finv_eq_can edgeK).
Qed.

Lemma order_mirror_edge (x : G) : @order mirror edge x = order edge (node x).
Proof.
have [_ De'] := mirror_edge_adj.
apply: etrans (card_image faceI _); apply: eq_card => y.
rewrite [y \in _]cedge1 {2}/edge {4}/mirror /= -(@nodeK G y) (mem_image faceI).
by rewrite -topredE /= -De' // (same_fconnect_finv edgeI).
Qed.

Remark clink_mirror : @clink mirror =2 (fun x y : G => clink y x).
Proof.
move=> x y; rewrite !(sameP clinkP pred2P) -(eq_sym y) eq_sym /=.
by rewrite (canF_eq (f_finv nodeI)) -(canF_eq (finv_f faceI)).
Qed.

Lemma gcomp_mirror : (gcomp : rel mirror) =2 (gcomp : rel G).
Proof.
move=> x y; rewrite -!clink_glink.
by rewrite (eq_connect clink_mirror) (same_connect_rev clinkC).
Qed.

Lemma connected_mirror : connected mirror = connected G.
Proof. by rewrite /connected (eq_n_comp gcomp_mirror). Qed.

Lemma genus_mirror : genus mirror = genus G.
Proof.
rewrite [LHS]/genus /Euler_rhs /Euler_lhs (eq_n_comp gcomp_mirror).
suffices <-: fcard edge G = fcard edge mirror.
  by rewrite (eq_n_comp cnode_mirror) (eq_n_comp cface_mirror).
have:= adjunction_n_comp _ cedgeC (@cedgeC dual) _ mirror_edge_adj.
by move->; first apply/esym/eq_n_comp/(same_fconnect_finv (@edgeI G)).
Qed.

Lemma planar_mirror : planar mirror = planar G.
Proof. by rewrite /planar genus_mirror. Qed.

Lemma Jordan_mirror : Jordan G -> Jordan mirror.
Proof.
move=> JordanG [] //= x /lastP[//|p z]; rewrite (finv_inv nodeI).
apply: contra (JordanG (z :: rev (x :: p))) => /and3P[/andP[p'x Up]] /=.
rewrite (eq_path clink_mirror) -[path _ _ _]rev_path last_rcons belast_rcons.
rewrite -cons_uniq -rev_rcons rev_uniq /= p'x {}Up => -> pnzn'x /=.
have{p'x} nz'x: x != node z by rewrite (memPnC p'x) ?(mem2l pnzn'x).
rewrite -cats1 mem2r_cat ?inE ?(canF_eq (f_finv nodeI)) {nz'x}// in pnzn'x.
case/splitP2r: p / pnzn'x => p1 p2; rewrite -cat_cons rev_cat -mem_rev.
by rewrite -(mem2_last x) !rev_cons last_cat !last_rcons mem2_cat => ->.
Qed.

End DerivedMaps.

Section EqualHypermap.

Variable G : hypermap.

Inductive eqm : hypermap -> Prop :=
    EqHypermap e n f Eenf of edge =1 e & node =1 n & face =1 f
     : eqm (@Hypermap G e n f Eenf).

Variable G' : hypermap.
Hypothesis eqGG' : eqm G'.

Remark eqm_gcomp : n_comp glink G = n_comp glink G'.
Proof.
have [e n f Eenf Ee En Ef] := eqGG'; apply: eq_n_comp.
by apply: eq_connect => x y; rewrite {1}/glink /= Ee En Ef.
Qed.

Lemma eqm_connected : connected G = connected G'.
Proof. by rewrite {2}/connected -eqm_gcomp. Qed.

Lemma eqm_genus : genus G = genus G'.
Proof.
rewrite {2}/genus /Euler_lhs -eqm_gcomp; have [e n f Eenf Ee En Ef] := eqGG'.
by rewrite /Euler_rhs /= -(eq_fcard Ee) -(eq_fcard En) -(eq_fcard Ef).
Qed.

Lemma eqm_planar : planar G = planar G'.
Proof. by rewrite {2}/planar -eqm_genus. Qed.

End EqualHypermap.

Notation "x '=m' y" := (eqm x y) (at level 70, no associativity).

Lemma eqm_sym G G': G =m G' -> G' =m G.
Proof. by case: G => d e n f EG [] *; apply: EqHypermap => x; auto. Qed.

Lemma dual_inv G : dual (dual G) =m G.
Proof.
case: G (@edgeI G) (@nodeI G) (@faceI G) => d e n f /= eK eI nI fI.
by apply: EqHypermap; apply: finv_inv.
Qed.

Lemma mirror_inv G : mirror (mirror G) =m G.
Proof.
case: G (@nodeI G) (@faceI G) => d e n f eK /= nI fI.
apply: EqHypermap; first 1 [move=> x /=] || exact: finv_inv.
by rewrite -[in LHS](eK x) !finv_f.
Qed.