(*  Nothing from this file is used (as of now). Jaziel wrote    *
 *  this lemmas while attepting to verify curve448Comp. It was  *
 *  verified without the lemmas in this file. Here saving them  *
 *  just in case...                                             *)

Require Import VST.floyd.proofauto.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

Local Open Scope Z.

Scheme Equality for list.

Lemma listeqb_refl (a : list Z) : list_beq Z Z.eqb a a = true.
Proof.
  induction a; simpl; auto.
  rewrite Z.eqb_refl; simpl; auto.
Qed.

Lemma listeqb_eq : forall a b : list Z, 
list_beq Z Z.eqb a b = true <-> a = b.
Proof.
  split. generalize dependent b.
  induction a.
  - intros. destruct b; simpl in H; auto; try discriminate.
  - induction b; intro.
    + simpl in H; discriminate.
    + simpl in H.
      destruct (a =? a1) eqn:E ; simpl in H.
      rewrite Z.eqb_eq in E.
      rewrite IHa with (b := b), E; auto.
      discriminate.
  - intro; rewrite H. 
    apply listeqb_refl.
Qed.

Lemma eqb_app (a1 a2 b1 b2 : list Z) : 
Zlength a1 = Zlength b1 ->
list_beq Z Z.eqb (a1 ++ a2) (b1 ++ b2) =
list_beq Z Z.eqb a1 b1 && list_beq Z Z.eqb a2 b2.
Proof.
  generalize dependent b1.
  induction a1; intros.
  - rewrite Zlength_nil in H; symmetry in H.
    apply Zlength_nil_inv in H.
    rewrite H; auto.
  - destruct b1.
    + rewrite Zlength_nil in H; apply Zlength_nil_inv in H.
      rewrite H; auto.
    + simpl. destruct (a =? z) eqn:E; simpl; auto.
      rewrite IHa1 with (b1 := b1); auto.
      rewrite !Zlength_cons in H.
      apply (f_equal Z.pred) in H;
      rewrite <- !Zpred_succ in H.
      auto.
Qed.

Lemma sublist_update_0th :
forall {A} (l: list A) lo v,
0 <= lo < Zlength l -> 
upd_Znth 0 (sublist.sublist lo (Zlength l) l) v = [v] ++ sublist.sublist (lo+1) (Zlength l) l.
Proof.
  intros.
  list_simplify.
  Qed.