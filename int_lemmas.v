(*  Additional lemmas on bitwise operations over ints.
 *  This is to complement the lemmas in Compcert's Library Integers *)

Require Import VST.floyd.proofauto.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

Local Open Scope Z.


Lemma bits_zero_iff (x : int) : 
x = Int.zero <-> (forall i, 0 <= i < Int.zwordsize -> Int.testbit x i = false).
Proof.
  split; intros.
  rewrite H. apply Int.bits_zero.
  rewrite (Int.same_bits_eq x Int.zero); auto.
  intros.
  rewrite H, Int.bits_zero; auto.
Qed.

Lemma bits_eq_iff (x y : int) :
x = y <-> (forall i, 0 <= i < Int.zwordsize -> Int.testbit x i = Int.testbit y i).
Proof.
  split; intros.
  rewrite H; auto.
  rewrite (Int.same_bits_eq x y); auto.
Qed.


Lemma or_eq0 (x y : int) : Int.or x y = Int.zero -> x = Int.zero /\ y = Int.zero.
Proof.
  intros.
  rewrite bits_zero_iff in H.
  split.
  - apply bits_eq_iff.
    intros.
    specialize (H i).
    assert (Int.testbit (Int.or x y) i = false).
    rewrite H; auto.
    rewrite Int.bits_or in H1 by auto.
    apply orb_false_iff in H1.
    destruct H1.
    rewrite H1, Int.bits_zero; auto.
  - apply bits_eq_iff.
    intros.
    specialize (H i).
    assert (Int.testbit (Int.or x y) i = false).
    rewrite H; auto.
    rewrite Int.bits_or in H1 by auto.
    apply orb_false_iff in H1.
    destruct H1.
    rewrite H2, Int.bits_zero; auto.
Qed.

Lemma lt_false_neg_true (x : int) : 0 < Int.unsigned x ->
Int.lt x Int.zero = false -> Int.lt (Int.neg x) Int.zero = true.
Proof.
  intros H0 H.
  apply lt_false_inv, Int.signed_positive in H.
  unfold Int.max_signed in H.
  unfold Int.lt.
  rewrite Int.signed_zero.
  unfold Int.neg.
  unfold Int.signed.
  rewrite Int.unsigned_repr_eq.
  remember (Int.unsigned x) as z.
  assert (z = z mod Int.modulus).
    pose proof (Int.unsigned_range x).
    rewrite <- Heqz in H1.
    symmetry.
    apply (Zmod_small z Int.modulus H1).
  replace z with (z mod Int.modulus) in H.
  destruct (zlt (- z mod Int.modulus) Int.half_modulus).
  - rewrite Z_mod_nz_opp_full in l.
    apply Zplus_lt_compat_r with (p := z mod Int.modulus) in l.
    rewrite Z.sub_add in l.
    apply Zplus_lt_compat_r with (p := -Int.half_modulus) in l.
    replace (Int.modulus + - Int.half_modulus) with (Int.half_modulus) in l by rep_lia.
    replace (Int.half_modulus + z mod Int.modulus + - Int.half_modulus) with 
      (z mod Int.modulus) in l by rep_lia.
    apply Zle_lt_succ in H.
    apply Z.lt_le_incl, Z.le_ge in l.
    contradiction.
    apply Z_lt_neq in H0.
    rewrite <- H1; auto.
  - pose proof (zero_in_range).
    destruct H2.
    pose proof (Z.mod_pos_bound (-z) Int.modulus H3).
    destruct H4.
    apply Zplus_lt_compat_r with (p := -Int.modulus) in H5.
    rewrite !Z.add_opp_r, Z.sub_diag in H5.
    destruct (zlt (- z mod Int.modulus - Int.modulus) 0); auto.
Qed.


Lemma lt_false_eq0 (x : int) :
Int.lt x Int.zero = false -> Int.lt (Int.neg x) Int.zero = false -> x = Int.zero.
Proof.
  intros.
  apply lt_false_inv, Int.signed_positive in H.
  apply lt_false_inv, Int.signed_positive in H0.
  unfold Int.max_signed in *.
  unfold Int.neg in H0.
  rewrite Int.unsigned_repr_eq in H0.
  remember (Int.unsigned x) as z.
  assert (z = z mod Int.modulus).
    pose proof (Int.unsigned_range x).
    rewrite <- Heqz in H1.
    symmetry.
    apply (Zmod_small z Int.modulus H1).
  rewrite H1 in H.
  apply Zle_lt_succ in H0, H.
  replace (Z.succ (Int.half_modulus - 1)) with Int.half_modulus in H0, H by lia.
  destruct (Z.eqb (z mod Int.modulus) 0) eqn:E.
  - apply Z.eqb_eq in E.
    rewrite E in H1.
    rewrite <- Int.unsigned_repr_eq in E.
    rewrite H1 in E.
    rewrite <- H1 in E at 2.
    rewrite Heqz in E.
    apply unsigned_eq_eq in E; auto.
  - apply Z.eqb_neq in E.
    rewrite Z_mod_nz_opp_full in H0 by apply E.
    apply Zplus_lt_compat_r with (p := z mod Int.modulus) in H0.
    rewrite Z.sub_add in H0.
    apply Zplus_lt_compat_r with (p := -Int.half_modulus) in H0.
    replace (Int.modulus + - Int.half_modulus) with (Int.half_modulus) in H0 by rep_lia.
    replace (Int.half_modulus + z mod Int.modulus + - Int.half_modulus) with 
      (z mod Int.modulus) in H0 by rep_lia.
    apply Z.lt_le_incl, Z.le_ge in H0; contradiction.
Qed.