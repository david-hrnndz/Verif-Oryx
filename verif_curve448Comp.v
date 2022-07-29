Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.
Require Import int_lemmas list_int_functions.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope Z.

(* The same mask that is computed in the body of curve448Comp *)
Fixpoint mask (a b : list Z) : int := 
    match a with
    | [] => Int.zero
    | a0 :: a => match b with
        | [] => Int.zero
        | b0 :: b => Int.or (Int.xor (Int.repr a0) (Int.repr b0)) (mask a b)
        end
    end.


Lemma mask_app (a1 a2 b1 b2 : list Z) : Zlength a1 = Zlength b1 ->
mask (a1 ++ a2) (b1 ++ b2) =
Int.or (mask a1 b1) (mask a2 b2).
Proof.
    generalize dependent b1.
    induction a1.
    - intros.
      rewrite Zlength_nil in H; symmetry in H.
      apply Zlength_nil_inv in H.
      rewrite H.
      simpl; rewrite Int.or_zero_l; auto.
    - destruct b1; intros.
      + rewrite Zlength_nil in H; apply Zlength_nil_inv in H.
        rewrite H; simpl; rewrite Int.or_zero_l; auto.
      + simpl.
        rewrite IHa1, Int.or_assoc; auto.
        rewrite !Zlength_cons in H.
        apply (f_equal Z.pred) in H;
        rewrite <- !Zpred_succ in H.
        assumption.
Qed.

Lemma list_Inteq_mask0 : forall a b : list Z, 
    list_Inteq a b = true -> mask a b = Int.zero.
Proof.
    induction a as [|a0 a]; intros; auto.
    destruct b as [|b0 b]; simpl in H; try discriminate.
    apply andb_prop in H; destruct H.
    pose proof (Int.eq_spec (Int.repr a0) (Int.repr b0)).
    rewrite H in H1.
    unfold mask.
    rewrite H1, Int.xor_idem, Int.or_zero_l.
    fold mask; rewrite IHa; auto.
Qed.

Lemma mask0_list_Inteq : forall a b : list Z, Zlength a = Zlength b -> 
    mask a b = Int.zero -> list_Inteq a b = true.
Proof.
    induction a as [ | a0 a]; intros.
    -   rewrite Zlength_nil in H.
        symmetry in H; apply Zlength_nil_inv in H.
        rewrite H; auto.
    -   destruct b as [|b0 b].
        +   rewrite Zlength_nil in H; apply Zlength_nil_inv in H.
            rewrite H; auto.
        +   simpl. 
            simpl in H0.
            apply or_eq0 in H0; destruct H0; auto.
            apply Int.xor_zero_equal in H0.
            rewrite H0.
            rewrite Int.eq_true, IHa; simpl; auto.
            rewrite !Zlength_cons in H.
            apply (f_equal Z.pred) in H;
            rewrite <- !Zpred_succ in H; auto.
Qed.


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Definition curve448Comp_spec : ident * funspec :=
DECLARE _curve448Comp
WITH a : val, contents_a : list Z,
     b : val, contents_b : list Z,
     gv : globals
PRE [ tptr tuint, tptr tuint ]
    PROP   (Zlength contents_a = 14;
            Zlength contents_b = 14)
    PARAMS ( a; b ) GLOBALS (gv)
    SEP    (data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b)
POST [ tuint ]
    PROP   ()
    RETURN (if (list_Inteq contents_a contents_b) then Vint Int.zero else Vint Int.one)
    SEP    (data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b).


Definition curve448Comp_INV a contents_a b contents_b := 
(EX i : Z,
(PROP   (Zlength contents_a = 14;
         Zlength contents_b = 14)
LOCAL   (temp _a a; temp _b b; temp _mask (Vint (mask 
         (sublist.sublist 0 i contents_a) 
         (sublist.sublist 0 i contents_b))))
SEP     (data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
         data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b
        )))%assert.


Definition Gprog : funspecs := ltac:(with_library prog [ curve448Comp_spec ]).

Lemma body_curve448Comp : semax_body Vprog Gprog f_curve448Comp curve448Comp_spec.
Proof.
    start_function.
    forward.
    forward_for_simple_bound 14 
    (curve448Comp_INV a contents_a b contents_b).
    -   entailer!.
    -   repeat forward.
        entailer!.
        apply f_equal.
        rewrite <- !(sublist_rejoin 0 i (i+1)); try split; try lia.
        rewrite mask_app, !sublist_len_1; simpl.
        rewrite Int.or_zero; auto.
        rewrite H0; auto.
        rewrite H; auto.
        list_simplify.
    -   forward.   
        entailer!.
        rewrite <- H at 1 3; rewrite <- H0.
        replace (sublist.sublist 0 (Zlength contents_a) contents_a) with contents_a
        by list_simplify.
        replace (sublist.sublist 0 (Zlength contents_b) contents_b) with contents_b
        by list_simplify.
        destruct (list_Inteq contents_a contents_b) eqn:E; f_equal.
        + apply list_Inteq_mask0 in E.
        rewrite E, Int.or_zero_l, Int.not_zero.
        unfold Int.add.
        replace (Int.repr 1) with Int.one by auto.
        rewrite Int.unsigned_one, Int.unsigned_mone.
        replace (Int.modulus - 1 + 1) with Int.modulus by rep_lia.
        rewrite Int.shru_lt_zero; auto.
        + remember (mask contents_a contents_b) as x.
        rewrite <- Int.or_shru, <- Int.neg_not,
        !Int.shru_lt_zero.
        destruct (Int.lt x Int.zero) eqn:E1;
        destruct (Int.lt (Int.neg x) Int.zero) eqn:E2; auto.
        pose proof (lt_false_eq0 x E1 E2).
        rewrite Heqx in H7.
        assert (Heq : Zlength contents_a = Zlength contents_b).
            rewrite H, H0; auto.
        apply (mask0_list_Inteq contents_a contents_b Heq) in H7.
        rewrite H7 in E; discriminate.
Qed.
