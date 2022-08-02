Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import list_lemmas.

(* /**
 * @brief Conditional swap
 * @param[in,out] a Pointer to the first integer
 * @param[in,out] b Pointer to the second integer
 * @param[in] c Condition variable
 **/

void curve448Swap(uint32_t *a, uint32_t *b, uint32_t c)
{
   uint_t i;
   uint32_t mask;
   uint32_t dummy;

   //The mask is the all-1 or all-0 word
   mask = ~c + 1;

   //Conditional swap
   for(i = 0; i < 14; i++)
   {
      //Constant time implementation
      dummy = mask & (a[i] ^ b[i]);
      a[i] ^= dummy;
      b[i] ^= dummy;
   }
}
*)

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope Z.

Definition curve448Swap_spec : ident * funspec :=
DECLARE _curve448Swap
WITH a : val, sha : share, contents_a : list Z,
     b : val, shb : share, contents_b : list Z,
     c : Z, (* Should be 0 or 1. See PROP in PRE.  *)
     gv : globals
PRE [ tptr tuint, tptr tuint, tuint ]
    PROP   (writable_share sha; 
            writable_share shb;
            Zlength contents_a = 14;
            Zlength contents_b = 14;
            forall x : Z, In x contents_a -> 0 ≤ x ≤ Int.max_unsigned;
            forall x : Z, In x contents_b -> 0 ≤ x ≤ Int.max_unsigned;
            c = 0 \/ c = 1)
    PARAMS ( a ; b ; Vint(Int.repr c)) GLOBALS (gv)
    SEP    (data_at sha (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
            data_at shb (tarray tuint 14) (map Vint (map Int.repr contents_b)) b)
POST [ tvoid ]
    PROP   ()
    RETURN ()
    SEP    (data_at sha (tarray tuint 14) 
                (if (Z.eqb c 0) then (map Vint (map Int.repr contents_a))
                 else map Vint (map Int.repr contents_b)) a;
            data_at shb (tarray tuint 14) 
                (if (Z.eqb c 0) then (map Vint (map Int.repr contents_b))
                else map Vint (map Int.repr contents_a)) b). 
            (* If c = 0, no swap. Else, swap. *)

(* Loop invariant: 
    If c = 0, then a = a and b = b.
    If c = 1, then a and b are partially swapped up to index i. *)
Definition curve448Swap_INV a contents_a sha b contents_b shb c:=
(EX i : Z,
(PROP   (Zlength contents_a = 14;
         Zlength contents_b = 14;
         forall x : Z, In x contents_a -> 0 ≤ x ≤ Int.max_unsigned;
         forall x : Z, In x contents_b -> 0 ≤ x ≤ Int.max_unsigned)
LOCAL   (temp _a a; temp _b b; temp _mask (Vint (Int.repr (((c + 1) mod 2) - 1))))
SEP     ( if (Z.eqb c 0) 
            then (data_at sha (tarray tuint 14) (map Vint (map Int.repr contents_a)) a)
         else  (data_at sha (tarray tuint 14) 
            ((sublist.sublist 0 i (map Vint (map Int.repr contents_b)))
            ++ sublist.sublist i 14 (map Vint (map Int.repr contents_a))) a);
         if (Z.eqb c 0) 
            then (data_at shb (tarray tuint 14) (map Vint (map Int.repr contents_b)) b)
         else  (data_at shb (tarray tuint 14) 
            ((sublist.sublist 0 i (map Vint (map Int.repr contents_a)))
            ++ sublist.sublist i 14 (map Vint (map Int.repr contents_b)))
            b
         )
        )))%assert.

Definition Gprog : funspecs := ltac:(with_library prog [ curve448Swap_spec ]).

Lemma body_curve448Swap : semax_body Vprog Gprog f_curve448Swap curve448Swap_spec.
Proof.
    start_function.
    forward.
    forward_for_simple_bound 14 (curve448Swap_INV a contents_a sha b contents_b shb c).
    - entailer!.
    destruct H3;
    rewrite H3; 
    f_equal;
    autorewrite with norm. 
        + replace (1 mod 2) with (1) by easy.
        replace (1-1) with (0) by easy.
        unfold Int.add.
        replace (Int.unsigned (Int.not (Int.repr 0)) + Int.unsigned (Int.repr 1)) with (2^32) by easy.
        rewrite (Int.eqm_samerepr (0) (2^32)); auto.
        unfold Int.eqm.
        unfold Int.modulus.
        replace (two_power_nat Int.wordsize) with (2^32) by easy.
        unfold Zbits.eqmod.
        exists (-1); lia.
        + replace ((1 + 1) mod 2 - 1) with (-1) by easy.
        unfold Int.add.
        replace (Int.unsigned (Int.not (Int.repr 1))) with (2^32-2) by easy.
        replace ((2^32-2 + Int.unsigned (Int.repr 1))) with (2^32-1) by easy.
        rewrite (Int.eqm_samerepr (-1) (2^32-1)); auto.
        unfold Int.eqm.
        unfold Int.modulus.
        unfold Zbits.eqmod.
        exists (-1); easy.
        + destruct H3; rewrite H3;
        destruct (_ =? 0) eqn:E; 
        try discriminate.
        * entailer!.
        * autorewrite with sublist; cancel.
    - Intros.
    destruct (c =? 0) eqn:E.
        + repeat forward.
        entailer!.
        rewrite Z.eqb_eq in E. 
        rewrite E.
        replace ((0 + 1) mod 2 - 1) with (0) by easy.
        replace ((Int.and (Int.repr 0)
        (Int.xor (Int.repr (Znth i contents_a))
        (Int.repr (Znth i contents_b))))) with (Int.repr 0) by easy.
        assert ((upd_Znth i (map Vint (map Int.repr contents_a))
                (Vint (Int.xor (Int.repr (Znth i contents_a)) (Int.repr 0))))
                = (map Vint (map Int.repr contents_a))) as H_a.
            list_simplify.
            rewrite Int.xor_zero.
            rewrite e.
            easy.
        assert ((upd_Znth i (map Vint (map Int.repr contents_b))
                (Vint (Int.xor (Int.repr (Znth i contents_b)) (Int.repr 0))))
                = (map Vint (map Int.repr contents_b))) as H_b.
            list_simplify.
            rewrite Int.xor_zero.
            rewrite e.
            easy.
        rewrite  H_a, H_b; cancel.
        + forward.
            entailer!.
            autorewrite with sublist.
            easy.
            forward.
            entailer!.
            autorewrite with sublist.
            easy.
        repeat forward.
        entailer!.
        rewrite Z.eqb_neq in E.
        destruct H3. (* This starts with c = 0, but we had c≠0 so: *)
        contradiction.
        rewrite H3.
        autorewrite with sublist.
        simpl.
        (* This entailment will be solved by showing (data_at ... a) and (data_at ... b) match
            with what we said they would respectively. *)
        assert ((sublist.sublist 0 i (map Vint (map Int.repr contents_b)) ++
            upd_Znth 0 (sublist.sublist i 14 (map Vint (map Int.repr contents_a)))
            (Vint
            (Int.xor (Int.repr (Znth i contents_a))
                (Int.and (Int.repr ((1 + 1) mod 2 - 1))
                (Int.xor (Int.repr (Znth i contents_a)) (Int.repr (Znth i contents_b))))))) 
        = (sublist.sublist 0 (i + 1) (map Vint (map Int.repr contents_b)) ++
        sublist.sublist (i + 1) 14 (map Vint (map Int.repr contents_a)))) as H_a.   
        rewrite <- !(sublist_rejoin 0 i (i+1)) by list_simplify; try split; try lia.
        rewrite !sublist_len_1 by list_simplify.
        replace  ((1 + 1) mod 2 - 1) with (-1) by easy.
        rewrite <- app_assoc; f_equal.
        assert (Zlength ((map Vint (map Int.repr contents_a))) = 14) as Hlen_a by list_solve.
        rewrite <- Hlen_a at 2.
        rewrite <- sublist_update_0th by list_simplify.
        f_equal. rewrite Hlen_a. reflexivity.
        autorewrite with sublist.
        replace ((Int.repr (-1))) with (Int.mone) by easy.
        rewrite Int.and_mone_l.
        rewrite <- Int.xor_assoc.
        rewrite Int.xor_idem.   
        rewrite Int.xor_zero_l.
        reflexivity.
        assert ((sublist.sublist 0 i (map Vint (map Int.repr contents_a)) ++
        upd_Znth 0 (sublist.sublist i 14 (map Vint (map Int.repr contents_b)))
            (Vint
            (Int.xor (Int.repr (Znth i contents_b))
                (Int.and (Int.repr ((1 + 1) mod 2 - 1))
                (Int.xor (Int.repr (Znth i contents_a)) (Int.repr (Znth i contents_b)))))))
        = (sublist.sublist 0 (i + 1) (map Vint (map Int.repr contents_a)) ++
        sublist.sublist (i + 1) 14 (map Vint (map Int.repr contents_b)))) as H_b.
        rewrite <- !(sublist_rejoin 0 i (i+1)) by list_simplify; try split; try lia.
        rewrite !sublist_len_1 by list_simplify.
        replace  ((1 + 1) mod 2 - 1) with (-1) by easy.
        rewrite <- app_assoc; f_equal.
        assert (Zlength ((map Vint (map Int.repr contents_b))) = 14) as Hlen_b by list_solve.
        rewrite <- Hlen_b at 2.
        rewrite <- sublist_update_0th by list_simplify.
        f_equal. rewrite Hlen_b. reflexivity.
        autorewrite with sublist.
        replace ((Int.repr (-1))) with (Int.mone) by easy.
        rewrite Int.and_mone_l.
        replace (Int.xor (Int.repr (Znth i contents_a)) (Int.repr (Znth i contents_b))) 
            with (Int.xor (Int.repr (Znth i contents_b)) (Int.repr (Znth i contents_a))).
        rewrite <- Int.xor_assoc.
        rewrite Int.xor_idem.
        rewrite Int.xor_zero_l.
        reflexivity.
        rewrite Int.xor_commut; easy.
        rewrite H_a, H_b; cancel.
    - entailer!.
    destruct (c =? 0); autorewrite with sublist; easy.
Qed.
