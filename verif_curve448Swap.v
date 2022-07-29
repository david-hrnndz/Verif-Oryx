Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

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

Scheme Equality for list.

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

Definition curve448Swap_INV a contents_a sha b contents_b shb c:=
(EX i : Z,
(PROP   (Zlength contents_a = 14;
         Zlength contents_b = 14;
         forall x : Z, In x contents_a -> 0 ≤ x ≤ Int.max_unsigned;
         forall x : Z, In x contents_b -> 0 ≤ x ≤ Int.max_unsigned)
LOCAL   (temp _a a; temp _b b; temp _mask (Vint (Int.repr (((c + 1) mod 2) - 1))))
SEP     ( (* What is the loop invariant? 
                Idea: 
                 If c = 0, then a = a and b = b.
                 If c = 1, then a and b are partially swapped up to index i. *)
<<<<<<< HEAD
         if (Z.eqb c 0) then (
            data_at sha (tarray tuint 14) (map Vint (map Int.repr contents_a)) a
         )
         else  (
            data_at sha (tarray tuint 14) 
            ((sublist.sublist 0 i (map Vint (map Int.repr contents_b)))
            ++ sublist.sublist i 14 (map Vint (map Int.repr contents_a)))
            a
               );
         if (Z.eqb c 0) then (
            data_at shb (tarray tuint 14) (map Vint (map Int.repr contents_b)) b
         )
         else (
            data_at shb (tarray tuint 14) 
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
    entailer!.
    destruct H3;
    rewrite H3; 
    f_equal;
    autorewrite with norm. 
    replace (1 mod 2) with (1) by easy.
    replace (1-1) with (0) by easy.
    unfold Int.add.
    (* Compute (Int.unsigned (Int.not (Int.repr 0)) + Int.unsigned (Int.repr 1)). *)
    replace (Int.unsigned (Int.not (Int.repr 0)) + Int.unsigned (Int.repr 1)) with (2^32) by easy.
    simpl.
    (* Need to make coq understand that 2^32 is 0 here. *)
    admit.
    replace ((1 + 1) mod 2 - 1) with (-1) by easy.
    unfold Int.add.
    replace (Int.unsigned (Int.not (Int.repr 1))) with (4294967294) by easy.
    replace ((4294967294 + Int.unsigned (Int.repr 1))) with (4294967295) by easy.
    (* Need to make coq understand that 2^32-1  is -1 here*)
    (* We are working modulo 2^32 because of C. *)
    admit.
    destruct H3; rewrite H3.
    destruct (_ =? 0) eqn:E.
    entailer!.
    discriminate.
    destruct (1 =? 0) eqn:E; try discriminate.
    autorewrite with sublist.
    cancel.
    hint.
    Intros.
    destruct (c =? 0) eqn:E.
    forward.
    forward.
    forward.
    forward.
    forward.
    forward.
    forward.
    entailer!.
    rewrite Z.eqb_eq in E. 
    rewrite E.
    replace ((0 + 1) mod 2 - 1) with (0) by easy.
    replace ((Int.and (Int.repr 0)
    (Int.xor (Int.repr (Znth i contents_a))
    (Int.repr (Znth i contents_b))))) with (Int.repr 0) by easy.
    assert (data_at sha (tarray tuint 14)
    (upd_Znth i (map Vint (map Int.repr contents_a))
        (Vint (Int.xor (Int.repr (Znth i contents_a)) (Int.repr 0)))) a = data_at sha (tarray tuint 14) (map Vint (map Int.repr contents_a)) a ).
    f_equal.
    unfold Int.xor.
    (* Compute (Int.repr (Z.lxor (Int.unsigned (Int.repr (2^32+1))) (Int.unsigned (Int.repr 0)))). *)
    replace ((Int.repr
    (Z.lxor (Int.unsigned (Int.repr (Znth i contents_a)))
        (Int.unsigned (Int.repr 0))))) with (Int.repr (Znth i contents_a)).
    list_simplify.
    (* Search Z.lxor. *)
    rewrite Z.lxor_0_r.
    remember (Znth i contents_a) as n.
    (* Search (Int.unsigned (Int.repr ( _ ))). *)
    f_equal.
    rewrite (Int.unsigned_repr); try lia.
    assert (In (n) contents_a).
    rewrite Heqn.
    apply Znth_In; lia.
    apply H1; assumption.
    rewrite  H11.

    assert (data_at shb (tarray tuint 14)
    (upd_Znth i (map Vint (map Int.repr contents_b))
        (Vint (Int.xor (Int.repr (Znth i contents_b)) (Int.repr 0)))) b
    = data_at shb (tarray tuint 14) (map Vint (map Int.repr contents_b)) b
    ).
    f_equal.
    unfold Int.xor.
    replace ((Int.repr
    (Z.lxor (Int.unsigned (Int.repr (Znth i contents_b)))
        (Int.unsigned (Int.repr 0))))) with (Int.repr (Znth i contents_b)).
    list_simplify.
    rewrite Z.lxor_0_r.
    remember (Znth i contents_b) as n.
    (* Search (Int.unsigned (Int.repr ( _ ))). *)
    f_equal.
    rewrite (Int.unsigned_repr); try lia.
    assert (In (n) contents_b).
    rewrite Heqn.
    apply Znth_In; lia.
    apply H2; assumption.
    rewrite  H12.
    cancel.

    forward.
    entailer!.
    autorewrite with sublist.
    easy.

    forward.
    entailer!.
    autorewrite with sublist.
    easy.

    forward.
    forward.
    forward.
    forward.
    forward.
    entailer!.
    rewrite Z.eqb_neq in E.
    destruct H3. (* This starts with c = 0, but we had c≠0 so: *)
    contradiction.
    rewrite H3.
    autorewrite with sublist.
    simpl.
    Compute ((Int.repr ((1 + 1) mod 2 - 1))).

    assert (data_at sha (tarray tuint 14)
    (sublist.sublist 0 i (map Vint (map Int.repr contents_b)) ++
        upd_Znth 0 (sublist.sublist i 14 (map Vint (map Int.repr contents_a)))
        (Vint
            (Int.xor (Int.repr (Znth i contents_a))
                (Int.and (Int.repr ((1 + 1) mod 2 - 1))
                (Int.xor (Int.repr (Znth i contents_a))
                    (Int.repr (Znth i contents_b))))))) a
    = data_at sha (tarray tuint 14)
    (sublist.sublist 0 (i + 1) (map Vint (map Int.repr contents_b)) ++
        sublist.sublist (i + 1) 14 (map Vint (map Int.repr contents_a))) a).   
    f_equal.
    (* list_simplify. *)
    (* f_equal. *)
    unfold Int.xor.
    unfold Int.and.
    (* Compute (Int.unsigned (Int.repr ((1 + 1) mod 2 - 1))). *)
    replace (Int.unsigned (Int.repr ((1 + 1) mod 2 - 1))) with 4294967295 by easy.
    admit.
    assert (
        data_at shb (tarray tuint 14)
    (sublist.sublist 0 i (map Vint (map Int.repr contents_a)) ++
    upd_Znth 0 (sublist.sublist i 14 (map Vint (map Int.repr contents_b)))
        (Vint
            (Int.xor (Int.repr (Znth i contents_b))
            (Int.and (Int.repr ((1 + 1) mod 2 - 1))
                (Int.xor (Int.repr (Znth i contents_a)) (Int.repr (Znth i contents_b))))))) b
    = data_at shb (tarray tuint 14)
    (sublist.sublist 0 (i + 1) (map Vint (map Int.repr contents_a)) ++
        sublist.sublist (i + 1) 14 (map Vint (map Int.repr contents_b))) b
    ).
    f_equal.
    unfold Int.xor.
    unfold Int.and.
    replace (Int.unsigned (Int.repr ((1 + 1) mod 2 - 1))) with 4294967295 by easy.   
    admit.
    
    rewrite H14, H15. 
    cancel.

    entailer!.

    destruct (c =? 0);
    autorewrite with sublist.

    cancel.

    cancel.

    Qed.

=======
         data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
         data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b
        )))%assert.

>>>>>>> 6c1af172651adfdb937395e059af52a6acd19906


    (* About Z.lxor. *)
