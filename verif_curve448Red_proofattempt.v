Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import list_int_functions.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.
Require Import list_lemmas.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope Z.

(* curve448Red proof attemp*)

Definition prime: Z := 2^448 - 2^224 - 1.
Definition prime_list : list Z := [-1; -1; -1; -1; -1; -1; -1;
                                   -2; -1; -1; -1; -1; -1; -1].

Definition undef14 := 
       [Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; 
        Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef].

Definition curve448Red_spec : ident * funspec :=
DECLARE _curve448Red
WITH    r : val,
        shr : share,
        a : val,
        contents_a : list Z,
        h : Z, (* may need writable share *)
        gv : globals
PRE [ tptr tuint, tptr tuint, tuint ]
    PROP   (writable_share shr;
            Zlength contents_a = 14;
            0 <= (list_to_int contents_a) < (2 * prime);
            forall x : Z, In x contents_a → x < 2 ^ 32 /\ x mod Int.modulus < 2^32
            (*TODO  * @param[in] h The highest term of A*))
    PARAMS (r ; a ; Vint(Int.repr h)) GLOBALS (gv)
    SEP    (data_at_ shr (tarray tuint 14) r;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a)
POST [ tvoid ]
    PROP   ()
    RETURN ()                               
    SEP    (data_at shr (tarray tuint 14) (* r contains the representation of A mod p *)
   (*cont*)(map Vint (map Int.repr (int_to_list ((list_to_int contents_a) mod prime)))) r ;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a).


Fixpoint allprev_mone_aux (n : nat) (a : list Z) : bool :=
   match n with 
   | O   => true
   | S n' => (Int.eq (Int.repr (Znth (Z.of_nat n') a)) Int.mone) 
            && allprev_mone_aux n' a
   end.
   
Definition allprev_mone (i : Z) (a : list Z) := allprev_mone_aux (Z.to_nat i) a.

            
Definition curve448Red_INV_1    (a : val)  (contents_a : list Z) 
                     (b : val)  (r : val) (shr : share)
                     (h : Z) (gv : globals) 
:= 
    (EX i : Z,
    (PROP   (Zlength contents_a = 14)
    LOCAL   (temp _temp (if allprev_mone i contents_a 
               then Vlong Int64.one else Vlong Int64.zero);
            lvar _b (tarray tuint 14) b; 
            gvars gv; 
            temp _a a; temp _h (Vint (Int.repr h)))
    SEP     ( 
                data_at_ shr (tarray tuint 14) r;
                data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a; 
                data_at Tsh (tarray tuint 14)  
                ((sublist.sublist 0 i (map Vint (map Int.repr (int_to_list ((list_to_int contents_a) - prime)))))
                ++ sublist.sublist i 14 undef14) b
            )))%assert.
                
Definition Gprog : funspecs := ltac:(with_library prog [ curve448Red_spec ]).


Lemma L1 (i : Z) (a : list Z) : 0 <= i -> 
   allprev_mone (i + 1) a = 
   Int.eq (Int.repr (Znth i a)) Int.mone && allprev_mone i a.
Proof.
   intros.
   unfold allprev_mone.
   replace (i + 1) with (Z.succ i) by easy.
   rewrite Z2Nat.inj_succ by apply H.
   assert (i = Z.of_nat (Z.to_nat i)).
      rewrite Z2Nat.id; auto.
   rewrite H0 at 2.
   induction (Z.to_nat i); auto.
Qed.

Lemma L2 :
Int64.add Int64.one (Int64.repr (Int.modulus - 1)) = Int64.repr Int.modulus.
Proof.
   auto.
   Qed.

Lemma L3 (z : Z) : 
0 <= z < Int64.modulus -> Int64.unsigned (Int64.repr z) = z.
Proof.
   intros.
   rewrite Int64.unsigned_repr_eq.
   rewrite Z.mod_small; auto.
Qed.

Lemma  L4' (z : Z): 
Int.eq (Int.repr z) Int.mone = false -> z mod Int.modulus ≠ Int.modulus - 1.
Proof.
   intros.
   apply int_eq_false_e in H.
   unfold "≠".
   intros.
   replace (Int.modulus - 1) with (Int.modulus - 1 mod Int.modulus) in H0.
   assert (Int.repr z = Int.repr (Int.modulus - 1)).
   apply modulo_samerepr.
   apply H0.
   replace (Int.repr (Int.modulus - 1)) with (Int.repr (- 1)) in H1.
   contradiction.
   rewrite modulo_samerepr with (y:= Int.modulus - 1); reflexivity.
   apply Zmod_small with (a := Int.modulus - 1) (n:= Int.modulus).
   easy.
Qed.

Lemma L4 (z : Z) :
Int.eq (Int.repr z) Int.mone = false -> z mod Int.modulus < Int.modulus - 1.
Proof.
   intros. 
   apply int_eq_false_e in H.
   unfold Int.mone in H.
   apply Znot_ge_lt.
   unfold not.
   intros.
   assert (Int.modulus ≠ 0) by easy.
   apply Z.mod_bound_or with (a := z) in H1.
   destruct H1.
   destruct H1.
   assert (z mod Int.modulus <= Int.modulus - 1).
   apply Zlt_succ_le.
   replace (Z.succ (Int.modulus - 1)) with (Int.modulus) by easy.
   assumption.
   assert ( z mod Int.modulus = Int.modulus - 1). 
   apply Z.ge_le in H0.
   apply Z.le_antisymm; assumption.
   replace (Int.modulus - 1) with (- 1 mod Int.modulus) in H4 by easy.
   apply modulo_samerepr in H4.
   contradiction.
   destruct H1.
   assert (Int.modulus < 0).
   apply Z.lt_le_trans with (m:= z mod Int.modulus); assumption.
   discriminate H3. 
   Qed.

Lemma L5 (z : Z) : 0 <= z < two_p 32 ->
   Int64.shru (Int64.repr z) (Int64.repr 32) = Int64.zero.
Proof.
   intros.
   rewrite Int64.shru_div_two_p. 
   assert (Int64.unsigned (Int64.repr z) / two_p (Int64.unsigned (Int64.repr 32)) = 0).
   rewrite Zdiv_small; try easy.
   split.
   destruct H.
   rewrite L3; try easy.
   split; try easy.
   assert ((two_p 32) < Int64.modulus) by easy.
   apply Z.lt_trans with (two_p 32); assumption.
   replace (Int64.unsigned (Int64.repr 32)) with 32 by easy.
   destruct H.
   rewrite L3; try easy.
   split; try easy.
   assert ((two_p 32) < Int64.modulus) by easy.
   apply Z.lt_trans with (two_p 32); assumption.
   rewrite H0. easy.
   Qed. 

   (*****************************)
(* Compute Int64.unsigned (Int64.repr (2^32-1)). *)
(* Search Int.repr (Int64.unsigned(_)). 
Compute (Int.repr (-1)).
Compute Int.mone.
Compute (int_to_list (prime)).
Compute ((prime) - 
list_to_int([2^32+1; 4294967295; 4294967295; 4294967295; 4294967295;
4294967295; 4294967295; 4294967295; 4294967295; 4294967295;
4294967295; 4294967295; 4294967295; 4294967295])). *)

Lemma repr_eq_32_64: forall n:Z, 
   Int.repr (Int64.unsigned (Int64.repr (n))) = Int.repr (Int.unsigned (Int.repr (n))).
Proof.
   intros.
   rewrite Int64.unsigned_repr_eq.
   rewrite Int.unsigned_repr_eq.
   rewrite modulo_samerepr with (y:= n mod Int.modulus); try easy.
   replace (Int64.modulus) with (Int.modulus * Int.modulus) by easy.
   rewrite Zaux.Zmod_mod_mult; try easy.
   symmetry; apply Zmod_mod.    
Qed.   

Lemma L6: forall x : Z,
0 <= x < Int.modulus -> Int64.unsigned (Int64.repr x) = Int.unsigned (Int.repr x).
Proof.
   intros.
   Search (Int64.unsigned _ = Int.unsigned _).
   assert (x = Int.unsigned(Int.repr x)).
   rewrite Int.unsigned_repr_eq.
   Search (_ mod _ = _).
   rewrite Z.mod_small; try lia.
   rewrite H0.
   rewrite Int64.int_unsigned_repr.
   rewrite H0 at 1.
   easy.
Qed.

Lemma L7: 
forall x y,
0 <= x < Int.modulus -> 0 < y <= 32 -> 
(Z.land x (Z.ones y)) mod Int.modulus = Z.land x (Z.ones y).
Proof.
   intros.
   rewrite Z.mod_small; try easy.
   split.
   apply Z.land_nonneg.
   lia. 
   rewrite Z.land_ones; try lia.
   replace (Int.modulus) with (2^32) by easy.
   assert (A1 : x mod 2 ^ y < 2^y).
   apply Z.mod_pos_bound; lia.
   assert (A2 : 2 ^ y <= 2 ^ 32).
   destruct H0.
   apply Z.pow_le_mono_r; try lia.
   apply Z.lt_le_trans with (m:= 2^y); try lia.
Qed.

   (*****************************)

Lemma body_curve448Red : semax_body Vprog Gprog f_curve448Red curve448Red_spec.
Proof.
   start_function.
   forward.
   forward_for_simple_bound 7 
      (curve448Red_INV_1 a contents_a v_b r shr h gv).
   entailer!.
   apply derives_refl.
   repeat forward.
   entailer!.
   rewrite L1 by easy.
   destruct (allprev_mone i contents_a) eqn:E1;
   destruct (Int.eq (Int.repr (Znth i contents_a)) Int.mone) eqn:E2;
   simpl; f_equal; remember (Znth i contents_a) as x.
     apply Int.same_if_eq in E2.
      rewrite E2, Int.unsigned_mone.
      easy.
     unfold Int64.add.
      assert (A : 0 <= x mod Int.modulus < Int64.modulus).
         assert (A0 : 0 < Int.modulus) by easy.
         pose proof (Z.mod_pos_bound x Int.modulus A0); clear A0.
         assert (A0 : Int.modulus < Int64.modulus) by easy.
         destruct H10.
         discriminate H9.
         destruct H11.
         pose proof (Z.lt_trans (x mod Int.modulus) Int.modulus Int64.modulus H13 A0);
         split; try easy.
      rewrite Int64.unsigned_one, L5; try rewrite !Int.unsigned_repr_eq;
         try rewrite L3; try easy. 
      split.
      assert (A0 : 0 < Int.modulus) by easy.
      pose proof (Z.mod_pos_bound x Int.modulus A0); clear A0.
      rewrite (Z.add_nonneg_nonneg 1 (x mod Int.modulus)); easy.
      replace (32 mod Int.modulus) with (32) by easy.
      apply L4 in E2.
      apply Zplus_lt_compat_l with (p := 1) in E2.
      replace (1 + (Int.modulus - 1)) with Int.modulus in E2 by lia.
      replace (two_p 32) with (Int.modulus) by easy; auto.
     apply Int.same_if_eq in E2.
      rewrite E2, Int.unsigned_mone.
      easy.
     rewrite Int64.add_zero_l, !Int.unsigned_repr_eq.
      replace (32 mod Int.modulus) with (32) by easy.
      rewrite L5; auto.
      replace (two_p 32) with (Int.modulus) by easy.
      assert (A0 : 0 < Int.modulus) by easy.
      pose proof (Z.mod_pos_bound x Int.modulus A0); clear A0.
      apply H11.
      (* Prove that if loop inv holds after i then it holds after doing the 
         i+1 iteration. *)
      destruct  (allprev_mone i contents_a) eqn:E.
         (* Case allprev_mone i contents_a = true. Means temp = 1. *)      
         assert ((upd_Znth i
            (sublist.sublist 0 i
               (map Vint
                  (map Int.repr (int_to_list (list_to_int contents_a - prime)))) ++
            sublist.sublist i 14 undef14)
            (force_val
               (sem_cast_l2i I32 Unsigned
                  (force_val
                     (sem_and tulong tuint
                        (force_val
                           (both_long
                              (λ n1 n2 : int64, Some (Vlong (Int64.add n1 n2)))
                              sem_cast_pointer (sem_cast_i2l Unsigned)
                              (Vlong Int64.one)
                              (Vint (Int.repr (Znth i contents_a)))))
                        (Vint (Int.repr (-1)))))))) 
      = (sublist.sublist 0 (i + 1)
               (map Vint
                  (map Int.repr (int_to_list (list_to_int contents_a - prime)))) ++
            sublist.sublist (i + 1) 14 undef14) 
         ) as H_v_b.

      rewrite <- !(sublist_rejoin 0 i (i+1)); try easy.
      rewrite <- app_assoc.   
      rewrite upd_list_app_upper.
      rewrite Zlength_sublist; try easy.
      autorewrite with sublist.  
      rewrite sublist_update_0th_gen; try easy; try lia.
      repeat f_equal.

      rewrite sublist_len_1.
      rewrite Znth_map_Vint_map_Int_repr.
      simpl.   (* simpl works really well here! *)
      f_equal; f_equal. 
      unfold Int64.and.
      rewrite repr_eq_32_64.
      unfold Int64.add.
      rewrite Int64.unsigned_one.
      rewrite Int.unsigned_repr_eq.
      (* rewrite modulo_samerepr with ( y:= (Znth i (int_to_list (list_to_int contents_a - prime)))); try easy. *)
      replace (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr (-1))))) with (Z.ones 32) by easy.
      rewrite Int.unsigned_repr_eq.
      (* replace (i) with (Z.of_nat (Z.to_nat i)) by lia.
      rewrite Znth_int_to_list.
      replace (Z.of_nat (Z.to_nat i)) with i by lia. *)
      rewrite L6. 
      rewrite L6.
      replace (Int.unsigned (Int.repr (Znth i contents_a mod Int.modulus)))
         with (Znth i contents_a mod Int.modulus).
      rewrite L7; try easy; try apply Int.unsigned_range.
      rewrite Z.land_ones; try easy.
      rewrite Int.unsigned_repr_eq.
      replace (Int.modulus) with (2^32) by easy.
      repeat rewrite Z.mod_mod; try easy.   
      replace (2 ^ (32 * i)) with 
         (two_p (Int.unsigned(Int.repr ((32 * i))))).
      replace ((list_to_int contents_a - prime)) with (Int.unsigned (Int.repr ((list_to_int contents_a - prime)))).
      replace (Int.repr
      ((Int.unsigned (Int.repr (list_to_int contents_a - prime)) /
        two_p (Int.unsigned (Int.repr (32 * i)))))) with Int.zero. (*BAD*)
        rewrite <- Int.shru_div_two_p.




      apply modulo_samerepr.
      (* shru_div_two_p
      Search Int.shru.
      two_p_equiv
          *)
      apply H1.
      

      (* HERE *)
      assert ((Znth i contents_a = -1) \/ (Znth i contents_a <> -1)) by
      lia.
      destruct H10; try rewrite H10.
      replace ((Int64.add Int64.one (Int64.repr (Int.unsigned (Int.repr (-1)))))) 
         with (Int64.repr(2^32)) by easy.
      replace ((Int64.and (Int64.repr (2 ^ 32))
      (Int64.repr (Int.unsigned (Int.repr (-1)))))) with (Int64.zero) by easy.
      replace (Int.repr (Int64.unsigned Int64.zero)) with (Int.repr 0) by easy.


      assert (((list_to_int contents_a - prime) / 2 ^ (32 * i)) mod 2 ^ 32= 
         ((list_to_int contents_a) / 2 ^ (32 * i)) mod 2 ^ 32
            -((prime) / 2 ^ (32 * i)) mod 2 ^ 32).

      simpl.
      Search (_ - _ mod _).
      
      rewrite eq_dec.
      assert (Int64.and
      (Int64.add Int64.one
         (Int64.repr (Int.unsigned (Int.repr (Znth i contents_a)))))
      (Int64.repr (Int.unsigned (Int.repr (-1)))) = 
      Int64.repr( Int64.intval (Int64.and
            (Int64.add Int64.one 
               (Int64.repr (Int.unsigned (Int.repr (Znth i contents_a)))))
            (Int64.repr (Int.unsigned (Int.repr (-1))))))).
      
      unfold Int64.and.
      
      

      (*****************************)

      admit.
         
      autorewrite with sublist; rewrite int_to_list_length; lia.
      autorewrite with sublist; rewrite int_to_list_length; lia.
      
      rewrite Zlength_sublist; try lia.
      autorewrite with sublist; rewrite int_to_list_length; lia.
      autorewrite with sublist; rewrite int_to_list_length; lia.

      rewrite H_v_b; cancel.
      
      assert(upd_Znth i
      (sublist.sublist 0 i (map Vint (map Int.repr (int_to_list (list_to_int contents_a mod prime)))) ++
         sublist.sublist i 14 undef14)
      (force_val
         (sem_cast_l2i I32 Unsigned
            (force_val
               (sem_and tulong tuint
                  (force_val
                     (both_long (λ n1 n2 : int64, Some (Vlong (Int64.add n1 n2))) sem_cast_pointer
                        (sem_cast_i2l Unsigned) (Vlong Int64.zero) (Vint (Int.repr (Znth i contents_a)))))
                  (Vint (Int.repr (-1))))))) 
         = sublist.sublist 0 (i + 1) (map Vint (map Int.repr (int_to_list (list_to_int contents_a mod prime)))) ++
         sublist.sublist (i + 1) 14 undef14).
         
      rewrite <- !(sublist_rejoin 0 i (i+1)); try easy.
      rewrite <- app_assoc.   
      rewrite upd_list_app_upper.
      rewrite Zlength_sublist; try easy.
      autorewrite with sublist.  
      rewrite sublist_update_0th_gen; try easy; try lia.
      rewrite sublist_len_1.
      repeat f_equal.
      simpl.

      Compute (Int64.repr (Int.unsigned (Int.repr (-1)))).
      Compute (Int64.repr (2^32-1)).
         (*****************************)

      (* Need to show that (int_to_list list_to_int) combo preserves length. *)


   (* I proved (modulo the lemmas L1--L5) the part that the contents of
   * temp is as defined in the loop invariant.
   * The part that the contents of b are as in the loop invariant is ugly. 
   * One need to prove that whatever its been done
   * in the code with the temp is does indeed the least significant 7 limbs
   * of B = A - (2^448 - 2^224 - 1). A Lemma (or several) are needed.
   *)



      
      
      