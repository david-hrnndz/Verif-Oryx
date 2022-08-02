Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import list_int_functions.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope Z.


Definition prime: Z := 2^448 - 2^224 - 1.
 
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
            0 <= (list_to_int contents_a) < (2 * prime)
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
                ((sublist.sublist 0 i (map Vint (map Int.repr (int_to_list ((list_to_int contents_a) mod prime)))))
                ++ sublist.sublist i 14 undef14)
             b
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

Lemma L4 (z : Z) :
Int.eq (Int.repr z) Int.mone = false -> z mod Int.modulus < Int.modulus - 1.
Proof.
   Admitted.

Lemma L5 (z n : Z) : 0 <= z < two_p n ->
   Int64.shru (Int64.repr z) (Int64.repr n) = Int64.zero.
Proof.
Admitted.

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
   -  apply Int.same_if_eq in E2.
      rewrite E2, Int.unsigned_mone.
      rewrite L2.
      rewrite Int64.shru_div_two_p, Int.unsigned_repr_eq.
      replace (32 mod Int.modulus) with (32) by easy.
      rewrite !Int64.unsigned_repr_eq.
      replace (Int.modulus mod Int64.modulus) with (Int.modulus) by easy.
      replace (32 mod Int64.modulus) with (32) by easy.
      replace (Int.modulus / two_p 32) with 1 by easy; auto.
   -  unfold Int64.add.
      assert (A : 0 <= x mod Int.modulus < Int64.modulus).
         assert (A0 : 0 < Int.modulus) by easy.
         pose proof (Z.mod_pos_bound x Int.modulus A0); clear A0.
         assert (A0 : Int.modulus < Int64.modulus) by easy.
         destruct H10.
         pose proof (Z.lt_trans (x mod Int.modulus) Int.modulus Int64.modulus H11 A0);
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
   -  apply Int.same_if_eq in E2.
      rewrite E2, Int.unsigned_mone.
      rewrite Int64.add_zero_l, !Int.unsigned_repr_eq.
      replace (32 mod Int.modulus) with (32) by easy.
      rewrite L5; auto.
      split; try easy.
   -  rewrite Int64.add_zero_l, !Int.unsigned_repr_eq.
      replace (32 mod Int.modulus) with (32) by easy.
      rewrite L5; auto.
      replace (two_p 32) with (Int.modulus) by easy.
      assert (A0 : 0 < Int.modulus) by easy.
      pose proof (Z.mod_pos_bound x Int.modulus A0); clear A0.
      apply H10.
   -  destruct  (allprev_mone i contents_a) eqn:E.
      autorewrite with sublist in *|-.
      hint.
(* I proved (modulo the lemmas L1--L5) the part that the contents of
 * temp is as defined in the loop invariant.
 * The part that the contents of b are as in the loop invariant is ugly. 
 * One need to prove that whatever its been done
 * in the code with the temp is does indeed the least significant 7 limbs
 * of B = A - (2^448 - 2^224 - 1). A Lemma (or several) are needed.
 *)



   
   
   