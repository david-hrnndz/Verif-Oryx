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

Definition prime: Z := 2^448 - 2^224 - 1.

Definition undef14 :=
       [Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef;
        Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef].

(* Functions to compute added lists. *)
Definition is_big (n : Z) (a : list Z) (b : Z) := 
   if (n =? 0) 
      then Znth n a + b >=? Int.modulus
      else Int.eq (Int.repr (Znth n a)) Int.mone.

Fixpoint allprev_big_aux (n : nat) (a : list Z) (b : Z) : bool :=
   match n with 
   | O   => true
   | S n' => is_big (Z.of_nat n') a b
            && allprev_big_aux n' a b
   end.
   
Definition allprev_big (i b : Z) (a : list Z) :=
   allprev_big_aux (Z.to_nat i) a b.

Definition allprev_big_compute (i b : Z) (a : list Z) :=
   if (i =? 0) then Vlong (Int64.repr b)
   else if (allprev_big i b a) 
                        then Vlong Int64.one
                        else Vlong Int64.zero.

Fixpoint added_list_aux (n : nat) (b : Z) (a : list Z):=
   match n with 
   | O    => [(Znth (Z.of_nat n) a) + b]
   | S n' => added_list_aux n' b a ++
             [(Znth (Z.of_nat (S n')) a) 
             + (if (allprev_big (Z.of_nat (S n')) b a) then 1 else 0) mod Int.modulus]
   end.

Definition added_list (a : list Z) (b : Z):=
   added_list_aux 13 b a.
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
(* %%%%%%%%%%%%% Lemmas about added_lists %%%%%%%%%%%%% *)
Lemma zlength_added_list: 
forall a: list Z, forall b : Z,
Zlength (added_list a b) = 14.
Proof.
   intros.
   unfold added_list.
   unfold added_list_aux.
   list_solve.
Qed.

Lemma znth_added_list:
forall i:nat, forall b: Z, forall a : list Z, 
0 < (Z.of_nat i) < Zlength (added_list a b) -> 
Znth (Z.of_nat i) (added_list a b) = 
         Znth (Z.of_nat i) a +
         (if allprev_big (Z.of_nat i) b a then 1 else 0) mod Int.modulus.
Proof. (* By manual induction for now. *)
   intros.
   destruct i.
   destruct H; discriminate H. 
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia. 
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia.  
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia. 
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia. 
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia.
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia.
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia.
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia.
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia.
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia.
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia.
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia.
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia.
   destruct i. unfold added_list; unfold added_list_aux; list_solve;
   replace (Z.of_nat (S i)) with ((Z.of_nat i)+1) in * by lia.
   rewrite zlength_added_list in H.
   assert (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S i))))))))))))) + 1 >= 14) by lia.
   destruct H.
   lia.
Qed.
   
Lemma allprev_big_unfoldable :
   forall (i b : Z) (a : list Z),
   0 <= i -> 
   0 <= b < 2^32-1 ->
   allprev_big (i + 1) b a = 
   is_big i a b && allprev_big i b a.
Proof.
   intros.
   unfold allprev_big.
   replace (i + 1) with (Z.succ i) by easy.
   rewrite Z2Nat.inj_succ by apply H.
   assert (i = Z.of_nat (Z.to_nat i)) by
      ((rewrite Z2Nat.id; auto)).
   rewrite H1 at 2.
   induction (Z.to_nat i); auto.
Qed.
(* %%%%%%%%%%%%% General Lemmas %%%%%%%%%%%%% *) 
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

Lemma int64_shru_small (z : Z) : 0 <= z < two_p 32 ->
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

Lemma div_eucl_by_hand: forall a b q r: Z,
0 < b -> 
0 <= r < b -> 
a = q * b + r -> 
Z.div_eucl a b = (q, r).
Proof.
    intros.
    rewrite Zaux.Zdiv_eucl_unique.
    rewrite H1 at 1.
    rewrite Z.div_add_l; try lia.
    rewrite Z.div_small; try lia.
    rewrite H1.
    rewrite Z.add_mod; try lia.
    rewrite Z.mod_mul; try lia.
    (* assert ((0 + r mod b) mod b = r). *)
    replace (0 + r mod b) with (r mod b) by lia.
    rewrite Z.mod_mod; try lia.
    rewrite Z.mod_small; try lia.
    replace (q + 0) with (q) by lia.
    reflexivity.
Qed.

Lemma  div_bound_double: forall n z : Z,
0 < n -> 
n <= z < 2 * n -> 
z / n = 1.
Proof.
    intros.
    unfold "/".
    assert (Z.div_eucl z (n) = (1, z-n)). 
    assert (z = n + (z - n)) by lia.
    rewrite div_eucl_by_hand with (q:= 1) (r:= z - n); try lia.
    reflexivity.
    rewrite H1.
    reflexivity.
Qed.

Lemma int64_shru_big (z : Z) : two_p 32 <= z < two_p 33 ->
   Int64.shru (Int64.repr z) (Int64.repr 32) = Int64.one.
Proof.
    intros.
    rewrite Int64.shru_div_two_p.
    replace (Int64.unsigned (Int64.repr 32)) with 32 by easy. 
    rewrite L3.
    assert (z / two_p 32 = 1).
    apply div_bound_double; try easy.
    rewrite H0; easy.
    destruct H.
    split.
    assert (0 <= two_p 32) by easy.
    lia.  
    assert (two_p 33 < Int64.modulus) by easy.
    lia.
Qed. 

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
   assert (x = Int.unsigned(Int.repr x)).
   rewrite Int.unsigned_repr_eq.
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

Lemma lt_max_unsigned_iff_le_mod: forall x : Z,
x <= Int.max_unsigned <-> x < Int.modulus.
Proof.
   replace Int.max_unsigned with (2^32-1) by easy.
   replace Int.modulus with (2^32) by easy.
   lia.
Qed.

(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
Definition curve448AddInt_spec : ident * funspec :=
DECLARE _curve448AddInt
WITH    r : val,
        shr : share,
        a : val,
        contents_a : list Z,
        b : Z,
        gv : globals
PRE [ tptr tuint, tptr tuint, tuint]
    PROP   (writable_share shr;
            Zlength contents_a = 14;
            0 <= (list_to_int contents_a) < prime; 0 <= b < 2^32 - 1;
            forall x : Z, In x contents_a → 0 <= x < 2 ^ 32 /\ x mod Int.modulus < 2^32)
    PARAMS (r ; a ; Vint (Int.repr b)) GLOBALS (gv)
    SEP    (data_at_ shr (tarray tuint 14) r;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a)
POST [ tvoid ]
    PROP   ()
    RETURN ()
    SEP    (data_at shr (tarray tuint 14) (* r contains the representation of A + B mod p *)
   (*cont*)(map Vint (map Int.repr (int_to_list (((list_to_int contents_a) + (b)) mod prime)))) r ;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a ).

Definition curve448AddInt_INV  (a : val)  (contents_a : list Z)
                            (b : Z)
                            (r : val) (shr : share) (gv : globals) :=
    (EX i : Z,
    (PROP   (Zlength contents_a = 14)
    (* ;t = (Int64.repr b) \/ t = Int64.one \/ t = Int64.zero) *)
    LOCAL   (temp _a a; temp _r r;
            temp _temp (allprev_big_compute i b contents_a);
            gvars gv)
    SEP     (
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
            data_at shr (tarray tuint 14)
            (
               (sublist.sublist 0 i (map Vint (map Int.repr (added_list contents_a b))))
               ++ (sublist.sublist i 14 undef14)
            )
            r)
    ))%assert.

Definition Gprog : funspecs := ltac:(with_library prog [ curve448AddInt_spec ])(*add red here*).

Lemma body_curve448AddInt : semax_body Vprog Gprog f_curve448AddInt curve448AddInt_spec.
Proof.
   start_function.
   forward.
   forward_for_simple_bound 14
   (curve448AddInt_INV a contents_a b r shr gv).
   entailer!.
   easy.
   repeat forward.
   entailer!.
   assert (a_i_bound : 0 <= Znth i contents_a < 2^32).
      apply H2; apply Znth_In; lia.
   unfold allprev_big_compute.
   rewrite allprev_big_unfoldable by lia.
   destruct (allprev_big i b contents_a) eqn : E_prev;
   destruct (i+1 =? 0) eqn : E_succ;
   destruct (i =? 0) eqn : E_i;
   simpl; try lia; try rewrite andb_true_r; try rewrite andb_false_r;
   try rewrite Z.eqb_eq in *; try rewrite Z.eqb_neq in *;
   try rewrite E_i in *.
   unfold is_big; simpl.

   unfold Int64.add.
   assert (b_bound : 0 <= b < Int.modulus);
   replace Int.modulus with (2^32) by easy; try lia.
   repeat rewrite L6; try easy; try apply Int.unsigned_range.
   repeat rewrite Int.unsigned_repr; try easy; 
   try (replace Int.max_unsigned with (2^32-1) by easy); try lia.
   destruct (Znth 0 contents_a + b >=? 2^32) eqn : a_geq_b; simpl.
   rewrite Z.geb_le in a_geq_b.
   rewrite int64_shru_big; auto.
   split; rewrite two_p_equiv; try lia.
   rewrite int64_shru_small; auto.
   split; try rewrite two_p_equiv; try lia.

   unfold is_big. 
   assert (i_not0: i=?0 = false) by lia; rewrite i_not0.
   unfold Int64.add. 
   destruct (Int.eq (Int.repr (Znth i contents_a)) Int.mone) eqn: aimone.
   apply Int.same_if_eq in aimone.
   unfold Int.mone in aimone.
   rewrite aimone.
   replace (Int.unsigned (Int.repr (-1))) with (2^32 -1) by easy.
   repeat rewrite Int64.unsigned_repr; try easy.
   
   apply L4 in aimone.
   rewrite int64_shru_small; auto.
   split; try lia.
      apply Z.add_nonneg_nonneg;
      apply Int64.unsigned_range.
      rewrite two_p_equiv.
      unfold Int64.one.
      repeat rewrite Int64.unsigned_repr; try easy.
      rewrite Int.unsigned_repr_eq.
      replace (Int.modulus) with (2^32) in aimone at 2 by easy.
      lia.
      split; try apply Int.unsigned_range.
      rewrite Int.unsigned_repr_eq.
      assert (Int.modulus - 1 < Int64.max_unsigned) by easy;
      lia.

   discriminate E_prev.

   rewrite Int64.add_zero_l.
      rewrite int64_shru_small; auto.
      rewrite two_p_equiv. 
      rewrite Int.unsigned_repr; auto.
      replace (Int.max_unsigned) with (2^32-1); try easy; try lia.

   (* Prove that if loop inv holds after i then it holds after doing the 
      i+1 iteration. *)
   assert (a_i_bound : 0 <= Znth i contents_a < 2^32).
      apply H2; apply Znth_In; lia.
   assert (b_bound : 0 <= b < Int.modulus).
      replace Int.modulus with (2^32) by easy; try lia.
   assert (b_64bound : 0 <= b <= Int64.max_unsigned). 
      split; try easy;
      assert (2^32-1 < Int64.max_unsigned) by easy; lia.
   assert (data_at_r : (upd_Znth i
   (sublist.sublist 0 i (map Vint (map Int.repr (added_list contents_a b))) ++
    sublist.sublist i 14 undef14)
   (force_val
      (sem_cast_l2i I32 Unsigned
         (force_val
            (sem_and tulong tuint
               (force_val
                  (both_long (λ n1 n2 : int64, Some (Vlong (Int64.add n1 n2)))
                     sem_cast_pointer (sem_cast_i2l Unsigned)
                     (allprev_big_compute i b contents_a)
                     (Vint (Int.repr (Znth i contents_a))))) (Vint (Int.repr (-1))))))))
   =
   (sublist.sublist 0 (i + 1) (map Vint (map Int.repr (added_list contents_a b))) ++
       sublist.sublist (i + 1) 14 undef14)).

   rewrite <- !(sublist_rejoin 0 i (i+1)); try easy.
   rewrite <- app_assoc.   
   rewrite upd_list_app_upper.
   assert (len_sublist : Zlength (sublist.sublist 0 i (map Vint (map Int.repr (added_list contents_a b)))) = i).
   rewrite calc_Zlength_sublist with (len := 14); try easy; try lia.
   rewrite len_sublist; autorewrite with sublist.
   rewrite sublist_update_0th_gen; try easy; try lia.
   rewrite sublist_len_1.
   repeat f_equal.
   autorewrite with sublist.
   unfold allprev_big_compute.

   destruct (i=?0) eqn: i_0.
   rewrite Z.eqb_eq in i_0; rewrite i_0 in *.
   unfold added_list.
   unfold added_list_aux.
   autorewrite with sublist.
   simpl.
   f_equal.
   unfold Int64.and.
   replace (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr (-1))))) 
      with (Z.ones 32) by easy.
   rewrite Z.land_ones by easy.
   rewrite L6.
   rewrite Int.unsigned_repr.
   unfold Int64.add.
   rewrite Int64.int_unsigned_repr.
   rewrite Int.unsigned_repr.
   rewrite Int64.unsigned_repr.
   rewrite Int64.unsigned_repr.
   apply modulo_samerepr.
   replace (Z.of_nat 0) with 0 by easy.
   replace (2^32) with Int.modulus by easy.
   rewrite Z.mod_mod by easy.
   rewrite Z.add_comm; lia.
   lia.
   rewrite Int64.unsigned_repr by lia.
   split.
   apply Z.add_nonneg_nonneg; try easy.
   assert (Int.modulus + 2^32 < Int64.max_unsigned) by easy; lia.
   replace Int.max_unsigned with (2^32-1) by easy. lia.
   split.
   apply Z.mod_bound_pos; try easy.
   apply Int64.unsigned_range.
   apply lt_max_unsigned_iff_le_mod.
   apply Z.mod_bound_pos; try easy; try apply Int64.unsigned_range.
   split.
   apply Z.mod_bound_pos; try easy.
   apply Int64.unsigned_range.
   apply Z.mod_bound_pos; try easy; try apply Int64.unsigned_range.

   rewrite Z.eqb_neq in i_0.
   
   replace (i) with (Z.of_nat (Z.to_nat i)) at 3 by lia.
   rewrite znth_added_list.
   replace (Z.of_nat (Z.to_nat i)) with i by lia.
   destruct (allprev_big i b contents_a) eqn: E_prev; simpl.
   unfold Int64.and.
   replace (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr (-1))))) 
      with (Z.ones 32) by easy.
   rewrite Z.land_ones by easy.
   rewrite L6.
   rewrite Int.unsigned_repr_eq.
   unfold Int64.add.
   rewrite Int64.int_unsigned_repr.
   rewrite Int.unsigned_repr.
   rewrite Int64.unsigned_repr.
   unfold Int64.one.
   rewrite Int64.unsigned_repr by easy.
   f_equal.
   apply modulo_samerepr.
   rewrite Z.mod_mod by easy.
   replace (2^32) with (Int.modulus) by easy.
   rewrite Z.mod_mod by easy.
   rewrite Z.add_comm.
   easy.
      replace (Int64.unsigned Int64.one) with (1) by easy.
      replace (Int64.max_unsigned) with (2^64-1) by easy; lia.
      rewrite lt_max_unsigned_iff_le_mod. easy.
      apply Z.mod_bound_pos; try easy; try apply Int64.unsigned_range.

   unfold Int64.and.
   replace (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr (-1))))) 
      with (Z.ones 32) by easy.
   rewrite Z.land_ones by easy.
   rewrite L6.
   rewrite Int.unsigned_repr_eq.
   rewrite Int64.add_zero_l.
   rewrite Int64.int_unsigned_repr.
   rewrite Int.unsigned_repr.
   f_equal.
   autorewrite with norm.
   rewrite Z.mod_mod by easy.
   rewrite modulo_samerepr with (y:=Znth i contents_a); auto.
   rewrite Z.mod_mod by easy.
   lia.
      rewrite lt_max_unsigned_iff_le_mod; easy.
      apply Z.mod_bound_pos; try easy; try apply Int64.unsigned_range.
      replace (Z.of_nat (Z.to_nat i)) with i; try lia.
      rewrite zlength_added_list; lia.
      autorewrite with sublist.
      rewrite zlength_added_list; lia.
      rewrite Zlength_sublist; try lia.
      autorewrite with sublist.
      rewrite zlength_added_list; lia.
      autorewrite with sublist.
      rewrite zlength_added_list; lia.
   
   rewrite data_at_r.
   cancel.


(* After verifying curve448Red, add it to Gprog and then perform 
   forward_call with it. *)
   




   
   


(* void curve448AddInt(uint32_t *r, const uint32_t *a, uint32_t b)
{
uint_t i;
uint64_t temp;

//Compute R = A + B
temp = b; 
for(i = 0; i < 14; i++)
{
   temp += a[i];
   r[i] = temp & 0xFFFFFFFF;
   temp >>= 32;
}

//Perform modular reduction
curve448Red(r, r, (uint32_t) temp);
} *)

(* Loop Analysis {
temp starts being b. Then it will either be 1 or 0.
If temp = b and we are inside the loop then i = 0.
   temp = b -> i = 0.
If temp = 1 then
   - temp + a[i] >= 2^32
   which can only happen if:
   - b + a[0] >= 2^32
   - temp = 1 and a[i] = -1
}*)